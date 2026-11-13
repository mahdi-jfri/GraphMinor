module

public import GraphMinor.LRPlanarity.SearchInvariants

/-!
# Correctness of the explicit-frame depth-first search

This file proves `SearchStatement` and `SearchRecordsStatement` from
`GraphMinor/LRPlanarity/Statements.lean`, following Part I, Section 1 of
`docs/planarity/planarity_test.tex`.
-/

@[expose] public section

namespace GraphMinor.LRPlanarity

open Classical

/-! ### Helper lemmas for step transitions -/

private theorem getElem!_mem_of_lt {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    l[k]! ∈ l := by
  rw [getElem!_pos l k hk]
  exact List.getElem_mem hk

private theorem isChain_imp_of_mem {α : Type*} {R S : α → α → Prop} {l : List α}
    (h : l.IsChain R) (himp : ∀ x ∈ l, ∀ y ∈ l, R x y → S x y) :
    l.IsChain S := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton a
    | cons b tail =>
      rw [List.isChain_cons_cons] at h ⊢
      refine ⟨himp a (by simp) b (by simp) h.1, ih h.2 (fun x hx y hy => ?_)⟩
      exact himp x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)

theorem DFSInv.not_edge_current {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (hAdj : Compute.IsAdjListFamily G lists)
    (h : DFSInv N G lists s (f :: rest))
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    {i : ℕ} (hi : i < s.edges.size) :
    ¬ ((s.edges[i]!).source = f.vertex ∧
        (s.edges[i]!).target = ((List.ofFn lists).toArray[f.vertex]!)[f.next]!) := by
  rintro ⟨hsrc, htgt⟩
  have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
  obtain ⟨_, _, _, _, ⟨k, hsc, hk⟩, _⟩ := h.edges_valid i hi
  rw [hsrc] at hsc hk
  have hk_lt : k < ((List.ofFn lists).toArray[f.vertex]!).length := hsc.2.1
  have heq_elem :
      ((List.ofFn lists).toArray[f.vertex]!)[k] =
        ((List.ofFn lists).toArray[f.vertex]!)[f.next] := by
    rw [← getElem!_pos _ k hk_lt, ← getElem!_pos _ f.next hlen, hk, htgt]
  have hnodup := adj_nodup hAdj hf_lt
  have hkeq : k = f.next := (List.Nodup.getElem_inj_iff hnodup).mp heq_elem
  subst hkeq
  exact not_scanned_current h hsc

theorem DFSInv.not_parent_current {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (hAdj : Compute.IsAdjListFamily G lists)
    (h : DFSInv N G lists s (f :: rest))
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length) :
    let w := ((List.ofFn lists).toArray[f.vertex]!)[f.next]!
    s.parent[w]?.join ≠ some f.vertex := by
  intro w hpar
  have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
  have hw_mem : w ∈ (List.ofFn lists).toArray[f.vertex]! := getElem!_mem_of_lt hlen
  have hw_lt : w < N := adj_mem_lt hAdj hf_lt hw_mem
  obtain ⟨i, hi, _, hsrc, htgt⟩ := (h.parent_iff_edge w hw_lt f.vertex).mp hpar
  exact h.not_edge_current hAdj hlen hi ⟨hsrc, htgt⟩

theorem DFSInv.scanned_visited_both {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack)
    {v k : ℕ} (hsc : Scanned N lists s stack v k) :
    s.Visited v ∧ s.Visited (((List.ofFn lists).toArray[v]!)[k]!) := by
  refine ⟨?_, h.scanned_visited v k hsc⟩
  rcases hsc with ⟨_, _, hpost | ⟨g, hg, rfl, _⟩⟩
  · exact (h.visited_iff v).mpr (Or.inr hpost)
  · exact (h.visited_iff g.vertex).mpr (Or.inl (List.mem_map_of_mem hg))

/-! ### Step 1: Pop frame when `f.next ≥ neighbors.length` -/

theorem DFSInv.step_pop {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (h : DFSInv N G lists s (f :: rest))
    (hge : ((List.ofFn lists).toArray[f.vertex]!).length ≤ f.next) :
    let s₁ : Search := { s with postorder := f.vertex :: s.postorder }
    let s₂ : Search := match s₁.parentEdge[f.vertex]?.join with
      | none => s₁
      | some p => GraphMinor.LRPlanarity.finishEdge s₁ p
    DFSInv N G lists s₂ rest := by
  intro s₁ s₂
  suffices h₁ : DFSInv N G lists s₁ rest by
    dsimp only [s₂]
    split
    · exact h₁
    · next p _ => exact h₁.finishEdge p
  have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
  have hsc_iff : ∀ u k, Scanned N lists s₁ rest u k ↔ Scanned N lists s (f :: rest) u k :=
    scanned_pop_iff rfl hge
  have hnodup_orig := h.nodup_verts
  simp only [List.map_cons, List.cons_append] at hnodup_orig
  have hperm :
      (rest.map Frame.vertex ++ (f.vertex :: s.postorder)).Perm
        (f.vertex :: (rest.map Frame.vertex ++ s.postorder)) :=
    List.perm_middle
  have hnodup_new : (rest.map Frame.vertex ++ s₁.postorder).Nodup :=
    hperm.nodup_iff.mpr hnodup_orig
  have hf_not_post : f.vertex ∉ s.postorder := by
    rw [List.nodup_cons, List.mem_append] at hnodup_orig
    exact fun hm => hnodup_orig.1 (Or.inr hm)
  refine
    { depth_size := h.depth_size
      parent_size := h.parent_size
      parentEdge_size := h.parentEdge_size
      active_lt := fun v hv => h.active_lt v (List.mem_cons_of_mem f.vertex hv)
      postorder_lt := fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hf_lt
        · exact h.postorder_lt v hv'
      nodup_verts := hnodup_new
      frame_next_le := fun g hg => h.frame_next_le g (List.mem_cons_of_mem f hg)
      visited_iff := fun v => by
        rw [Search.Visited, show s₁.depth = s.depth from rfl, ← Search.Visited, h.visited_iff]
        simp [s₁, or_assoc, or_left_comm]
      unvisited_none := h.unvisited_none
      root_depth := h.root_depth
      parent_spec := fun v u hp => by
        obtain ⟨hu, hvv, huv, hadj, hd, k, hsc, hk⟩ := h.parent_spec v u hp
        exact ⟨hu, hvv, huv, hadj, hd, k, (hsc_iff u k).mpr hsc, hk⟩
      stack_chain := h.stack_chain.tail
      active_parent_mem := fun v hv u hp => by
        have hum := h.active_parent_mem v (List.mem_cons_of_mem f.vertex hv) u hp
        rcases List.mem_cons.mp hum with rfl | hum'
        · exact absurd hp (h.not_parent_of_mem_stack_tail hv)
        · exact hum'
      postorder_order := by
        dsimp only [s₁]
        rw [List.pairwise_cons]
        refine ⟨fun w hw hpar => ?_, h.postorder_order⟩
        have hwm := h.active_parent_mem f.vertex (by simp) w hpar
        rw [List.nodup_cons, List.mem_append] at hnodup_orig
        rcases List.mem_cons.mp hwm with rfl | hwm'
        · exact hf_not_post hw
        · have hdisj := (List.nodup_append.mp hnodup_orig.2).2.2
          exact hdisj w hwm' w hw rfl
      scanned_visited := fun v k hsc => h.scanned_visited v k ((hsc_iff v k).mp hsc)
      completed_adj := fun u v hu hadj => by
        rcases List.mem_cons.mp hu with hu_eq | hu_old
        · have huf : u = ⟨f.vertex, hf_lt⟩ := Fin.ext hu_eq
          subst huf
          refine ⟨fun hv_act => ?_, fun hv_post => ?_⟩
          · exact h.ancestor_of_mem_stack_tail hv_act v.2 hf_lt
          · rcases List.mem_cons.mp hv_post with hv_eq | hv_old
            · have hvf : v = ⟨f.vertex, hf_lt⟩ := Fin.ext hv_eq
              subst hvf
              exact Or.inl (Forest.Ancestor.refl _ _)
            · exact Or.inl ((h.completed_adj v ⟨f.vertex, hf_lt⟩ hv_old hadj.symm).1 (by simp))
        · refine ⟨fun hv_act => ?_, fun hv_post => ?_⟩
          · exact (h.completed_adj u v hu_old hadj).1 (List.mem_cons_of_mem f.vertex hv_act)
          · rcases List.mem_cons.mp hv_post with hv_eq | hv_old
            · exact Or.inr ((h.completed_adj u v hu_old hadj).1 (by simp [hv_eq]))
            · exact (h.completed_adj u v hu_old hadj).2 hv_old
      edges_valid := fun i hi => by
        obtain ⟨hs, ht, hvs, hvt, ⟨k, hsc, hk⟩, htree⟩ := h.edges_valid i hi
        exact ⟨hs, ht, hvs, hvt, ⟨k, (hsc_iff _ k).mpr hsc, hk⟩, htree⟩
      parentEdge_iff := h.parentEdge_iff
      parent_iff_edge := h.parent_iff_edge
      edges_inj := h.edges_inj
      scanned_edge_exists := fun v k hsc hv hw hcond =>
        h.scanned_edge_exists v k ((hsc_iff v k).mp hsc) hv hw hcond }

/-! ### Step 2: Skip already-visited neighbor -/

theorem DFSInv.step_skip {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (hAdj : Compute.IsAdjListFamily G lists)
    (h : DFSInv N G lists s (f :: rest))
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (hw_vis : s.Visited (((List.ofFn lists).toArray[f.vertex]!)[f.next]!))
    (hskip : ¬ (s.parent[f.vertex]?.join ≠
        some (((List.ofFn lists).toArray[f.vertex]!)[f.next]!) ∧
      (s.depth[(((List.ofFn lists).toArray[f.vertex]!)[f.next]!)]?.join).getD 0 <
        (s.depth[f.vertex]?.join).getD 0)) :
    DFSInv N G lists s ({ f with next := f.next + 1 } :: rest) := by
  have hsc_iff := scanned_step_iff h rfl hlen
  refine
    { depth_size := h.depth_size
      parent_size := h.parent_size
      parentEdge_size := h.parentEdge_size
      active_lt := h.active_lt
      postorder_lt := h.postorder_lt
      nodup_verts := h.nodup_verts
      frame_next_le := fun g hg => by
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact Nat.succ_le_of_lt hlen
        · exact h.frame_next_le g (List.mem_cons_of_mem f hg')
      visited_iff := h.visited_iff
      unvisited_none := h.unvisited_none
      root_depth := h.root_depth
      parent_spec := fun v u hp => by
        obtain ⟨hu, hvv, huv, hadj, hd, k, hsc, hk⟩ := h.parent_spec v u hp
        exact ⟨hu, hvv, huv, hadj, hd, k, (hsc_iff u k).mpr (Or.inr hsc), hk⟩
      stack_chain := by
        cases rest with
        | nil => exact List.isChain_singleton _
        | cons g rest' =>
          have hch := h.stack_chain
          rw [List.isChain_cons_cons] at hch ⊢
          exact hch
      active_parent_mem := h.active_parent_mem
      postorder_order := h.postorder_order
      scanned_visited := fun v k hsc => by
        rcases (hsc_iff v k).mp hsc with ⟨rfl, rfl⟩ | hsc_old
        · exact hw_vis
        · exact h.scanned_visited v k hsc_old
      completed_adj := h.completed_adj
      edges_valid := fun i hi => by
        obtain ⟨hs, ht, hvs, hvt, ⟨k, hsc, hk⟩, htree⟩ := h.edges_valid i hi
        exact ⟨hs, ht, hvs, hvt, ⟨k, (hsc_iff _ k).mpr (Or.inr hsc), hk⟩, htree⟩
      parentEdge_iff := h.parentEdge_iff
      parent_iff_edge := h.parent_iff_edge
      edges_inj := h.edges_inj
      scanned_edge_exists := fun v k hsc hv hw hcond => by
        rcases (hsc_iff v k).mp hsc with ⟨rfl, rfl⟩ | hsc_old
        · exfalso
          rcases hcond with hpar | hback
          · exact h.not_parent_current hAdj hlen hpar
          · exact hskip hback
        · exact h.scanned_edge_exists v k hsc_old hv hw hcond }

/-! ### Step 3: Add back edge -/

theorem DFSInv.step_back {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (hAdj : Compute.IsAdjListFamily G lists)
    (h : DFSInv N G lists s (f :: rest))
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (hw_vis : s.Visited (((List.ofFn lists).toArray[f.vertex]!)[f.next]!))
    (hback : s.parent[f.vertex]?.join ≠
        some (((List.ofFn lists).toArray[f.vertex]!)[f.next]!) ∧
      (s.depth[(((List.ofFn lists).toArray[f.vertex]!)[f.next]!)]?.join).getD 0 <
        (s.depth[f.vertex]?.join).getD 0) :
    let w := ((List.ofFn lists).toArray[f.vertex]!)[f.next]!
    let p := addEdge s f.vertex w false
    DFSInv N G lists (GraphMinor.LRPlanarity.finishEdge p.1 p.2)
      ({ f with next := f.next + 1 } :: rest) := by
  intro w p
  apply DFSInv.finishEdge
  have hsc_iff := scanned_step_iff h (s' := p.1) rfl hlen
  have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
  have hf_vis : s.Visited f.vertex := (h.visited_iff f.vertex).mpr (Or.inl (by simp))
  have hw_mem : w ∈ (List.ofFn lists).toArray[f.vertex]! := getElem!_mem_of_lt hlen
  have hw_lt : w < N := adj_mem_lt hAdj hf_lt hw_mem
  refine
    { depth_size := h.depth_size
      parent_size := h.parent_size
      parentEdge_size := h.parentEdge_size
      active_lt := h.active_lt
      postorder_lt := h.postorder_lt
      nodup_verts := h.nodup_verts
      frame_next_le := fun g hg => by
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact Nat.succ_le_of_lt hlen
        · exact h.frame_next_le g (List.mem_cons_of_mem f hg')
      visited_iff := h.visited_iff
      unvisited_none := h.unvisited_none
      root_depth := h.root_depth
      parent_spec := fun v u hp => by
        obtain ⟨hu, hvv, huv, hadj, hd, k, hsc, hk⟩ := h.parent_spec v u hp
        exact ⟨hu, hvv, huv, hadj, hd, k, (hsc_iff u k).mpr (Or.inr hsc), hk⟩
      stack_chain := by
        cases rest with
        | nil => exact List.isChain_singleton _
        | cons g rest' =>
          have hch := h.stack_chain
          rw [List.isChain_cons_cons] at hch ⊢
          exact hch
      active_parent_mem := h.active_parent_mem
      postorder_order := h.postorder_order
      scanned_visited := fun v k hsc => by
        rcases (hsc_iff v k).mp hsc with ⟨rfl, rfl⟩ | hsc_old
        · exact hw_vis
        · exact h.scanned_visited v k hsc_old
      completed_adj := h.completed_adj
      edges_valid := fun i hi => by
        rw [addEdge_fst_edges_size] at hi
        have hi_le : i ≤ s.edges.size := by omega
        have hsrc_eq := addEdge_edges_source s f.vertex w false i hi_le
        have htg_eq := addEdge_edges_target s f.vertex w false i hi_le
        have htr_eq := addEdge_edges_tree s f.vertex w false i hi_le
        change
          let r := p.1.edges[i]!
          ∃ (hs : r.source < N) (ht : r.target < N),
            s.Visited r.source ∧ s.Visited r.target ∧
            (∃ k, Scanned N lists p.1 ({ f with next := f.next + 1 } :: rest) r.source k ∧
              ((List.ofFn lists).toArray[r.source]!)[k]! = r.target) ∧
            (if r.tree then
              s.parent[r.target]?.join = some r.source ∧ s.parentEdge[r.target]?.join = some i
             else
              s.parent[r.source]?.join ≠ some r.target ∧
                (s.forest N).depth ⟨r.target, ht⟩ < (s.forest N).depth ⟨r.source, hs⟩)
        dsimp only
        rw [hsrc_eq, htg_eq, htr_eq]
        by_cases hieq : i = s.edges.size
        · subst hieq
          simp only [↓reduceIte, Bool.false_eq_true]
          exact ⟨hf_lt, hw_lt, hf_vis, hw_vis,
            ⟨f.next, (hsc_iff f.vertex f.next).mpr (Or.inl ⟨rfl, rfl⟩), rfl⟩, hback⟩
        · simp only [hieq, ↓reduceIte]
          have hi_lt : i < s.edges.size := by omega
          obtain ⟨hs, ht, hvs, hvt, ⟨k, hsc, hk⟩, htree⟩ := h.edges_valid i hi_lt
          exact ⟨hs, ht, hvs, hvt, ⟨k, (hsc_iff _ k).mpr (Or.inr hsc), hk⟩, htree⟩
      parentEdge_iff := fun u hu i => by
        rw [addEdge_fst_parentEdge, h.parentEdge_iff u hu i, addEdge_fst_edges_size]
        constructor
        · rintro ⟨hi_lt, htr, htg⟩
          have hi_le : i ≤ s.edges.size := Nat.le_of_lt hi_lt
          have hne : i ≠ s.edges.size := Nat.ne_of_lt hi_lt
          rw [addEdge_edges_tree s f.vertex w false i hi_le,
            addEdge_edges_target s f.vertex w false i hi_le]
          simp only [hne, ↓reduceIte]
          exact ⟨by omega, htr, htg⟩
        · rintro ⟨hi_lt, htr, htg⟩
          have hi_le : i ≤ s.edges.size := by omega
          by_cases hieq : i = s.edges.size
          · subst hieq
            have htr' := addEdge_edges_tree s f.vertex w false s.edges.size le_rfl
            simp only [↓reduceIte] at htr'
            exact absurd (htr'.symm.trans htr) Bool.false_ne_true
          · rw [addEdge_edges_tree s f.vertex w false i hi_le] at htr
            rw [addEdge_edges_target s f.vertex w false i hi_le] at htg
            simp only [hieq, ↓reduceIte] at htr htg
            exact ⟨by omega, htr, htg⟩
      parent_iff_edge := fun u hu v => by
        rw [addEdge_fst_parent, h.parent_iff_edge u hu v]
        constructor
        · rintro ⟨i, hi_lt, htr, hsrc, htg⟩
          have hi_le : i ≤ s.edges.size := Nat.le_of_lt hi_lt
          have hne : i ≠ s.edges.size := Nat.ne_of_lt hi_lt
          refine ⟨i, by rw [addEdge_fst_edges_size]; omega, ?_⟩
          rw [addEdge_edges_tree s f.vertex w false i hi_le,
            addEdge_edges_source s f.vertex w false i hi_le,
            addEdge_edges_target s f.vertex w false i hi_le]
          simp only [hne, ↓reduceIte]
          exact ⟨htr, hsrc, htg⟩
        · rintro ⟨i, hi_lt, htr, hsrc, htg⟩
          rw [addEdge_fst_edges_size] at hi_lt
          have hi_le : i ≤ s.edges.size := by omega
          by_cases hieq : i = s.edges.size
          · subst hieq
            have htr' := addEdge_edges_tree s f.vertex w false s.edges.size le_rfl
            simp only [↓reduceIte] at htr'
            exact absurd (htr'.symm.trans htr) Bool.false_ne_true
          · rw [addEdge_edges_tree s f.vertex w false i hi_le] at htr
            rw [addEdge_edges_source s f.vertex w false i hi_le] at hsrc
            rw [addEdge_edges_target s f.vertex w false i hi_le] at htg
            simp only [hieq, ↓reduceIte] at htr hsrc htg
            exact ⟨i, by omega, htr, hsrc, htg⟩
      edges_inj := fun i hi j hj hsrc htg => by
        rw [addEdge_fst_edges_size] at hi hj
        have hi_le : i ≤ s.edges.size := by omega
        have hj_le : j ≤ s.edges.size := by omega
        rw [addEdge_edges_source s f.vertex w false i hi_le,
          addEdge_edges_source s f.vertex w false j hj_le] at hsrc
        rw [addEdge_edges_target s f.vertex w false i hi_le,
          addEdge_edges_target s f.vertex w false j hj_le] at htg
        split_ifs at hsrc htg with hieq hjeq hjeq
        · omega
        · exfalso
          exact h.not_edge_current hAdj hlen (by omega) ⟨hsrc.symm, htg.symm⟩
        · exfalso
          exact h.not_edge_current hAdj hlen (by omega) ⟨hsrc, htg⟩
        · exact h.edges_inj i (by omega) j (by omega) hsrc htg
      scanned_edge_exists := fun v k hsc hv hw' hcond => by
        rcases (hsc_iff v k).mp hsc with ⟨rfl, rfl⟩ | hsc_old
        · refine ⟨s.edges.size, by rw [addEdge_fst_edges_size]; omega, ?_⟩
          rw [addEdge_edges_source s f.vertex w false s.edges.size le_rfl,
            addEdge_edges_target s f.vertex w false s.edges.size le_rfl]
          simp [w]
        · obtain ⟨i, hi_lt, hsrc, htg⟩ := h.scanned_edge_exists v k hsc_old hv hw' hcond
          have hi_le : i ≤ s.edges.size := Nat.le_of_lt hi_lt
          have hne : i ≠ s.edges.size := Nat.ne_of_lt hi_lt
          refine ⟨i, by rw [addEdge_fst_edges_size]; omega, ?_⟩
          rw [addEdge_edges_source s f.vertex w false i hi_le,
            addEdge_edges_target s f.vertex w false i hi_le]
          simp only [hne, ↓reduceIte]
          exact ⟨hsrc, htg⟩ }

/-! ### Step 4: Discover tree child when `(s.depth[w]?.join).isNone = true` -/

theorem DFSInv.step_tree {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (hAdj : Compute.IsAdjListFamily G lists)
    (h : DFSInv N G lists s (f :: rest))
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (hunvis : (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).isNone = true) :
    let w := ((List.ofFn lists).toArray[f.vertex]!)[f.next]!
    let p := addEdge s f.vertex w true
    let s₂ : Search := { p.1 with
      parent := p.1.parent.set! w (some f.vertex)
      parentEdge := p.1.parentEdge.set! w (some p.2)
      depth := p.1.depth.set! w (some ((p.1.depth[f.vertex]?.join).getD 0 + 1)) }
    DFSInv N G lists s₂ (⟨w, 0⟩ :: { f with next := f.next + 1 } :: rest) := by
  intro w p s₂
  have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
  have hf_vis : s.Visited f.vertex := (h.visited_iff f.vertex).mpr (Or.inl (by simp))
  have hw_mem : w ∈ (List.ofFn lists).toArray[f.vertex]! := getElem!_mem_of_lt hlen
  have hw_lt : w < N := adj_mem_lt hAdj hf_lt hw_mem
  have hadj_vw : G.Adj ⟨f.vertex, hf_lt⟩ ⟨w, hw_lt⟩ := (adj_mem_iff hAdj hf_lt hw_lt).mp hw_mem
  have hw_not_vis : ¬ s.Visited w := (Search.not_visited_iff s w).mpr hunvis
  have hw_ne_vis : ∀ u, s.Visited u → u ≠ w := fun u hu heq => hw_not_vis (heq ▸ hu)
  have hw_not_act : w ∉ (f :: rest).map Frame.vertex := fun hm =>
    hw_not_vis ((h.visited_iff w).mpr (Or.inl hm))
  have hw_not_post : w ∉ s.postorder := fun hm =>
    hw_not_vis ((h.visited_iff w).mpr (Or.inr hm))
  have hw_depth_sz : w < s.depth.size := by rw [h.depth_size]; exact hw_lt
  have hw_par_sz : w < s.parent.size := by rw [h.parent_size]; exact hw_lt
  have hw_pe_sz : w < s.parentEdge.size := by rw [h.parentEdge_size]; exact hw_lt
  have hdepth_s2 : ∀ u, s₂.depth[u]?.join =
      if u = w then some ((s.depth[f.vertex]?.join).getD 0 + 1) else s.depth[u]?.join :=
    getElem?_join_set! s.depth w _ hw_depth_sz
  have hpar_s2 : ∀ u, s₂.parent[u]?.join =
      if u = w then some f.vertex else s.parent[u]?.join :=
    getElem?_join_set! s.parent w _ hw_par_sz
  have hpe_s2 : ∀ u, s₂.parentEdge[u]?.join =
      if u = w then some s.edges.size else s.parentEdge[u]?.join :=
    getElem?_join_set! s.parentEdge w _ hw_pe_sz
  have hvis_s2 : ∀ u, s₂.Visited u ↔ u = w ∨ s.Visited u := by
    intro u
    simp only [Search.Visited, hdepth_s2]
    split_ifs with huw
    · subst huw; simp
    · simp [huw]
  have hdepth_old : ∀ u : Fin N, s.Visited u.val → (s₂.forest N).depth u = (s.forest N).depth u := by
    intro u hu
    have huw : u.val ≠ w := hw_ne_vis u.val hu
    simp [Search.forest, hdepth_s2, huw]
  have hdepth_w : (s₂.forest N).depth ⟨w, hw_lt⟩ = (s.forest N).depth ⟨f.vertex, hf_lt⟩ + 1 := by
    simp [Search.forest, hdepth_s2]
  have hanc_mono : ∀ u v : Fin N, (s.forest N).Ancestor u v → (s₂.forest N).Ancestor u v := by
    intro u v
    apply Forest.Ancestor.mono
    intro x y hxy
    rw [h.forest_parent_some_iff] at hxy
    obtain ⟨_, hy_vis, _⟩ := h.parent_spec y x.val hxy
    have hyw : y.val ≠ w := hw_ne_vis y.val hy_vis
    simp [Search.forest, hpar_s2, hyw, hxy, x.2]
  have hsc_iff : ∀ u k,
      Scanned N lists s₂ (⟨w, 0⟩ :: { f with next := f.next + 1 } :: rest) u k ↔
        (u = f.vertex ∧ k = f.next) ∨ Scanned N lists s (f :: rest) u k := by
    intro u k
    rw [scanned_push_zero_iff, scanned_step_iff h (s' := s₂) rfl hlen]
  refine
    { depth_size := by simp [s₂, p, h.depth_size]
      parent_size := by simp [s₂, p, h.parent_size]
      parentEdge_size := by simp [s₂, p, h.parentEdge_size]
      active_lt := fun u hu => by
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hw_lt
        · exact h.active_lt u hu'
      postorder_lt := h.postorder_lt
      nodup_verts := by
        change (w :: ((f :: rest).map Frame.vertex ++ s.postorder)).Nodup
        rw [List.nodup_cons, List.mem_append, not_or]
        exact ⟨⟨hw_not_act, hw_not_post⟩, h.nodup_verts⟩
      frame_next_le := fun g hg => by
        rcases List.mem_cons.mp hg with rfl | hg1
        · exact Nat.zero_le _
        · rcases List.mem_cons.mp hg1 with rfl | hg'
          · exact Nat.succ_le_of_lt hlen
          · exact h.frame_next_le g (List.mem_cons_of_mem f hg')
      visited_iff := fun u => by
        rw [hvis_s2, h.visited_iff]
        simp [s₂, p, or_assoc]
      unvisited_none := fun u hu => by
        rw [hvis_s2, not_or] at hu
        rw [hpar_s2, hpe_s2]
        simp only [hu.1, ↓reduceIte]
        exact h.unvisited_none u hu.2
      root_depth := fun v hv hp => by
        rw [hpar_s2] at hp
        by_cases hvw : v.val = w
        · simp [hvw] at hp
        · simp only [hvw, ↓reduceIte] at hp
          rw [hvis_s2] at hv
          have hv' : s.Visited v.val := hv.resolve_left hvw
          rw [hdepth_old v hv', hpe_s2]
          simp only [hvw, ↓reduceIte]
          exact h.root_depth v hv' hp
      parent_spec := fun v u hp => by
        rw [hpar_s2] at hp
        split_ifs at hp with hvw
        · injection hp with huf
          subst huf
          have hveq : v = ⟨w, hw_lt⟩ := Fin.ext hvw
          subst hveq
          refine ⟨hf_lt, (hvis_s2 w).mpr (Or.inl rfl), (hvis_s2 f.vertex).mpr (Or.inr hf_vis),
            hadj_vw, ?_, f.next, (hsc_iff f.vertex f.next).mpr (Or.inl ⟨rfl, rfl⟩), rfl⟩
          rw [hdepth_w, hdepth_old ⟨f.vertex, hf_lt⟩ hf_vis]
        · obtain ⟨hu, hvv, huv, hadj, hd, k, hsc, hk⟩ := h.parent_spec v u hp
          refine ⟨hu, (hvis_s2 v.val).mpr (Or.inr hvv), (hvis_s2 u).mpr (Or.inr huv),
            hadj, ?_, k, (hsc_iff u k).mpr (Or.inr hsc), hk⟩
          rw [hdepth_old v hvv, hdepth_old ⟨u, hu⟩ huv]
          exact hd
      stack_chain := by
        rw [List.isChain_cons_cons]
        refine ⟨by simp [hpar_s2], ?_⟩
        have hch : ((f :: rest).IsChain
            (fun f₁ f₂ => s₂.parent[f₁.vertex]?.join = some f₂.vertex)) := by
          refine isChain_imp_of_mem h.stack_chain ?_
          intro x hx y _ hxy
          have hx_vis : s.Visited x.vertex :=
            (h.visited_iff x.vertex).mpr (Or.inl (List.mem_map_of_mem hx))
          rw [hpar_s2]
          simp only [hw_ne_vis x.vertex hx_vis, ↓reduceIte]
          exact hxy
        cases rest with
        | nil => exact List.isChain_singleton _
        | cons g rest' =>
          rw [List.isChain_cons_cons] at hch ⊢
          exact hch
      active_parent_mem := fun v hv u hp => by
        rw [hpar_s2] at hp
        split_ifs at hp with hvw
        · injection hp with huf
          subst huf
          simp
        · rcases List.mem_cons.mp hv with rfl | hv'
          · exact absurd rfl hvw
          · exact List.mem_cons_of_mem w (h.active_parent_mem v hv' u hp)
      postorder_order := by
        refine h.postorder_order.imp_of_mem ?_
        intro x y hx _ hxy
        have hx_vis : s.Visited x := (h.visited_iff x).mpr (Or.inr hx)
        rw [hpar_s2]
        simp only [hw_ne_vis x hx_vis, ↓reduceIte]
        exact hxy
      scanned_visited := fun v k hsc => by
        rcases (hsc_iff v k).mp hsc with ⟨rfl, rfl⟩ | hsc_old
        · exact (hvis_s2 w).mpr (Or.inl rfl)
        · exact (hvis_s2 _).mpr (Or.inr (h.scanned_visited v k hsc_old))
      completed_adj := fun u v hu hadj => by
        refine ⟨fun hv_act => ?_, fun hv_post => ?_⟩
        · rcases List.mem_cons.mp hv_act with hvw | hv_old
          · exfalso
            have hmem : v.val ∈ (List.ofFn lists).toArray[u.val]! :=
              (adj_mem_iff hAdj u.2 v.2).mpr hadj
            obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
            have hsc : Scanned N lists s (f :: rest) u.val k := ⟨u.2, hk, Or.inl hu⟩
            have hvis_v := h.scanned_visited u.val k hsc
            rw [getElem!_pos _ k hk, hget, hvw] at hvis_v
            exact hw_not_vis hvis_v
          · exact hanc_mono v u ((h.completed_adj u v hu hadj).1 hv_old)
        · rcases (h.completed_adj u v hu hadj).2 hv_post with h1 | h2
          · exact Or.inl (hanc_mono u v h1)
          · exact Or.inr (hanc_mono v u h2)
      edges_valid := fun i hi => by
        have hi_sz : s₂.edges.size = s.edges.size + 1 := by simp [s₂, p]
        have hi_le : i ≤ s.edges.size := by omega
        have hsrc_eq := addEdge_edges_source s f.vertex w true i hi_le
        have htg_eq := addEdge_edges_target s f.vertex w true i hi_le
        have htr_eq := addEdge_edges_tree s f.vertex w true i hi_le
        change
          let r := p.1.edges[i]!
          ∃ (hs : r.source < N) (ht : r.target < N),
            s₂.Visited r.source ∧ s₂.Visited r.target ∧
            (∃ k, Scanned N lists s₂ (⟨w, 0⟩ :: { f with next := f.next + 1 } :: rest) r.source k ∧
              ((List.ofFn lists).toArray[r.source]!)[k]! = r.target) ∧
            (if r.tree then
              s₂.parent[r.target]?.join = some r.source ∧ s₂.parentEdge[r.target]?.join = some i
             else
              s₂.parent[r.source]?.join ≠ some r.target ∧
                (s₂.forest N).depth ⟨r.target, ht⟩ < (s₂.forest N).depth ⟨r.source, hs⟩)
        dsimp only
        rw [hsrc_eq, htg_eq, htr_eq]
        by_cases hieq : i = s.edges.size
        · subst hieq
          simp only [↓reduceIte]
          refine ⟨hf_lt, hw_lt, (hvis_s2 f.vertex).mpr (Or.inr hf_vis),
            (hvis_s2 w).mpr (Or.inl rfl),
            ⟨f.next, (hsc_iff f.vertex f.next).mpr (Or.inl ⟨rfl, rfl⟩), rfl⟩, ?_⟩
          simp [hpar_s2, hpe_s2]
        · simp only [hieq, ↓reduceIte]
          have hi_lt : i < s.edges.size := by omega
          obtain ⟨hs, ht, hvs, hvt, ⟨k, hsc, hk⟩, htree⟩ := h.edges_valid i hi_lt
          have hsrc_ne : (s.edges[i]!).source ≠ w := hw_ne_vis _ hvs
          have htg_ne : (s.edges[i]!).target ≠ w := hw_ne_vis _ hvt
          refine ⟨hs, ht, (hvis_s2 _).mpr (Or.inr hvs), (hvis_s2 _).mpr (Or.inr hvt),
            ⟨k, (hsc_iff _ k).mpr (Or.inr hsc), hk⟩, ?_⟩
          rw [hpar_s2, hpe_s2, hpar_s2]
          simp only [htg_ne, hsrc_ne, ↓reduceIte,
            hdepth_old ⟨_, ht⟩ hvt, hdepth_old ⟨_, hs⟩ hvs]
          exact htree
      parentEdge_iff := fun u hu i => by
        rw [hpe_s2]
        have hi_sz : s₂.edges.size = s.edges.size + 1 := by simp [s₂, p]
        rw [hi_sz]
        split_ifs with huw
        · subst u
          constructor
          · intro h1
            injection h1 with hieq
            subst hieq
            rw [addEdge_edges_tree s f.vertex w true s.edges.size le_rfl,
              addEdge_edges_target s f.vertex w true s.edges.size le_rfl]
            simp
          · rintro ⟨hi_lt, htr, htg⟩
            have hi_le : i ≤ s.edges.size := by omega
            rw [addEdge_edges_tree s f.vertex w true i hi_le] at htr
            rw [addEdge_edges_target s f.vertex w true i hi_le] at htg
            split_ifs at htr htg with hieq
            · subst hieq; rfl
            · exfalso
              obtain ⟨_, _, _, hvt, _⟩ := h.edges_valid i (by omega)
              rw [htg] at hvt
              exact hw_not_vis hvt
        · rw [h.parentEdge_iff u hu i]
          constructor
          · rintro ⟨hi_lt, htr, htg⟩
            have hi_le : i ≤ s.edges.size := Nat.le_of_lt hi_lt
            have hne : i ≠ s.edges.size := Nat.ne_of_lt hi_lt
            rw [addEdge_edges_tree s f.vertex w true i hi_le,
              addEdge_edges_target s f.vertex w true i hi_le]
            simp only [hne, ↓reduceIte]
            exact ⟨by omega, htr, htg⟩
          · rintro ⟨hi_lt, htr, htg⟩
            have hi_le : i ≤ s.edges.size := by omega
            rw [addEdge_edges_tree s f.vertex w true i hi_le] at htr
            rw [addEdge_edges_target s f.vertex w true i hi_le] at htg
            split_ifs at htr htg with hieq
            · exfalso; exact huw htg.symm
            · exact ⟨by omega, htr, htg⟩
      parent_iff_edge := fun u hu v => by
        rw [hpar_s2]
        have hi_sz : s₂.edges.size = s.edges.size + 1 := by simp [s₂, p]
        rw [hi_sz]
        split_ifs with huw
        · subst u
          constructor
          · intro h1
            injection h1 with hvf
            subst hvf
            refine ⟨s.edges.size, by omega, ?_⟩
            rw [addEdge_edges_tree s f.vertex w true s.edges.size le_rfl,
              addEdge_edges_source s f.vertex w true s.edges.size le_rfl,
              addEdge_edges_target s f.vertex w true s.edges.size le_rfl]
            simp
          · rintro ⟨i, hi_lt, htr, hsrc, htg⟩
            have hi_le : i ≤ s.edges.size := by omega
            rw [addEdge_edges_tree s f.vertex w true i hi_le] at htr
            rw [addEdge_edges_source s f.vertex w true i hi_le] at hsrc
            rw [addEdge_edges_target s f.vertex w true i hi_le] at htg
            split_ifs at htr hsrc htg with hieq
            · subst hsrc; rfl
            · exfalso
              obtain ⟨_, _, _, hvt, _⟩ := h.edges_valid i (by omega)
              rw [htg] at hvt
              exact hw_not_vis hvt
        · rw [h.parent_iff_edge u hu v]
          constructor
          · rintro ⟨i, hi_lt, htr, hsrc, htg⟩
            have hi_le : i ≤ s.edges.size := Nat.le_of_lt hi_lt
            have hne : i ≠ s.edges.size := Nat.ne_of_lt hi_lt
            refine ⟨i, by omega, ?_⟩
            rw [addEdge_edges_tree s f.vertex w true i hi_le,
              addEdge_edges_source s f.vertex w true i hi_le,
              addEdge_edges_target s f.vertex w true i hi_le]
            simp only [hne, ↓reduceIte]
            exact ⟨htr, hsrc, htg⟩
          · rintro ⟨i, hi_lt, htr, hsrc, htg⟩
            have hi_le : i ≤ s.edges.size := by omega
            rw [addEdge_edges_tree s f.vertex w true i hi_le] at htr
            rw [addEdge_edges_source s f.vertex w true i hi_le] at hsrc
            rw [addEdge_edges_target s f.vertex w true i hi_le] at htg
            split_ifs at htr hsrc htg with hieq
            · exfalso; exact huw htg.symm
            · exact ⟨i, by omega, htr, hsrc, htg⟩
      edges_inj := fun i hi j hj hsrc htg => by
        have hi_sz : s₂.edges.size = s.edges.size + 1 := by simp [s₂, p]
        rw [hi_sz] at hi hj
        have hi_le : i ≤ s.edges.size := by omega
        have hj_le : j ≤ s.edges.size := by omega
        rw [addEdge_edges_source s f.vertex w true i hi_le,
          addEdge_edges_source s f.vertex w true j hj_le] at hsrc
        rw [addEdge_edges_target s f.vertex w true i hi_le,
          addEdge_edges_target s f.vertex w true j hj_le] at htg
        split_ifs at hsrc htg with hieq hjeq hjeq
        · omega
        · exfalso
          exact h.not_edge_current hAdj hlen (by omega) ⟨hsrc.symm, htg.symm⟩
        · exfalso
          exact h.not_edge_current hAdj hlen (by omega) ⟨hsrc, htg⟩
        · exact h.edges_inj i (by omega) j (by omega) hsrc htg
      scanned_edge_exists := fun v k hsc hv hw' hcond => by
        have hi_sz : s₂.edges.size = s.edges.size + 1 := by simp [s₂, p]
        rw [hi_sz]
        rcases (hsc_iff v k).mp hsc with ⟨rfl, rfl⟩ | hsc_old
        · refine ⟨s.edges.size, by omega, ?_⟩
          rw [addEdge_edges_source s f.vertex w true s.edges.size le_rfl,
            addEdge_edges_target s f.vertex w true s.edges.size le_rfl]
          simp [w]
        · obtain ⟨hv_vis, hx_vis⟩ := h.scanned_visited_both hsc_old
          have hvw : v ≠ w := hw_ne_vis v hv_vis
          have hxw : ((List.ofFn lists).toArray[v]!)[k]! ≠ w := hw_ne_vis _ hx_vis
          rw [hpar_s2, hpar_s2] at hcond
          simp only [hxw, hvw, ↓reduceIte,
            hdepth_old ⟨_, hw'⟩ hx_vis, hdepth_old ⟨v, hv⟩ hv_vis] at hcond
          obtain ⟨i, hi_lt, hsrc, htg⟩ := h.scanned_edge_exists v k hsc_old hv hw' hcond
          have hi_le : i ≤ s.edges.size := Nat.le_of_lt hi_lt
          have hne : i ≠ s.edges.size := Nat.ne_of_lt hi_lt
          refine ⟨i, by omega, ?_⟩
          rw [addEdge_edges_source s f.vertex w true i hi_le,
            addEdge_edges_target s f.vertex w true i hi_le]
          simp only [hne, ↓reduceIte]
          exact ⟨hsrc, htg⟩ }

/-- `searchFrames` terminates without exhausting fuel and preserves `DFSInv` and visited vertices. -/
theorem searchFrames_spec {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hAdj : Compute.IsAdjListFamily G lists) :
    ∀ (fuel : ℕ) (s : Search) (stack : List Frame),
      DFSInv N G lists s stack →
      workDone (List.ofFn lists).toArray s stack + fuel >
        (List.ofFn lists).toArray.foldl (fun total l => total + l.length) 0 + N →
      ∃ s', searchFrames (List.ofFn lists).toArray fuel s stack = some s' ∧
        DFSInv N G lists s' [] ∧
        (∀ u, s.Visited u → s'.Visited u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s stack h hfuel
    cases stack with
    | nil =>
      exact ⟨s, rfl, h, fun _ hu => hu⟩
    | cons f rest =>
      exfalso
      have hle := h.workDone_le
      dsimp only at hle
      have hsz : (List.ofFn lists).toArray.size = N := by simp
      omega
  | succ fuel ih =>
    intro s stack h hfuel
    cases stack with
    | nil =>
      exact ⟨s, rfl, h, fun _ hu => hu⟩
    | cons f rest =>
      unfold searchFrames
      dsimp only [Id.run]
      by_cases hlen : f.next ≥ ((List.ofFn lists).toArray[f.vertex]!).length
      · simp only [hlen, ↓reduceIte]
        have h' := h.step_pop hlen
        dsimp only at h'
        have hle_next := h.frame_next_le f (by simp)
        have hwd : workDone (List.ofFn lists).toArray
            (match s.parentEdge[f.vertex]?.join with
             | none => { s with postorder := f.vertex :: s.postorder }
             | some p => finishEdge { s with postorder := f.vertex :: s.postorder } p) rest =
            workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
          cases s.parentEdge[f.vertex]?.join <;>
          · simp only [workDone, finishEdge_postorder, List.map_cons, List.sum_cons]
            omega
        obtain ⟨s', hs', hinv', hvis'⟩ := ih _ rest h' (by omega)
        refine ⟨s', hs', hinv', fun u hu => hvis' u ?_⟩
        cases s.parentEdge[f.vertex]?.join <;>
          simpa [Search.Visited] using hu
      · simp only [hlen, ↓reduceIte]
        have hlen' : f.next < ((List.ofFn lists).toArray[f.vertex]!).length := by omega
        have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
        have hmem_w : ((List.ofFn lists).toArray[f.vertex]!)[f.next]! ∈
            (List.ofFn lists).toArray[f.vertex]! := getElem!_mem_of_lt hlen'
        have hw_lt : ((List.ofFn lists).toArray[f.vertex]!)[f.next]! < N :=
          adj_mem_lt hAdj hf_lt hmem_w
        have hw_not_ge : ¬ (((List.ofFn lists).toArray[f.vertex]!)[f.next]! ≥
            (List.ofFn lists).toArray.size) := by
          simp only [List.size_toArray, List.length_ofFn, not_le]
          exact hw_lt
        simp only [hw_not_ge, ↓reduceIte]
        by_cases hw_none : (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).isNone = true
        · simp only [hw_none, ↓reduceIte]
          have h' := h.step_tree hAdj hlen' hw_none
          dsimp only at h'
          have hwd : workDone (List.ofFn lists).toArray
              (let p := addEdge s f.vertex ((List.ofFn lists).toArray[f.vertex]!)[f.next]! true
               { p.1 with
                 parent := p.1.parent.set! ((List.ofFn lists).toArray[f.vertex]!)[f.next]! (some f.vertex)
                 parentEdge := p.1.parentEdge.set! ((List.ofFn lists).toArray[f.vertex]!)[f.next]! (some p.2)
                 depth := p.1.depth.set! ((List.ofFn lists).toArray[f.vertex]!)[f.next]!
                   (some ((p.1.depth[f.vertex]?.join).getD 0 + 1)) })
              (⟨((List.ofFn lists).toArray[f.vertex]!)[f.next]!, 0⟩ :: { f with next := f.next + 1 } :: rest) =
              workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
            simp only [workDone, addEdge_fst_postorder, List.map_cons, List.sum_cons]
            omega
          dsimp only at hwd
          obtain ⟨s', hs', hinv', hvis'⟩ := ih _ _ h' (by omega)
          refine ⟨s', hs', hinv', fun u hu => hvis' u ?_⟩
          have hw_sz : ((List.ofFn lists).toArray[f.vertex]!)[f.next]! < s.depth.size := by
            rw [h.depth_size]; exact hw_lt
          simp only [Search.Visited, addEdge_fst_depth, getElem?_join_set! s.depth _ _ hw_sz]
          split_ifs with huw
          · simp
          · exact hu
        · simp only [hw_none, Bool.false_eq_true, ↓reduceIte]
          have hw_vis : s.Visited (((List.ofFn lists).toArray[f.vertex]!)[f.next]!) := by
            simp only [Search.Visited]
            exact Option.ne_none_iff_isSome.mp (by simpa using hw_none)
          split_ifs with hback
          · have h' := h.step_back hAdj hlen' hw_vis hback
            dsimp only at h'
            have hwd : workDone (List.ofFn lists).toArray
                (finishEdge (addEdge s f.vertex ((List.ofFn lists).toArray[f.vertex]!)[f.next]! false).1
                  (addEdge s f.vertex ((List.ofFn lists).toArray[f.vertex]!)[f.next]! false).2)
                ({ f with next := f.next + 1 } :: rest) =
                workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
              simp only [workDone, finishEdge_postorder, addEdge_fst_postorder, List.map_cons, List.sum_cons]
              omega
            obtain ⟨s', hs', hinv', hvis'⟩ := ih _ _ h' (by omega)
            refine ⟨s', hs', hinv', fun u hu => hvis' u ?_⟩
            simpa [Search.Visited] using hu
          · have h' := h.step_skip hAdj hlen' hw_vis hback
            have hwd : workDone (List.ofFn lists).toArray s ({ f with next := f.next + 1 } :: rest) =
                workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
              simp only [workDone, List.map_cons, List.sum_cons]
              omega
            exact ih _ _ h' (by omega)

set_option linter.auxLemma false in
/-- Inductive loop invariant for the outer root-scan loop in `depthFirstSearch`. -/
private theorem dfs_loop_spec {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hAdj : Compute.IsAdjListFamily G lists) :
    let adj := (List.ofFn lists).toArray
    let fuel := adj.foldl (fun total l => total + l.length) 0 + adj.size + 1
    ∀ (k : ℕ) (_hk : k ≤ N) (s : Search),
      DFSInv N G lists s [] →
      (∀ u < N - k, s.Visited u) →
      ∃ s', (forIn (m := Id) (List.range' (N - k) k) (none, s)
          (fun root (__s : Option (Option Search) × Search) =>
            if (__s.2.depth[root]?.join).isNone = true then
              depthFirstSearch.match_1
                (fun _ => Id (ForInStep (Option (Option Search) × Search)))
                (searchFrames adj fuel
                  { depth := __s.2.depth.set! root (some 0)
                    parent := __s.2.parent
                    parentEdge := __s.2.parentEdge
                    edges := __s.2.edges
                    postorder := __s.2.postorder }
                  [⟨root, 0⟩])
                (fun _ =>
                  pure (ForInStep.done
                    (some none,
                      { depth := __s.2.depth.set! root (some 0)
                        parent := __s.2.parent
                        parentEdge := __s.2.parentEdge
                        edges := __s.2.edges
                        postorder := __s.2.postorder })))
                (fun t => pure (ForInStep.yield (none, t)))
            else pure (ForInStep.yield (none, __s.2)))) = (none, s') ∧
        DFSInv N G lists s' [] ∧
        (∀ u < N, s'.Visited u) := by
  intro adj fuel k
  induction k with
  | zero =>
    intro hk s h hall
    simp only [List.range'_zero, List.forIn_nil]
    exact ⟨s, rfl, h, fun u hu => hall u (by omega)⟩
  | succ k ih =>
    intro hk s h hall
    have hroot_lt : N - (k + 1) < N := by omega
    rw [List.range'_succ]
    simp only [List.forIn_cons]
    dsimp only [bind, pure, Id.run]
    by_cases hnone : (s.depth[N - (k + 1)]?.join).isNone = true
    · simp only [hnone, ↓reduceIte]
      have hpush := h.push_root hAdj hroot_lt hnone
      have hfuel : workDone adj { s with depth := s.depth.set! (N - (k + 1)) (some 0) }
          [⟨N - (k + 1), 0⟩] + fuel >
          adj.foldl (fun total l => total + l.length) 0 + N := by
        have hsz : adj.size = N := by simp [adj]
        omega
      obtain ⟨t, ht, hinv_t, hvis_t⟩ := searchFrames_spec hAdj fuel _ _ hpush hfuel
      rw [ht]
      dsimp only
      have hsz : N - (k + 1) < s.depth.size := by rw [h.depth_size]; exact hroot_lt
      have hroot_vis : t.Visited (N - (k + 1)) := by
        apply hvis_t
        unfold Search.Visited
        rw [getElem?_join_set! s.depth _ _ hsz]
        simp
      have hall_t : ∀ u < N - k, t.Visited u := by
        intro u hu
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : u < (N - (k + 1)) + 1)) with hlt | rfl
        · apply hvis_t
          unfold Search.Visited
          rw [getElem?_join_set! s.depth _ _ hsz]
          split_ifs with heq
          · simp
          · exact hall u hlt
        · exact hroot_vis
      have heq_start : N - (k + 1) + 1 = N - k := by omega
      rw [heq_start]
      exact ih (by omega) t hinv_t hall_t
    · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
      have hroot_vis : s.Visited (N - (k + 1)) := by
        simp [Search.Visited]
        exact Option.ne_none_iff_isSome.mp (by simpa using hnone)
      have hall_s : ∀ u < N - k, s.Visited u := by
        intro u hu
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : u < (N - (k + 1)) + 1)) with hlt | rfl
        · exact hall u hlt
        · exact hroot_vis
      have heq_start : N - (k + 1) + 1 = N - k := by omega
      rw [heq_start]
      exact ih (by omega) s h hall_s

/-- Full specification of `depthFirstSearch` on a valid adjacency list family. -/
theorem depthFirstSearch_spec {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hAdj : Compute.IsAdjListFamily G lists) :
    ∃ s, depthFirstSearch (List.ofFn lists).toArray =
      some { s with postorder := s.postorder.reverse } ∧
      DFSInv N G lists s [] ∧
      (∀ u < N, s.Visited u) := by
  unfold depthFirstSearch
  dsimp only [Id.run]
  have hsz : (List.ofFn lists).toArray.size = N := by simp
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange :
      List.range' [:(List.ofFn lists).toArray.size].start
        [:(List.ofFn lists).toArray.size].size
        [:(List.ofFn lists).toArray.size].step =
      List.range' (N - N) N := by
    simp
  rw [hrange]
  have hinit : DFSInv N G lists (initialSearch (List.ofFn lists).toArray.size) [] := by
    rw [hsz]
    exact DFSInv.init N G lists
  obtain ⟨s', hs', hinv', hall'⟩ := dfs_loop_spec hAdj N le_rfl
    (initialSearch (List.ofFn lists).toArray.size) hinit (fun u hu => by omega)
  refine ⟨s', ?_, hinv', hall'⟩
  rw [hs']
  rfl

/-- Part I, Section 1: explicit frames compute a depth-first forest and do not
exhaust the prescribed fuel on valid adjacency lists. -/
theorem searchStatement : SearchStatement := by
  intro N G lists hAdj
  obtain ⟨s, hs, hinv, hall⟩ := depthFirstSearch_spec hAdj
  refine ⟨{ s with postorder := s.postorder.reverse }, hs, ?_⟩
  exact hinv.isDFS_of_nil hall

/-- Non-equal ancestor implies strict depth inequality in a `DFSInv` forest. -/
theorem DFSInv.depth_lt_of_ancestor_ne {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} {stack : List Frame}
    (h : DFSInv N G lists s stack) {u v : Fin N}
    (hanc : (s.forest N).Ancestor u v) (hne : u ≠ v) :
    (s.forest N).depth u < (s.forest N).depth v := by
  cases hanc with
  | refl => exact absurd rfl hne
  | tail hp_anc hp =>
    have hd_le := Forest.depth_le_of_ancestor h.depth_step hp_anc
    have hd_step := h.depth_step _ v hp
    omega

/-- Part I, Section 1: each undirected edge has exactly one oriented record.
The orientation is the parent-to-child or descendant-to-ancestor orientation. -/
theorem searchRecordsStatement : SearchRecordsStatement := by
  intro N G lists search hAdj hdfs
  obtain ⟨s, hs, hinv, hall⟩ := depthFirstSearch_spec hAdj
  rw [hs] at hdfs
  injection hdfs with hsearch_eq
  subst hsearch_eq
  have hforest : ({ s with postorder := s.postorder.reverse } : Search).forest N = s.forest N := rfl
  have hedges : ({ s with postorder := s.postorder.reverse } : Search).edges = s.edges := rfl
  rw [hforest, hedges]
  have hisDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
  have hrec_spec : ∀ i, i < s.edges.size → ∃ e : Arc N,
      s.edges[i]!.source = e.1.val ∧ s.edges[i]!.target = e.2.val ∧
      (((s.edges[i]!).tree = true ∧ (s.forest N).TreeEdge e) ∨
        ((s.edges[i]!).tree = false ∧ (s.forest N).BackEdge G e)) := by
    intro i hi
    obtain ⟨hs_lt, ht_lt, hvs, hvt, ⟨k, hsc, hk⟩, htree⟩ := hinv.edges_valid i hi
    let e : Arc N := (⟨(s.edges[i]!).source, hs_lt⟩, ⟨(s.edges[i]!).target, ht_lt⟩)
    refine ⟨e, rfl, rfl, ?_⟩
    have hadj : G.Adj e.1 e.2 := by
      rw [← adj_mem_iff hAdj hs_lt ht_lt, ← hk]
      rcases hsc with ⟨_, hk_len, _⟩
      rw [getElem!_pos _ k hk_len]
      exact List.getElem_mem hk_len
    cases htr_bool : (s.edges[i]!).tree
    · right
      simp only [htr_bool, Bool.false_eq_true, ↓reduceIte] at htree
      refine ⟨rfl, hadj, ?_, htree.2, ?_⟩
      · rcases hisDFS.2.2 e.1 e.2 hadj with h1 | h2
        · have hd_le := Forest.depth_le_of_ancestor hinv.depth_step h1
          dsimp only [e] at hd_le
          exact absurd hd_le (by omega)
        · exact h2
      · intro hpar
        exact htree.1 ((hinv.forest_parent_some_iff e.2 e.1).mp hpar)
    · left
      refine ⟨rfl, ?_⟩
      simp only [htr_bool, ↓reduceIte] at htree
      exact (hinv.forest_parent_some_iff e.1 e.2).mpr htree.1
  refine ⟨hrec_spec, ?_⟩
  intro u v hadj
  have huv_ne : u ≠ v := G.ne_of_adj hadj
  -- Helper: any record with endpoints `(x, y)` has either `parent y = some x` or
  -- (`parent x ≠ some y` and `depth y < depth x`).
  have hedge_orient : ∀ (i : ℕ) (hi : i < s.edges.size) (x y : Fin N),
      s.edges[i]!.source = x.val → s.edges[i]!.target = y.val →
      ((s.forest N).parent y = some x ∧ (s.forest N).depth y = (s.forest N).depth x + 1) ∨
      ((s.forest N).parent x ≠ some y ∧ (s.forest N).depth y < (s.forest N).depth x) := by
    intro i hi x y hx hy
    obtain ⟨e, he1, he2, hkind⟩ := hrec_spec i hi
    have hex : e.1 = x := Fin.ext (he1.symm.trans hx)
    have hey : e.2 = y := Fin.ext (he2.symm.trans hy)
    rcases hkind with ⟨_, hte⟩ | ⟨_, hbe⟩
    · left
      change (s.forest N).parent e.2 = some e.1 at hte
      rw [hex, hey] at hte
      exact ⟨hte, hinv.depth_step x y hte⟩
    · right
      rcases hbe with ⟨_, _, hd_lt, hnp⟩
      rw [hex, hey] at hd_lt hnp
      exact ⟨hnp, hd_lt⟩
  -- Uniqueness: any two records matching `{u, v}` must have the same orientation and index
  have huniq : ∀ (i j : Fin s.edges.size),
      ((s.edges[i.val]!.source = u.val ∧ s.edges[i.val]!.target = v.val) ∨
        (s.edges[i.val]!.source = v.val ∧ s.edges[i.val]!.target = u.val)) →
      ((s.edges[j.val]!.source = u.val ∧ s.edges[j.val]!.target = v.val) ∨
        (s.edges[j.val]!.source = v.val ∧ s.edges[j.val]!.target = u.val)) →
      i = j := by
    intro i j hi hj
    have hnot_opp : ∀ (a b : Fin s.edges.size),
        s.edges[a.val]!.source = u.val → s.edges[a.val]!.target = v.val →
        s.edges[b.val]!.source = v.val → s.edges[b.val]!.target = u.val → False := by
      intro a b ha1 ha2 hb1 hb2
      rcases hedge_orient a.val a.2 u v ha1 ha2 with ⟨hp1, hd1⟩ | ⟨hnp1, hd1⟩ <;>
        rcases hedge_orient b.val b.2 v u hb1 hb2 with ⟨hp2, hd2⟩ | ⟨hnp2, hd2⟩
      · omega
      · exact hnp2 hp1
      · exact hnp1 hp2
      · omega
    rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
    · exact Fin.ext (hinv.edges_inj i.val i.2 j.val j.2 (hi1.trans hj1.symm) (hi2.trans hj2.symm))
    · exact False.elim (hnot_opp i j hi1 hi2 hj1 hj2)
    · exact False.elim (hnot_opp j i hj1 hj2 hi1 hi2)
    · exact Fin.ext (hinv.edges_inj i.val i.2 j.val j.2 (hi1.trans hj1.symm) (hi2.trans hj2.symm))
  -- Existence: check parent relation first, otherwise use `scanned_edge_exists`
  by_cases hpv : s.parent[v.val]?.join = some u.val
  · obtain ⟨i, hi_lt, _, hsrc, htg⟩ := (hinv.parent_iff_edge v.val v.2 u.val).mp hpv
    exact ⟨⟨i, hi_lt⟩, Or.inl ⟨hsrc, htg⟩, fun j hj => huniq j ⟨i, hi_lt⟩ hj (Or.inl ⟨hsrc, htg⟩)⟩
  · by_cases hpu : s.parent[u.val]?.join = some v.val
    · obtain ⟨i, hi_lt, _, hsrc, htg⟩ := (hinv.parent_iff_edge u.val u.2 v.val).mp hpu
      exact ⟨⟨i, hi_lt⟩, Or.inr ⟨hsrc, htg⟩, fun j hj => huniq j ⟨i, hi_lt⟩ hj (Or.inr ⟨hsrc, htg⟩)⟩
    · rcases hisDFS.2.2 u v hadj with hanc_uv | hanc_vu
      · have hd_lt : (s.forest N).depth u < (s.forest N).depth v :=
          hinv.depth_lt_of_ancestor_ne hanc_uv huv_ne
        have hmem : u.val ∈ (List.ofFn lists).toArray[v.val]! :=
          (adj_mem_iff hAdj v.2 u.2).mpr hadj.symm
        obtain ⟨k, hk_lt, hget⟩ := List.getElem_of_mem hmem
        have hv_post : v.val ∈ s.postorder := by
          have := (hinv.visited_iff v.val).mp (hall v.val v.2)
          simpa using this
        have hsc : Scanned N lists s [] v.val k := ⟨v.2, hk_lt, Or.inl hv_post⟩
        have hget! : ((List.ofFn lists).toArray[v.val]!)[k]! = u.val := by
          rw [getElem!_pos _ k hk_lt, hget]
        have hu' : ((List.ofFn lists).toArray[v.val]!)[k]! < N := by
          rw [hget!]; exact u.2
        have hcond : s.parent[v.val]?.join ≠ some ((List.ofFn lists).toArray[v.val]!)[k]! ∧
            (s.forest N).depth ⟨((List.ofFn lists).toArray[v.val]!)[k]!, hu'⟩ <
              (s.forest N).depth v := by
          refine ⟨by rw [hget!]; exact hpv, ?_⟩
          convert hd_lt using 2
          exact Fin.ext hget!
        obtain ⟨i, hi_lt, hsrc, htg⟩ := hinv.scanned_edge_exists v.val k hsc v.2 hu' (Or.inr hcond)
        rw [hget!] at htg
        exact ⟨⟨i, hi_lt⟩, Or.inr ⟨hsrc, htg⟩, fun j hj => huniq j ⟨i, hi_lt⟩ hj (Or.inr ⟨hsrc, htg⟩)⟩
      · have hd_lt : (s.forest N).depth v < (s.forest N).depth u :=
          hinv.depth_lt_of_ancestor_ne hanc_vu huv_ne.symm
        have hmem : v.val ∈ (List.ofFn lists).toArray[u.val]! :=
          (adj_mem_iff hAdj u.2 v.2).mpr hadj
        obtain ⟨k, hk_lt, hget⟩ := List.getElem_of_mem hmem
        have hu_post : u.val ∈ s.postorder := by
          have := (hinv.visited_iff u.val).mp (hall u.val u.2)
          simpa using this
        have hsc : Scanned N lists s [] u.val k := ⟨u.2, hk_lt, Or.inl hu_post⟩
        have hget! : ((List.ofFn lists).toArray[u.val]!)[k]! = v.val := by
          rw [getElem!_pos _ k hk_lt, hget]
        have hv' : ((List.ofFn lists).toArray[u.val]!)[k]! < N := by
          rw [hget!]; exact v.2
        have hcond : s.parent[u.val]?.join ≠ some ((List.ofFn lists).toArray[u.val]!)[k]! ∧
            (s.forest N).depth ⟨((List.ofFn lists).toArray[u.val]!)[k]!, hv'⟩ <
              (s.forest N).depth u := by
          refine ⟨by rw [hget!]; exact hpu, ?_⟩
          convert hd_lt using 2
          exact Fin.ext hget!
        obtain ⟨i, hi_lt, hsrc, htg⟩ := hinv.scanned_edge_exists u.val k hsc u.2 hv' (Or.inr hcond)
        rw [hget!] at htg
        exact ⟨⟨i, hi_lt⟩, Or.inl ⟨hsrc, htg⟩, fun j hj => huniq j ⟨i, hi_lt⟩ hj (Or.inl ⟨hsrc, htg⟩)⟩

end GraphMinor.LRPlanarity
