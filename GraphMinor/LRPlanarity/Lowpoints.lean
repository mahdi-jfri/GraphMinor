module

public import GraphMinor.LRPlanarity.LowpointsInvariants

/-!
# Lowpoints and Edge Keys (Part I, Section 1)

This module completes the inductive proof of `LowInv` across back-edge and
tree-edge steps of `depthFirstSearch`, and proves `LowpointsStatement` from
`GraphMinor/LRPlanarity/Statements.lean`, following Part I, Section 1 of
`docs/planarity/planarity_test.tex`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

theorem LowInv.step_back {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame} (h : LowInv N G lists s (f :: rest))
    (hAdj : Compute.IsAdjListFamily G lists)
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (hw_none : ¬ (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).isNone = true)
    (hback : s.parent[f.vertex]?.join ≠
        some (((List.ofFn lists).toArray[f.vertex]!)[f.next]!) ∧
      (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).getD 0 <
        (s.depth[f.vertex]?.join).getD 0) :
    let w := ((List.ofFn lists).toArray[f.vertex]!)[f.next]!
    let res := addEdge s f.vertex w false
    LowInv N G lists (finishEdge res.1 res.2) ({ f with next := f.next + 1 } :: rest) := by
  intro w res
  have hw_vis : s.Visited w := by
    by_contra hnot
    exact hw_none ((Search.not_visited_iff s w).mp hnot)
  let s₁ := res.1
  let b_new := s.edges.size
  let s' := finishEdge s₁ b_new
  let stack' := { f with next := f.next + 1 } :: rest
  change LowInv N G lists s' stack'
  have hdfs' : DFSInv N G lists s' stack' := h.dfs.step_back hAdj hlen hw_vis hback
  have hv_top : f.vertex < N := h.dfs.active_lt f.vertex (by simp)
  have hb_lt : b_new < s₁.edges.size := by simp [s₁, res, b_new]
  have hb_new_eq : s₁.edges[b_new]! =
      ⟨f.vertex, w, false,
        ⟨(s.depth[w]?.join).getD 0, (s.depth[f.vertex]?.join).getD 0⟩, 0⟩ := by
    dsimp [s₁, res, addEdge, b_new]
    rw [getElem!_push_EdgeRecord s.edges _ s.edges.size le_rfl]
    simp
  have h_old_eq : ∀ j < s.edges.size, s₁.edges[j]! = s.edges[j]! := by
    intro j hj
    dsimp [s₁, res, addEdge]
    rw [getElem!_push_EdgeRecord s.edges _ j (le_of_lt hj)]
    simp [ne_of_lt hj]
  have hp_bound : ∀ p, s₁.parentEdge[(s₁.edges[b_new]!).source]?.join = some p →
      p < s₁.edges.size ∧ p ≠ b_new := by
    intro p hp
    rw [hb_new_eq] at hp
    obtain ⟨hp_lt, _, _⟩ := (h.dfs.parentEdge_iff f.vertex hv_top p).mp hp
    exact ⟨by simp [s₁, res]; omega, ne_of_lt hp_lt⟩
  obtain ⟨hpair_b, hkey_b, hparent_p, hother⟩ := finishEdge_edges_getElem! s₁ b_new hb_lt hp_bound
  have hmap : stack'.map Frame.vertex = (f :: rest).map Frame.vertex := rfl
  have hacc_vtop : accDepths N s' stack' ⟨f.vertex, hv_top⟩ =
      insert ((s.depth[w]?.join).getD 0) (accDepths N s (f :: rest) ⟨f.vertex, hv_top⟩) := by
    dsimp [s']
    rw [accDepths_finishEdge]
    unfold accDepths
    have hfilter_eq : accBackEdges N s₁ stack' ⟨f.vertex, hv_top⟩ =
        insert b_new (accBackEdges N s (f :: rest) ⟨f.vertex, hv_top⟩) := by
      ext j
      simp only [accBackEdges, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      have hsz1 : s₁.edges.size = s.edges.size + 1 := by simp [s₁, res]
      have hfor1 : s₁.forest N = s.forest N := rfl
      rw [hsz1, hfor1]
      have hin_sub : ∀ x : Fin N,
          InAccSubtree (s.forest N) stack' ⟨f.vertex, hv_top⟩ x ↔
            InAccSubtree (s.forest N) (f :: rest) ⟨f.vertex, hv_top⟩ x := by
        intro x; unfold InAccSubtree; rw [hmap]
      by_cases hj : j = b_new
      · subst hj
        rw [hb_new_eq]
        refine ⟨fun _ => Or.inl rfl, fun _ => ⟨by omega, rfl, ⟨f.vertex, hv_top⟩, rfl,
          (hin_sub _).mpr ((h.dfs.inAccSubtree_top_iff hv_top _).mpr rfl)⟩⟩
      · simp only [hj, false_or]
        have hnot_eq : j ≠ s.edges.size := hj
        constructor
        · rintro ⟨hj_lt, htree, x, hx_src, hsub⟩
          have hj_lt' : j < s.edges.size := by omega
          rw [h_old_eq j hj_lt'] at htree hx_src
          exact ⟨hj_lt', htree, x, hx_src, (hin_sub x).mp hsub⟩
        · rintro ⟨hj_lt', htree, x, hx_src, hsub⟩
          rw [h_old_eq j hj_lt']
          exact ⟨by omega, htree, x, hx_src, (hin_sub x).mpr hsub⟩
    rw [hfilter_eq, Finset.image_insert]
    have htarget_eq : (s₁.depth[(s₁.edges[b_new]!).target]?.join).getD 0 =
        (s.depth[w]?.join).getD 0 := by
      rw [hb_new_eq]; rfl
    rw [htarget_eq]
    congr 1
    apply Finset.image_congr
    intro j hj
    simp only [Finset.mem_coe, accBackEdges, Finset.mem_filter, Finset.mem_range] at hj
    dsimp only
    rw [h_old_eq j hj.1]
    rfl
  have hacc_other : ∀ v : Fin N, v ≠ ⟨f.vertex, hv_top⟩ →
      accDepths N s' stack' v = accDepths N s (f :: rest) v := by
    intro v hv_ne
    dsimp [s']
    rw [accDepths_finishEdge]
    unfold accDepths
    have hfilter_eq : accBackEdges N s₁ stack' v = accBackEdges N s (f :: rest) v := by
      ext j
      simp only [accBackEdges, Finset.mem_filter, Finset.mem_range]
      have hsz1 : s₁.edges.size = s.edges.size + 1 := by simp [s₁, res]
      have hfor1 : s₁.forest N = s.forest N := rfl
      rw [hsz1, hfor1]
      have hin_sub : ∀ x : Fin N,
          InAccSubtree (s.forest N) stack' v x ↔
            InAccSubtree (s.forest N) (f :: rest) v x := by
        intro x; unfold InAccSubtree; rw [hmap]
      by_cases hj : j = b_new
      · subst hj
        rw [hb_new_eq]
        have hnot_sub : ¬ InAccSubtree (s.forest N) (f :: rest) v ⟨f.vertex, hv_top⟩ := by
          rw [h.dfs.inAccSubtree_top_iff hv_top v]
          exact hv_ne
        have hnot_lt : ¬ b_new < s.edges.size := lt_irrefl b_new
        simp only [hnot_lt, false_and, iff_false, not_and, not_exists]
        intro _ _ x hx_src hsub
        have hx_eq : x = ⟨f.vertex, hv_top⟩ := Fin.ext hx_src.symm
        rw [hx_eq] at hsub
        exact hnot_sub ((hin_sub _).mp hsub)
      · have hnot_eq : j ≠ s.edges.size := hj
        constructor
        · rintro ⟨hj_lt, htree, x, hx_src, hsub⟩
          have hj_lt' : j < s.edges.size := by omega
          rw [h_old_eq j hj_lt'] at htree hx_src
          exact ⟨hj_lt', htree, x, hx_src, (hin_sub x).mp hsub⟩
        · rintro ⟨hj_lt', htree, x, hx_src, hsub⟩
          rw [h_old_eq j hj_lt']
          exact ⟨by omega, htree, x, hx_src, (hin_sub x).mpr hsub⟩
    rw [hfilter_eq]
    apply Finset.image_congr
    intro j hj
    simp only [Finset.mem_coe, accBackEdges, Finset.mem_filter, Finset.mem_range] at hj
    dsimp only
    rw [h_old_eq j hj.1]
    rfl
  refine ⟨hdfs', ?_, ?_, ?_⟩
  · intro i hi htree
    have hi_sz : i < s.edges.size + 1 := by
      simpa [s', s₁, res, finishEdge_edges_size, addEdge_fst_edges_size] using hi
    have htree1 : (s₁.edges[i]!).tree = false := by
      simpa [s', finishEdge_edges_tree] using htree
    change ((finishEdge s₁ b_new).edges[i]!).pair = _ ∧
      ((finishEdge s₁ b_new).edges[i]!).key = _
    rw [finishEdge_depth, finishEdge_edges_target, finishEdge_edges_source]
    by_cases hib : i = b_new
    · subst hib
      rw [hpair_b, hkey_b, hb_new_eq]
      have hd1 : s₁.depth = s.depth := rfl
      rw [hd1]
      simp
    · have hnot_eq : i ≠ s.edges.size := hib
      have hi_lt : i < s.edges.size := by omega
      rw [h_old_eq i hi_lt] at htree1
      have hip : s₁.parentEdge[(s₁.edges[b_new]!).source]?.join ≠ some i := by
        rw [hb_new_eq]
        intro hp
        obtain ⟨_, hp_tree, _⟩ := (h.dfs.parentEdge_iff f.vertex hv_top i).mp hp
        rw [hp_tree] at htree1; exact Bool.noConfusion htree1
      rw [hother i hib hip, h_old_eq i hi_lt]
      exact h.back_spec i hi_lt htree1
  · intro i hi htree u v hu hv
    have hi_sz : i < s.edges.size + 1 := by
      simpa [s', s₁, res, finishEdge_edges_size, addEdge_fst_edges_size] using hi
    have htree1 : (s₁.edges[i]!).tree = true := by
      simpa [s', finishEdge_edges_tree] using htree
    have hib : i ≠ b_new := by
      intro heq; subst heq; rw [hb_new_eq] at htree1; exact Bool.noConfusion htree1
    have hnot_eq : i ≠ s.edges.size := hib
    have hi_lt : i < s.edges.size := by omega
    have hu' : (s.edges[i]!).source = u.val := by
      have h1 : (s'.edges[i]!).source = (s.edges[i]!).source := by
        dsimp [s']; rw [finishEdge_edges_source, h_old_eq i hi_lt]
      exact h1.symm.trans hu
    have hv' : (s.edges[i]!).target = v.val := by
      have h1 : (s'.edges[i]!).target = (s.edges[i]!).target := by
        dsimp [s']; rw [finishEdge_edges_target, h_old_eq i hi_lt]
      exact h1.symm.trans hv
    have hfor_eq : s'.forest N = s.forest N := by
      dsimp [s', s₁, res]; rw [finishEdge_forest, addEdge_fst_forest]
    rw [hfor_eq]
    have htree_s : (s.edges[i]!).tree = true := by rwa [← h_old_eq i hi_lt]
    by_cases hip : s₁.parentEdge[(s₁.edges[b_new]!).source]?.join = some i
    · have hip' : s.parentEdge[f.vertex]?.join = some i := by rwa [hb_new_eq] at hip
      obtain ⟨_, _, hi_tgt⟩ := (h.dfs.parentEdge_iff f.vertex hv_top i).mp hip'
      obtain ⟨_, _, _, _, _, htree_i⟩ := h.dfs.edges_valid i hi_lt
      simp only [htree_s, ↓reduceIte, hi_tgt] at htree_i
      have hi_par : s.parent[f.vertex]?.join = some (s.edges[i]!).source := htree_i.1
      have htgt_f : v = ⟨f.vertex, hv_top⟩ := Fin.ext (hv'.symm.trans hi_tgt)
      rw [htgt_f, hacc_vtop]
      change LowPairSpec _ _ ((finishEdge s₁ b_new).edges[i]!).pair
      rw [(hparent_p i hip).1, h_old_eq i hi_lt, hb_new_eq]
      dsimp only
      have hpair_i := h.tree_pair_spec i hi_lt htree_s u ⟨f.vertex, hv_top⟩ hu' hi_tgt
      have hins1 := lowpointInsertionStatement _ _ _ ((s.depth[w]?.join).getD 0) hpair_i
      have hins2 := lowpointInsertionStatement _ _ _ ((s.depth[f.vertex]?.join).getD 0) hins1
      apply (LowPairSpec.congr_lt ?_).mp hins2
      intro x hx
      simp only [Finset.mem_insert]
      have hfpar_i : (s.forest N).parent ⟨f.vertex, hv_top⟩ = some u :=
        (h.dfs.forest_parent_some_iff u ⟨f.vertex, hv_top⟩).mpr (hu' ▸ hi_par)
      have hd_step : (s.depth[f.vertex]?.join).getD 0 = (s.forest N).depth u + 1 :=
        h.dfs.depth_step u ⟨f.vertex, hv_top⟩ hfpar_i
      have hne_x : x ≠ (s.depth[f.vertex]?.join).getD 0 := by omega
      simp [hne_x]
    · have htgt_ne : v ≠ ⟨f.vertex, hv_top⟩ := by
        intro heq
        have hval : (s.edges[i]!).target = f.vertex := hv'.trans (congrArg Fin.val heq)
        apply hip
        rw [hb_new_eq]
        exact (h.dfs.parentEdge_iff f.vertex hv_top i).mpr ⟨hi_lt, htree_s, hval⟩
      rw [hacc_other v htgt_ne]
      change LowPairSpec _ _ ((finishEdge s₁ b_new).edges[i]!).pair
      rw [hother i hib hip, h_old_eq i hi_lt]
      exact h.tree_pair_spec i hi_lt htree_s u v hu' hv'
  · intro i hi htree hnot_mem u hu
    have hi_sz : i < s.edges.size + 1 := by
      simpa [s', s₁, res, finishEdge_edges_size, addEdge_fst_edges_size] using hi
    have htree1 : (s₁.edges[i]!).tree = true := by
      simpa [s', finishEdge_edges_tree] using htree
    have hib : i ≠ b_new := by
      intro heq; subst heq; rw [hb_new_eq] at htree1; exact Bool.noConfusion htree1
    have hnot_eq : i ≠ s.edges.size := hib
    have hi_lt : i < s.edges.size := by omega
    have hu' : (s.edges[i]!).source = u.val := by
      have h1 : (s'.edges[i]!).source = (s.edges[i]!).source := by
        dsimp [s']; rw [finishEdge_edges_source, h_old_eq i hi_lt]
      exact h1.symm.trans hu
    have hfor_eq : s'.forest N = s.forest N := by
      dsimp [s', s₁, res]; rw [finishEdge_forest, addEdge_fst_forest]
    rw [hfor_eq]
    have hnot_mem' : (s.edges[i]!).target ∉ (f :: rest).map Frame.vertex := by
      have htgt : (s'.edges[i]!).target = (s.edges[i]!).target := by
        dsimp [s']; rw [finishEdge_edges_target, h_old_eq i hi_lt]
      rwa [htgt, hmap] at hnot_mem
    have hne_f : (s.edges[i]!).target ≠ f.vertex := by
      intro heq; apply hnot_mem'; simp [heq]
    have hip : s₁.parentEdge[(s₁.edges[b_new]!).source]?.join ≠ some i := by
      rw [hb_new_eq]
      intro hp
      obtain ⟨_, _, hi_tgt⟩ := (h.dfs.parentEdge_iff f.vertex hv_top i).mp hp
      exact hne_f hi_tgt
    change ((finishEdge s₁ b_new).edges[i]!).key = _
    rw [hother i hib hip, h_old_eq i hi_lt]
    have htree_s : (s.edges[i]!).tree = true := by rwa [← h_old_eq i hi_lt]
    exact h.tree_key_spec i hi_lt htree_s hnot_mem' u hu'

theorem LowInv.step_tree {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame} (h : LowInv N G lists s (f :: rest))
    (hAdj : Compute.IsAdjListFamily G lists)
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (hw_none : (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).isNone = true) :
    let w := ((List.ofFn lists).toArray[f.vertex]!)[f.next]!
    let res := addEdge s f.vertex w true
    let s₁ := res.1
    let i_new := res.2
    let s' := { s₁ with
      parent := s₁.parent.set! w (some f.vertex)
      parentEdge := s₁.parentEdge.set! w (some i_new)
      depth := s₁.depth.set! w (some ((s₁.depth[f.vertex]?.join).getD 0 + 1)) }
    LowInv N G lists s' (⟨w, 0⟩ :: { f with next := f.next + 1 } :: rest) := by
  intro w res s₁ i_new s'
  let stack' := ⟨w, 0⟩ :: { f with next := f.next + 1 } :: rest
  change LowInv N G lists s' stack'
  have hdfs' : DFSInv N G lists s' stack' := h.dfs.step_tree hAdj hlen hw_none
  have hv_top : f.vertex < N := h.dfs.active_lt f.vertex (by simp)
  have hw_lt : w < N := hdfs'.active_lt w (by simp [stack'])
  have hw_unvis : ¬ s.Visited w := (Search.not_visited_iff s w).mpr hw_none
  have hsz_d : w < s.depth.size := by rw [h.dfs.depth_size]; exact hw_lt
  have hsz_p : w < s.parent.size := by rw [h.dfs.parent_size]; exact hw_lt
  have hdepth_s' : ∀ u, s'.depth[u]?.join =
      if u = w then some ((s.depth[f.vertex]?.join).getD 0 + 1) else s.depth[u]?.join :=
    getElem?_join_set! s.depth w _ hsz_d
  have hpar_s' : ∀ u, s'.parent[u]?.join =
      if u = w then some f.vertex else s.parent[u]?.join :=
    getElem?_join_set! s.parent w _ hsz_p
  have hdepth_eq : ∀ u, s.Visited u →
      (s'.depth[u]?.join).getD 0 = (s.depth[u]?.join).getD 0 := by
    intro u hu_vis
    have hne : u ≠ w := fun heq => hw_unvis (heq ▸ hu_vis)
    rw [hdepth_s' u]
    simp [hne]
  have hpar_eq : ∀ u : Fin N, u.val ≠ w →
      (s'.forest N).parent u = (s.forest N).parent u := by
    intro u hne
    unfold Search.forest
    dsimp only
    rw [hpar_s' u.val]
    simp [hne]
  have hanc_vis : ∀ {y x : Fin N}, s.Visited x.val →
      ((s'.forest N).Ancestor y x ↔ (s.forest N).Ancestor y x) ∧
      ((s'.forest N).Ancestor y x → s.Visited y.val) := by
    intro y x hx_vis
    have imp1 : ∀ {a b : Fin N}, (s'.forest N).Ancestor a b → s.Visited b.val →
        s.Visited a.val ∧ (s.forest N).Ancestor a b := by
      intro a b hanc
      induction hanc using Relation.ReflTransGen.head_induction_on with
      | refl => intro hb; exact ⟨hb, Relation.ReflTransGen.refl⟩
      | @head a c hp _ ih =>
        intro hb
        obtain ⟨hc_vis, hanc_cb⟩ := ih hb
        have hcw : c.val ≠ w := fun heq => hw_unvis (heq ▸ hc_vis)
        have hp_s : (s.forest N).parent c = some a := by rwa [← hpar_eq c hcw]
        have hpar_raw : s.parent[c.val]?.join = some a.val :=
          (h.dfs.forest_parent_some_iff a c).mp hp_s
        obtain ⟨_, _, ha_vis, _⟩ := h.dfs.parent_spec c a.val hpar_raw
        exact ⟨ha_vis, Relation.ReflTransGen.head hp_s hanc_cb⟩
    have imp2 : ∀ {a b : Fin N}, (s.forest N).Ancestor a b → s.Visited b.val →
        (s'.forest N).Ancestor a b := by
      intro a b hanc
      induction hanc using Relation.ReflTransGen.head_induction_on with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | @head a c hp hanc' ih =>
        intro hb
        have hc_vis : s.Visited c.val := by
          clear hp a ih
          induction hanc' using Relation.ReflTransGen.head_induction_on with
          | refl => exact hb
          | @head d e hp' _ ih' =>
            have hpar_raw : s.parent[e.val]?.join = some d.val :=
              (h.dfs.forest_parent_some_iff d e).mp hp'
            obtain ⟨_, _, hd_vis, _⟩ := h.dfs.parent_spec e d.val hpar_raw
            exact hd_vis
        have hcw : c.val ≠ w := fun heq => hw_unvis (heq ▸ hc_vis)
        have hp_s' : (s'.forest N).parent c = some a := by rwa [hpar_eq c hcw]
        exact Relation.ReflTransGen.head hp_s' (ih hb)
    exact ⟨⟨fun h1 => (imp1 h1 hx_vis).2, fun h2 => imp2 h2 hx_vis⟩,
      fun h1 => (imp1 h1 hx_vis).1⟩
  have hi_new_eq : s'.edges[s.edges.size]! =
      ⟨f.vertex, w, true,
        ⟨(s.depth[f.vertex]?.join).getD 0, (s.depth[f.vertex]?.join).getD 0⟩, 0⟩ := by
    dsimp [s', s₁, res, addEdge]
    rw [getElem!_push_EdgeRecord s.edges _ s.edges.size le_rfl]
    simp
  have h_old_eq : ∀ j < s.edges.size, s'.edges[j]! = s.edges[j]! := by
    intro j hj
    dsimp [s', s₁, res, addEdge]
    rw [getElem!_push_EdgeRecord s.edges _ j (le_of_lt hj)]
    simp [ne_of_lt hj]
  have hacc_w : accDepths N s' stack' ⟨w, hw_lt⟩ = ∅ := by
    unfold accDepths
    rw [Finset.image_eq_empty]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    simp only [accBackEdges, Finset.mem_filter, Finset.mem_range] at hb
    rcases hb with ⟨hb_lt, htree, x, hx_src, hsub⟩
    have hb_sz : s'.edges.size = s.edges.size + 1 := by simp [s', s₁, res]
    have hne_new : b ≠ s.edges.size := by
      intro heq; subst heq; rw [hi_new_eq] at htree; exact Bool.noConfusion htree
    have hb_old : b < s.edges.size := by omega
    rw [h_old_eq b hb_old] at hx_src
    obtain ⟨_, _, hx_vis, _⟩ := h.dfs.edges_valid b hb_old
    have hx_vis' : s.Visited x.val := hx_src ▸ hx_vis
    have hw_vis := (hanc_vis hx_vis').2 hsub.1
    exact hw_unvis hw_vis
  have hacc_old : ∀ v : Fin N,
      accDepths N s' stack' v = accDepths N s (f :: rest) v := by
    intro v
    unfold accDepths
    have hfilter_eq : accBackEdges N s' stack' v = accBackEdges N s (f :: rest) v := by
      ext b
      simp only [accBackEdges, Finset.mem_filter, Finset.mem_range]
      have hb_sz : s'.edges.size = s.edges.size + 1 := by simp [s', s₁, res]
      rw [hb_sz]
      by_cases hb_new : b = s.edges.size
      · subst hb_new
        rw [hi_new_eq]
        simp
      · constructor
        · rintro ⟨hb_lt, htree, x, hx_src, hsub⟩
          have hb_old : b < s.edges.size := by omega
          rw [h_old_eq b hb_old] at htree hx_src
          obtain ⟨_, _, hx_vis, _⟩ := h.dfs.edges_valid b hb_old
          have hx_vis' : s.Visited x.val := hx_src ▸ hx_vis
          refine ⟨hb_old, htree, x, hx_src, (hanc_vis hx_vis').1.mp hsub.1, ?_⟩
          intro c hc hpc hanc_cx
          have hc_vis : s.Visited c.val := (h.dfs.visited_iff c.val).mpr (Or.inl hc)
          have hcw' : c.val ≠ w := fun heq => hw_unvis (heq ▸ hc_vis)
          have hpc' : (s'.forest N).parent c = some v := by rwa [hpar_eq c hcw']
          have hanc_cx' : (s'.forest N).Ancestor c x := (hanc_vis hx_vis').1.mpr hanc_cx
          have hc_mem' : c.val ∈ stack'.map Frame.vertex := by
            dsimp [stack']
            simp only [List.map_cons, List.mem_cons] at hc ⊢
            exact Or.inr hc
          exact hsub.2 c hc_mem' hpc' hanc_cx'
        · rintro ⟨hb_old, htree, x, hx_src, hsub⟩
          rw [h_old_eq b hb_old]
          obtain ⟨_, _, hx_vis, _⟩ := h.dfs.edges_valid b hb_old
          have hx_vis' : s.Visited x.val := hx_src ▸ hx_vis
          refine ⟨by omega, htree, x, hx_src, (hanc_vis hx_vis').1.mpr hsub.1, ?_⟩
          intro c hc' hpc' hanc_cx'
          dsimp [stack'] at hc'
          simp only [List.map_cons, List.mem_cons] at hc'
          rcases hc' with hcw_eq | hc_old
          · have hc_eq_w : c = ⟨w, hw_lt⟩ := Fin.ext hcw_eq
            rw [hc_eq_w] at hanc_cx'
            exact hw_unvis ((hanc_vis hx_vis').2 hanc_cx')
          · have hc_old' : c.val ∈ (f :: rest).map Frame.vertex := by
              simp only [List.map_cons, List.mem_cons]
              exact hc_old
            have hc_vis : s.Visited c.val := (h.dfs.visited_iff c.val).mpr (Or.inl hc_old')
            have hcw' : c.val ≠ w := fun heq => hw_unvis (heq ▸ hc_vis)
            have hpc : (s.forest N).parent c = some v := by rwa [← hpar_eq c hcw']
            have hanc_cx : (s.forest N).Ancestor c x := (hanc_vis hx_vis').1.mp hanc_cx'
            exact hsub.2 c hc_old' hpc hanc_cx
    rw [hfilter_eq]
    apply Finset.image_congr
    intro b hb
    simp only [Finset.mem_coe, accBackEdges, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨hb_old, _⟩ := hb
    dsimp only
    rw [h_old_eq b hb_old]
    obtain ⟨_, _, _, hy_vis, _⟩ := h.dfs.edges_valid b hb_old
    exact hdepth_eq _ hy_vis
  refine ⟨hdfs', ?_, ?_, ?_⟩
  · intro i hi htree
    have hb_sz : s'.edges.size = s.edges.size + 1 := by simp [s', s₁, res]
    have hne_new : i ≠ s.edges.size := by
      intro heq; subst heq; rw [hi_new_eq] at htree; exact Bool.noConfusion htree
    have hi_old : i < s.edges.size := by omega
    rw [h_old_eq i hi_old] at htree ⊢
    obtain ⟨_, _, hu_vis, hy_vis, _⟩ := h.dfs.edges_valid i hi_old
    rw [hdepth_eq _ hy_vis, hdepth_eq _ hu_vis]
    exact h.back_spec i hi_old htree
  · intro i hi htree u v hu hv
    have hb_sz : s'.edges.size = s.edges.size + 1 := by simp [s', s₁, res]
    by_cases hi_new : i = s.edges.size
    · subst hi_new
      rw [hi_new_eq] at hu hv ⊢
      have hv_eq : v = ⟨w, hw_lt⟩ := Fin.ext hv.symm
      have hu_eq : u = ⟨f.vertex, hv_top⟩ := Fin.ext hu.symm
      have hf_vis : s.Visited f.vertex := (h.dfs.visited_iff f.vertex).mpr (Or.inl (by simp))
      have hdf : (s'.forest N).depth ⟨f.vertex, hv_top⟩ = (s.depth[f.vertex]?.join).getD 0 :=
        hdepth_eq f.vertex hf_vis
      rw [hv_eq, hu_eq, hacc_w, hdf]
      unfold LowPairSpec
      simp
    · have hi_old : i < s.edges.size := by omega
      rw [h_old_eq i hi_old] at htree hu hv ⊢
      obtain ⟨_, _, hu_vis, _⟩ := h.dfs.edges_valid i hi_old
      have hdu : (s'.forest N).depth u = (s.forest N).depth u := by
        unfold Search.forest; dsimp only
        exact hdepth_eq u.val (hu ▸ hu_vis)
      rw [hacc_old, hdu]
      exact h.tree_pair_spec i hi_old htree u v hu hv
  · intro i hi htree hnot_mem u hu
    have hb_sz : s'.edges.size = s.edges.size + 1 := by simp [s', s₁, res]
    have hi_ne_new : i ≠ s.edges.size := by
      intro heq; subst heq
      apply hnot_mem
      rw [hi_new_eq]
      dsimp [stack']
      simp
    have hi_old : i < s.edges.size := by omega
    rw [h_old_eq i hi_old] at htree hu hnot_mem ⊢
    obtain ⟨_, _, hu_vis, _⟩ := h.dfs.edges_valid i hi_old
    have hdu : (s'.forest N).depth u = (s.forest N).depth u := by
      unfold Search.forest; dsimp only
      exact hdepth_eq u.val (hu ▸ hu_vis)
    have hnot_mem' : (s.edges[i]!).target ∉ (f :: rest).map Frame.vertex := by
      intro hmem
      apply hnot_mem
      dsimp [stack']
      simp only [List.map_cons, List.mem_cons] at hmem ⊢
      exact Or.inr hmem
    rw [hdu]
    exact h.tree_key_spec i hi_old htree hnot_mem' u hu

/-! ## Main Lowpoints Theorem -/

theorem searchFrames_lowInv {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hAdj : Compute.IsAdjListFamily G lists) :
    ∀ (fuel : ℕ) (s : Search) (stack : List Frame),
      LowInv N G lists s stack →
      workDone (List.ofFn lists).toArray s stack + fuel >
        (List.ofFn lists).toArray.foldl (fun total l => total + l.length) 0 + N →
      ∃ s', searchFrames (List.ofFn lists).toArray fuel s stack = some s' ∧
        LowInv N G lists s' [] ∧
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
      have hle := h.dfs.workDone_le
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
        have hle_next := h.dfs.frame_next_le f (by simp)
        have hwd : workDone (List.ofFn lists).toArray
            (match s.parentEdge[f.vertex]?.join with
             | none => { s with postorder := f.vertex :: s.postorder }
             | some p => finishEdge { s with postorder := f.vertex :: s.postorder } p) rest =
            workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
          cases s.parentEdge[f.vertex]?.join <;>
          · simp only [workDone, finishEdge_postorder, List.map_cons, List.sum_cons]
            omega
        have hfuel' : workDone (List.ofFn lists).toArray
            (match s.parentEdge[f.vertex]?.join with
             | none => { s with postorder := f.vertex :: s.postorder }
             | some p => finishEdge { s with postorder := f.vertex :: s.postorder } p) rest + fuel >
            (List.ofFn lists).toArray.foldl (fun total l => total + l.length) 0 + N := by
          rw [hwd]; omega
        obtain ⟨s', hs', hinv', hvis'⟩ := ih _ rest h' hfuel'
        refine ⟨s', hs', hinv', fun u hu => hvis' u ?_⟩
        cases s.parentEdge[f.vertex]?.join <;>
          simpa [Search.Visited] using hu
      · simp only [hlen, ↓reduceIte]
        have hlen' : f.next < ((List.ofFn lists).toArray[f.vertex]!).length := by omega
        have hf_lt : f.vertex < N := h.dfs.active_lt f.vertex (by simp)
        have hmem_w : ((List.ofFn lists).toArray[f.vertex]!)[f.next]! ∈
            (List.ofFn lists).toArray[f.vertex]! := by
          rw [getElem!_pos _ f.next hlen']
          exact List.getElem_mem hlen'
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
            rw [h.dfs.depth_size]; exact hw_lt
          simp only [Search.Visited, addEdge_fst_depth, getElem?_join_set! s.depth _ _ hw_sz]
          split_ifs with huw
          · simp
          · exact hu
        · simp only [hw_none, Bool.false_eq_true, ↓reduceIte]
          split_ifs with hback
          · have h' := h.step_back hAdj hlen' hw_none hback
            dsimp only at h'
            have hwd : workDone (List.ofFn lists).toArray
                (let p := addEdge s f.vertex ((List.ofFn lists).toArray[f.vertex]!)[f.next]! false
                 finishEdge p.1 p.2)
                ({ f with next := f.next + 1 } :: rest) =
                workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
              simp only [workDone, finishEdge_postorder, addEdge_fst_postorder,
                List.map_cons, List.sum_cons]
              omega
            dsimp only at hwd
            obtain ⟨s', hs', hinv', hvis'⟩ := ih _ _ h' (by omega)
            refine ⟨s', hs', hinv', fun u hu => hvis' u ?_⟩
            simpa [Search.Visited] using hu
          · have h' := h.step_skip hAdj hlen' hw_none hback
            have hwd : workDone (List.ofFn lists).toArray s
                ({ f with next := f.next + 1 } :: rest) =
                workDone (List.ofFn lists).toArray s (f :: rest) + 1 := by
              simp only [workDone, List.map_cons, List.sum_cons]
              omega
            exact ih _ _ h' (by omega)

set_option linter.auxLemma false in
private theorem dfs_loop_lowInv {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hAdj : Compute.IsAdjListFamily G lists) :
    let adj := (List.ofFn lists).toArray
    let fuel := adj.foldl (fun total l => total + l.length) 0 + adj.size + 1
    ∀ (k : ℕ) (_hk : k ≤ N) (s : Search),
      LowInv N G lists s [] →
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
        LowInv N G lists s' [] ∧
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
      obtain ⟨t, ht, hinv_t, hvis_t⟩ := searchFrames_lowInv hAdj fuel _ _ hpush hfuel
      rw [ht]
      dsimp only
      have hsz : N - (k + 1) < s.depth.size := by rw [h.dfs.depth_size]; exact hroot_lt
      have hroot_vis : t.Visited (N - (k + 1)) := by
        apply hvis_t
        have hd_s0 := getElem?_join_set! s.depth (N - (k + 1)) (some 0) hsz (N - (k + 1))
        unfold Search.Visited
        rw [hd_s0]
        simp
      have hall_t : ∀ u < N - k, t.Visited u := by
        intro u hu
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : u < (N - (k + 1)) + 1)) with hlt | rfl
        · apply hvis_t
          have hd_s0 := getElem?_join_set! s.depth (N - (k + 1)) (some 0) hsz u
          unfold Search.Visited
          rw [hd_s0]
          split_ifs with heq
          · simp
          · exact hall u hlt
        · exact hroot_vis
      have heq_start : N - (k + 1) + 1 = N - k := by omega
      rw [heq_start]
      exact ih (by omega) t hinv_t hall_t
    · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
      have hroot_vis : s.Visited (N - (k + 1)) := by
        by_contra hnot
        exact hnone ((Search.not_visited_iff s _).mp hnot)
      have hall_s : ∀ u < N - k, s.Visited u := by
        intro u hu
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : u < (N - (k + 1)) + 1)) with hlt | rfl
        · exact hall u hlt
        · exact hroot_vis
      have heq_start : N - (k + 1) + 1 = N - k := by omega
      rw [heq_start]
      exact ih (by omega) s h hall_s

theorem depthFirstSearch_lowInv {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hAdj : Compute.IsAdjListFamily G lists) :
    ∃ s, depthFirstSearch (List.ofFn lists).toArray =
      some { s with postorder := s.postorder.reverse } ∧
      LowInv N G lists s [] ∧
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
  have hinit : LowInv N G lists (initialSearch (List.ofFn lists).toArray.size) [] := by
    rw [hsz]
    exact LowInv.init N G lists
  obtain ⟨s', hs', hinv', hall'⟩ := dfs_loop_lowInv hAdj N le_rfl
    (initialSearch (List.ofFn lists).toArray.size) hinit (fun u hu => by omega)
  refine ⟨s', ?_, hinv', hall'⟩
  rw [hs']
  rfl

/-- Part I, Section 1: postorder lowpoint propagation computes strict returns,
the thick bit, and the key, without enumerating returns. -/
theorem lowpointsStatement : LowpointsStatement := by
  intro N G lists search hAdj hsearch i hi
  obtain ⟨s, hs, hlow, hall⟩ := depthFirstSearch_lowInv hAdj
  rw [hs] at hsearch
  injection hsearch with hsearch_eq
  have hedges_eq : search.edges = s.edges := by rw [← hsearch_eq]
  have hforest_eq : search.forest N = s.forest N := by rw [← hsearch_eq]; rfl
  rw [hedges_eq] at hi ⊢
  rw [hforest_eq]
  obtain ⟨hrec, hex_rec⟩ := searchRecordsStatement N G lists search hAdj
    (by rw [hs, hsearch_eq])
  obtain ⟨e, he_src, he_tgt, hspec⟩ := hrec i (by rwa [hedges_eq])
  rw [hedges_eq] at he_src he_tgt hspec
  rw [hforest_eq] at hspec
  refine ⟨e, he_src, he_tgt, ?_⟩
  let T := s.forest N
  let depths := (Finset.univ.filter (fun b => b ∈ T.returns G e)).image (fun b => T.depth b.2)
  have hdepths_lt : ∀ d ∈ depths, d < T.depth e.1 := by
    intro d hd
    obtain ⟨b, hb_mem, rfl⟩ := Finset.mem_image.mp hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb_mem
    rcases hb_mem.2 with ⟨hbe_e, rfl⟩ | ⟨_, _, hlt⟩
    · exact hbe_e.2.2.1
    · exact hlt
  rcases hspec with ⟨htree, htree_edge⟩ | ⟨hback_tree, hbe_e⟩
  · -- Case 1: Tree edge
    have hnot_back : ¬ T.BackEdge G e := by
      intro hbe
      have hd : T.depth e.2 = T.depth e.1 + 1 := hlow.dfs.depth_step e.1 e.2 htree_edge
      have hlt : T.depth e.2 < T.depth e.1 := hbe.2.2.1
      omega
    have hpair_acc := hlow.tree_pair_spec i hi htree e.1 e.2 he_src he_tgt
    have hpair_depths : LowPairSpec depths (T.depth e.1) (s.edges[i]!).pair := by
      apply (LowPairSpec.congr_lt ?_).mp hpair_acc
      intro d hd_lt
      constructor
      · intro hd_acc
        obtain ⟨b, hb_mem, rfl⟩ := Finset.mem_image.mp hd_acc
        simp only [accBackEdges, Finset.mem_filter, Finset.mem_range] at hb_mem
        obtain ⟨hb_lt, hbtree, x, hx_src, hsub⟩ := hb_mem
        obtain ⟨b_arc, hb_src, hb_tgt, hbspec⟩ := hrec b (by rwa [hedges_eq])
        rw [hedges_eq] at hb_src hb_tgt hbspec
        rw [hforest_eq] at hbspec
        rcases hbspec with ⟨ht, _⟩ | ⟨_, hbe_b⟩
        · rw [ht] at hbtree; exact Bool.noConfusion hbtree
        · have hx_eq : x = b_arc.1 := Fin.ext (hx_src.symm.trans hb_src)
          rw [hx_eq] at hsub
          have hdy : (s.depth[(s.edges[b]!).target]?.join).getD 0 = T.depth b_arc.2 := by
            simp [T, Search.forest, hb_tgt]
          rw [hdy] at hd_lt ⊢
          have hret : b_arc ∈ T.returns G e :=
            ⟨hbe_b, Or.inr ⟨htree_edge, hsub.1, hd_lt⟩⟩
          exact Finset.mem_image.mpr ⟨b_arc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hret⟩, rfl⟩
      · intro hd_depths
        obtain ⟨b_arc, hb_mem, rfl⟩ := Finset.mem_image.mp hd_depths
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb_mem
        rcases hb_mem with ⟨hbe_b, ⟨hbe_e, _⟩ | ⟨_, hanc_eb, hlt_eb⟩⟩
        · exact absurd hbe_e hnot_back
        · obtain ⟨⟨b_idx, hb_idx_lt⟩, hb_idx, _⟩ := hex_rec b_arc.1 b_arc.2 hbe_b.1
          dsimp only at hb_idx
          have hb_lt : b_idx < s.edges.size := by rw [← hedges_eq]; exact hb_idx_lt
          rw [hedges_eq] at hb_idx
          obtain ⟨b_rec, hbr_src, hbr_tgt, hbspec⟩ := hrec b_idx hb_idx_lt
          rw [hedges_eq] at hbr_src hbr_tgt hbspec
          rw [hforest_eq] at hbspec
          have hbtree : (s.edges[b_idx]!).tree = false := by
            rcases hbspec with ⟨_, hte_b⟩ | ⟨ht, _⟩
            · exfalso
              unfold Forest.TreeEdge at hte_b
              rcases hb_idx with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
              · have heq1 : b_rec.1 = b_arc.1 := Fin.ext (hbr_src.symm.trans hsrc)
                have heq2 : b_rec.2 = b_arc.2 := Fin.ext (hbr_tgt.symm.trans htgt)
                rw [heq1, heq2] at hte_b
                have hd : T.depth b_arc.2 = T.depth b_arc.1 + 1 :=
                  hlow.dfs.depth_step b_arc.1 b_arc.2 hte_b
                have hlt := hbe_b.2.2.1
                omega
              · have heq1 : b_rec.1 = b_arc.2 := Fin.ext (hbr_src.symm.trans hsrc)
                have heq2 : b_rec.2 = b_arc.1 := Fin.ext (hbr_tgt.symm.trans htgt)
                rw [heq1, heq2] at hte_b
                exact hbe_b.2.2.2 hte_b
            · exact ht
          rcases hbspec with ⟨ht, _⟩ | ⟨_, hbe_rec⟩
          · rw [ht] at hbtree; exact Bool.noConfusion hbtree
          · have hdir : (s.edges[b_idx]!).source = b_arc.1.val ∧
                (s.edges[b_idx]!).target = b_arc.2.val := by
              rcases hb_idx with h1 | ⟨hsrc, htgt⟩
              · exact h1
              · exfalso
                have heq1 : b_rec.1 = b_arc.2 := Fin.ext (hbr_src.symm.trans hsrc)
                have heq2 : b_rec.2 = b_arc.1 := Fin.ext (hbr_tgt.symm.trans htgt)
                have hd1 : T.depth b_arc.1 < T.depth b_arc.2 := by
                  have h1 := hbe_rec.2.2.1
                  rwa [heq1, heq2] at h1
                have hd2 : T.depth b_arc.2 < T.depth b_arc.1 := hbe_b.2.2.1
                omega
            refine Finset.mem_image.mpr ⟨b_idx, ?_, ?_⟩
            · simp only [accBackEdges, Finset.mem_filter, Finset.mem_range]
              refine ⟨hb_lt, hbtree, b_arc.1, hdir.1, ?_⟩
              exact ⟨hanc_eb, fun c hc => by simp at hc⟩
            · simp [T, Search.forest, hdir.2]
    have hlow_eq : (s.edges[i]!).pair.low = T.low G e :=
      hpair_depths.low_eq_min'
    have hkey_eq : (s.edges[i]!).key = T.key G e := by
      have hkey_i := hlow.tree_key_spec i hi htree (by simp) e.1 he_src
      rw [hkey_i, hlow_eq]
      unfold Forest.key Forest.thick
      congr 1
      congr 1
      rw [decide_eq_decide]
      rw [hpair_depths.second_lt_iff hdepths_lt]
      constructor
      · rintro ⟨d₁, hd₁, d₂, hd₂, hne⟩
        obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp hd₁
        obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.mp hd₂
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
        exact ⟨b₁, hb₁, b₂, hb₂, hne⟩
      · rintro ⟨b₁, hb₁, b₂, hb₂, hne⟩
        exact ⟨T.depth b₁.2,
          Finset.mem_image.mpr ⟨b₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₁⟩, rfl⟩,
          T.depth b₂.2,
          Finset.mem_image.mpr ⟨b₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₂⟩, rfl⟩,
          hne⟩
    exact ⟨hpair_depths, hlow_eq, hkey_eq⟩
  · -- Case 2: Back edge
    have hnot_tree : ¬ T.TreeEdge e := by
      intro hte
      have hd : T.depth e.2 = T.depth e.1 + 1 := hlow.dfs.depth_step e.1 e.2 hte
      have hlt : T.depth e.2 < T.depth e.1 := hbe_e.2.2.1
      omega
    have hret_iff : ∀ b, b ∈ T.returns G e ↔ b = e := by
      intro b
      constructor
      · rintro ⟨_, ⟨_, rfl⟩ | ⟨hte, _⟩⟩
        · rfl
        · exact absurd hte hnot_tree
      · rintro rfl
        exact ⟨hbe_e, Or.inl ⟨hbe_e, rfl⟩⟩
    have hdepths_eq : depths = {T.depth e.2} := by
      ext d
      simp only [depths, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        hret_iff, Finset.mem_singleton]
      exact ⟨fun ⟨b, hb, hd⟩ => by subst hb; exact hd.symm, fun hd => ⟨e, rfl, hd.symm⟩⟩
    obtain ⟨hpair_b, hkey_b⟩ := hlow.back_spec i hi hback_tree
    have hlt_e : T.depth e.2 < T.depth e.1 := hbe_e.2.2.1
    have hpair_depths : LowPairSpec depths (T.depth e.1) (s.edges[i]!).pair := by
      rw [hdepths_eq, hpair_b]
      unfold LowPairSpec
      have hd1 : (s.depth[(s.edges[i]!).source]?.join).getD 0 = T.depth e.1 := by
        simp [T, Search.forest, he_src]
      have hd2 : (s.depth[(s.edges[i]!).target]?.join).getD 0 = T.depth e.2 := by
        simp [T, Search.forest, he_tgt]
      dsimp only
      rw [hd1, hd2]
      refine ⟨by omega, le_rfl, by omega, ?_, Or.inr (Finset.mem_singleton_self _), Or.inl rfl, ?_⟩
      · intro k hk
        rw [Finset.mem_singleton.mp hk]
      · intro k hk hlt
        rw [Finset.mem_singleton.mp hk] at hlt
        omega
    have hlow_eq : (s.edges[i]!).pair.low = T.low G e :=
      hpair_depths.low_eq_min'
    have hthick_false : T.thick G e = false := by
      unfold Forest.thick
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro b hb c hc hne
      rw [(hret_iff b).mp hb, (hret_iff c).mp hc] at hne
      exact hne rfl
    have hkey_eq : (s.edges[i]!).key = T.key G e := by
      rw [hkey_b, hlow_eq]
      unfold Forest.key
      rw [hthick_false]
      simp
    exact ⟨hpair_depths, hlow_eq, hkey_eq⟩

end GraphMinor.LRPlanarity
