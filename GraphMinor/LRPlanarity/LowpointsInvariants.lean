module

public import GraphMinor.LRPlanarity.Search

/-!
# Lowpoint Invariants (Part I, Section 1)

This module proves `LowpointInsertionStatement` and establishes the inductive
invariant `LowInv` for the two-lowpoint pair recurrence during `depthFirstSearch`,
following Part I, Section 1 of `docs/planarity/planarity_test.tex`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-! ## Lowpoint Pair Algebra -/

/-- Part I, Section 1, `INSERT`: insert one value into a two-lowpoint pair. -/
theorem lowpointInsertionStatement : LowpointInsertionStatement := by
  intro values c pair k h
  rcases h with ⟨hlow_c, hsec_c, hlow_sec, hmin1, hmem1, hmem2, hmin2⟩
  unfold insertLow
  split_ifs with hk1 hk2
  · unfold LowPairSpec
    dsimp only
    refine ⟨by omega, hlow_c, by omega, ?_, Or.inr (Finset.mem_insert_self k values), ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact le_of_lt (lt_of_lt_of_le hk1 (hmin1 x hx))
    · rcases hmem1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨Finset.mem_insert_of_mem h1, hk1⟩
    · intro x hx hkx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hmin1 x hx
  · unfold LowPairSpec
    dsimp only
    refine ⟨hlow_c, by omega, by omega, ?_, ?_,
      Or.inr ⟨Finset.mem_insert_self k values, hk2.1⟩, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hmin1 x hx
    · rcases hmem1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Finset.mem_insert_of_mem h1)
    · intro x hx hkx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact le_of_lt (lt_of_lt_of_le hk2.2 (hmin2 x hx hkx))
  · unfold LowPairSpec
    refine ⟨hlow_c, hsec_c, hlow_sec, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hmin1 x hx
    · rcases hmem1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Finset.mem_insert_of_mem h1)
    · rcases hmem2 with h2 | ⟨h2, hlt⟩
      · exact Or.inl h2
      · exact Or.inr ⟨Finset.mem_insert_of_mem h2, hlt⟩
    · intro x hx hkx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hmin2 x hx hkx

/-- Values at or above the sentinel `c` do not affect `LowPairSpec`. -/
theorem LowPairSpec.congr_lt {S T : Finset ℕ} {c : ℕ} {pair : LowPair}
    (hST : ∀ x < c, x ∈ S ↔ x ∈ T) :
    LowPairSpec S c pair ↔ LowPairSpec T c pair := by
  have imp : ∀ {A B : Finset ℕ}, (∀ x < c, x ∈ A ↔ x ∈ B) →
      LowPairSpec A c pair → LowPairSpec B c pair := by
    intro A B hAB ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkc : k < c
      · exact h4 k ((hAB k hkc).mpr hk)
      · omega
    · rcases h5 with hlow_eq | hlow_mem
      · exact Or.inl hlow_eq
      · by_cases hlow_lt : pair.low < c
        · exact Or.inr ((hAB pair.low hlow_lt).mp hlow_mem)
        · exact Or.inl (by omega)
    · rcases h6 with hsec_eq | ⟨hsec_mem, hlt⟩
      · exact Or.inl hsec_eq
      · by_cases hsec_lt : pair.second < c
        · exact Or.inr ⟨(hAB pair.second hsec_lt).mp hsec_mem, hlt⟩
        · exact Or.inl (by omega)
    · intro k hk hlt
      by_cases hkc : k < c
      · exact h7 k ((hAB k hkc).mpr hk) hlt
      · omega
  exact ⟨imp hST, imp (fun x hx => (hST x hx).symm)⟩

/-- Propagating a child's `LowPair` into a parent's `LowPair` with sentinel `c ≤ c'`
computes a valid `LowPair` for `A ∪ B`. -/
theorem LowPairSpec.union_insert {A B : Finset ℕ} {c c' : ℕ} {pairA pairB : LowPair}
    (hA : LowPairSpec A c pairA) (hB : LowPairSpec B c' pairB) (hcc' : c ≤ c') :
    LowPairSpec (A ∪ B) c (insertLow (insertLow pairA pairB.low) pairB.second) := by
  have h1 := lowpointInsertionStatement A c pairA pairB.low hA
  have h2 := lowpointInsertionStatement (insert pairB.low A) c
    (insertLow pairA pairB.low) pairB.second h1
  rcases h2 with ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩
  rcases hB with ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  have hlow_le_b : (insertLow (insertLow pairA pairB.low) pairB.second).low ≤ pairB.low :=
    hr4 pairB.low (by simp)
  have hsec_le_b1 :
      (insertLow (insertLow pairA pairB.low) pairB.second).low < pairB.low →
        (insertLow (insertLow pairA pairB.low) pairB.second).second ≤ pairB.low :=
    hr7 pairB.low (by simp)
  have hsec_le_b2 :
      (insertLow (insertLow pairA pairB.low) pairB.second).low < pairB.second →
        (insertLow (insertLow pairA pairB.low) pairB.second).second ≤ pairB.second :=
    hr7 pairB.second (by simp)
  refine ⟨hr1, hr2, hr3, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases Finset.mem_union.mp hk with hkA | hkB
    · exact hr4 k (by simp [hkA])
    · exact le_trans hlow_le_b (hb4 k hkB)
  · rcases hr5 with hlow_eq | hlow_mem
    · exact Or.inl hlow_eq
    · simp only [Finset.mem_insert] at hlow_mem
      rcases hlow_mem with hsecB | hlowB | hmemA
      · rcases hb6 with hsec_c' | ⟨hsec_mem, _⟩
        · exact Or.inl (by omega)
        · right
          rw [hsecB]
          exact Finset.mem_union_right A hsec_mem
      · rcases hb5 with hlow_c' | hlow_memB
        · exact Or.inl (by omega)
        · right
          rw [hlowB]
          exact Finset.mem_union_right A hlow_memB
      · exact Or.inr (Finset.mem_union_left B hmemA)
  · rcases hr6 with hsec_eq | ⟨hsec_mem, hlt⟩
    · exact Or.inl hsec_eq
    · simp only [Finset.mem_insert] at hsec_mem
      rcases hsec_mem with hsecB | hlowB | hmemA
      · rcases hb6 with hsec_c' | ⟨hsec_memB, _⟩
        · exact Or.inl (by omega)
        · right
          refine ⟨?_, hlt⟩
          rw [hsecB]
          exact Finset.mem_union_right A hsec_memB
      · rcases hb5 with hlow_c' | hlow_memB
        · exact Or.inl (by omega)
        · right
          refine ⟨?_, hlt⟩
          rw [hlowB]
          exact Finset.mem_union_right A hlow_memB
      · exact Or.inr ⟨Finset.mem_union_left B hmemA, hlt⟩
  · intro k hk hlt
    rcases Finset.mem_union.mp hk with hkA | hkB
    · exact hr7 k (by simp [hkA]) hlt
    · have hbk : pairB.low ≤ k := hb4 k hkB
      rcases eq_or_lt_of_le hlow_le_b with heq | hlt_b
      · have hbk_lt : pairB.low < k := heq ▸ hlt
        have hbsec_k : pairB.second ≤ k := hb7 k hkB hbk_lt
        by_cases hlt_sec : (insertLow (insertLow pairA pairB.low) pairB.second).low < pairB.second
        · exact le_trans (hsec_le_b2 hlt_sec) hbsec_k
        · rcases hb6 with hsec_c' | ⟨_, hlt_bsec⟩ <;> omega
      · exact le_trans (hsec_le_b1 hlt_b) hbk

/-- If `LowPairSpec values c pair` holds, `pair.low` is the minimum of `insert c values`. -/
theorem LowPairSpec.low_eq_min' {values : Finset ℕ} {c : ℕ} {pair : LowPair}
    (h : LowPairSpec values c pair) :
    pair.low = (insert c values).min' (Finset.insert_nonempty c values) := by
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact h.1
    · exact h.2.2.2.1 y hy
  · apply Finset.min'_le
    rcases h.2.2.2.2.1 with hlow | hlow
    · exact Finset.mem_insert.mpr (Or.inl hlow)
    · exact Finset.mem_insert.mpr (Or.inr hlow)

/-- Characterization of `pair.second < c` when all elements of `values` are `< c`. -/
theorem LowPairSpec.second_lt_iff {values : Finset ℕ} {c : ℕ} {pair : LowPair}
    (h : LowPairSpec values c pair) (h_lt : ∀ x ∈ values, x < c) :
    pair.second < c ↔ ∃ x ∈ values, ∃ y ∈ values, x ≠ y := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  constructor
  · intro hsec_lt
    rcases h6 with hsec_eq | ⟨hsec_mem, hlow_lt_sec⟩
    · omega
    · rcases h5 with hlow_eq | hlow_mem
      · omega
      · exact ⟨pair.low, hlow_mem, pair.second, hsec_mem, ne_of_lt hlow_lt_sec⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hx_lt : x < c := h_lt x hx
    have hy_lt : y < c := h_lt y hy
    have hlow_x : pair.low ≤ x := h4 x hx
    have hlow_y : pair.low ≤ y := h4 y hy
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · have hlow_lt_y : pair.low < y := lt_of_le_of_lt hlow_x hlt
      exact lt_of_le_of_lt (h7 y hy hlow_lt_y) hy_lt
    · have hlow_lt_x : pair.low < x := lt_of_le_of_lt hlow_y hlt
      exact lt_of_le_of_lt (h7 x hx hlow_lt_x) hx_lt

/-! ## Effect of `finishEdge` on Edge Records -/

private theorem getElem!_set!_EdgeRecord' (edges : Array EdgeRecord) (k j : ℕ) (e : EdgeRecord)
    (hk : k < edges.size) :
    (edges.set! k e)[j]! = if j = k then e else edges[j]! := by
  by_cases hj : j < edges.size
  · have hj' : j < (edges.set! k e).size := by simp [hj]
    rw [getElem!_pos (edges.set! k e) j hj', getElem!_pos edges j hj]
    simp only [Array.set!, Array.setIfInBounds, hk, ↓reduceDIte, Array.getElem_set]
    by_cases hjk : j = k
    · subst hjk; simp
    · have hkj : k ≠ j := Ne.symm hjk
      simp [hjk, hkj]
  · have hj' : ¬ j < (edges.set! k e).size := by simp [hj]
    have hjk : j ≠ k := by omega
    rw [getElem!_neg (edges.set! k e) j hj', getElem!_neg edges j hj]
    simp [hjk]

theorem finishEdge_edges_getElem! (s : Search) (i : ℕ) (hi : i < s.edges.size)
    (hp_bound : ∀ p, s.parentEdge[(s.edges[i]!).source]?.join = some p →
      p < s.edges.size ∧ p ≠ i) :
    ((finishEdge s i).edges[i]!).pair = (s.edges[i]!).pair ∧
    ((finishEdge s i).edges[i]!).key =
      2 * (s.edges[i]!).pair.low +
        (decide ((s.edges[i]!).pair.second < (s.depth[(s.edges[i]!).source]?.join).getD 0)).toNat ∧
    (∀ p, s.parentEdge[(s.edges[i]!).source]?.join = some p →
      ((finishEdge s i).edges[p]!).pair =
        insertLow (insertLow (s.edges[p]!).pair (s.edges[i]!).pair.low)
          (s.edges[i]!).pair.second ∧
      ((finishEdge s i).edges[p]!).key = (s.edges[p]!).key) ∧
    (∀ j, j ≠ i → s.parentEdge[(s.edges[i]!).source]?.join ≠ some j →
      (finishEdge s i).edges[j]! = s.edges[j]!) := by
  unfold finishEdge
  dsimp only [Id.run, bind, pure]
  let e' : EdgeRecord := { s.edges[i]! with key := 2 * (s.edges[i]!).pair.low +
    (decide ((s.edges[i]!).pair.second < (s.depth[(s.edges[i]!).source]?.join).getD 0)).toNat }
  split
  · next p hp =>
    obtain ⟨hp_lt, hp_ne⟩ := hp_bound p hp
    have hp_lt' : p < (s.edges.set! i e').size := by simp [hp_lt]
    have hpe : (s.edges.set! i e')[p]! = s.edges[p]! := by
      rw [getElem!_set!_EdgeRecord' s.edges i p e' hi]
      simp [hp_ne]
    let pe' : EdgeRecord := { (s.edges.set! i e')[p]! with
      pair := insertLow (insertLow ((s.edges.set! i e')[p]!).pair e'.pair.low) e'.pair.second }
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (((s.edges.set! i e').set! p pe')[i]!).pair = (s.edges[i]!).pair
      rw [getElem!_set!_EdgeRecord' _ p i pe' hp_lt',
        getElem!_set!_EdgeRecord' s.edges i i e' hi]
      simp [Ne.symm hp_ne, e']
    · change (((s.edges.set! i e').set! p pe')[i]!).key = _
      rw [getElem!_set!_EdgeRecord' _ p i pe' hp_lt',
        getElem!_set!_EdgeRecord' s.edges i i e' hi]
      simp [Ne.symm hp_ne, e']
    · intro q hq
      rw [hp] at hq
      injection hq with hpq
      subst hpq
      change (((s.edges.set! i e').set! p pe')[p]!).pair = _ ∧
        (((s.edges.set! i e').set! p pe')[p]!).key = _
      rw [getElem!_set!_EdgeRecord' _ p p pe' hp_lt']
      simp only [↓reduceIte]
      dsimp only [pe', e']
      rw [hpe]
      exact ⟨rfl, rfl⟩
    · intro j hji hjp
      have hjp' : j ≠ p := fun h => hjp (h ▸ hp)
      change ((s.edges.set! i e').set! p pe')[j]! = s.edges[j]!
      rw [getElem!_set!_EdgeRecord' _ p j pe' hp_lt',
        getElem!_set!_EdgeRecord' s.edges i j e' hi]
      simp [hjp', hji]
  · next hp =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ((s.edges.set! i e')[i]!).pair = (s.edges[i]!).pair
      rw [getElem!_set!_EdgeRecord' s.edges i i e' hi]
      simp [e']
    · change ((s.edges.set! i e')[i]!).key = _
      rw [getElem!_set!_EdgeRecord' s.edges i i e' hi]
      simp [e']
    · intro p hp'
      exact False.elim (hp p hp')
    · intro j hji _
      change (s.edges.set! i e')[j]! = s.edges[j]!
      rw [getElem!_set!_EdgeRecord' s.edges i j e' hi]
      simp [hji]

/-! ## Accumulated Subtree Returns Invariant -/

/-- A vertex `x` is in the accumulated subtree of `v` at state `(T, stack)` if `v` is an
ancestor of `x` and no child `c` of `v` currently on `stack` is an ancestor of `x`. -/
def InAccSubtree {N : ℕ} (T : Forest N) (stack : List Frame) (v x : Fin N) : Prop :=
  T.Ancestor v x ∧
  ∀ c : Fin N, c.val ∈ stack.map Frame.vertex → T.parent c = some v → ¬ T.Ancestor c x

/-- Indices of back edges in `s.edges` whose source lies in the accumulated subtree of `v`. -/
noncomputable def accBackEdges (N : ℕ) (s : Search) (stack : List Frame) (v : Fin N) : Finset ℕ :=
  (Finset.range s.edges.size).filter (fun b =>
    (s.edges[b]!).tree = false ∧
    ∃ x : Fin N, (s.edges[b]!).source = x.val ∧ InAccSubtree (s.forest N) stack v x)

/-- Target depths of back edges accumulated into the subtree of `v`. -/
noncomputable def accDepths (N : ℕ) (s : Search) (stack : List Frame) (v : Fin N) : Finset ℕ :=
  (accBackEdges N s stack v).image (fun b =>
    (s.depth[(s.edges[b]!).target]?.join).getD 0)

theorem DFSInv.mem_stack_of_ancestor {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack)
    {c z : Fin N} (hanc : (s.forest N).Ancestor c z) (hz : z.val ∈ stack.map Frame.vertex) :
    c.val ∈ stack.map Frame.vertex := by
  induction hanc with
  | refl => exact hz
  | @tail a b _ hp ih =>
    apply ih
    have hpar : s.parent[b.val]?.join = some a.val :=
      (h.forest_parent_some_iff a b).mp hp
    exact h.active_parent_mem b.val hz a.val hpar

theorem DFSInv.inAccSubtree_top_iff {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame} (h : DFSInv N G lists s (f :: rest))
    (hv_top : f.vertex < N) (v : Fin N) :
    InAccSubtree (s.forest N) (f :: rest) v ⟨f.vertex, hv_top⟩ ↔ v = ⟨f.vertex, hv_top⟩ := by
  constructor
  · rintro ⟨hanc, hno_child⟩
    rcases Relation.ReflTransGen.cases_head hanc with rfl | ⟨c, hp, hanc'⟩
    · rfl
    · exfalso
      have hc_mem : c.val ∈ (f :: rest).map Frame.vertex :=
        h.mem_stack_of_ancestor hanc' (by simp)
      exact hno_child c hc_mem hp hanc'
  · rintro rfl
    refine ⟨Relation.ReflTransGen.refl, ?_⟩
    intro c hc hp
    have hpar : s.parent[c.val]?.join = some f.vertex :=
      (h.forest_parent_some_iff ⟨f.vertex, hv_top⟩ c).mp hp
    simp only [List.map_cons, List.mem_cons] at hc
    rcases hc with hceq | hc_rest
    · have hdepth := h.depth_step ⟨f.vertex, hv_top⟩ c hp
      have hc_eq_f : c = ⟨f.vertex, hv_top⟩ := Fin.ext hceq
      rw [hc_eq_f] at hdepth
      omega
    · exact absurd hpar (h.not_parent_of_mem_stack_tail hc_rest)

theorem accDepths_finishEdge (N : ℕ) (s : Search) (i : ℕ) (stack : List Frame) (v : Fin N) :
    accDepths N (finishEdge s i) stack v = accDepths N s stack v := by
  have hbe : accBackEdges N (finishEdge s i) stack v = accBackEdges N s stack v := by
    unfold accBackEdges
    simp only [finishEdge_edges_size, finishEdge_forest]
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [finishEdge_edges_tree, finishEdge_edges_source]
  unfold accDepths
  rw [hbe]
  apply Finset.image_congr
  intro b _
  simp only [finishEdge_depth, finishEdge_edges_target]

/-- Invariant tracking lowpoint pairs and keys of all edges during DFS. -/
structure LowInv (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (s : Search) (stack : List Frame) : Prop where
  dfs : DFSInv N G lists s stack
  back_spec : ∀ i < s.edges.size, (s.edges[i]!).tree = false →
    (s.edges[i]!).pair =
      ⟨(s.depth[(s.edges[i]!).target]?.join).getD 0,
        (s.depth[(s.edges[i]!).source]?.join).getD 0⟩ ∧
    (s.edges[i]!).key = 2 * (s.edges[i]!).pair.low
  tree_pair_spec : ∀ i < s.edges.size, (s.edges[i]!).tree = true →
    ∀ (u v : Fin N), (s.edges[i]!).source = u.val → (s.edges[i]!).target = v.val →
      LowPairSpec (accDepths N s stack v) ((s.forest N).depth u) (s.edges[i]!).pair
  tree_key_spec : ∀ i < s.edges.size, (s.edges[i]!).tree = true →
    (s.edges[i]!).target ∉ stack.map Frame.vertex →
    ∀ (u : Fin N), (s.edges[i]!).source = u.val →
      (s.edges[i]!).key =
        2 * (s.edges[i]!).pair.low +
          (decide ((s.edges[i]!).pair.second < (s.forest N).depth u)).toNat

theorem LowInv.init (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) :
    LowInv N G lists (initialSearch N) [] where
  dfs := DFSInv.init N G lists
  back_spec := by simp [initialSearch]
  tree_pair_spec := by simp [initialSearch]
  tree_key_spec := by simp [initialSearch]

theorem LowInv.push_root {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {root : ℕ} (h : LowInv N G lists s [])
    (hAdj : Compute.IsAdjListFamily G lists) (hroot : root < N)
    (hnone : (s.depth[root]?.join).isNone = true) :
    LowInv N G lists { s with depth := s.depth.set! root (some 0) } [⟨root, 0⟩] := by
  let s' : Search := { s with depth := s.depth.set! root (some 0) }
  have hdfs' : DFSInv N G lists s' [⟨root, 0⟩] := h.dfs.push_root hAdj hroot hnone
  have hroot_unvis : ¬ s.Visited root := (Search.not_visited_iff s root).mpr hnone
  have hsz_d : root < s.depth.size := by rw [h.dfs.depth_size]; exact hroot
  have hdepth_s' : ∀ u, s'.depth[u]?.join = if u = root then some 0 else s.depth[u]?.join :=
    getElem?_join_set! s.depth root (some 0) hsz_d
  have hdepth_eq : ∀ u, s.Visited u →
      (s'.depth[u]?.join).getD 0 = (s.depth[u]?.join).getD 0 := by
    intro u hu_vis
    have hne : u ≠ root := fun heq => hroot_unvis (heq ▸ hu_vis)
    rw [hdepth_s' u]
    simp [hne]
  have hparent_eq : (s'.forest N).parent = (s.forest N).parent := rfl
  have hanc_eq : ∀ u v : Fin N, (s'.forest N).Ancestor u v ↔ (s.forest N).Ancestor u v := by
    intro u v
    unfold Forest.Ancestor
    rw [hparent_eq]
  have hacc_eq : ∀ v : Fin N, accDepths N s' [⟨root, 0⟩] v = accDepths N s [] v := by
    intro v
    unfold accDepths
    have hfilter_eq : accBackEdges N s' [⟨root, 0⟩] v = accBackEdges N s [] v := by
      ext b
      simp only [accBackEdges, Finset.mem_filter, Finset.mem_range]
      refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun x =>
        and_congr_right fun _ => ?_
      unfold InAccSubtree
      rw [hanc_eq]
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      refine and_congr_right fun _ => ⟨fun _ c hc => False.elim hc, fun _ c hc hpar => ?_⟩
      have hc_eq : c = ⟨root, hroot⟩ := Fin.ext hc
      rw [hc_eq, hparent_eq] at hpar
      have hroot_par_none : s.parent[root]?.join = none := (h.dfs.unvisited_none root hroot_unvis).1
      have hroot_fpar_none : (s.forest N).parent ⟨root, hroot⟩ = none :=
        (h.dfs.forest_parent_none_iff ⟨root, hroot⟩).mpr hroot_par_none
      rw [hroot_fpar_none] at hpar
      nomatch hpar
    rw [hfilter_eq]
    apply Finset.image_congr
    intro b hb
    simp only [Finset.mem_coe, accBackEdges, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨_, _, _, hw_vis, _⟩ := h.dfs.edges_valid b hb.1
    exact hdepth_eq (s.edges[b]!).target hw_vis
  refine ⟨hdfs', ?_, ?_, ?_⟩
  · intro i hi htree
    obtain ⟨_, _, hu_vis, hw_vis, _⟩ := h.dfs.edges_valid i hi
    rw [hdepth_eq _ hw_vis, hdepth_eq _ hu_vis]
    exact h.back_spec i hi htree
  · intro i hi htree u v hu hv
    obtain ⟨_, _, hu_vis, _, _⟩ := h.dfs.edges_valid i hi
    have hdu : (s'.forest N).depth u = (s.forest N).depth u := by
      unfold Search.forest; dsimp only
      exact hdepth_eq u.val (hu ▸ hu_vis)
    rw [hacc_eq v, hdu]
    exact h.tree_pair_spec i hi htree u v hu hv
  · intro i hi htree _ u hu
    obtain ⟨_, _, hu_vis, _, _⟩ := h.dfs.edges_valid i hi
    have hdu : (s'.forest N).depth u = (s.forest N).depth u := by
      unfold Search.forest; dsimp only
      exact hdepth_eq u.val (hu ▸ hu_vis)
    rw [hdu]
    exact h.tree_key_spec i hi htree (by simp) u hu

theorem LowInv.step_skip {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame} (h : LowInv N G lists s (f :: rest))
    (hAdj : Compute.IsAdjListFamily G lists)
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (hw_none : ¬ (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).isNone = true)
    (hback : ¬ (s.parent[f.vertex]?.join ≠
        some (((List.ofFn lists).toArray[f.vertex]!)[f.next]!) ∧
      (s.depth[((List.ofFn lists).toArray[f.vertex]!)[f.next]!]?.join).getD 0 <
        (s.depth[f.vertex]?.join).getD 0)) :
    LowInv N G lists s ({ f with next := f.next + 1 } :: rest) := by
  have hw_vis : s.Visited (((List.ofFn lists).toArray[f.vertex]!)[f.next]!) := by
    by_contra hnot
    exact hw_none ((Search.not_visited_iff s _).mp hnot)
  have hmap : ({ f with next := f.next + 1 } :: rest).map Frame.vertex =
      (f :: rest).map Frame.vertex := rfl
  have hacc : ∀ v : Fin N,
      accDepths N s ({ f with next := f.next + 1 } :: rest) v = accDepths N s (f :: rest) v := by
    intro v
    unfold accDepths accBackEdges InAccSubtree
    rw [hmap]
  refine ⟨h.dfs.step_skip hAdj hlen hw_vis hback, h.back_spec, ?_, ?_⟩
  · intro i hi htree u v hu hv
    rw [hacc]
    exact h.tree_pair_spec i hi htree u v hu hv
  · intro i hi htree hnot_mem u hu
    rw [hmap] at hnot_mem
    exact h.tree_key_spec i hi htree hnot_mem u hu

theorem LowInv.step_pop {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame} (h : LowInv N G lists s (f :: rest))
    (hlen : ((List.ofFn lists).toArray[f.vertex]!).length ≤ f.next) :
    let s₁ := { s with postorder := f.vertex :: s.postorder }
    let s' := match s₁.parentEdge[f.vertex]?.join with
      | none => s₁
      | some p => finishEdge s₁ p
    LowInv N G lists s' rest := by
  intro s₁ s'
  have hdfs' : DFSInv N G lists s' rest := h.dfs.step_pop hlen
  have hv_top : f.vertex < N := h.dfs.active_lt f.vertex (by simp)
  have hno_child_vtop : ∀ c : Fin N, c.val ∈ (f :: rest).map Frame.vertex →
      (s.forest N).parent c ≠ some ⟨f.vertex, hv_top⟩ := by
    intro c hc hp
    have htop := (h.dfs.inAccSubtree_top_iff hv_top ⟨f.vertex, hv_top⟩).mpr rfl
    have hrefl : (s.forest N).Ancestor c c := Relation.ReflTransGen.refl
    have hc_eq : c = ⟨f.vertex, hv_top⟩ := by
      exfalso
      have hpar : s.parent[c.val]?.join = some f.vertex :=
        (h.dfs.forest_parent_some_iff ⟨f.vertex, hv_top⟩ c).mp hp
      simp only [List.map_cons, List.mem_cons] at hc
      rcases hc with hceq | hc_rest
      · have hdepth := h.dfs.depth_step ⟨f.vertex, hv_top⟩ c hp
        have hc_eq_f : c = ⟨f.vertex, hv_top⟩ := Fin.ext hceq
        rw [hc_eq_f] at hdepth
        omega
      · exact h.dfs.not_parent_of_mem_stack_tail hc_rest hpar
    exact htop.2 c hc hp (hc_eq ▸ hrefl)
  cases hp : s.parentEdge[f.vertex]?.join with
  | none =>
    have hs' : s' = s₁ := by simp [s', s₁, hp]
    rw [hs']
    have hpar_none : s.parent[f.vertex]?.join = none := by
      cases hpar : s.parent[f.vertex]?.join with
      | none => rfl
      | some u =>
        exfalso
        obtain ⟨i, hi, htree, _, htgt⟩ := (h.dfs.parent_iff_edge f.vertex hv_top u).mp hpar
        obtain ⟨_, _, _, _, _, htree_spec⟩ := h.dfs.edges_valid i hi
        simp only [htree, ↓reduceIte, htgt, hp] at htree_spec
        nomatch htree_spec.2
    have hfpar_none : (s.forest N).parent ⟨f.vertex, hv_top⟩ = none :=
      (h.dfs.forest_parent_none_iff ⟨f.vertex, hv_top⟩).mpr hpar_none
    have hacc_eq : ∀ v : Fin N, accDepths N s₁ rest v = accDepths N s (f :: rest) v := by
      intro v
      unfold accDepths
      have hbe : accBackEdges N s₁ rest v = accBackEdges N s (f :: rest) v := by
        ext b
        simp only [accBackEdges, Finset.mem_filter, Finset.mem_range]
        refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun x =>
          and_congr_right fun _ => ?_
        unfold InAccSubtree
        refine and_congr_right fun _ => ⟨?_, ?_⟩
        · intro hrest c hc hpc
          simp only [List.map_cons, List.mem_cons] at hc
          rcases hc with hceq | hc_rest
          · have hc_eq : c = ⟨f.vertex, hv_top⟩ := Fin.ext hceq
            change (s.forest N).parent c = some v at hpc
            rw [hc_eq, hfpar_none] at hpc
            nomatch hpc
          · exact hrest c hc_rest hpc
        · intro hall c hc_rest hpc
          exact hall c (List.mem_cons_of_mem _ hc_rest) hpc
      rw [hbe]
    refine ⟨hs' ▸ hdfs', h.back_spec, ?_, ?_⟩
    · intro i hi htree u v hu hv
      rw [hacc_eq]
      exact h.tree_pair_spec i hi htree u v hu hv
    · intro i hi htree hnot_mem u hu
      have hne_f : (s.edges[i]!).target ≠ f.vertex := by
        intro heq
        have hpe := (h.dfs.parentEdge_iff f.vertex hv_top i).mpr ⟨hi, htree, heq⟩
        rw [hp] at hpe
        nomatch hpe
      have hnot_mem' : (s.edges[i]!).target ∉ (f :: rest).map Frame.vertex := by
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨hne_f, hnot_mem⟩
      exact h.tree_key_spec i hi htree hnot_mem' u hu
  | some p =>
    have hs' : s' = finishEdge s₁ p := by simp [s', s₁, hp]
    rw [hs']
    obtain ⟨hp_lt, hp_tree, hp_tgt⟩ := (h.dfs.parentEdge_iff f.vertex hv_top p).mp hp
    obtain ⟨hu, _, _, _, _, htree_p⟩ := h.dfs.edges_valid p hp_lt
    simp only [hp_tree, ↓reduceIte, hp_tgt] at htree_p
    have hp_par : s.parent[f.vertex]?.join = some (s.edges[p]!).source := htree_p.1
    let u := (s.edges[p]!).source
    have hfpar_u : (s.forest N).parent ⟨f.vertex, hv_top⟩ = some ⟨u, hu⟩ :=
      (h.dfs.forest_parent_some_iff ⟨u, hu⟩ ⟨f.vertex, hv_top⟩).mpr hp_par
    have hp_bound : ∀ q, s₁.parentEdge[(s₁.edges[p]!).source]?.join = some q →
        q < s₁.edges.size ∧ q ≠ p := by
      intro q hq
      obtain ⟨hq_lt, _, hq_tgt⟩ := (h.dfs.parentEdge_iff u hu q).mp hq
      refine ⟨hq_lt, ?_⟩
      intro hqp
      subst hqp
      have hd := h.dfs.depth_step ⟨u, hu⟩ ⟨f.vertex, hv_top⟩ hfpar_u
      have heq_uv : (⟨f.vertex, hv_top⟩ : Fin N) = ⟨u, hu⟩ := Fin.ext (hp_tgt.symm.trans hq_tgt)
      rw [heq_uv] at hd
      omega
    obtain ⟨hpair_p, hkey_p, hparent_q, hother⟩ := finishEdge_edges_getElem! s₁ p hp_lt hp_bound
    have hrest_cons : ∃ f_u rest', rest = f_u :: rest' ∧ f_u.vertex = u := by
      rcases rest with _ | ⟨f_u, rest'⟩
      · exfalso
        have hum := h.dfs.active_parent_mem f.vertex (by simp) u hp_par
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hum
        have heq_uv : (⟨f.vertex, hv_top⟩ : Fin N) = ⟨u, hu⟩ := Fin.ext hum.symm
        have hd := h.dfs.depth_step ⟨u, hu⟩ ⟨f.vertex, hv_top⟩ hfpar_u
        rw [heq_uv] at hd
        omega
      · have hchain := h.dfs.stack_chain
        rw [List.isChain_cons_cons] at hchain
        rw [hchain.1] at hp_par
        injection hp_par with heq
        exact ⟨f_u, rest', rfl, heq⟩
    obtain ⟨f_u, rest', hrest_eq, hfu_eq⟩ := hrest_cons
    have hno_child_u_rest : ∀ c : Fin N, c.val ∈ rest.map Frame.vertex →
        (s.forest N).parent c ≠ some ⟨u, hu⟩ := by
      intro c hc hpc
      have hdfs_rest : DFSInv N G lists s' (f_u :: rest') := hrest_eq ▸ hdfs'
      have hc' : c.val ∈ (f_u :: rest').map Frame.vertex := hrest_eq ▸ hc
      have hu_top : f_u.vertex < N := hfu_eq ▸ hu
      have hpc' : (s'.forest N).parent c = some ⟨f_u.vertex, hu_top⟩ := by
        rw [hs', finishEdge_forest]
        change (s.forest N).parent c = some ⟨f_u.vertex, hu_top⟩
        rw [hpc]
        congr 1
        exact Fin.ext hfu_eq.symm
      have hpar_raw : s'.parent[c.val]?.join = some f_u.vertex :=
        (hdfs_rest.forest_parent_some_iff ⟨f_u.vertex, hu_top⟩ c).mp hpc'
      simp only [List.map_cons, List.mem_cons] at hc'
      rcases hc' with hceq | hc_rest'
      · have hdepth := hdfs_rest.depth_step ⟨f_u.vertex, hu_top⟩ c hpc'
        have hc_eq_fu : c = ⟨f_u.vertex, hu_top⟩ := Fin.ext hceq
        rw [hc_eq_fu] at hdepth
        omega
      · exact hdfs_rest.not_parent_of_mem_stack_tail hc_rest' hpar_raw
    have hacc_other : ∀ v : Fin N, v ≠ ⟨u, hu⟩ →
        accDepths N (finishEdge s₁ p) rest v = accDepths N s (f :: rest) v := by
      intro v hv_ne
      rw [accDepths_finishEdge]
      unfold accDepths
      have hbe : accBackEdges N s₁ rest v = accBackEdges N s (f :: rest) v := by
        ext b
        simp only [accBackEdges, Finset.mem_filter, Finset.mem_range]
        refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun x =>
          and_congr_right fun _ => ?_
        unfold InAccSubtree
        refine and_congr_right fun _ => ⟨?_, ?_⟩
        · intro hrest c hc hpc
          simp only [List.map_cons, List.mem_cons] at hc
          rcases hc with hceq | hc_rest
          · have hc_eq : c = ⟨f.vertex, hv_top⟩ := Fin.ext hceq
            change (s.forest N).parent c = some v at hpc
            rw [hc_eq, hfpar_u] at hpc
            injection hpc with hvu
            exact absurd hvu.symm hv_ne
          · exact hrest c hc_rest hpc
        · intro hall c hc_rest hpc
          exact hall c (List.mem_cons_of_mem _ hc_rest) hpc
      rw [hbe]
    have hacc_u : accDepths N (finishEdge s₁ p) rest ⟨u, hu⟩ =
        accDepths N s (f :: rest) ⟨u, hu⟩ ∪ accDepths N s (f :: rest) ⟨f.vertex, hv_top⟩ := by
      rw [accDepths_finishEdge]
      unfold accDepths
      have hbe : accBackEdges N s₁ rest ⟨u, hu⟩ =
          accBackEdges N s (f :: rest) ⟨u, hu⟩ ∪ accBackEdges N s (f :: rest) ⟨f.vertex, hv_top⟩ := by
        ext b
        simp only [accBackEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hb_lt, htree, x, hx_src, hsub⟩
          by_cases hanc_f : (s.forest N).Ancestor ⟨f.vertex, hv_top⟩ x
          · right
            refine ⟨hb_lt, htree, x, hx_src, hanc_f, ?_⟩
            intro c hc hpc
            exact absurd hpc (hno_child_vtop c hc)
          · left
            refine ⟨hb_lt, htree, x, hx_src, hsub.1, ?_⟩
            intro c hc hpc
            simp only [List.map_cons, List.mem_cons] at hc
            rcases hc with hceq | hc_rest
            · have hc_eq : c = ⟨f.vertex, hv_top⟩ := Fin.ext hceq
              rw [hc_eq]
              exact hanc_f
            · exact absurd hpc (hno_child_u_rest c hc_rest)
        · rintro (⟨hb_lt, htree, x, hx_src, hsub⟩ | ⟨hb_lt, htree, x, hx_src, hsub⟩)
          · refine ⟨hb_lt, htree, x, hx_src, hsub.1, ?_⟩
            intro c hc_rest hpc
            exact hsub.2 c (List.mem_cons_of_mem _ hc_rest) hpc
          · refine ⟨hb_lt, htree, x, hx_src, Relation.ReflTransGen.head hfpar_u hsub.1, ?_⟩
            intro c hc_rest hpc
            exact absurd hpc (hno_child_u_rest c hc_rest)
      rw [hbe, Finset.image_union]
    refine ⟨hs' ▸ hdfs', ?_, ?_, ?_⟩
    · intro i hi htree
      rw [finishEdge_edges_size] at hi
      rw [finishEdge_edges_tree] at htree
      have hip : i ≠ p := by
        intro heq; subst heq; rw [hp_tree] at htree; exact Bool.noConfusion htree
      have hiq : s₁.parentEdge[(s₁.edges[p]!).source]?.join ≠ some i := by
        intro hq
        obtain ⟨_, hq_tree, _⟩ := (h.dfs.parentEdge_iff u hu i).mp hq
        rw [hq_tree] at htree; exact Bool.noConfusion htree
      rw [finishEdge_depth, finishEdge_edges_target, finishEdge_edges_source, hother i hip hiq]
      exact h.back_spec i hi htree
    · intro i hi htree u_i v_i hu_i hv_i
      rw [finishEdge_edges_size] at hi
      rw [finishEdge_edges_tree] at htree
      rw [finishEdge_edges_source] at hu_i
      rw [finishEdge_edges_target] at hv_i
      rw [finishEdge_forest]
      rcases eq_or_ne i p with rfl | hip
      · have hvi_eq : v_i = ⟨f.vertex, hv_top⟩ := Fin.ext (hv_i.symm.trans hp_tgt)
        rw [hvi_eq, hacc_other ⟨f.vertex, hv_top⟩ ?_, hpair_p]
        · exact h.tree_pair_spec i hi htree u_i ⟨f.vertex, hv_top⟩ hu_i hp_tgt
        · intro heq
          have hd := h.dfs.depth_step ⟨u, hu⟩ ⟨f.vertex, hv_top⟩ hfpar_u
          rw [heq] at hd
          omega
      · by_cases hiq : s₁.parentEdge[(s₁.edges[p]!).source]?.join = some i
        · obtain ⟨_, _, hi_tgt⟩ := (h.dfs.parentEdge_iff u hu i).mp hiq
          obtain ⟨_, _, _, _, _, htree_i⟩ := h.dfs.edges_valid i hi
          change (s.edges[i]!).tree = true at htree
          simp only [htree, ↓reduceIte, hi_tgt] at htree_i
          have hi_par : s.parent[u]?.join = some (s.edges[i]!).source := htree_i.1
          have hvi_eq : v_i = ⟨u, hu⟩ := Fin.ext (hv_i.symm.trans hi_tgt)
          rw [hvi_eq, hacc_u, (hparent_q i hiq).1]
          have hpair_i := h.tree_pair_spec i hi htree u_i ⟨u, hu⟩ hu_i hi_tgt
          have hpair_p_spec := h.tree_pair_spec p hp_lt hp_tree ⟨u, hu⟩ ⟨f.vertex, hv_top⟩ rfl hp_tgt
          have hfpar_i : (s.forest N).parent ⟨u, hu⟩ = some u_i :=
            (h.dfs.forest_parent_some_iff u_i ⟨u, hu⟩).mpr (hu_i ▸ hi_par)
          have hdepth_le : (s.forest N).depth u_i ≤ (s.forest N).depth ⟨u, hu⟩ := by
            have hd := h.dfs.depth_step u_i ⟨u, hu⟩ hfpar_i
            omega
          exact LowPairSpec.union_insert hpair_i hpair_p_spec hdepth_le
        · have htgt_ne_u : v_i ≠ ⟨u, hu⟩ := by
            intro heq
            have hval : (s.edges[i]!).target = u := hv_i.trans (congrArg Fin.val heq)
            exact hiq ((h.dfs.parentEdge_iff u hu i).mpr ⟨hi, htree, hval⟩)
          rw [hacc_other _ htgt_ne_u, hother i hip hiq]
          exact h.tree_pair_spec i hi htree u_i v_i hu_i hv_i
    · intro i hi htree hnot_mem u_i hu_i
      rw [finishEdge_edges_size] at hi
      rw [finishEdge_edges_tree] at htree
      rw [finishEdge_edges_target] at hnot_mem
      rw [finishEdge_edges_source] at hu_i
      rw [finishEdge_forest]
      rcases eq_or_ne i p with rfl | hip
      · rw [hkey_p, hpair_p]
        have hui_eq : u_i = ⟨u, hu⟩ := Fin.ext hu_i.symm
        rw [hui_eq]
        rfl
      · have hne_f : (s.edges[i]!).target ≠ f.vertex := by
          intro heq
          have hpe := (h.dfs.parentEdge_iff f.vertex hv_top i).mpr ⟨hi, htree, heq⟩
          rw [hp] at hpe
          injection hpe with hpi
          exact hip hpi.symm
        have hne_u : (s.edges[i]!).target ≠ u := by
          intro heq
          apply hnot_mem
          rw [hrest_eq, List.map_cons, List.mem_cons]
          exact Or.inl (heq.trans hfu_eq.symm)
        have hiq : s₁.parentEdge[(s₁.edges[p]!).source]?.join ≠ some i := by
          intro hq
          obtain ⟨_, _, hq_tgt⟩ := (h.dfs.parentEdge_iff u hu i).mp hq
          exact hne_u hq_tgt
        rw [hother i hip hiq]
        have hnot_mem' : (s.edges[i]!).target ∉ (f :: rest).map Frame.vertex := by
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨hne_f, hnot_mem⟩
        exact h.tree_key_spec i hi htree hnot_mem' u_i hu_i

end GraphMinor.LRPlanarity
