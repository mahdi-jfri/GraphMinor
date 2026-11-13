module

public import GraphMinor.GM05.SeriesParallelDefs
import GraphMinor.GM05.BagPruning
import GraphMinor.GM05.ForestDecomposition

/-!
# Graph Minors V, (1.2): series-parallel graphs and tree-width two

Pruning contained leaf bags finds a vertex with at most two neighbours.
Suppress it and delete it from the bags. Conversely, a bag containing the
neighbours exists after suppression, since there are at most two neighbours
and they are adjacent. Attach the suppressed vertex in a new leaf bag.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V ι : Type*}

/-- A graph admitting finitely many series-parallel reductions has finitely
many vertices. -/
theorem IsSeriesParallelSimple.finiteVerts {G : (⊤ : SimpleGraph V).Subgraph}
    (h : IsSeriesParallelSimple G) : G.verts.Finite := by
  induction h with
  | empty h => rw [h]; exact finite_empty
  | @reduce G v hv hd h ih =>
    apply (ih.insert v).subset
    intro x hx
    by_cases he : x = v
    · exact Or.inl he
    · exact Or.inr ⟨hx, he⟩

private lemma bag_subset [Fintype ι] {G : (⊤ : SimpleGraph V).Subgraph}
    {T : SimpleGraph ι} {χ : ι → Set V} (h : IsTreeDecomposition G T χ) (t : ι) :
    χ t ⊆ G.verts := by
  rw [← h.iUnion_eq]
  exact subset_iUnion χ t

private lemma eliminate_decomposition [Fintype ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι} {χ : ι → Set V}
    (h : IsTreeDecomposition G T χ) {v : V} {t₀ : ι}
    (hN : G.neighborSet v ⊆ χ t₀) :
    IsTreeDecomposition (eliminateVertex G v) T (fun t ↦ χ t \ {v}) := by
  refine ⟨h.isTree, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_iUnion, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, hxv⟩
      exact ⟨bag_subset h t ht, hxv⟩
    · rintro ⟨hx, hxv⟩
      rw [← h.iUnion_eq] at hx
      obtain ⟨t, ht⟩ := mem_iUnion.mp hx
      exact ⟨t, ht, hxv⟩
  · intro x y hxy
    rcases hxy.2.2.2 with hxy' | ⟨hvx, hvy⟩
    · obtain ⟨t, hx, hy⟩ := h.adj_mem hxy'
      exact ⟨t, ⟨hx, hxy.2.1.2⟩, ⟨hy, hxy.2.2.1.2⟩⟩
    · exact ⟨t₀, ⟨hN hvx, hxy.2.1.2⟩, ⟨hN hvy, hxy.2.2.1.2⟩⟩
  · intro a c b hp x hx
    exact ⟨h.inter_subset hp ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩

/-- A finite graph of width at most two can be reduced by series and parallel
reductions. At every stage a leaf bag supplies the next vertex. -/
theorem isSeriesParallelSimple_of_treeWidthLE_two
    {G : (⊤ : SimpleGraph V).Subgraph} (hfin : G.verts.Finite)
    (hw : TreeWidthLE G 2) : IsSeriesParallelSimple G := by
  classical
  have main : ∀ n, ∀ G : (⊤ : SimpleGraph V).Subgraph,
      G.verts.ncard = n → G.verts.Finite → TreeWidthLE G 2 → IsSeriesParallelSimple G := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hcard hfin hw
      by_cases hemp : G.verts = ∅
      · exact .empty hemp
      · obtain ⟨ι, _, T, χ, htd, hwidth⟩ := hw
        obtain ⟨v, hv, t, hvt, hN⟩ :=
          htd.exists_vertex_neighbours_in_bag (nonempty_iff_ne_empty.mpr hemp)
        have hχfin := hfin.subset (bag_subset htd t)
        have hNsub : G.neighborSet v ⊆ χ t \ {v} :=
          fun x hx ↦ ⟨hN hx, hx.ne.symm⟩
        have hdeg : (G.neighborSet v).ncard ≤ 2 := by
          have hle := ncard_le_ncard hNsub hχfin.sdiff
          have heq := ncard_sdiff_singleton_add_one hvt hχfin
          have hbound := hwidth t
          omega
        apply IsSeriesParallelSimple.reduce v hv hdeg
        have hHfin : (eliminateVertex G v).verts.Finite := hfin.sdiff
        have hlt : (eliminateVertex G v).verts.ncard < n := by
          rw [← hcard]
          exact ncard_sdiff_singleton_lt_of_mem hv hfin
        apply ih _ hlt _ rfl hHfin
        apply treeWidthLE_of_isTreeDecomposition (eliminate_decomposition htd hN)
        intro q
        exact (ncard_le_ncard sdiff_subset (hfin.subset (bag_subset htd q))).trans (hwidth q)
  exact main _ G rfl hfin hw

private lemma delete_decomposition [Fintype ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι} {χ : ι → Set V} {v : V}
    (h : IsTreeDecomposition (eliminateVertex G v) T χ) :
    IsTreeDecomposition (G.deleteVerts {v}) T χ := by
  refine ⟨h.isTree, h.iUnion_eq, ?_, h.inter_subset⟩
  intro x y hxy
  obtain ⟨hx, hy, hxy⟩ := hxy
  exact h.adj_mem ⟨hxy.ne, hx, hy, Or.inl hxy⟩

private lemma exists_bag_of_two_neighbours [Fintype ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι} {χ : ι → Set V} {v : V}
    (h : IsTreeDecomposition (eliminateVertex G v) T χ)
    (hdeg : (G.neighborSet v).ncard ≤ 2) (hfin : G.verts.Finite) :
    ∃ t, G.neighborSet v ⊆ χ t := by
  classical
  have hNfin : (G.neighborSet v).Finite := hfin.subset (fun _ hx ↦ hx.snd_mem)
  have hmem : ∀ x ∈ G.neighborSet v, x ∈ (eliminateVertex G v).verts :=
    fun x hx ↦ ⟨hx.snd_mem, hx.ne.symm⟩
  by_cases hsmall : (G.neighborSet v).ncard ≤ 1
  · by_cases hne : (G.neighborSet v).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxH := hmem x hx
      rw [← h.iUnion_eq] at hxH
      obtain ⟨t, ht⟩ := mem_iUnion.mp hxH
      refine ⟨t, fun y hy ↦ ?_⟩
      have he := (ncard_le_one hNfin).mp hsmall y hy x hx
      exact he ▸ ht
    · obtain ⟨t⟩ := h.isTree.connected.nonempty
      exact ⟨t, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩
  · have htwo : (G.neighborSet v).ncard = 2 := by omega
    obtain ⟨x, y, hxy, heq⟩ := ncard_eq_two.mp htwo
    have hx : x ∈ G.neighborSet v := heq ▸ mem_insert x {y}
    have hy : y ∈ G.neighborSet v := heq ▸ mem_insert_of_mem x (mem_singleton y)
    obtain ⟨t, hxt, hyt⟩ := h.adj_mem ⟨hxy, hmem x hx, hmem y hy, Or.inr ⟨hx, hy⟩⟩
    refine ⟨t, ?_⟩
    rw [heq]
    intro z hz
    rcases hz with rfl | rfl
    · exact hxt
    · exact hyt

/-- Reversing a series-parallel reduction adds a leaf bag of at most three
vertices, containing the suppressed vertex and its neighbours. -/
theorem treeWidthLE_two_of_isSeriesParallelSimple
    {G : (⊤ : SimpleGraph V).Subgraph} (h : IsSeriesParallelSimple G) : TreeWidthLE G 2 := by
  classical
  induction h with
  | @empty G hemp =>
    have htd : IsTreeDecomposition G (⊥ : SimpleGraph Unit) (fun _ ↦ ∅) := by
      refine ⟨IsTree.of_subsingleton, ?_, ?_, ?_⟩
      · simpa using hemp.symm
      · intro x y hxy
        exact (hemp ▸ hxy.fst_mem).elim
      · intro a b c hp
        exact inter_subset_left
    exact treeWidthLE_of_isTreeDecomposition htd (fun _ ↦ by simp)
  | @reduce G v hv hdeg h ih =>
    have hfin : G.verts.Finite := (IsSeriesParallelSimple.reduce v hv hdeg h).finiteVerts
    obtain ⟨ι, _, T, χ, htd, hw⟩ := ih
    obtain ⟨t₀, hN⟩ := exists_bag_of_two_neighbours htd hdeg hfin
    apply treeWidthLE_of_isTreeDecomposition
      (attach_vertex_decomposition hv (delete_decomposition htd) t₀
        (G.neighborSet v) hN (fun _ hx ↦ hx))
    intro t
    cases t with
    | none => exact (ncard_insert_le v _).trans (Nat.add_le_add_right hdeg 1)
    | some t => exact hw t

/-- The simple-graph form of Graph Minors V, (1.2), page 93. -/
theorem treeWidthLE_two_iff_isSeriesParallelSimple
    {G : (⊤ : SimpleGraph V).Subgraph} (hfin : G.verts.Finite) :
    TreeWidthLE G 2 ↔ IsSeriesParallelSimple G :=
  ⟨isSeriesParallelSimple_of_treeWidthLE_two hfin, treeWidthLE_two_of_isSeriesParallelSimple⟩

/-- Graph Minors V, (1.2), page 93:
"The graphs of tree-width $\le 2$ are precisely the series-parallel graphs."
Vertex bags see the same ends in the simple shadow as in the multigraph.
The proof suppresses vertices supplied by leaf bags and reverses those
reductions by attaching bags with at most three vertices. -/
theorem theorem_1_2_proof {α β : Type*} (G : Graph α β)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    TreeWidthLE (simpleShadow G) 2 ↔ IsSeriesParallel G := by
  exact ⟨fun h ↦ ⟨hV, hE, isSeriesParallelSimple_of_treeWidthLE_two hV h⟩,
    fun h ↦ treeWidthLE_two_of_isSeriesParallelSimple h.2.2⟩

end GraphMinor.GM05
