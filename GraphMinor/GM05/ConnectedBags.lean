module

public import GraphMinor.GM05.Defs
import GraphMinor.GM05.TreeHelly
import GraphMinor.GM10.TreeWidthBasic

/-!
# Bags meeting connected subgraphs

The bags meeting a connected subgraph form a subtree of the decomposition
tree. If connected subgraphs touch pairwise, their bag subtrees intersect
pairwise. The Helly property then gives a bag meeting them all. This is the
bag bound used for the grid in Graph Minors V, (1.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V ι J : Type*}

private lemma path_triangle {T : SimpleGraph ι} {a b c q : ι}
    (h : OnTreePath T a b c) : OnTreePath T a q c ∨ OnTreePath T q b c := by
  classical
  by_cases h₁ : OnTreePath T a q c
  · exact Or.inl h₁
  · change ¬ ∀ p : T.Walk a q, p.IsPath → c ∈ p.support at h₁
    push Not at h₁
    obtain ⟨p, hp, hpc⟩ := h₁
    right
    intro r hr
    have hc := GM10.mem_support_of_onTreePath h (p.append r)
    exact (Walk.mem_support_append_iff p r).mp hc |>.resolve_left hpc

private lemma bag_meets_walk [Fintype ι]
    {C G : (⊤ : SimpleGraph V).Subgraph} (hCG : C ≤ G)
    {T : SimpleGraph ι} {χ : ι → Set V} (htd : IsTreeDecomposition G T χ)
    {x y : C.verts} (p : C.coe.Walk x y) :
    ∀ {a b c}, x.1 ∈ χ a → y.1 ∈ χ b → OnTreePath T a b c →
      ∃ z ∈ C.verts, z ∈ χ c := by
  induction p with
  | @nil x =>
    intro a b c hx hy hp
    exact ⟨x.1, x.2, htd.inter_subset hp ⟨hx, hy⟩⟩
  | @cons x y z hxy p ih =>
    intro a b c hx hz hp
    obtain ⟨q, hqx, hqy⟩ := htd.adj_mem (hCG.2 hxy)
    rcases path_triangle (q := q) hp with hpa | hpb
    · exact ⟨x.1, x.2, htd.inter_subset hpa ⟨hx, hqx⟩⟩
    · exact ih hqy hz hpb

/-- A connected subgraph meeting the two endpoint bags also meets every bag
on the path between them. -/
theorem IsTreeDecomposition.meets_connected_on_path [Fintype ι]
    {C G : (⊤ : SimpleGraph V).Subgraph} (hCG : C ≤ G) (hC : C.Connected)
    {T : SimpleGraph ι} {χ : ι → Set V} (htd : IsTreeDecomposition G T χ)
    {a b c : ι} (hp : OnTreePath T a b c)
    (ha : (χ a ∩ C.verts).Nonempty) (hb : (χ b ∩ C.verts).Nonempty) :
    (χ c ∩ C.verts).Nonempty := by
  obtain ⟨x, hxa, hxC⟩ := ha
  obtain ⟨y, hyb, hyC⟩ := hb
  obtain ⟨p⟩ := hC.coe ⟨x, hxC⟩ ⟨y, hyC⟩
  obtain ⟨z, hzC, hzc⟩ := bag_meets_walk hCG htd p hxa hyb hp
  exact ⟨z, hzc, hzC⟩

/-- Every family of pairwise touching connected subgraphs is met by one bag
of a finite tree-decomposition. Two subgraphs touch when they share a vertex
or an edge of the ambient graph joins them. -/
theorem IsTreeDecomposition.exists_bag_meeting_touching [Fintype ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι} {χ : ι → Set V}
    (htd : IsTreeDecomposition G T χ)
    (C : J → (⊤ : SimpleGraph V).Subgraph)
    (hCG : ∀ i, C i ≤ G) (hC : ∀ i, (C i).Connected)
    (htouch : ∀ i j, ∃ x ∈ (C i).verts, ∃ y ∈ (C j).verts,
      x = y ∨ G.Adj x y) :
    ∃ t, ∀ i, (χ t ∩ (C i).verts).Nonempty := by
  classical
  let A : J → Set ι := fun i ↦ {t | (χ t ∩ (C i).verts).Nonempty}
  apply tree_helly htd.isTree A
  · intro i a ha b hb c hp
    exact htd.meets_connected_on_path (hCG i) (hC i) hp ha hb
  · intro i j
    obtain ⟨x, hx, y, hy, hxy⟩ := htouch i j
    rcases hxy with he | he
    · subst y
      have hxG : x ∈ G.verts := (hCG i).1 hx
      rw [← htd.iUnion_eq] at hxG
      obtain ⟨t, ht⟩ := mem_iUnion.mp hxG
      exact ⟨t, ⟨x, ht, hx⟩, ⟨x, ht, hy⟩⟩
    · obtain ⟨t, hxt, hyt⟩ := htd.adj_mem he
      exact ⟨t, ⟨x, hxt, hx⟩, ⟨y, hyt, hy⟩⟩

end GraphMinor.GM05
