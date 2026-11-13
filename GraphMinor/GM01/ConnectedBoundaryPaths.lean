module

public import GraphMinor.GM01.GraphSeparators

/-!
# Extending a connected region by one boundary edge

For Graph Minors I, (4.11), page 58, the middle part of `H` is
connected and contains the vertex adjacent to `w_2`. Follow a path in
that middle part and then the boundary edge. A path extracted from
these walks stays in the middle part together with `w_2`, so only its
final vertex can belong to the forbidden early and late block sets.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09

/-- An edge from a connected induced set extends paths to its far end.
All vertices of the resulting path remain in that set or at the far end. -/
theorem exists_path_across_boundary_edge {α β : Type*} {G : Graph α β} {C : Set α}
    (hCG : C ⊆ V(G)) (hconn : GraphConnected (G.induce C)) {a w x : α}
    (ha : a ∈ C) (haw : G.Adj a w) (hx : x ∈ C) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P x w ∧ V(P) ⊆ insert w C := by
  obtain ⟨e, he⟩ := haw
  have hle : G.induce (insert w C) ≤ G := G.induce_le
    (by intro y hy; rcases hy with rfl | hy; exact he.right_mem; exact hCG hy)
  have hreach : ReflTransGen (G.induce (insert w C)).Adj x a := by
    apply ReflTransGen.mono ?_ x a (hconn.2 x hx a ha)
    intro y z hyz
    obtain ⟨f, hf⟩ := hyz
    exact ⟨f, hf.1, Or.inr hf.2.1, Or.inr hf.2.2⟩
  have hlast : (G.induce (insert w C)).Adj a w := ⟨e, he, Or.inr ha, Or.inl rfl⟩
  obtain ⟨P, hP⟩ := exists_path_of_adj_reachable (Or.inr hx) (hreach.tail hlast)
  exact ⟨P, hP.mono hle, hP.le.vertexSet_mono⟩

/-- The avoidance form used in GM01 (4.11), page 58. The connected
set avoids the forbidden set, while the final boundary vertex is allowed. -/
theorem exists_avoiding_path_across_boundary_edge {α β : Type*} {G : Graph α β}
    {C F : Set α} (hC : C ⊆ V(G) \ F) (hconn : GraphConnected (G.induce C))
    {a w x : α} (ha : a ∈ C) (haw : G.Adj a w) (hx : x ∈ C) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P x w ∧ Disjoint V(P) (F \ {w}) := by
  obtain ⟨P, hP, hV⟩ := exists_path_across_boundary_edge (hC.trans sdiff_subset) hconn ha haw hx
  refine ⟨P, hP, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hyF
  rcases hV hy with hyw | hyC
  · exact hyF.2 hyw
  · exact (hC hyC).2 hyF.1

end GraphMinor.GM01
