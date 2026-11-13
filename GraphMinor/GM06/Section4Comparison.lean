module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4SubgraphDrawing
import GraphMinor.GM11.Walks

/-!
# The comparison drawing G′ in VI (4.2)

On page 126, the paper takes G′ with vertices the boundary vertices of
a component K of H. It retains the edges of G with distinct ends whose
paths in H are homotopic to the edges. We express this with injective
parameterizations of the edge closure and of a path drawing in H.
The endpoint labels are arbitrary, so the condition covers either
orientation. Spanning these vertices and edges gives the drawing G′.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- The edges retained in G′ in Graph Minors VI (4.2), page 126: their
ends are distinct boundary vertices of K, and the path of H between
those ends is homotopic to the edge. -/
@[expose] def componentHomotopicEdges
    {S : Type u} [TopologicalSpace S] (G H : Drawing S) (K : Graph S (Set S)) : Set (Set S) :=
  {e | e ∈ G.E ∧ ∀ a b, G.toGraph.IsLink e a b →
    a ∈ Graph.vertexSet K ∩ bd S ∧ b ∈ Graph.vertexSet K ∩ bd S ∧ a ≠ b ∧
      ∃ P : Drawing S, IsSubpathOf H P a b ∧
        ∃ f g : Curve S, ParametrizesSet f (closure e) a b ∧
          ParametrizesSet g P.U a b ∧ CurvesHomotopic f g}

/-- G′ in the final argument of Graph Minors VI (4.2), page 126. -/
def componentComparisonDrawing
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G H : Drawing S) (K : Graph S (Set S)) : Drawing S :=
  G.span (Graph.vertexSet K ∩ bd S) (componentHomotopicEdges G H K)

/-- G′ is a subdrawing of G. -/
theorem componentComparisonDrawing_isSubdrawing
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G H : Drawing S) (K : Graph S (Set S)) :
    (componentComparisonDrawing G H K).IsSubdrawing G :=
  Drawing.span_isSubdrawing G _ _

/-- The span used to construct G′ adds no vertex outside its prescribed
boundary vertex set. -/
theorem componentComparisonDrawing_V
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G H : Drawing S) (K : Graph S (Set S))
    (hW : Graph.vertexSet K ∩ bd S ⊆ G.V) :
    (componentComparisonDrawing G H K).V = Graph.vertexSet K ∩ bd S := by
  rw [componentComparisonDrawing, Drawing.span_V, Drawing.spanV]
  apply Subset.antisymm
  · rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨a, b, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet he.2
      have hends := he.1.2 a b hl
      rw [hl.2.2.2] at hxe
      rcases hxe with rfl | hxb
      · exact hends.1
      · exact hxb ▸ hends.2.1
  · intro x hx
    exact Or.inl ⟨hx, hW hx⟩

/-- The edges of G′ are precisely the homotopic edges selected above. -/
theorem componentComparisonDrawing_E
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G H : Drawing S) (K : Graph S (Set S)) :
    (componentComparisonDrawing G H K).E = componentHomotopicEdges G H K := by
  rw [componentComparisonDrawing, Drawing.span_E]
  exact inter_eq_left.mpr fun e he => he.1

/-- A link of G′ supplies the path and homotopy data in its definition. -/
theorem componentComparisonDrawing_edge_data
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G H : Drawing S) (K : Graph S (Set S)) {e : Set S} {a b : S}
    (hl : (componentComparisonDrawing G H K).toGraph.IsLink e a b) :
    a ∈ Graph.vertexSet K ∩ bd S ∧ b ∈ Graph.vertexSet K ∩ bd S ∧ a ≠ b ∧
      ∃ P : Drawing S, IsSubpathOf H P a b ∧
        ∃ f g : Curve S, ParametrizesSet f (closure e) a b ∧
          ParametrizesSet g P.U a b ∧ CurvesHomotopic f g := by
  have he : e ∈ componentHomotopicEdges G H K := by
    rw [← componentComparisonDrawing_E G H K]
    exact hl.1
  exact he.2 a b (((componentComparisonDrawing_isSubdrawing G H K).isLink_iff hl.1).mp hl)

/-- G′ is proper when G is proper. -/
theorem componentComparisonDrawing_isProper
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {G H : Drawing S} (hG : G.IsProper) (K : Graph S (Set S)) :
    (componentComparisonDrawing G H K).IsProper :=
  isProper_of_isSubdrawing hG (componentComparisonDrawing_isSubdrawing G H K)

end GraphMinor.GM06
