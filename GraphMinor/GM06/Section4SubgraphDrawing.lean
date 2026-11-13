module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks

/-!
# Realizing subgraphs as subdrawings

In the final argument of Graph Minors VI (4.2), page 126, the graph G′
and a spanning tree of it must be viewed as drawings. We take the span
of their vertices and edges in the original drawing. For a subgraph,
the span adds no vertices, and its graph is exactly the specified one.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- The drawing spanned in `G` by the vertices and edges of `T`. -/
def drawingOfSubgraph {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) (T : Graph S (Set S)) : Drawing S :=
  G.span (Graph.vertexSet T) (Graph.edgeSet T)

/-- A subgraph's drawing is a subdrawing of the ambient drawing. -/
theorem drawingOfSubgraph_isSubdrawing
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) (T : Graph S (Set S)) : (drawingOfSubgraph G T).IsSubdrawing G :=
  Drawing.span_isSubdrawing G _ _

/-- Spanning the vertices and edges of a subgraph adds no new vertices. -/
theorem drawingOfSubgraph_V
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {T : Graph S (Set S)} (hT : T ≤ G.toGraph) :
    (drawingOfSubgraph G T).V = Graph.vertexSet T := by
  rw [drawingOfSubgraph, Drawing.span_V, Drawing.spanV]
  apply Subset.antisymm
  · rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨a, b, hl⟩ := T.exists_isLink_of_mem_edgeSet he.1
      have hG := hl.mono hT
      rw [hG.2.2.2] at hxe
      rcases hxe with rfl | hxb
      · exact hl.left_mem
      · exact hxb ▸ hl.right_mem
  · intro x hx
    exact Or.inl ⟨hx, hT.vertexSet_mono hx⟩

/-- The edges of a realized subgraph are exactly its edges. -/
theorem drawingOfSubgraph_E
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {T : Graph S (Set S)} (hT : T ≤ G.toGraph) :
    (drawingOfSubgraph G T).E = Graph.edgeSet T := by
  rw [drawingOfSubgraph, Drawing.span_E]
  exact inter_eq_left.mpr hT.edgeSet_mono

/-- The graph underlying the subgraph drawing is the specified subgraph. -/
theorem drawingOfSubgraph_toGraph
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {T : Graph S (Set S)} (hT : T ≤ G.toGraph) :
    (drawingOfSubgraph G T).toGraph = T := by
  have hsub := drawingOfSubgraph_isSubdrawing G T
  have hE := drawingOfSubgraph_E G hT
  refine Graph.ext (drawingOfSubgraph_V G hT) ?_
  intro e a b
  constructor
  · intro hl
    have heT : e ∈ Graph.edgeSet T := hE ▸ hl.1
    exact (hT.isLink_iff heT).mpr ((hsub.isLink_iff hl.1).mp hl)
  · intro hl
    have he : e ∈ (drawingOfSubgraph G T).E := hE.symm ▸ hl.edge_mem
    exact (hsub.isLink_iff he).mpr (hl.mono hT)

/-- A subdrawing of a proper drawing is proper. -/
theorem isProper_of_isSubdrawing
    {S : Type u} [TopologicalSpace S] {G P : Drawing S}
    (hG : G.IsProper) (hP : P.IsSubdrawing G) : P.IsProper := by
  rintro x ⟨hxbd, hxP⟩
  have hxG : x ∈ G.V := hG ⟨hxbd, hP.U_subset hxP⟩
  by_contra hxPV
  obtain ⟨e, he, hxe⟩ := P.exists_edge_of_mem hxP hxPV
  exact ((hP.2 he).2.1 hxe).2 hxG

end GraphMinor.GM06
