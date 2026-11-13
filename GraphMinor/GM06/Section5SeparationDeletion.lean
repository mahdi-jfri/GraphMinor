module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.Forest
import GraphMinor.GM11.Section5
import GraphMinor.GM11.Walks

/-!
# Deleting an edge on the discarded side of Reduction 2

For VI (5.5), page 130, a clockwise edge of the discarded side
can first be deleted by the proved Reduction 1 case. The retained
side is unchanged, and deleting the same edge on the other side
preserves the graph separation. This is the separation calculation
needed for induction over such deletions.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A subdrawing is a subgraph of the associated drawing graph. -/
theorem toGraph_le_of_isSubdrawing
    {S : Type*} [TopologicalSpace S] {G H : Drawing S} (hHG : H.IsSubdrawing G) :
    H.toGraph ≤ G.toGraph where
  vertexSet_mono := hHG.1
  isLink_mono _ _ _ hl := (hHG.isLink_iff hl.1).1 hl

/-- Deleting an edge on the second side preserves a graph separation,
with the first side retained and the second side's edge deleted. -/
theorem graph_separation_after_discarded_edge_deletion
    {S : Type*} [TopologicalSpace S] [T2Space S] {G G₁ G₂ H : Drawing S}
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    {e : Set S} (he : e ∈ G₂.E) (hV : H.V = G.V) (hE : H.E = G.E \ {e}) :
    IsGraphSeparation H.toGraph G₁.toGraph (G₂.deleteEdge e).toGraph := by
  have he₁ : e ∉ G₁.E := fun he₁ => disjoint_left.mp hsep.2.2.2.2 he₁ he
  have h₁ : G₁.IsSubdrawing H := by
    constructor
    · rw [hV]
      exact hsep.1.vertexSet_mono
    · rw [hE]
      intro f hf
      exact ⟨hsep.1.edgeSet_mono hf, fun hfe => he₁ ((mem_singleton_iff.mp hfe) ▸ hf)⟩
  have h₂ : (G₂.deleteEdge e).IsSubdrawing H := by
    constructor
    · rw [GraphMinor.GM11.deleteEdge_V, hV]
      exact hsep.2.1.vertexSet_mono
    · rw [GraphMinor.GM11.deleteEdge_E, hE]
      exact fun f hf => ⟨hsep.2.1.edgeSet_mono hf.1, hf.2⟩
  refine ⟨toGraph_le_of_isSubdrawing h₁, toGraph_le_of_isSubdrawing h₂, ?_, ?_, ?_⟩
  · change G₁.V ∪ (G₂.deleteEdge e).V = H.V
    rw [GraphMinor.GM11.deleteEdge_V, hV]
    exact hsep.2.2.1
  · change G₁.E ∪ (G₂.deleteEdge e).E = H.E
    rw [GraphMinor.GM11.deleteEdge_E, hE]
    have hOld : G₁.E ∪ G₂.E = G.E := hsep.2.2.2.1
    rw [← hOld]
    ext f
    constructor
    · rintro (hf | hf)
      · exact ⟨Or.inl hf, fun hfe => he₁ ((mem_singleton_iff.mp hfe) ▸ hf)⟩
      · exact ⟨Or.inr hf.1, hf.2⟩
    · rintro ⟨hf | hf, hfe⟩
      · exact Or.inl hf
      · exact Or.inr ⟨hf, hfe⟩
  · change Disjoint G₁.E (G₂.deleteEdge e).E
    rw [GraphMinor.GM11.deleteEdge_E]
    exact hsep.2.2.2.2.mono_right sdiff_subset

end GraphMinor.GM06
