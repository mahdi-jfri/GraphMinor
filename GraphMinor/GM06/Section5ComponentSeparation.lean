module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Basic

/-!
# Separating a graph component

To use Reduction 2 in the proof of VI (5.1), a component not used by
the linkage can be discarded. A component and the graph induced on
all remaining vertices form a separation with disjoint vertex sets.
An edge cannot join the two sides, since a component contains both
ends of each incident edge.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Graph

universe u v

/-- A component and the induced graph on its remaining vertices form
a separation of the graph. -/
theorem isGraphSeparation_of_component
    {α : Type u} {β : Type v} {G C : Graph α β} (hC : IsGraphComponent C G) :
    IsGraphSeparation G (G.induce (Graph.vertexSet G \ Graph.vertexSet C)) C := by
  let F := G.induce (Graph.vertexSet G \ Graph.vertexSet C)
  have hF : F ≤ G := G.induce_le sdiff_subset
  refine ⟨hF, hC.1, ?_, ?_, ?_⟩
  · change (Graph.vertexSet G \ Graph.vertexSet C) ∪ Graph.vertexSet C = Graph.vertexSet G
    exact sdiff_union_of_subset hC.1.vertexSet_mono
  · apply Subset.antisymm
    · exact union_subset hF.edgeSet_mono hC.1.edgeSet_mono
    · intro e he
      obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet he
      by_cases ha : a ∈ Graph.vertexSet C
      · exact Or.inr ((hC.isLink_iff_of_mem ha).mpr hl).edge_mem
      · have hb : b ∉ Graph.vertexSet C := fun hb => ha ((hC.mem_iff_of_isLink hl).mpr hb)
        exact Or.inl (show F.IsLink e a b from ⟨hl, ⟨hl.left_mem, ha⟩, ⟨hl.right_mem, hb⟩⟩).edge_mem
  · apply disjoint_left.mpr
    intro e heF heC
    obtain ⟨a, b, hlC⟩ := C.exists_isLink_of_mem_edgeSet heC
    have hlF : F.IsLink e a b := (hF.isLink_iff heF).mpr (hlC.mono hC.1)
    exact hlF.2.1.2 hlC.left_mem

end GraphMinor.GM06
