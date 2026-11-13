module

public import GraphMinor.GM06.Section4Comparison
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4CuffConnected
import GraphMinor.GM06.Section4ComparisonConnected
import GraphMinor.GM06.Section4TwoParts

/-!
# The cuff parts are components of G′

On pages 126–127 of VI (4.2), each cuff base lies in one part of a
partition of G′. Since each base is joined in G′ and G′ is disconnected,
a nonempty cuff part is exactly a component. This gives the connected
restriction to which the paper applies (4.3).
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Each nonempty cuff part is the vertex set of a component of G′
when neither obstruction nor reduction applies in VI (4.2). -/
theorem exists_comparison_component_on_cuff
    {G H : Drawing ClosedCylinder} (hG : G.IsProper) (hH : H.IsProper)
    (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder)
    (hno41 : ¬ Section4Condition41Applies G H)
    (hno1 : ¬ Section4Reduction1Applies G H) (hno2 : ¬ Section4Reduction2Applies G H)
    {K : Graph ClosedCylinder (Set ClosedCylinder)} (hK : IsGraphComponent K H.toGraph)
    (hbases : ∀ C ∈ cuffs ClosedCylinder, IsIntervalBasedOn H K C)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    (hX : (Graph.vertexSet K ∩ C).Nonempty) :
    ∃ L : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent L (componentComparisonDrawing G H K).toGraph ∧
      Graph.vertexSet L = Graph.vertexSet K ∩ C := by
  have hcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
    rw [cuffs_closedCylinder] at hC
    exact hC
  have hother : ∃ D ∈ cuffs ClosedCylinder, bd ClosedCylinder = C ∪ D := by
    rcases hcases with rfl | rfl
    · exact ⟨cylinderCuff2, by rw [cuffs_closedCylinder]; exact Or.inr rfl, bd_closedCylinder⟩
    · exact ⟨cylinderCuff1, by rw [cuffs_closedCylinder]; exact Or.inl rfl,
        bd_closedCylinder.trans (union_comm _ _)⟩
  obtain ⟨D, hD, hBD⟩ := hother
  have hW : Graph.vertexSet K ∩ bd ClosedCylinder ⊆ G.V := by
    intro v hv
    exact (hbd ▸ (show v ∈ H.V ∩ bd ClosedCylinder from ⟨hK.1.vertexSet_mono hv.1, hv.2⟩)).1
  have hcover : (componentComparisonDrawing G H K).toGraph.vertexSet =
      (Graph.vertexSet K ∩ C) ∪ (Graph.vertexSet K ∩ D) := by
    change (componentComparisonDrawing G H K).V = _
    rw [componentComparisonDrawing_V G H K hW, hBD, inter_union_distrib_left]
  obtain ⟨A, hA⟩ := hbases C hC
  obtain ⟨B, hB⟩ := hbases D hD
  exact exists_component_of_two_joined_parts hcover hX
    (fun a ha b hb => exists_comparison_walk_of_cuffBase hforest hbd hno41 hno2 hA ha hb)
    (fun a ha b hb => exists_comparison_walk_of_cuffBase hforest hbd hno41 hno2 hB ha hb)
    (not_connected_componentComparisonDrawing_of_not_reduction1 hG hH hforest hbd hK hno1)

end GraphMinor.GM06
