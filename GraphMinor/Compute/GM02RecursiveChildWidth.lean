module

public import GraphMinor.Compute.GM02RecursiveChosenChild
public import GraphMinor.Compute.GM02RecursiveSides
public import GraphMinor.GM02.RecursiveWidthReports

/-!
# Propagating the exact compact child's width report

The machine's child is a numbered copy of the corrected induced graph.
Its numerical width is therefore the induced graph's width. That graph
is a subgraph of the parent, so (2.7) transfers every threshold report
back to the parent, for either side of the selected crossing scheme.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- The numerical width of either constructed recursive child is at most the parent's width. -/
theorem gm02RecursiveChosenInput_width_le (right allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hvalid : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    (gm02RecursiveChosenInput right x L R C).width ≤ x.width := by
  have hsep := gm02RecursiveSides_canonical allVertices x q L R hvalid
  cases right with
  | false =>
    change (gm02CanonicalLeftInput x.G L R x.A _).width ≤ x.width
    rw [gm02CanonicalLeftInput_eq_numbered]
    change (gm02NumberedInstance _ _ _).width ≤ x.width
    rw [gm02NumberedInstance_width _ _ _ (Set.toFinite _) (Set.toFinite _)]
    exact treeWidth_le_of_subgraph (Set.toFinite _) (Set.toFinite _)
      ((gm02CanonicalBoundaryScheme x L R C).inducedLeft_le hsep)
  | true =>
    change (gm02CanonicalRightInput x.G L R x.A _).width ≤ x.width
    rw [gm02CanonicalRightInput_eq_numbered]
    change (gm02NumberedInstance _ _ _).width ≤ x.width
    rw [gm02NumberedInstance_width _ _ _ (Set.toFinite _) (Set.toFinite _)]
    exact treeWidth_le_of_subgraph (Set.toFinite _) (Set.toFinite _)
      ((gm02CanonicalBoundaryScheme x L R C).inducedRight_le hsep)

/-- A width flag returned on a compact child is valid for its parent. -/
theorem gm02RecursiveChosenInput_width_report (right allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hvalid : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R))
    (hchild : q ≤ (gm02RecursiveChosenInput right x L R C).width) : q ≤ x.width :=
  hchild.trans (gm02RecursiveChosenInput_width_le right allVertices x q L R C hvalid)

end GraphMinor.Compute
