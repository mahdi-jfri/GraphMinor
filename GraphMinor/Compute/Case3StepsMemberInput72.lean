module

public import GraphMinor.Compute.Case3StepsCompactCounts
public import GraphMinor.Compute.Specs13

/-!
# The compact member as an input to (7.2)

The input graph uses the member's increasing vertex numbering and retains
its full directed multiplicities. Its size expression is rewritten using
the edge-count preservation lemma, ready for summing the member calls in
XIII (9.9), step 6, pp. 105–106.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The graph passed to (7.2) for one selected division member. -/
noncomputable def case3MemberAlgorithm72Input (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z) : Algorithm72Input where
  n := (case3SelectedMember x Z i).verts.card
  G := case3CompactMember x D Z i

/-- Ordered renumbering leaves the member call's edge contribution unchanged. -/
theorem case3MemberAlgorithm72Size_eq (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (i : Case3SelectedGroup x Z) :
    algorithm72Size (case3MemberAlgorithm72Input x D Z i) =
      ((case3SelectedMember x Z i).verts.card + 1) ^ 2 +
        (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges +
        (case3SelectedMember x Z i).verts.card + 1 := by
  change _ + (case3CompactMember x D Z i).numEdges + _ + 1 = _
  rw [case3CompactMember_numEdges x D hG Z hdiv i]
  rfl

end GraphMinor.Compute
