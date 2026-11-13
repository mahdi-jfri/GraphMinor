module

public import GraphMinor.Compute.Case3StepsMemberCompact

/-!
# Renumbering preserves member edge counts and pair order

The compact-deletion map is a bijection on the retained vertices, and its
active pair list maps back in the original order. Summing the unchanged
multiplicities shows that compact numbering preserves the deleted graph's
edge count. For a selected member, deleting the complement removes nothing.
-/

public section

namespace GraphMinor.Compute

/-- Ordered renumbering preserves the total edge multiplicity after deletion. -/
theorem case3DeleteVerticesCompact_numEdges {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVerticesCompact Z).numEdges = (G.deleteVertices Z).numEdges := by
  have hmult (u v : Fin Zᶜ.card) :
      (G.deleteVertices Z).edgeMult (compactEmb Z u) (compactEmb Z v) =
        (G.deleteVerticesCompact Z).edgeMult u v := by
    simp only [MultiDigraph.deleteVertices_edgeMult, compactEmb_not_mem,
      and_self, not_false_eq_true, ↓reduceIte, MultiDigraph.deleteVerticesCompact_edgeMult]
  rw [← MultiDigraph.sumEdgeMult_activePairsList (G.deleteVerticesCompact Z),
    ← MultiDigraph.sumEdgeMult_activePairsList (G.deleteVertices Z),
    G.activePairsList_deleteVertices_eq_map Z,
    MultiDigraph.sumEdgeMult_eq_map_sum, MultiDigraph.sumEdgeMult_eq_map_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  exact (hmult p.1 p.2).symm

/-- Compact member numbering keeps its full number of directed edges. -/
theorem case3CompactMember_numEdges (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (i : Case3SelectedGroup x Z) :
    (case3CompactMember x D Z i).numEdges =
      (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges := by
  let R := case3RoutedMember x D Z (case3RawIndexLabel x i.1)
  let S := (case3SelectedMember x Z i).verts
  have hc : (R.deleteVerticesCompact Sᶜ).numEdges = (case3CompactMember x D Z i).numEdges := by
    unfold MultiDigraph.deleteVerticesCompact compactEmb case3CompactMember
    exact congrArg (fun T : Finset (Fin x.n) => (R.induce (T.orderEmbOfFin rfl)).numEdges) (compl_compl S)
  rw [← hc, case3DeleteVerticesCompact_numEdges, case3RoutedMember_delete_compl x D hG Z hdiv i]

/-- Compact member numbering keeps its number of positive pair records. -/
theorem case3CompactMember_numActivePairs (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (i : Case3SelectedGroup x Z) :
    (case3CompactMember x D Z i).numActivePairs =
      (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs := by
  let R := case3RoutedMember x D Z (case3RawIndexLabel x i.1)
  let S := (case3SelectedMember x Z i).verts
  have hc : (R.deleteVerticesCompact Sᶜ).numActivePairs = (case3CompactMember x D Z i).numActivePairs := by
    unfold MultiDigraph.deleteVerticesCompact compactEmb case3CompactMember
    exact congrArg (fun T : Finset (Fin x.n) => (R.induce (T.orderEmbOfFin rfl)).numActivePairs) (compl_compl S)
  rw [← hc, MultiDigraph.numActivePairs_deleteVerticesCompact,
    case3RoutedMember_delete_compl x D hG Z hdiv i]

end GraphMinor.Compute
