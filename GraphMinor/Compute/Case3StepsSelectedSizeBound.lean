module

public import GraphMinor.Compute.Case3StepsPrivateContribution

/-!
# Summing the selected member sizes

The estimate in XIII (9.9), p. 106 charges each member to its private
outside vertices and its full directed edges. The outside sets are disjoint,
and each directed copy has at most one owner. Multiplying by the ambient
vertex bound gives the running-time sum used in step (6).
-/

public section

namespace GraphMinor.Compute

/-- The page 106 private-contribution estimate summed over all selected
members, with full multiplicities. -/
theorem case3SelectedMembers_sum_size_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) :
    (∑ i : Case3SelectedGroup x d.core.Z,
      ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
        (case3SelectedMember x d.core.Z i).verts.card + 1)) ≤ 4 * (x.n + D.numEdges) := by
  classical
  calc
    _ ≤ ∑ i : Case3SelectedGroup x d.core.Z,
        4 * (((case3SelectedMember x d.core.Z i).verts \ d.core.Z).card +
          (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges) :=
      Finset.sum_le_sum (fun i _ => case3SelectedMember_size_le_four_private x D hG d hd i)
    _ = 4 * ((∑ i : Case3SelectedGroup x d.core.Z,
        ((case3SelectedMember x d.core.Z i).verts \ d.core.Z).card) +
        ∑ i : Case3SelectedGroup x d.core.Z,
          (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.add_le_add
      (case3SelectedMembers_sum_outside_card_le x d.core.Z)
      (case3SelectedMembers_sum_numEdges_le x D d.core.Z))

/-- Graph Minors XIII, (9.9), p. 106: the sum of the member products is
bounded by four times the ambient product. Here the extra ones are the
paper's conventions for vertex and edge size. -/
theorem case3SelectedMembers_sum_vertex_mul_size_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) :
    (∑ i : Case3SelectedGroup x d.core.Z,
      ((case3SelectedMember x d.core.Z i).verts.card + 1) *
        ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
          (case3SelectedMember x d.core.Z i).verts.card + 1)) ≤
      4 * (x.n + 1) * (D.numEdges + x.n + 1) := by
  classical
  calc
    _ ≤ ∑ i : Case3SelectedGroup x d.core.Z, (x.n + 1) *
        ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
          (case3SelectedMember x d.core.Z i).verts.card + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right
        ((Finset.card_le_univ _).trans_eq (Fintype.card_fin x.n)) 1)
    _ = (x.n + 1) * (∑ i : Case3SelectedGroup x d.core.Z,
        ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
          (case3SelectedMember x d.core.Z i).verts.card + 1)) := (Finset.mul_sum ..).symm
    _ ≤ (x.n + 1) * (4 * (x.n + D.numEdges)) :=
      Nat.mul_le_mul_left _ (case3SelectedMembers_sum_size_le x D hG d hd)
    _ ≤ _ := by
      rw [← Nat.mul_assoc, Nat.mul_comm (x.n + 1) 4]
      exact Nat.mul_le_mul_left _ (by omega)

/-- A buffer with this capacity can hold every selected member record:
there are six words per directed copy, one per vertex, and four headers
and tree words in the uniform bound. -/
theorem case3SelectedMembers_sum_recordCapacity_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) :
    (∑ i : Case3SelectedGroup x d.core.Z,
      ((case3SelectedMember x d.core.Z i).verts.card +
        6 * (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges + 4)) ≤
      24 * (x.n + D.numEdges) := by
  classical
  calc
    _ ≤ ∑ i : Case3SelectedGroup x d.core.Z,
        6 * ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
          (case3SelectedMember x d.core.Z i).verts.card + 1) :=
      Finset.sum_le_sum (fun i _ => by omega)
    _ = 6 * (∑ i : Case3SelectedGroup x d.core.Z,
        ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
          (case3SelectedMember x d.core.Z i).verts.card + 1)) := (Finset.mul_sum ..).symm
    _ ≤ 6 * (4 * (x.n + D.numEdges)) :=
      Nat.mul_le_mul_left 6 (case3SelectedMembers_sum_size_le x D hG d hd)
    _ = _ := by ring

end GraphMinor.Compute
