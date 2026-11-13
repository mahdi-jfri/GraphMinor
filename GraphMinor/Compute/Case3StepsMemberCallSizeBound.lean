module

public import GraphMinor.Compute.Case3StepsSelectedSizeBound
public import GraphMinor.Compute.Case3StepsMemberInput72

/-!
# The total input size of the member calls

The RAM size for (7.2) is at most twice the paper's vertex-times-edge size.
The selected-member sum from XIII (9.9), p. 106 therefore bounds all the
calls together, including all directed parallel copies.
-/

public section

namespace GraphMinor.Compute

/-- The size charged by the RAM interface of (7.2) is at most twice the
member product used in the paper. -/
theorem case3MemberAlgorithm72Size_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (i : Case3SelectedGroup x Z) :
    algorithm72Size (case3MemberAlgorithm72Input x D Z i) ≤
      2 * (((case3SelectedMember x Z i).verts.card + 1) *
        ((case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges +
          (case3SelectedMember x Z i).verts.card + 1)) := by
  rw [case3MemberAlgorithm72Size_eq x D hG Z hdiv i]
  have harith (n e : ℕ) : (n + 1) ^ 2 + e + n + 1 ≤
      2 * ((n + 1) * (e + n + 1)) := by
    nlinarith [Nat.zero_le (n * e)]
  exact harith _ _

/-- Each call size is at most twice the ambient product, independently
of how many other members occur in the division. -/
theorem case3MemberAlgorithm72Size_le_ambient (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (i : Case3SelectedGroup x Z) :
    algorithm72Size (case3MemberAlgorithm72Input x D Z i) ≤
      2 * ((x.n + 1) * (D.numEdges + x.n + 1)) := by
  have hv : (case3SelectedMember x Z i).verts.card ≤ x.n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (case3SelectedMember x Z i).verts
  have he := MultiDigraph.numEdges_mono (case3RoutedMember_le x D Z (case3RawIndexLabel x i.1))
  exact (case3MemberAlgorithm72Size_le x D hG Z hdiv i).trans
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul
      (Nat.add_le_add_right hv 1) (Nat.add_le_add_right (Nat.add_le_add he hv) 1)))

/-- The total size of every (7.2) member call is bounded before the RAM
program constants are chosen. -/
theorem case3SelectedMembers_sum_algorithm72Size_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z)) :
    (∑ i : Case3SelectedGroup x d.core.Z,
      algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) ≤
      8 * (x.n + 1) * (D.numEdges + x.n + 1) := by
  classical
  calc
    _ ≤ ∑ i : Case3SelectedGroup x d.core.Z,
        2 * (((case3SelectedMember x d.core.Z i).verts.card + 1) *
          ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
            (case3SelectedMember x d.core.Z i).verts.card + 1)) :=
      Finset.sum_le_sum (fun i _ => case3MemberAlgorithm72Size_le x D hG d.core.Z hdiv i)
    _ = 2 * (∑ i : Case3SelectedGroup x d.core.Z,
        ((case3SelectedMember x d.core.Z i).verts.card + 1) *
          ((case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
            (case3SelectedMember x d.core.Z i).verts.card + 1)) := (Finset.mul_sum ..).symm
    _ ≤ 2 * (4 * (x.n + 1) * (D.numEdges + x.n + 1)) :=
      Nat.mul_le_mul_left 2 (case3SelectedMembers_sum_vertex_mul_size_le x D hG d hd)
    _ = _ := by ring

end GraphMinor.Compute
