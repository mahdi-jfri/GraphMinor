module

public import GraphMinor.Compute.Case3StepsCandidateCosts
public import GraphMinor.Compute.Case3StepsMemberCallSizeBound

/-!
# Size bounds in numeric scan order

Transfer the page 106 estimates to the contiguous candidate labels used by
the program. Unselected labels have zero member charge. Each individual
member size is also bounded by the same total, which supplies its word-size
bound from the ambient input size.
-/

public section

namespace GraphMinor.Compute

/-- The numeric candidate charges for (7.2) satisfy the member-call sum bound. -/
theorem case3CandidateCost_algorithm72Size_sum_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z)) :
    (∑ j : Fin (x.n + (case3InputEdges x).length),
      case3CandidateCost x d.core.Z
        (fun i => algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) j) ≤
      8 * (x.n + 1) * (D.numEdges + x.n + 1) := by
  rw [case3CandidateCost_sum]
  exact case3SelectedMembers_sum_algorithm72Size_le x D hG d hd hdiv

/-- Every individual member-call input fits the same uniform total-size
bound used for the whole scan. -/
theorem case3MemberAlgorithm72Size_le_total (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (i : Case3SelectedGroup x d.core.Z) :
    algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i) ≤
      8 * (x.n + 1) * (D.numEdges + x.n + 1) := by
  classical
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le
    (algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z j))) (Finset.mem_univ i)).trans
      (case3SelectedMembers_sum_algorithm72Size_le x D hG d hd hdiv)

/-- Doubling the size argument costs at most doubling the word-size
constant. This transfers each member call to the ambient word size. -/
theorem case3WordSize_le_of_le_two_mul (c : ℕ) {m N : ℕ} (hm : m ≤ 2 * N) :
    wordSize c m ≤ wordSize (2 * c) N := by
  have hlog : Nat.log 2 (m + 2) ≤ Nat.log 2 (N + 2) + 1 := by
    calc
      _ ≤ Nat.log 2 ((N + 2) * 2) := Nat.log_mono_right (by omega)
      _ = _ := Nat.log_mul_base (by decide) (by omega)
  unfold wordSize
  calc
    _ ≤ c * (2 * (Nat.log 2 (N + 2) + 1)) := Nat.mul_le_mul_left c (by omega)
    _ = _ := by ring

end GraphMinor.Compute
