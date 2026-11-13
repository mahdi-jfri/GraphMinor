module

public import GraphMinor.Compute.Logic
public import GraphMinor.Compute.Case3StepsScanCostBounds
import GraphMinor.Compute.Case3StepsMultigraphComponents
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-!
# The weighted cost of the stopping scan

The decreasing measure reads candidate labels in reverse order. Reflecting
the finite sum gives the usual increasing candidate scan. The unselected
labels have zero member charge, while every iteration and condition test
has a fixed overhead.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Extend the candidate charge by zero outside the numeric label range. -/
noncomputable def case3CandidateCostNat (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) (k : ℕ) : ℕ :=
  if hk : k < x.n + (case3InputEdges x).length then case3CandidateCost x Z f ⟨k, hk⟩ else 0

/-- The numeric extension has the exact selected member charge. -/
theorem case3CandidateCostNat_selected (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) (i : Case3SelectedGroup x Z) :
    case3CandidateCostNat x Z f (case3RawIndexLabel x i.1) = f i := by
  rw [case3CandidateCostNat, dite_eq_left (case3RawIndexLabel_lt x i.1)]
  have heq : (⟨case3RawIndexLabel x i.1, case3RawIndexLabel_lt x i.1⟩ :
      Fin (x.n + (case3InputEdges x).length)) = case3GroupLabelEquiv x i.1 :=
    Fin.ext (case3GroupLabelEquiv_val x i.1).symm
  rw [heq, case3CandidateCost_selected]

/-- An unset mask label has zero nonconstant iteration charge. -/
theorem case3CandidateCostNat_unselected (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) (j : Fin (x.n + (case3InputEdges x).length))
    (hj : j ∉ case3GroupLabelSet x Z) : case3CandidateCostNat x Z f j.1 = 0 := by
  classical
  have hn : ¬ case3GroupActive x Z ((case3GroupLabelEquiv x).symm j) := by
    intro ha
    have hm := (mem_case3GroupLabelSet x Z ((case3GroupLabelEquiv x).symm j)).mpr ha
    rw [Equiv.apply_symm_apply] at hm
    exact hj hm
  simp only [case3CandidateCostNat, j.2, ↓reduceDIte, case3CandidateCost, hn]

/-- Summing the numeric extension counts each selected member exactly once. -/
theorem case3CandidateCostNat_sum (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) :
    (∑ k ∈ Finset.range (x.n + (case3InputEdges x).length), case3CandidateCostNat x Z f k) =
      ∑ i : Case3SelectedGroup x Z, f i := by
  rw [Finset.sum_range]
  calc
    _ = ∑ j : Fin (x.n + (case3InputEdges x).length), case3CandidateCost x Z f j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [case3CandidateCostNat, j.2, ↓reduceDIte]
    _ = _ := case3CandidateCost_sum x Z f

/-- Reversing the decreasing measure gives the increasing scan cost. -/
theorem case3WhileCost_reverse (C L : ℕ) (f : ℕ → ℕ) :
    whileCost 7 (fun r => 7 + C * f (L - r)) L =
      7 + 14 * L + C * (∑ k ∈ Finset.range L, f k) := by
  unfold whileCost
  have heq : (∑ k ∈ Finset.range L, (7 + (7 + C * f (L - (k + 1))))) =
      ∑ k ∈ Finset.range L, (14 + C * f (L - 1 - k)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show L - (k + 1) = L - 1 - k by omega]
    omega
  rw [heq, Finset.sum_range_reflect (fun k => 14 + C * f k) L, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
  omega

/-- The complete while-cost budget is bounded by the ambient product,
even when the scan stops at its first wall result. -/
theorem case3MemberScan_whileCost_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (N C : ℕ) (hn : x.n ≤ N) :
    whileCost 7 (fun r => 7 + C * case3CandidateCostNat x d.core.Z
      (case3MemberScanCharge x D d.core.Z N) (x.n + (case3InputEdges x).length - r))
      (x.n + (case3InputEdges x).length) ≤
        (13 * C + 21) * ((N + 1) * (D.numEdges + N + 1)) := by
  let V := (N + 1) * (D.numEdges + N + 1)
  have hsum := case3MemberScanCharge_sum_le x D hG d hd hdiv N hn
  have hsimple := (case3InputEdges_length_le x D hG).trans D.numActivePairs_le_numEdges
  have hbase : N + D.numEdges + 1 ≤ V := by
    have hmul := Nat.mul_le_mul_right (D.numEdges + N + 1) (show 1 ≤ N + 1 by omega)
    dsimp only [V]
    omega
  have hL : x.n + (case3InputEdges x).length ≤ V := by omega
  have hV : 1 ≤ V := by dsimp only [V]; exact Nat.mul_pos (by omega) (by omega)
  rw [case3WhileCost_reverse, case3CandidateCostNat_sum]
  change (∑ i : Case3SelectedGroup x d.core.Z, case3MemberScanCharge x D d.core.Z N i) ≤ 13 * V at hsum
  have hmul := Nat.mul_le_mul_left C hsum
  have hseven : 7 ≤ 7 * V := by omega
  calc
    _ ≤ 7 * V + 14 * V + C * (13 * V) := by omega
    _ = _ := by dsimp only [V]; ring

end GraphMinor.Compute
