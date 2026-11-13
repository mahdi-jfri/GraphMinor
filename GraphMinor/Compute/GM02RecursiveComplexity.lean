module

public import GraphMinor.Compute.GM02RecursiveMachineExec
public import GraphMinor.Compute.GM02TerminatedEncoding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial running time of the complete A2 program

Use the paper's alternating recurrence bound for the loop. Initialization
copies a quadratic input and allocates a cubic stack, so it fits the
same polynomial after increasing its coefficient. This proves the
Word RAM specification for the actual plain-input simple-graph A2
program, with no supplied recursive data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A common constant for the two alternating time recurrences. -/
noncomputable def gm02RecursivePolynomialConstant (q : ℕ) : ℕ :=
  2 * gm02RecursiveTimeCoefficient q + 2 * gm02RecursiveCodeBound q + 1

/-- The fixed polynomial exponent obtained by the paper's recurrence calculation. -/
noncomputable def gm02RecursivePolynomialExponent (q : ℕ) : ℕ :=
  8 * (gm02RecursivePolynomialConstant q * gm02RecursivePolynomialConstant q) + (q + 3)

/-- The coefficient also covers root input copying, stack allocation, and final return. -/
noncomputable def gm02RecursivePolynomialCoefficient (q : ℕ) : ℕ :=
  gm02RecursivePolynomialConstant q +
    2 * (gm02RecursivePolynomialConstant q + gm02RecursivePolynomialConstant q * gm02RecursivePolynomialConstant q) +
    1 + 180

/-- The complete root execution budget is bounded by a fixed polynomial in its vertex count. -/
theorem gm02RecursiveMachineTime_polynomial (q : ℕ) (hq : 1 ≤ q) (x : GM02SimpleTerminatedInput) :
    16 * x.enc.length + gm02SavedFrameCapacity x.n +
      gm02RecursiveTime q (2 * gm02RecursiveTimeCoefficient q) (q + 3) (2 * x.n + 1) + 52 ≤
        gm02RecursivePolynomialCoefficient q * (x.n + 1) ^ gm02RecursivePolynomialExponent q := by
  let c := gm02RecursivePolynomialConstant q
  let D := gm02RecursivePolynomialExponent q
  let P := (x.n + 1) ^ D
  let A := c + 2 * (c + c * c) + 1
  have hD : 3 ≤ D := by dsimp only [D, gm02RecursivePolynomialExponent]; omega
  have h1 : 1 ≤ P := Nat.one_le_pow D _ (by omega)
  have h2 : (x.n + 1) ^ 2 ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (x.n + 1) ^ 3 ≤ P := Nat.pow_le_pow_right (by omega) hD
  have hEnc : x.enc.length ≤ 6 * (x.n + 1) ^ 2 := by
    have h := x.enc_length_le le_rfl
    nlinarith
  have hEnc' : 16 * x.enc.length ≤ 96 * P := by
    have h := Nat.mul_le_mul_left 16 (hEnc.trans (Nat.mul_le_mul_left 6 h2))
    simpa only [← Nat.mul_assoc] using h
  have hCap : gm02SavedFrameCapacity x.n ≤ 32 * (x.n + 1) ^ 3 := by
    unfold gm02SavedFrameCapacity gm02SavedFrameSizeBound
    nlinarith [Nat.zero_le (x.n * x.n * x.n)]
  have hCap' : gm02SavedFrameCapacity x.n ≤ 32 * P := hCap.trans (Nat.mul_le_mul_left 32 h3)
  have hFinal : 52 ≤ 52 * P := Nat.le_mul_of_pos_right _ h1
  have hLoop : gm02RecursiveTime q (2 * gm02RecursiveTimeCoefficient q) (q + 3) (2 * x.n + 1) ≤ A * P :=
    gm02RecursiveTime_polynomial q (2 * gm02RecursiveTimeCoefficient q) (q + 3) hq x.n
  calc
    16 * x.enc.length + gm02SavedFrameCapacity x.n +
        gm02RecursiveTime q (2 * gm02RecursiveTimeCoefficient q) (q + 3) (2 * x.n + 1) + 52 ≤
      96 * P + 32 * P + A * P + 52 * P :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hEnc' hCap') hLoop) hFinal
    _ = gm02RecursivePolynomialCoefficient q * (x.n + 1) ^ gm02RecursivePolynomialExponent q := by
      dsimp only [gm02RecursivePolynomialCoefficient, A, c, P, D]
      ring

/-- The actual A2 program on plain simple terminated graphs is polynomial, as in II, pages 316–318. -/
theorem gm02RecursiveMachine_computes (q : ℕ) (hq : 1 ≤ q) :
    ComputesRelInTime gm02SimpleTerminatedSize
      (fun x s => s.arrs inArr = x.enc ∧ x.A.index ≤ 3 * q)
      (fun x s => x.recursiveCorrect q s) (gm02RecursiveMachineProg q)
      (fun n => (n + 1) ^ gm02RecursivePolynomialExponent q) := by
  refine ⟨gm02RecursivePolynomialCoefficient q, gm02RecursiveWordConstant q,
    by unfold gm02RecursivePolynomialCoefficient; omega,
    by have h := (gm02RecursiveWordConstant_bounds q).2.1; omega, ?_⟩
  intro x s hin
  obtain ⟨s', t, he, ht, hout⟩ := gm02RecursiveMachineProg_exec q x s hin.1 hin.2 le_rfl
  exact ⟨s', t, he, ht.trans (gm02RecursiveMachineTime_polynomial q hq x), hout⟩

end GraphMinor.Compute
