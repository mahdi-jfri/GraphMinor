module

public import GraphMinor.Compute.GM02TopologicalDecisionExec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A fixed polynomial bound for one candidate test

The numeric split size is at most a fixed multiple of one plus the
original input size. Raise this inequality to the fixed recursive time
exponent. That exponent also covers the quadratic graph construction,
the linear pattern scan, and the fixed digit-decoding work.
-/

public section
namespace GraphMinor.Compute

/-- The coefficient for one complete raw-code test, including counting-loop overhead. -/
@[expose] noncomputable def gm02TopologicalCodeCoefficient (q K : ℕ) : ℕ :=
  (281 + (2 * K) * (12 + 4 * (2 * K))) + 276 + 200 * (2 * K + 1) ^ 2 +
    gm02RecursivePolynomialCoefficient q * (2 * K + 1) ^ gm02RecursivePolynomialExponent q

/-- A fixed polynomial in the original input size bounds a full candidate test and its loop overhead. -/
theorem gm02PortCodeBudget_polynomial (q K : ℕ) (x : GM02TopologicalInput) :
    gm02PortCodeBudget q x K + 15 ≤ gm02TopologicalCodeCoefficient q K *
      (gm02TopologicalSize x + 1) ^ gm02RecursivePolynomialExponent q := by
  let s := gm02TopologicalSize x
  let N := gm02FullPortSize x K
  let A := 2 * K + 1
  let D := gm02RecursivePolynomialExponent q
  let C := gm02RecursivePolynomialCoefficient q
  let P := (s + 1) ^ D
  let fixed := 281 + (2 * K) * (12 + 4 * (2 * K))
  have hD : 2 ≤ D := by dsimp only [D, gm02RecursivePolynomialExponent]; omega
  have hNadd : N ≤ s + 2 * K := by
    unfold N gm02FullPortSize s gm02TopologicalSize GM02EdgeListInput.size
    omega
  have hm : x.edges.length ≤ s := by unfold s gm02TopologicalSize; omega
  have hNplus : N + 1 ≤ A * (s + 1) := by
    dsimp only [A]
    nlinarith [Nat.zero_le (K * s)]
  have hNlinear : N ≤ A * (s + 1) := (Nat.le_succ N).trans hNplus
  have hsq0 := Nat.mul_le_mul hNlinear hNlinear
  have hsq : N * N ≤ A ^ 2 * (s + 1) ^ 2 := by
    convert hsq0 using 1 <;> ring
  have hPone : 1 ≤ P := Nat.one_le_pow D _ (by omega)
  have hsP : s + 1 ≤ P := Nat.le_self_pow (by omega) _
  have hsquare : (s + 1) ^ 2 ≤ P := Nat.pow_le_pow_right (by omega) hD
  have hNP : N * N ≤ A ^ 2 * P := hsq.trans (Nat.mul_le_mul_left _ hsquare)
  have hpower : (N + 1) ^ D ≤ A ^ D * P := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hNplus D
  have hfixed : fixed ≤ fixed * P := Nat.le_mul_of_pos_right _ hPone
  have hpattern : 276 * x.edges.length ≤ 276 * P := Nat.mul_le_mul_left _ (hm.trans ((Nat.le_succ s).trans hsP))
  have hgraph : 200 * (N * N) ≤ 200 * (A ^ 2 * P) := Nat.mul_le_mul_left _ hNP
  have hrecursive : C * (N + 1) ^ D ≤ C * (A ^ D * P) := Nat.mul_le_mul_left _ hpower
  have hbudget : gm02PortCodeBudget q x K + 15 =
      fixed + 276 * x.edges.length + 200 * (N * N) + C * (N + 1) ^ D := by
    dsimp only [gm02PortCodeBudget, gm02PortCandidateBudget, fixed, N, C, D]
    omega
  rw [hbudget]
  calc
    fixed + 276 * x.edges.length + 200 * (N * N) + C * (N + 1) ^ D ≤
        fixed * P + 276 * P + 200 * (A ^ 2 * P) + C * (A ^ D * P) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfixed hpattern) hgraph) hrecursive
    _ = gm02TopologicalCodeCoefficient q K * (s + 1) ^ D := by
      dsimp only [gm02TopologicalCodeCoefficient, fixed, P, A, C, D]
      ring

end GraphMinor.Compute
