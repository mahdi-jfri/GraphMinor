module

public import GraphMinor.Compute.GM02TopologicalCodeTime
import Mathlib.Tactic.Ring

/-!
# Polynomial time for the complete topological containment program

There are at most a fixed power of one plus the input size many candidate
codes. Multiply this bound by the candidate-test bound and include the
quadratic preprocessing cost.
-/

public section
namespace GraphMinor.Compute

/-- The time exponent includes the fixed number of candidate-code digits. -/
@[expose] noncomputable def gm02TopologicalPolynomialExponent (q K : ℕ) : ℕ :=
  gm02RecursivePolynomialExponent q + 2 * K

/-- The coefficient includes preprocessing, initialization, and all candidate tests. -/
@[expose] noncomputable def gm02TopologicalPolynomialCoefficient (q K : ℕ) : ℕ :=
  133 + 8 * K + gm02TopologicalCodeCoefficient q K

/-- The complete execution budget is polynomial in the original plain input size. -/
theorem gm02TopologicalBudget_polynomial (q K : ℕ) (x : GM02TopologicalInput) :
    gm02TopologicalBudget q x K ≤ gm02TopologicalPolynomialCoefficient q K *
      (gm02TopologicalSize x + 1) ^ gm02TopologicalPolynomialExponent q K := by
  let b := gm02TopologicalSize x + 1
  let D := gm02RecursivePolynomialExponent q
  let E := gm02TopologicalPolynomialExponent q K
  let C := gm02TopologicalCodeCoefficient q K
  have hb : 1 ≤ b := by dsimp only [b]; omega
  have hm : x.G.edges.length + 1 ≤ b := by
    dsimp only [b, gm02TopologicalSize, GM02EdgeListInput.size]
    omega
  have hE : 2 ≤ E := by
    dsimp only [E, gm02TopologicalPolynomialExponent, gm02RecursivePolynomialExponent]
    omega
  have hp : b ^ 2 ≤ b ^ E := Nat.pow_le_pow_right hb hE
  have hone : 1 ≤ b ^ E := Nat.one_le_pow E _ hb
  have hcodes := Nat.pow_le_pow_left hm (2 * K)
  have htest := gm02PortCodeBudget_polynomial q K x
  have hall : (x.G.edges.length + 1) ^ (2 * K) * (gm02PortCodeBudget q x K + 15) ≤
      C * b ^ E := by
    calc
      _ ≤ b ^ (2 * K) * (C * b ^ D) := Nat.mul_le_mul hcodes htest
      _ = C * b ^ E := by
        dsimp only [E, gm02TopologicalPolynomialExponent, D]
        rw [pow_add]
        ring
  have hpre := Nat.mul_le_mul_left 120 hp
  have hinit : 13 + 8 * K ≤ (13 + 8 * K) * b ^ E :=
    Nat.le_mul_of_pos_right _ hone
  unfold gm02TopologicalBudget
  calc
    _ ≤ 120 * b ^ E + (13 + 8 * K) * b ^ E + C * b ^ E := by
      change 120 * b ^ 2 + 13 + 8 * K + _ ≤ _
      have h := Nat.add_le_add (Nat.add_le_add hpre hinit) hall
      simpa only [Nat.add_assoc] using h
    _ = gm02TopologicalPolynomialCoefficient q K * b ^ E := by
      dsimp only [gm02TopologicalPolynomialCoefficient, C]
      ring

end GraphMinor.Compute
