module

public import GraphMinor.Compute.GM02InjectionCodeTime
public import GraphMinor.Compute.GM02InjectionDecisionExec
import Mathlib.Tactic.Ring

/-!
# Polynomial time for the complete injection search

The fixed pattern has a fixed number of vertices, so its candidate
range is bounded by a fixed power of one plus the host size. Multiply
that bound by the proved candidate-time polynomial and include the
fixed initialization and final answer copy.
-/

public section
namespace GraphMinor.Compute

/-- The exponent includes the fixed number of pattern vertex slots. -/
@[expose] noncomputable def gm02InjectionPolynomialExponent (q : ℕ) (H : GM02EdgeListInput) : ℕ :=
  gm02TopologicalPolynomialExponent q H.edges.length + H.n

/-- The coefficient covers initialization and every coded candidate. -/
@[expose] noncomputable def gm02InjectionPolynomialCoefficient (q : ℕ) (H : GM02EdgeListInput) : ℕ :=
  14 + 4 * H.n + gm02InjectionCodeCoefficient q H

/-- The full injection-search budget is polynomial in the original host's vertex-plus-edge size. -/
theorem gm02InjectionBudget_polynomial (q : ℕ) (G H : GM02EdgeListInput) :
    gm02InjectionBudget q G H ≤ gm02InjectionPolynomialCoefficient q H *
      (G.size + 1) ^ gm02InjectionPolynomialExponent q H := by
  let b := G.size + 1
  let D := gm02TopologicalPolynomialExponent q H.edges.length
  let E := gm02InjectionPolynomialExponent q H
  let C := gm02InjectionCodeCoefficient q H
  have hb : 1 ≤ b := by dsimp only [b]; omega
  have hm : G.n + 1 ≤ b := by dsimp only [b, GM02EdgeListInput.size]; omega
  have hcodes := Nat.pow_le_pow_left hm H.n
  have htest := gm02InjectionCodeBudget_polynomial q G H
  have hall : (G.n + 1) ^ H.n * (gm02InjectionCodeBudget q G H + 15) ≤ C * b ^ E := by
    calc
      _ ≤ b ^ H.n * (C * b ^ D) := Nat.mul_le_mul hcodes htest
      _ = C * b ^ E := by
        dsimp only [E, gm02InjectionPolynomialExponent, D]
        rw [pow_add]
        ring
  have hone : 1 ≤ b ^ E := Nat.one_le_pow E _ hb
  have hinit : 14 + 4 * H.n ≤ (14 + 4 * H.n) * b ^ E := Nat.le_mul_of_pos_right _ hone
  unfold gm02InjectionBudget
  calc
    _ ≤ (14 + 4 * H.n) * b ^ E + C * b ^ E := Nat.add_le_add hinit hall
    _ = gm02InjectionPolynomialCoefficient q H * b ^ E := by
      dsimp only [gm02InjectionPolynomialCoefficient, C]
      ring

end GraphMinor.Compute
