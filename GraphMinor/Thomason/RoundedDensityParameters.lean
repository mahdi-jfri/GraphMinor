module
public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Rounding the density parameter

Reserve three parts in a million of the degree surplus for the
exceptional-set count. A power-of-two reserve with exponent twenty
is smaller than this. Rounding up to a multiple of the fixed rational
density denominator then preserves the required integer budget.
-/

public section
namespace GraphMinor.Thomason

/-- Rounding a positive required order up to a multiple of `999997`
provides the reserve used in the integer parameter inequality. -/
theorem rounded_density_budget (A : ℕ) (hA : 0 < A) :
    let t := (A + 999996) / 999997
    0 < t ∧ A ≤ 999997 * t ∧ 999997 * t ≤ A + 999996 ∧
      2679 * (1000 * t) + 2 ^ 20 * A ≤ 2 ^ 20 * (1000 * (1000 * t)) := by
  dsimp only
  let t := (A + 999996) / 999997
  have hdiv := Nat.mod_add_div (A + 999996) 999997
  have hmod := Nat.mod_lt (A + 999996) (by decide : 0 < 999997)
  have hupper := Nat.div_mul_le_self (A + 999996) 999997
  have hceil : A ≤ 999997 * t := by dsimp only [t]; omega
  have ht : 0 < t := by omega
  refine ⟨ht, hceil, ?_, ?_⟩
  · omega
  · have h := Nat.mul_le_mul_left 1048576 hceil
    norm_num only [Nat.reducePow]
    omega

/-- The density after rounding is at most `2.6795*q*m`, if the branch
size costs at most `1.0001*m` and `q*m` is large enough. -/
theorem rounded_density_upper_bound (A l q m : ℕ)
    (hA : A ≤ q * l) (hl : 10000 * l ≤ 10001 * m)
    (hqm : 1000000000000 ≤ q * m) :
    10000 * (2679 * (1000 * ((A + 999996) / 999997))) ≤ 26795 * q * m := by
  have ht := Nat.div_mul_le_self (A + 999996) 999997
  have hq := Nat.mul_le_mul_left q hl
  nlinarith only [ht, hq, hA, hqm]

end GraphMinor.Thomason
