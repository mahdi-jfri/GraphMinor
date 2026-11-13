module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import GraphMinor.Thomason.LargeParameterEstimates
import GraphMinor.Thomason.RoundedDensityParameters
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# An explicit large-parameter choice

Take the selected-set size to be the integer square root of the binary
logarithm plus twenty-one. Round the required branch budget to a fixed
denominator. The resulting integer density is at most `2.6795*p*m`,
where `m` is the integer square root of the binary logarithm of `p`.
-/

public section
namespace GraphMinor.Thomason

/-- Above an explicit threshold, the integer parameters meet the room,
reserve, and counting requirements while staying below `2.68*p*m`. -/
theorem exists_large_density_parameters (q : ℕ)
    (hm : 1048576 ≤ Nat.sqrt (Nat.log 2 q)) :
    ∃ s k : ℕ, 0 < s ∧ 5 ≤ k ∧ 20 ≤ k ∧
      q - 1 < 2 ^ (k * (k - 20)) ∧
      2679 * s + 2 ^ 20 *
        ((q - 1) * (k + 2 * Nat.log 2 k + 1) + k + 4) ≤ 2 ^ 20 * (1000 * s) ∧
      10000 * (2679 * s) ≤ 26795 * q * Nat.sqrt (Nat.log 2 q) := by
  let m := Nat.sqrt (Nat.log 2 q)
  let k := m + 21
  let l := k + 2 * Nat.log 2 k + 1
  let A := (q - 1) * l + k + 4
  let t := (A + 999996) / 999997
  have hm' : 1048576 ≤ m := hm
  have hmq : m ≤ q := (Nat.sqrt_le_self _).trans (Nat.log_le_self _ _)
  have hqpos : 1 ≤ q := by omega
  have hlog : 2 ≤ Nat.log 2 k := by
    have h := Nat.log_mono_right (b := 2) (by omega : 4 ≤ k)
    have h4 : Nat.log 2 4 = 2 := by decide
    simpa only [h4] using h
  have hA : A ≤ q * l := by
    have heq : q * l = (q - 1) * l + l := by
      calc
        q * l = (q - 1 + 1) * l := congrArg (· * l) (Nat.sub_add_cancel hqpos).symm
        _ = (q - 1) * l + l := by rw [Nat.add_mul, Nat.one_mul]
    rw [heq]
    dsimp only [A, l]
    omega
  have hAlarge : 0 < A := by dsimp only [A]; omega
  have hl : 10000 * l ≤ 10001 * m := large_selection_size_bound m hm'
  have hqm : 1000000000000 ≤ q * m := by nlinarith only [hm', hmq]
  obtain ⟨ht, _, _, hbudget⟩ := rounded_density_budget A hAlarge
  have hupper := rounded_density_upper_bound A l q m hA hl hqm
  refine ⟨1000 * t, k, by dsimp only [t]; omega, by dsimp only [k]; omega,
    by dsimp only [k]; omega, sqrt_log_target_lt_pow q, hbudget, hupper⟩

end GraphMinor.Thomason
