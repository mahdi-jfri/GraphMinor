module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A rational constant for the logarithmic reduction

The positive root used by Thomason (1984), pp. 262–263, satisfies
`a = 1 + log(2a)` and is less than `2.679`. A finite lower bound on the
exponential series verifies that `2.679` satisfies the inequality needed
by the logarithmic-potential reduction.
-/

public section
namespace GraphMinor.Thomason

/-- The rational number `2.679`, strictly below `2.68`, satisfies the
logarithmic inequality used in Thomason's density reduction. -/
theorem logarithmic_reduction_constant :
    1 + Real.log (2 * (2679 / 1000 : ℝ)) ≤ (2679 / 1000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (1679 / 1000 : ℝ)) (by norm_num) 8
  have hs : (2679 / 500 : ℝ) ≤
      ∑ i ∈ Finset.range 8, (1679 / 1000 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he : (2679 / 500 : ℝ) ≤ Real.exp (1679 / 1000) := hs.trans h
  have hl := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2679 / 500)).mpr he
  have heq : (2 : ℝ) * (2679 / 1000) = 2679 / 500 := by norm_num
  rw [heq]
  linarith

end GraphMinor.Thomason
