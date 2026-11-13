module
public import GraphMinor.Thomason.CliqueCriterion
import GraphMinor.Thomason.DensityCriterion
import GraphMinor.Thomason.NumericConstant
import GraphMinor.Thomason.BinomialCriterion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# An integer density criterion with a fixed rational constant

Use `a=2.679` in the logarithmic reduction and clear its denominator.
Together with the integer power estimate this leaves a criterion whose
numeric conditions contain no real logarithms, square roots, or rounding.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- A density-to-clique criterion using the proved constant `2.679`.
The power inequality bounds all exceptional subset families. -/
theorem clique_isIsoMinor_of_integral_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d b k q : ℕ)
    (hscale : 2679 * (b + 4) ≤ 1000 * d)
    (hden : d * Fintype.card V ≤ G.edgeFinset.card) (hk : 0 < k)
    (hroom : (q - 1) * (k + 2 * Nat.log 2 k + 1) + (Nat.log 2 k + 3) ≤ b)
    (hpower : (q - 1) * d ^ k <
      (2 ^ k * (b - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 1 - k)) ^ k) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  let a : ℝ := 2679 / 1000
  let r : ℝ := (1000 * d : ℝ) / 2679
  have hscaleR : (2679 : ℝ) * ((b : ℝ) + 4) ≤ 1000 * (d : ℝ) := by
    exact_mod_cast hscale
  have hr : 1 < r := by dsimp only [r]; nlinarith only [hscaleR, (show (0 : ℝ) ≤ (b : ℝ) from Nat.cast_nonneg b)]
  have hb : (b : ℝ) ≤ r - 4 := by dsimp only [r]; linarith only [hscaleR]
  have hd : (d : ℝ) = a * r := by dsimp only [a, r]; ring
  exact clique_isIsoMinor_of_density_counting G a r d b k q hr (by norm_num [a])
    logarithmic_reduction_constant hd hb hden hk hroom
    (mul_choose_div_pow_lt_choose _ _ _ _ hpower)

end GraphMinor.Thomason
