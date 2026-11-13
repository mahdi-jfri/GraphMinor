module
public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Sqrt
import GraphMinor.Thomason.GeneralGraphCriterion
import GraphMinor.Thomason.LargeParameters
import GraphMinor.Thomason.IntegerParameters
import Mathlib.Tactic.Linarith

/-!
# Thomason's bound above an explicit threshold

The proved large-parameter choice has density at most `2.6795` times
the target order times the integer square root of its binary logarithm.
This is smaller than the `2.68` coefficient in XIII (5.5). The integer
parameter criterion therefore proves the exact graph-model conclusion
above an explicit threshold, following Thomason (1984), pp. 262–264.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM13 GraphMinor.GM16
universe u v

/-- Thomason's density implication with its exact `2.68` coefficient,
for the explicit large-parameter range shown. -/
theorem hasGraphModel_of_density_of_large {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ)
    (hp : 1048576 ≤ Nat.sqrt (Nat.log 2 p))
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    HasGraphModel (completeGraph p) G := by
  obtain ⟨s, k, hspos, hk, hEk, hbits, hbudget, hupper⟩ := exists_large_density_parameters p hp
  obtain ⟨hroom, hpower⟩ := integer_parameter_bounds s k 20 p hspos hk hEk hbits hbudget
  have hfour : 4 ≤ 1000 * s := (by decide : 4 ≤ 1000 * 1).trans
    (Nat.mul_le_mul_left 1000 hspos)
  have hscale : 2679 * (1000 * s - 4 + 4) ≤ 1000 * (2679 * s) := by
    rw [Nat.sub_add_cancel hfour, Nat.mul_left_comm]
  have hlog := Real.natLog_le_logb p 2
  have hm : ((Nat.sqrt (Nat.log 2 p) : ℕ) : ℝ) ≤ Real.sqrt (Real.logb 2 p) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hlog)).mpr
    exact (show ((Nat.sqrt (Nat.log 2 p) : ℕ) : ℝ) ^ 2 ≤ (Nat.log 2 p : ℝ) by
      exact_mod_cast Nat.sqrt_le' (Nat.log 2 p)).trans hlog
  have hupperR : (10000 : ℝ) * (2679 * s : ℕ) ≤
      26795 * (p : ℝ) * (Nat.sqrt (Nat.log 2 p) : ℝ) := by exact_mod_cast hupper
  have hpm := mul_le_mul_of_nonneg_left hm
    (show (0 : ℝ) ≤ 26795 * (p : ℝ) from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hpnonneg : (0 : ℝ) ≤ (p : ℝ) * Real.sqrt (Real.logb 2 p) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hc : ((2679 * s : ℕ) : ℝ) ≤ (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) := by
    nlinarith only [hupperR, hpm, hpnonneg]
  have hden : (2679 * s) * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (V(G).ncard))).trans hd
    exact_mod_cast hh
  exact hasGraphModel_of_integral_density G hV hE hne hs (2679 * s) (1000 * s - 4) k p
    hscale hden (lt_of_lt_of_le (by decide : 0 < 5) hk) hroom hpower

end GraphMinor.Thomason
