module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5Interval
import Mathlib.Tactic

/-!
# The number of successor calls in VI (5.11)

Each successful call increases the winding by one over the path count.
Apply (5.12) to the initial and current feasible windings. Multiplying
by the square of the path count bounds the number of successful calls
by the vertex count divided by the path count. One final unsuccessful
call gives the bound on pages 134–135. The rejection rule follows from
(5.8): after a failed successor call, no larger target is feasible.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface

/-- In VI (5.11), after `rounds` successful calls from a feasible starting
value, (5.12) bounds `rounds * k` by the number of vertices. -/
theorem alg511_successful_rounds_mul_le {k rounds : ℕ}
    {G : Drawing ClosedCylinder} {start : ℝ}
    (hG : IsCylinderSection5Drawing k G)
    (hstart : IsThetaFeasible k G start)
    (hcurrent : IsThetaFeasible k G (start + (rounds : ℝ) / (k : ℝ))) :
    rounds * k ≤ G.V.ncard := by
  have hk : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hG.1
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hk
  have hs := theorem_5_12_proof k G start (start + (rounds : ℝ) / (k : ℝ))
    hG hstart hcurrent
  have hd : |start - (start + (rounds : ℝ) / (k : ℝ))| =
      (rounds : ℝ) / (k : ℝ) := by
    rw [show start - (start + (rounds : ℝ) / (k : ℝ)) =
      -((rounds : ℝ) / (k : ℝ)) by ring, abs_neg,
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hk))]
  rw [hd] at hs
  have hc : (rounds : ℝ) / (k : ℝ) ≤ (G.V.ncard : ℝ) / (k : ℝ) ^ 2 := by
    simpa only [one_div_mul_eq_div] using hs
  have hbound : (rounds : ℝ) * (k : ℝ) ≤ (G.V.ncard : ℝ) := by
    calc
      (rounds : ℝ) * (k : ℝ) = ((rounds : ℝ) / (k : ℝ)) * (k : ℝ) ^ 2 := by
        field_simp
      _ ≤ ((G.V.ncard : ℝ) / (k : ℝ) ^ 2) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = (G.V.ncard : ℝ) := div_mul_cancel₀ _ (pow_ne_zero _ hk0)
  exact_mod_cast hbound

/-- One final failed call, after any number of successful calls, fits
the bound on the calls of (5.7) in VI (5.11), pages 134–135. -/
theorem alg511_calls_le {k rounds : ℕ} {G : Drawing ClosedCylinder} {start : ℝ}
    (hG : IsCylinderSection5Drawing k G)
    (hstart : IsThetaFeasible k G start)
    (hcurrent : IsThetaFeasible k G (start + (rounds : ℝ) / (k : ℝ))) :
    rounds + 1 ≤ 1 + G.V.ncard / k := by
  have hmul := alg511_successful_rounds_mul_le hG hstart hcurrent
  have hdiv : rounds ≤ G.V.ncard / k := (Nat.le_div_iff_mul_le hG.1).mpr hmul
  omega

/-- The rejection branch in VI (5.11): a failed successor call rules
out the target whenever the target is greater than the current winding. -/
theorem alg511_reject_of_no_successor {k : ℕ} {G : Drawing ClosedCylinder}
    {current target : ℝ} (hG : IsCylinderSection5Drawing k G)
    (hcurrent : IsThetaFeasible k G current) (hlt : current < target)
    (hnext : ¬ IsThetaFeasible k G (current + 1 / (k : ℝ))) :
    ¬ IsThetaFeasible k G target := by
  exact ((theorem_5_8_proof k G current hG hcurrent).2.mp hnext) target hlt

end GraphMinor.GM06
