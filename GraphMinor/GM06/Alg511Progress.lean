module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Arithmetic progress in the loop of VI (5.11)

The first test restricts the target to multiples of one over the path
count. Every linkage winding has the same property. Hence a successful
successor call cannot pass the target. The remaining difference falls
by exactly one over the path count, as stated on page 134. Expressing
the difference by a nonnegative integer gives the number of successful
steps needed to reach the target.
-/

public section
namespace GraphMinor.GM06

/-- Successive grid values cannot pass a larger target on the same
grid. This is the arithmetic invariant of the loop in VI (5.11). -/
theorem alg511_step_le_target {k : ℕ} (hk : 0 < k) {current target : ℝ}
    (hcurrent : ∃ m : ℤ, (k : ℝ) * current = m)
    (htarget : ∃ n : ℤ, (k : ℝ) * target = n) (hlt : current < target) :
    current + 1 / (k : ℝ) ≤ target := by
  obtain ⟨m, hm⟩ := hcurrent
  obtain ⟨n, hn⟩ := htarget
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmn : m < n := by
    have hh := mul_lt_mul_of_pos_left hlt hk'
    rw [hm, hn] at hh
    exact_mod_cast hh
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hmn)
  have hmul : (k : ℝ) * (current + 1 / (k : ℝ)) ≤ (k : ℝ) * target := by
    rw [mul_add, hm, mul_one_div_cancel (ne_of_gt hk'), hn]
    exact hmn'
  exact (mul_le_mul_iff_right₀ hk').mp hmul

/-- Each successful call decreases the target difference by exactly
one over the path count, and that difference stays nonnegative. -/
theorem alg511_distance_after_step {k : ℕ} (hk : 0 < k) {current target : ℝ}
    (hcurrent : ∃ m : ℤ, (k : ℝ) * current = m)
    (htarget : ∃ n : ℤ, (k : ℝ) * target = n) (hlt : current < target) :
    |target - (current + 1 / (k : ℝ))| = |target - current| - 1 / (k : ℝ) := by
  have hstep := alg511_step_le_target hk hcurrent htarget hlt
  rw [abs_of_nonneg (sub_nonneg.mpr hstep), abs_of_nonneg (sub_nonneg.mpr (le_of_lt hlt))]
  ring

/-- After orientation has been chosen, the difference of two grid
values is a natural number of successor steps. -/
theorem alg511_target_eq_after_steps {k : ℕ} (hk : 0 < k) {current target : ℝ}
    (hcurrent : ∃ m : ℤ, (k : ℝ) * current = m)
    (htarget : ∃ n : ℤ, (k : ℝ) * target = n) (hle : current ≤ target) :
    ∃ rounds : ℕ, target = current + (rounds : ℝ) / (k : ℝ) := by
  obtain ⟨m, hm⟩ := hcurrent
  obtain ⟨n, hn⟩ := htarget
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmn : m ≤ n := by
    have hh := mul_le_mul_of_nonneg_left hle (le_of_lt hk')
    rw [hm, hn] at hh
    exact_mod_cast hh
  refine ⟨(n - m).toNat, ?_⟩
  have hc : (((n - m).toNat : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hmn)
  rw [hc]
  apply (mul_left_cancel₀ (ne_of_gt hk'))
  rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hk'), hm]
  linarith

end GraphMinor.GM06
