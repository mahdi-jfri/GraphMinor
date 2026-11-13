module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The logarithmic threshold in Thomason's reduction

Thomason's Lemma 1, page 262 (1984), uses the threshold
`r x (log (x / r) + 1) / 2`. Its change after deleting a vertex has a
positive gap above its average contribution. We prove the exact
identity, a lower bound on this gap, and the complete-graph cutoff.
-/

@[expose] public section

namespace GraphMinor.Thomason

/-- The real edge threshold in Thomason's Lemma 1, page 262. -/
noncomputable def logarithmicPotential (r x : ℝ) : ℝ :=
  r * x * (Real.log (x / r) + 1) / 2

/-- The integer edge threshold for a graph on `n` vertices. -/
noncomputable def logarithmicThreshold (r : ℝ) (n : ℕ) : ℕ :=
  ⌈logarithmicPotential r n⌉₊

/-- Above order `r`, the potential is nonnegative. -/
theorem logarithmicPotential_nonneg {r x : ℝ} (hr : 0 < r) (hx : r ≤ x) :
    0 ≤ logarithmicPotential r x := by
  have hxpos : 0 < x := lt_of_lt_of_le hr hx
  have hlog : 0 ≤ Real.log (x / r) := Real.log_nonneg ((one_le_div hr).mpr hx)
  dsimp only [logarithmicPotential]
  positivity

/-- Above order `r`, the logarithmic potential increases with the order. -/
theorem logarithmicPotential_mono {r x y : ℝ} (hr : 0 < r)
    (hrx : r ≤ x) (hxy : x ≤ y) : logarithmicPotential r x ≤ logarithmicPotential r y := by
  have hxpos : 0 < x := lt_of_lt_of_le hr hrx
  have hlogx : 0 ≤ Real.log (x / r) := Real.log_nonneg ((one_le_div hr).mpr hrx)
  have hlogs : Real.log (x / r) ≤ Real.log (y / r) :=
    Real.log_le_log (div_pos hxpos hr) (div_le_div_of_nonneg_right hxy hr.le)
  dsimp only [logarithmicPotential]
  exact div_le_div_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hxy hr.le) (add_le_add hlogs le_rfl)
      (by linarith) (mul_nonneg hr.le (le_trans hxpos.le hxy))) (by norm_num)

/-- Up to order `2 a r`, the potential is at most `a r x / 2` when
`a ≥ 1 + log (2 a)`. This places the first dense minor in the potential class. -/
theorem logarithmicPotential_le_density {a r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (ha : 1 + Real.log (2 * a) ≤ a) (hxa : x ≤ 2 * a * r) :
    2 * logarithmicPotential r x ≤ a * r * x := by
  have hxdiv : x / r ≤ 2 * a := (div_le_iff₀ hr).mpr hxa
  have hlog := Real.log_le_log (div_pos hx hr) hxdiv
  have hb : Real.log (x / r) + 1 ≤ a := by linarith
  have hmul := mul_le_mul_of_nonneg_left hb (mul_nonneg hr.le hx.le)
  dsimp only [logarithmicPotential]
  nlinarith

/-- The cancellation identity in the proof of Thomason's Lemma 1, page 262. -/
theorem logarithmicPotential_difference_gap {r x : ℝ} (hr : 0 < r) (hx : 1 < x) :
    2 * (logarithmicPotential r x - logarithmicPotential r (x - 1)) -
      2 * logarithmicPotential r x / x = r * (x - 1) * Real.log (x / (x - 1)) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hp : 0 < x - 1 := sub_pos.mpr hx
  simp only [logarithmicPotential, Real.log_div hxpos.ne' hr.ne',
    Real.log_div hp.ne' hr.ne', Real.log_div hxpos.ne' hp.ne']
  field_simp
  ring

/-- The potential difference has a gap greater than `r - 1`. The standard
lower bound `log t ≥ 1 - 1/t` gives this estimate for `t = x/(x-1)`. -/
theorem logarithmicPotential_gap_gt {r x : ℝ} (hr : 0 < r)
    (hx : 1 < x) (hrx : r < x) :
    r - 1 < 2 * (logarithmicPotential r x - logarithmicPotential r (x - 1)) -
      2 * logarithmicPotential r x / x := by
  rw [logarithmicPotential_difference_gap hr hx]
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hp : 0 < x - 1 := sub_pos.mpr hx
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hxpos hp)
  have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg hr.le hp.le)
  have hid : r * (x - 1) * (1 - (x / (x - 1))⁻¹) = r - r / x := by
    rw [inv_div]
    field_simp
    ring
  rw [hid] at hmul
  have hfrac : r / x < 1 := (div_lt_one hxpos).mpr hrx
  exact lt_of_lt_of_le (by linarith) hmul

/-- At `m = ceil r`, the potential exceeds the complete-graph edge count.
This rules out order `m` in the minimal-potential construction. -/
theorem completeGraph_lt_logarithmicThreshold {r : ℝ} (hr : 1 < r) :
    (⌈r⌉₊).choose 2 < logarithmicThreshold r ⌈r⌉₊ := by
  let m : ℕ := ⌈r⌉₊
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hmr : r ≤ (m : ℝ) := Nat.le_ceil r
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hrpos hmr
  have hmlt : (m : ℝ) < r + 1 := Nat.ceil_lt_add_one hrpos.le
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hmpos hrpos)
  rw [inv_div] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg hrpos.le hmpos.le)
  have hid : r * (m : ℝ) * (1 - r / m) = r * m - r ^ 2 := by
    field_simp
  rw [hid] at hmul
  have hsquare : ((m : ℝ) - r) ^ 2 < 1 := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hmr) (le_of_lt (by linarith : 0 < 1 - ((m : ℝ) - r)))
    nlinarith
  have hbound : (m : ℝ) * ((m : ℝ) - 1) / 2 < logarithmicPotential r m := by
    dsimp only [logarithmicPotential]
    nlinarith
  have hceil := Nat.le_ceil (logarithmicPotential r m)
  have hreal : ((m.choose 2 : ℕ) : ℝ) < (logarithmicThreshold r m : ℝ) := by
    rw [Nat.cast_choose_two]
    exact lt_of_lt_of_le hbound hceil
  exact_mod_cast hreal

end GraphMinor.Thomason
