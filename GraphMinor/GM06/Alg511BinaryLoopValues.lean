module

public import GraphMinor.Compute.GM06Alg511BinaryOrientation
public import GraphMinor.GM06.Alg511Progress
import GraphMinor.Compute.GM06Alg511BinaryIntegral
import Mathlib.Tactic

/-!
# Interpreting the scaled binary comparison values

The denominator magnitude is positive for a valid target. Moving
its sign to the numerator gives the same rational target. Multiplying
both current and target values by the positive factor k times that
magnitude preserves comparison. Each winding increment 1/k then
adds exactly the denominator magnitude to the stored integer.

The integral grid conditions imply that an ordered target differs
from the current winding by a natural number of such increments.
These equations connect the binary preprocessing and comparison to
the loop invariant of VI (5.11), page 134.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- The supplied denominator sign is its exact integer sign, with
the magnitude still interpreted from its supplied binary digits. -/
theorem alg511_binary_denominator_real (b : GM06Alg511BinaryInteger) :
    (b.value : ℝ) = if b.negative then -(b.value.natAbs : ℝ) else (b.value.natAbs : ℝ) := by
  rw [b.natAbs_value]
  cases b with
  | mk negative digits => cases negative <;> simp [GM06Alg511BinaryInteger.value]

/-- Moving a supplied denominator sign to the numerator leaves
the rational target unchanged, including either sign of zero. -/
theorem alg511_binary_normalized_target (a b : GM06Alg511BinaryInteger) :
    (((if b.negative then -a.value else a.value) : ℤ) : ℝ) / b.value.natAbs =
      (a.value : ℝ) / b.value := by
  conv_rhs => rw [alg511_binary_denominator_real b]
  cases b.negative <;> simp [div_neg, neg_div]

/-- The comparison target computed by binary normalization,
divided by k times the positive denominator, is the actual target. -/
theorem alg511_binary_scaled_target (k : ℕ) (a b : GM06Alg511BinaryInteger) (hk : 0 < k) :
    (((if b.negative.toNat = 1 then -((k : ℤ) * a.value) else (k : ℤ) * a.value) : ℤ) : ℝ) /
        ((k : ℝ) * b.value.natAbs) = (a.value : ℝ) / b.value := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hnum : (((if b.negative.toNat = 1 then -((k : ℤ) * a.value) else (k : ℤ) * a.value) : ℤ) : ℝ) =
      (k : ℝ) * (((if b.negative then -a.value else a.value) : ℤ) : ℝ) := by
    cases b.negative <;> simp
  rw [hnum]
  calc
    _ = (((if b.negative then -a.value else a.value) : ℤ) : ℝ) / b.value.natAbs := by
      exact mul_div_mul_left _ _ hk0
    _ = _ := alg511_binary_normalized_target a b

/-- Scaling the current binary winding numerator by the positive
denominator gives exactly the same current winding. -/
theorem alg511_binary_scaled_current (k D : ℕ) (W : ℤ) (hD : 0 < D) :
    (((W * D : ℤ) : ℝ) / ((k : ℝ) * D)) = (W : ℝ) / k := by
  push_cast
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hD.ne')

/-- The fixed positive scaling preserves and reflects comparison
of the current winding and target. No interpreted integer needs to
fit in a word for this order equivalence. -/
theorem alg511_binary_scaled_le_iff {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (current target : ℤ) :
    ((current : ℝ) / ((k : ℝ) * D) ≤ (target : ℝ) / ((k : ℝ) * D)) ↔ current ≤ target := by
  rw [div_le_div_iff_of_pos_right (mul_pos (Nat.cast_pos.mpr hk) (Nat.cast_pos.mpr hD))]
  exact_mod_cast Iff.rfl

/-- Once orientation is chosen, the two integral grid values
supply a natural target-step index. The exact stored target integer
is then the current integer plus that many denominator increments. -/
theorem alg511_binary_target_steps {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (current target : ℤ)
    (hcurrent : ∃ m : ℤ, (k : ℝ) * ((current : ℝ) / ((k : ℝ) * D)) = m)
    (htarget : ∃ m : ℤ, (k : ℝ) * ((target : ℝ) / ((k : ℝ) * D)) = m)
    (hle : current ≤ target) :
    ∃ steps : ℕ,
      (target : ℝ) / ((k : ℝ) * D) = (current : ℝ) / ((k : ℝ) * D) + (steps : ℝ) / k ∧
      target = current + (steps : ℤ) * D := by
  obtain ⟨steps, hsteps⟩ := alg511_target_eq_after_steps hk hcurrent htarget
    ((alg511_binary_scaled_le_iff hk hD current target).mpr hle)
  refine ⟨steps, hsteps, ?_⟩
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hD0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hreal : (target : ℝ) = (current : ℝ) + (steps : ℝ) * D := by
    have hm := congrArg (fun r : ℝ => r * ((k : ℝ) * D)) hsteps
    field_simp at hm
    nlinarith only [hm]
  exact_mod_cast hreal

end GraphMinor.GM06
