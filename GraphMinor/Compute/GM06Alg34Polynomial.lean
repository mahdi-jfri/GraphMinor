module

public import GraphMinor.Compute.GM06Alg34RoundBound
import Mathlib.Tactic.Ring

/-!
# A fixed polynomial bound for the complete program

The common round base is quadratic in the supplied size. Its
22nd power, multiplied by the quadratic initial work, has degree 46.
The initial scan and queue allocation have smaller degrees and fit
the same polynomial. The constants do not depend on the instance.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A fixed coefficient for the disc algorithm's degree-46 bound. -/
def gm06Alg34TimeConstant : ℕ := (3 * (100000 * 86 ^ 22 + 1) + 503) * 2 ^ 46

/-- The coefficient of the program's polynomial running time is positive. -/
theorem gm06Alg34TimeConstant_pos : 0 < gm06Alg34TimeConstant := by
  unfold gm06Alg34TimeConstant
  exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)

/-- The sum of scan, queue allocation and loop bounds is polynomial in
 the original supplied size, with fixed coefficient and degree. -/
theorem gm06Alg34_time_polynomial (Q : ℕ) :
    452 * (Q + 2) ^ 4 + (Q + 2) ^ 16 + 50 +
      (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2) ≤
        gm06Alg34TimeConstant * (Q + 1) ^ 46 := by
  have hB : 1 ≤ Q + 2 := by omega
  have hsq : 1 ≤ (Q + 2) ^ 2 := Nat.one_le_pow _ _ hB
  have hbase : gm06RoundBase Q ≤ 86 * (Q + 2) ^ 2 := by
    unfold gm06RoundBase
    rw [gm06TaskRecordBound_value]
    omega
  have hp := Nat.pow_le_pow_left hbase 22
  simp only [Nat.mul_pow, ← Nat.pow_mul, Nat.reduceMul] at hp
  have h44 : 1 ≤ (Q + 2) ^ 44 := Nat.one_le_pow _ _ hB
  have hround : gm06RoundBound Q + 1 ≤ (100000 * 86 ^ 22 + 1) * (Q + 2) ^ 44 := by
    have hh := Nat.mul_le_mul_left 100000 hp
    unfold gm06RoundBound
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    omega
  have hwork := Nat.mul_le_mul_right (3 * (Q + 2) ^ 2) hround
  have heq : ((100000 * 86 ^ 22 + 1) * (Q + 2) ^ 44) * (3 * (Q + 2) ^ 2) =
      (3 * (100000 * 86 ^ 22 + 1)) * (Q + 2) ^ 46 := by ring
  rw [heq] at hwork
  have h4 := Nat.pow_le_pow_right hB (by decide : 4 ≤ 46)
  have h16 := Nat.pow_le_pow_right hB (by decide : 16 ≤ 46)
  have h46 : 1 ≤ (Q + 2) ^ 46 := Nat.one_le_pow _ _ hB
  have hscan := Nat.mul_le_mul_left 452 h4
  have h50 := Nat.mul_le_mul_left 50 h46
  have hsum : 452 * (Q + 2) ^ 4 + (Q + 2) ^ 16 + 50 +
      (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2) ≤
      (3 * (100000 * 86 ^ 22 + 1) + 503) * (Q + 2) ^ 46 := by
    omega
  have hlast := Nat.mul_le_mul_left (3 * (100000 * 86 ^ 22 + 1) + 503)
    (Nat.pow_le_pow_left (show Q + 2 ≤ 2 * (Q + 1) by omega) 46)
  rw [Nat.mul_pow, ← Nat.mul_assoc] at hlast
  exact hsum.trans hlast

end GraphMinor.Compute
