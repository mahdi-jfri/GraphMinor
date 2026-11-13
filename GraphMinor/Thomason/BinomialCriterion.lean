module
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A power bound for the exceptional-set count

The last step in Thomason's main theorem, p. 264 (1984), bounds a ratio
of binomial coefficients. Bounding each descending product above and
below by a power gives a sufficient integer inequality. The common
factorial cancels without division or rounding.
-/

public section
namespace GraphMinor.Thomason

/-- A power inequality sufficient for the strict binomial inequality
in Thomason's exceptional-set count. -/
theorem mul_choose_lt_choose_of_pow (j A B k : ℕ)
    (h : j * A ^ k < (B + 1 - k) ^ k) : j * A.choose k < B.choose k := by
  have hleft : k.factorial * (j * A.choose k) ≤ j * A ^ k := by
    calc
      k.factorial * (j * A.choose k) = j * (k.factorial * A.choose k) := by ring
      _ = j * A.descFactorial k := by rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ ≤ j * A ^ k := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  have hright : (B + 1 - k) ^ k ≤ k.factorial * B.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.pow_sub_le_descFactorial _ _
  exact (mul_lt_mul_iff_of_pos_left (Nat.factorial_pos k)).mp
    (hleft.trans_lt (h.trans_le hright))

/-- Clearing the power of two removes the rounded numerator from the
sufficient binomial inequality. -/
theorem mul_choose_div_pow_lt_choose (j N B k : ℕ)
    (h : j * N ^ k < (2 ^ k * (B + 1 - k)) ^ k) :
    j * (N / 2 ^ k).choose k < B.choose k := by
  apply mul_choose_lt_choose_of_pow
  have hscaled : (2 ^ k) ^ k * (j * (N / 2 ^ k) ^ k) ≤ j * N ^ k := by
    calc
      (2 ^ k) ^ k * (j * (N / 2 ^ k) ^ k) =
          j * (2 ^ k * (N / 2 ^ k)) ^ k := by rw [mul_pow]; ring
      _ ≤ j * N ^ k := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.mul_div_le N (2 ^ k)) k)
  have hh := hscaled.trans_lt h
  rw [mul_pow] at hh
  exact (mul_lt_mul_iff_of_pos_left (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) k) k)).mp hh

/-- A gap of `s` bits per selected vertex gives the strict power
comparison needed in the exceptional-set count. -/
theorem mul_pow_lt_scaled_pow_of_bits (j N L k s : ℕ)
    (hs : s ≤ k) (hL : 0 < L)
    (hN : N ≤ 2 ^ (k - s) * L) (hj : j < 2 ^ (s * k)) :
    j * N ^ k < (2 ^ k * L) ^ k := by
  calc
    j * N ^ k ≤ j * (2 ^ (k - s) * L) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN k)
    _ < 2 ^ (s * k) * (2 ^ (k - s) * L) ^ k :=
      Nat.mul_lt_mul_of_pos_right hj (pow_pos (Nat.mul_pos (pow_pos (by decide) _) hL) k)
    _ = (2 ^ k * L) ^ k := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
      have he : s * k + (k - s) * k = k * k := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hs]
      rw [he]

/-- The power comparison in the last paragraph of Thomason's main proof,
p. 264: a gap of `s` bits per selected vertex covers fewer than `2^(s*k)`
exceptional sets. -/
theorem mul_choose_div_pow_lt_choose_of_bits (j N B k s : ℕ)
    (hs : s ≤ k) (hL : 0 < B + 1 - k)
    (hN : N ≤ 2 ^ (k - s) * (B + 1 - k)) (hj : j < 2 ^ (s * k)) :
    j * (N / 2 ^ k).choose k < B.choose k := by
  exact mul_choose_div_pow_lt_choose _ _ _ _
    (mul_pow_lt_scaled_pow_of_bits _ _ _ _ _ hs hL hN hj)

end GraphMinor.Thomason
