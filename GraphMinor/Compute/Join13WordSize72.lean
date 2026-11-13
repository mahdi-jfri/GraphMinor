module

public import GraphMinor.Compute.Specs4

/-!
# Choosing one word size for the adapter

All adapter buffers have length bounded by a fixed constant times the input
size. Increasing the word-size exponent once covers every such bound.
-/

public section
namespace GraphMinor.Compute

/-- A linear bound fits at any word size with a large enough exponent. -/
theorem linear_lt_wordSize72 {w c D N : ℕ} (hc : 0 < c) (hD : D ≤ c)
    (hw : wordSize c N ≤ w) : D * (N + 1) < 2 ^ w := by
  have hlin := (Nat.mul_le_mul_right (N + 1) hD).trans (mul_succ_le_pow_add_two c N)
  have hpow := pow_lt_two_pow_wordSize (c := c) hc N
  exact hlin.trans_lt (hpow.trans_le (Nat.pow_le_pow_right (by decide) hw))

end GraphMinor.Compute
