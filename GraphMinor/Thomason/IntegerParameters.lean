module
public import Mathlib.Data.Nat.Log
import GraphMinor.Thomason.BinomialCriterion
import GraphMinor.Thomason.SelectionSize
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Integer parameters for the branch construction

The parameter choice in Thomason's main theorem, p. 264 (1984), reserves
a small fraction of the degree surplus for the exceptional-set count.
We express that reserve using a power of two. This avoids real rounding
when applying the density criterion with the rational constant `2.679`.
-/

public section
namespace GraphMinor.Thomason

/-- Explicit sufficient integer conditions for the room and power
inequalities in the density criterion. The density is `2679*s` and the
degree surplus is `1000*s-4`. -/
theorem integer_parameter_bounds (s k E q : ℕ) (hs : 0 < s) (hk : 5 ≤ k)
    (hE : E ≤ k)
    (hq : q - 1 < 2 ^ (k * (k - E)))
    (hbudget : 2679 * s + 2 ^ E *
      ((q - 1) * (k + 2 * Nat.log 2 k + 1) + k + 4) ≤ 2 ^ E * (1000 * s)) :
    (q - 1) * (k + 2 * Nat.log 2 k + 1) + (Nat.log 2 k + 3) ≤ 1000 * s - 4 ∧
    (q - 1) * (2679 * s) ^ k <
      (2 ^ k * (1000 * s - 4 - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 1 - k)) ^ k := by
  let P := (q - 1) * (k + 2 * Nat.log 2 k + 1)
  have hpow : 0 < 2 ^ E := pow_pos (by decide) _
  have htotal : P + k + 4 ≤ 1000 * s := by
    apply (mul_le_mul_iff_of_pos_left hpow).mp
    exact (Nat.le_add_left _ _).trans hbudget
  have hlog := log_add_three_le hk
  have hroom : P + (Nat.log 2 k + 3) ≤ 1000 * s - 4 := by omega
  refine ⟨hroom, ?_⟩
  let L := 1000 * s - 4 - P + 1 - k
  have hL : 0 < L := by dsimp only [L]; omega
  have heq : L + (P + k + 3) = 1000 * s := by dsimp only [L]; omega
  have hN : 2679 * s ≤ 2 ^ E * L := by
    have hsplit : 2 ^ E * (P + k + 4) = 2 ^ E * (P + k + 3) + 2 ^ E := by ring
    change 2679 * s + 2 ^ E * (P + k + 4) ≤ 2 ^ E * (1000 * s) at hbudget
    rw [hsplit, ← heq, Nat.mul_add (2 ^ E) L] at hbudget
    omega
  apply mul_pow_lt_scaled_pow_of_bits (q - 1) (2679 * s) L k (k - E)
    (Nat.sub_le k E) hL
  · rwa [Nat.sub_sub_self hE]
  · simpa only [Nat.mul_comm] using hq

end GraphMinor.Thomason
