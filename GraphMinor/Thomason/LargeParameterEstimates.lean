module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Elementary estimates for large parameters

Thomason's main theorem, p. 264 (1984), chooses the subset size near the
square root of the logarithm of the target order. We give explicit
integer estimates for that choice. Dividing by a fixed power of two
bounds the small logarithmic cost of connecting each selected set.
-/

public section
namespace GraphMinor.Thomason

/-- Above an explicit threshold, the connection cost and a fixed
21-vertex margin cost at most one part in ten thousand of `m`. -/
theorem large_selection_size_bound (m : ℕ) (hm : 1048576 ≤ m) :
    10000 * (m + 21 + 2 * Nat.log 2 (m + 21) + 1) ≤ 10001 * m := by
  have hh := Nat.log_le_self 2 ((m + 21) / 2 ^ 16)
  rw [Nat.log_div_base_pow] at hh
  have hdiv := Nat.div_mul_le_self (m + 21) 65536
  norm_num only [Nat.reducePow] at hh
  omega

/-- The selected size `sqrt(log₂ q)+21` leaves twenty bits for the
exceptional-set reserve in the counting inequality. -/
theorem sqrt_log_target_lt_pow (q : ℕ) :
    q - 1 < 2 ^ ((Nat.sqrt (Nat.log 2 q) + 21) *
      (Nat.sqrt (Nat.log 2 q) + 21 - 20)) := by
  have hs := Nat.lt_succ_sqrt (Nat.log 2 q)
  have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
  have he : Nat.log 2 q + 1 ≤ (Nat.sqrt (Nat.log 2 q) + 21) *
      (Nat.sqrt (Nat.log 2 q) + 21 - 20) := by
    have heq : Nat.sqrt (Nat.log 2 q) + 21 - 20 = Nat.sqrt (Nat.log 2 q) + 1 := by omega
    rw [heq]
    nlinarith only [hs]
  exact (Nat.sub_le q 1).trans_lt (hp.trans_le (Nat.pow_le_pow_right (by decide) he))

end GraphMinor.Thomason
