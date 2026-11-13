module

public import GraphMinor.Compute.GM06Alg34DualPayloadWrite
import Mathlib.Tactic.Ring

/-!
# A quartic bound for complete dual serialization

Bound all supplied counts and the cuff length by the input size. The
structural scans are quadratic, and the canonical division scan is
quartic. Their explicit sum is bounded by one quartic polynomial.
-/

public section
namespace GraphMinor.Compute

private theorem write_budget (S : ℕ) :
    40 + (100 * (S + 1) + 37) * S + (200 * (S + S + 2) + 13) * S +
      30 * (S + 1) + (500 * (S + 1) ^ 3 + 16) * S + 20 ≤ 1000 * (S + 2) ^ 4 := by
  ring_nf
  omega

/-- The complete dual serializer's explicit scan sum has a quartic
bound in the original drawing size. -/
theorem gm06DualWriteTime_le (x : GM06DrawingData) (L : List (Fin x.n))
    (hk : L.length ≤ x.size) : gm06DualWriteTime x L ≤ 1000 * (x.size + 2) ^ 4 := by
  have hc := x.counts_le_size
  have he := Nat.mul_le_mul (show 100 * (x.regions.length + 1) + 37 ≤
    100 * (x.size + 1) + 37 by omega) hc.2.1
  have hr := Nat.mul_le_mul (show 200 * (x.regions.length + x.ends.length + 2) + 13 ≤
    200 * (x.size + x.size + 2) + 13 by omega) hc.1
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 3
  have hd := Nat.mul_le_mul (show 500 * (L.length + 1) ^ 3 + 16 ≤
    500 * (x.size + 1) ^ 3 + 16 by omega) hk
  have ht : gm06DualWriteTime x L ≤
      40 + (100 * (x.size + 1) + 37) * x.size +
        (200 * (x.size + x.size + 2) + 13) * x.size +
        30 * (x.size + 1) + (500 * (x.size + 1) ^ 3 + 16) * x.size + 20 := by
    unfold gm06DualWriteTime
    omega
  exact ht.trans (write_budget x.size)

end GraphMinor.Compute
