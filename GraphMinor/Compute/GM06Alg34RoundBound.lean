module

public import GraphMinor.Compute.GM06Alg34QueueBounds
public import GraphMinor.Compute.GM06Alg34UniformWordSize
import Mathlib.Tactic.Ring

/-!
# A common polynomial budget for one driver pass

Use one fixed base larger than every current input and saved task.
Its twenty-second power dominates all existing phase bounds. A fixed
multiple pays for their composition in a driver pass. The queue capacity
and record bounds also fit the common logarithmic word size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A fixed base larger than all current input and task size bounds. -/
def gm06RoundBase (Q : ℕ) : ℕ := 40 * (Q + 2) ^ 2 + gm06TaskRecordBound Q + 2

/-- Uniform time budget for one complete pass through the driver. -/
def gm06RoundBound (Q : ℕ) : ℕ := 100000 * (gm06RoundBase Q) ^ 22

/-- The common base is positive and dominates the current input bound plus two. -/
theorem gm06RoundBase_bounds (Q : ℕ) :
    1 ≤ gm06RoundBase Q ∧ 40 * (Q + 2) ^ 2 + 2 ≤ gm06RoundBase Q ∧
      gm06TaskRecordBound Q + 2 ≤ gm06RoundBase Q := by
  unfold gm06RoundBase
  omega

/-- Any fixed phase power through degree twenty-two fits the common power budget. -/
theorem gm06Round_power_le (Q a d : ℕ) (ha : a ≤ gm06RoundBase Q) (hd : d ≤ 22) :
    a ^ d ≤ (gm06RoundBase Q) ^ 22 :=
  (Nat.pow_le_pow_left ha d).trans (Nat.pow_le_pow_right (gm06RoundBase_bounds Q).1 hd)

/-- The reserved queue capacity fits the fixed logarithmic machine words. -/
theorem gm06Loop_capacity_lt (Q : ℕ) : (Q + 2) ^ 16 < 2 ^ wordSize 256 Q := by
  exact (Nat.pow_le_pow_right (by omega : 1 ≤ Q + 2) (by decide : 16 ≤ 256)).trans_lt
    (pow_lt_two_pow_wordSize (by decide) Q)

/-- Every uniformly bounded saved task fits one common machine word. -/
theorem gm06TaskRecordBound_lt (Q : ℕ) : gm06TaskRecordBound Q < 2 ^ wordSize 256 Q := by
  have hs : 1 ≤ (Q + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcap := gm06Queue_capacity_bound Q 1 (by omega)
  have hle : gm06TaskRecordBound Q ≤ (Q + 2) ^ 16 := by omega
  exact hle.trans_lt (gm06Loop_capacity_lt Q)

end GraphMinor.Compute
