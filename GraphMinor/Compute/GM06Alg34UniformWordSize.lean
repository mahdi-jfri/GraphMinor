module

public import GraphMinor.Compute.GM06Alg34UniformSize
import Mathlib.Tactic.Ring

/-!
# One logarithmic word size for all reduction states

A polynomial bound on the current input gives a constant-factor bound
on its logarithm. Apply this to the uniform quadratic input bound.
The word size chosen from the original input then suffices for every
local singleton, interior, split, dual and component program.
-/

public section
namespace GraphMinor.Compute

/-- A polynomial bound on an input size gives a fixed multiple of the
original logarithmic word size. -/
theorem gm06WordSize_le_of_power (c d Q M : ℕ) (hd : 1 ≤ d)
    (hM : M + 2 ≤ (Q + 2) ^ d) : wordSize c M ≤ wordSize (c * d) Q := by
  have hp := pow_lt_two_pow_wordSize hd Q
  have hl := Nat.log_lt_of_lt_pow (by omega : M + 2 ≠ 0) (hM.trans_lt hp)
  have hlog : Nat.log 2 (M + 2) + 1 ≤ d * (Nat.log 2 (Q + 2) + 1) := by
    change Nat.log 2 (M + 2) < d * (Nat.log 2 (Q + 2) + 1) at hl
    omega
  unfold wordSize
  exact (Nat.mul_le_mul_left c hlog).trans_eq (by ring)

private theorem quadratic_le_power (Q M : ℕ) (hM : M ≤ 40 * (Q + 2) ^ 2) :
    M + 2 ≤ (Q + 2) ^ 8 := by
  have h42 : 42 ≤ (Q + 2) ^ 6 :=
    (by decide : 42 ≤ 2 ^ 6).trans (Nat.pow_le_pow_left (by omega : 2 ≤ Q + 2) 6)
  have hsq : 1 ≤ (Q + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hp := Nat.mul_le_mul_left ((Q + 2) ^ 2) h42
  rw [← Nat.pow_add] at hp
  have hmul : (Q + 2) ^ 2 * 42 = 42 * (Q + 2) ^ 2 := Nat.mul_comm _ _
  rw [hmul] at hp
  change 42 * (Q + 2) ^ 2 ≤ (Q + 2) ^ 8 at hp
  omega

/-- The original logarithmic word size suffices for the largest local
coefficient, that of the singleton exhaustion program. -/
theorem gm06Uniform_wordSize (Q M : ℕ) (hM : M ≤ 40 * (Q + 2) ^ 2) :
    wordSize 21 M ≤ wordSize 256 Q := by
  exact (gm06WordSize_le_of_power 21 8 Q M (by decide) (quadratic_le_power Q M hM)).trans
    (wordSize_mono_left (by decide : 21 * 8 ≤ 256) Q)

end GraphMinor.Compute
