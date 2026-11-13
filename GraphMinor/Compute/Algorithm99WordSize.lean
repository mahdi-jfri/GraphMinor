module

public import GraphMinor.Compute.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Word sizes for the caller of Algorithm (9.9)

The caller measures its word size using the linear graph size, while the core
uses the product of that size and the number of vertices plus one. The product
is at most the square of the linear size. Doubling the word-size constant
covers this square without changing the asymptotic word size.
-/

public section
namespace GraphMinor.Compute

/-- Doubling the word-size constant covers the square of the input size. -/
theorem alg99_wordSize_square (c N : ℕ) :
    wordSize c (N * N) ≤ wordSize (2 * c) N := by
  have hb := lt_two_pow_log_succ N
  have hs : N * N + 2 < (N + 2) ^ 2 := by nlinarith
  have hp := Nat.pow_lt_pow_left hb (by decide : (2 : ℕ) ≠ 0)
  rw [← Nat.pow_mul] at hp
  have hl := Nat.log_lt_of_lt_pow (by omega : N * N + 2 ≠ 0) (hs.trans hp)
  unfold wordSize
  calc
    c * (Nat.log 2 (N * N + 2) + 1) ≤
        c * (2 * (Nat.log 2 (N + 2) + 1)) := Nat.mul_le_mul_left c (by omega)
    _ = (2 * c) * (Nat.log 2 (N + 2) + 1) := by ring

/-- The core word-size bound follows from the caller's linear-size bound. -/
theorem alg99_wordSize_core {c m N w : ℕ} (hm : m + 1 ≤ N)
    (hw : wordSize (2 * c) N ≤ w) : wordSize c ((m + 1) * N) ≤ w := by
  exact (wordSize_mono_right c (Nat.mul_le_mul_right N hm)).trans
    ((alg99_wordSize_square c N).trans hw)

end GraphMinor.Compute
