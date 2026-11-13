module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Bounding insertion choices for crossing schemes

For the counting argument of II (2.8), inserting a new separator vertex
into a family of path lists gives at most one choice for each existing
vertex, one for each original pair, and two unused choices. For at least
three separator vertices, the product of these bounds is at most the
printed power bound. The cases with fewer vertices require the parity
conditions separately.
-/

public section
namespace GraphMinor.GM02
open Finset

/-- The insertion-choice product needed for II (2.8). -/
theorem insertion_product_le_pow (k n : ℕ) (hn : 3 ≤ n) :
    (∏ i ∈ Finset.range n, (k + i + 2)) ≤ (k + n) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.add_zero, one_mul]
    nlinarith
  | @succ n hn ih =>
    have hn1 : n - 1 + 1 = n := by omega
    have hpair : (k + n + 2) * (k + n) ≤ (k + n + 1) ^ 2 := by nlinarith
    have hp : (k + n) ^ (n - 1) ≤ (k + n + 1) ^ (n - 1) :=
      Nat.pow_le_pow_left (by omega) _
    calc
      (∏ i ∈ range (n + 1), (k + i + 2)) =
          (k + n + 2) * (∏ i ∈ range n, (k + i + 2)) := by
        rw [Finset.prod_range_succ, Nat.mul_comm]
      _ ≤ (k + n + 2) * (k + n) ^ n := Nat.mul_le_mul_left _ ih
      _ = ((k + n + 2) * (k + n)) * (k + n) ^ (n - 1) := by
        have he : (k + n) ^ n = (k + n) * (k + n) ^ (n - 1) := by
          calc
            _ = (k + n) ^ (n - 1 + 1) := congrArg (fun r => (k + n) ^ r) hn1.symm
            _ = _ := pow_succ' _ _
        rw [he, Nat.mul_assoc]
      _ ≤ (k + n + 1) ^ 2 * (k + n + 1) ^ (n - 1) := Nat.mul_le_mul hpair hp
      _ = (k + (n + 1)) ^ (n + 1) := by
        rw [← pow_add]
        congr 1; omega

end GraphMinor.GM02
