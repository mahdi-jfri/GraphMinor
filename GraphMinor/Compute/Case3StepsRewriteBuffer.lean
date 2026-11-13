module

import GraphMinor.Compute.BitSet
import Mathlib.Data.List.GetD

/-!
# Replacing an array from left to right

A scan retains the old suffix until it reaches each entry. Writing that
entry extends the new prefix by one value. The identity permits the
loop-owner scan to read an old owner and then replace it in the same array.
-/

public section

namespace GraphMinor.Compute

/-- Replacing the next old entry advances the completed prefix. -/
theorem case3RewriteBuffer_set (old values : List ℕ) (hlen : old.length = values.length)
    (k : ℕ) (hk : k < values.length) :
    (values.take k ++ old.drop k).set k values[k] =
      values.take (k + 1) ++ old.drop (k + 1) := by
  have htake : (values.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  rw [List.set_append_right _ _ (by omega), htake, Nat.sub_self,
    List.drop_eq_getElem_cons (show k < old.length by omega), List.set_cons_zero,
    take_add_one_eq_append_getElem values k hk]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The current entry of a replacement scan still has its old value. -/
theorem case3RewriteBuffer_getD (old values : List ℕ) (k : ℕ)
    (hk : k ≤ values.length) :
    (values.take k ++ old.drop k).getD k 0 = old.getD k 0 := by
  have htake : (values.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk]
  rw [List.getD_append_right _ _ _ _ (by omega), htake, Nat.sub_self]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]

end GraphMinor.Compute
