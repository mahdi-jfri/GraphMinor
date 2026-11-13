module

public import GraphMinor.Compute.BitSet
import Mathlib.Data.List.GetD

/-!
# Updating a mapped vertex slice in place

A wall's length words must remain unchanged while the vertex labels between
them are renamed. The completed prefix uses new labels, and the remaining
suffix still uses old labels. These identities justify one in-place update.
-/

public section

namespace GraphMinor.Compute

/-- The next entry of a mapped slice still contains its old label. -/
theorem case3MapSliceBuffer_getD (pre old values suf : List ℕ)
    (k : ℕ) (hk : k < old.length) (hv : k ≤ values.length) :
    (pre ++ values.take k ++ old.drop k ++ suf).getD (pre.length + k) 0 = old[k] := by
  have htake : (values.take k).length = k := by rw [List.length_take, Nat.min_eq_left hv]
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [List.length_append, htake]),
    List.length_append, htake, Nat.sub_self, List.drop_eq_getElem_cons hk]
  rfl

/-- Updating one label extends the mapped prefix by one and preserves
both surrounding sections of the wall encoding. -/
theorem case3MapSliceBuffer_set (pre old values suf : List ℕ)
    (hlen : old.length = values.length) (k : ℕ) (hk : k < old.length) :
    (pre ++ values.take k ++ old.drop k ++ suf).set (pre.length + k) values[k] =
      pre ++ values.take (k + 1) ++ old.drop (k + 1) ++ suf := by
  have htake : (values.take k).length = k := by rw [List.length_take, Nat.min_eq_left (by omega)]
  rw [List.set_append_left _ _ (by simp only [List.length_append, htake, List.length_drop]; omega)]
  rw [List.set_append_right _ _ (by simp only [List.length_append, htake]; exact le_rfl)]
  simp only [List.length_append, htake, Nat.sub_self]
  rw [List.drop_eq_getElem_cons hk, List.set_cons_zero,
    take_add_one_eq_append_getElem values k (by omega)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

end GraphMinor.Compute
