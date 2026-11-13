module

import GraphMinor.Compute.BitSet

/-!
# Advancing a flag-array buffer

The selected-group scan writes one flag into a preallocated block. Its
prefix already contains the computed flags, its remaining slots are zero,
and the surrounding arrays stay in their original order. This list identity
is the exact buffer update used by that scan.
-/

public section

namespace GraphMinor.Compute

/-- Writing the next zero slot appends one value to the completed prefix. -/
theorem case3FlagBuffer_set (pre values suf : List ℕ) (k : ℕ) (hk : k < values.length) :
    (pre ++ values.take k ++ List.replicate (values.length - k) 0 ++ suf).set
        (pre.length + k) values[k] =
      pre ++ values.take (k + 1) ++ List.replicate (values.length - (k + 1)) 0 ++ suf := by
  have htake : (values.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  rw [take_add_one_eq_append_getElem values k hk]
  rw [List.set_append_left _ _ (by
    simp only [List.length_append, htake, List.length_replicate]
    omega)]
  rw [List.set_append_right _ _ (by simp only [List.length_append, htake]; exact le_rfl)]
  simp only [List.length_append, htake, Nat.sub_self]
  rw [show values.length - k = (values.length - (k + 1)) + 1 by omega,
    List.replicate_succ, List.set_cons_zero]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

end GraphMinor.Compute
