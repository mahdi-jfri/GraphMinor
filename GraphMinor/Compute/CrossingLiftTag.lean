module

public import GraphMinor.Compute.CrossingLiftRead

/-!
# Reading the operation tag of an encoded record

Each record starts with its operation tag: zero for a replacement, one for a contraction
and two for a deletion. The reverse dispatcher reads that word at the start offset
already obtained from the trailer.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The operation tag fixed by the record encoding. -/
def liftRecordTag {V : Type*} : CrossRecord V → ℕ
  | .repl _ => 0
  | .contr _ => 1
  | .del _ _ => 2

/-- An encoded record begins with its operation tag. -/
theorem IsRecordEnc.tag {N : ℕ} {r : CrossRecord (Fin N)} {words : List ℕ}
    (h : IsRecordEnc r words) : words[0]? = some (liftRecordTag r) := by
  cases r with
  | repl r => obtain ⟨B, C, E, _, _, _, _, _, _, rfl⟩ := h; simp [withLength, liftRecordTag]
  | contr r => obtain ⟨Nv, _, _, rfl⟩ := h; simp [withLength, liftRecordTag]
  | del G S => rw [h]; rfl

/-- The tag read succeeds at a stored record start. The hypotheses specify the encoding,
its buffer slice and the start register, with bounds for the index and the tag. -/
theorem eval_liftRecordTag {w N : ℕ} (a_rec R : ℕ) (r : CrossRecord (Fin N))
    (pre words spare : List ℕ) (henc : IsRecordEnc r words) (s : State)
    (hrec : s.arrs a_rec = pre ++ words ++ spare) (hstart : s.regs R = pre.length)
    (hw : pre.length + words.length + 3 < 2 ^ w) :
    (Expr.read a_rec (.reg R)).eval w s = some (liftRecordTag r) := by
  have hnonempty : 0 < words.length := lt_of_lt_of_le (by decide : 0 < 2) henc.two_le_length
  have hget : (s.arrs a_rec)[pre.length]? = some (liftRecordTag r) := by
    rw [hrec, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self]
    rw [List.getElem?_append_left hnonempty]
    exact henc.tag
  obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp hget
  have htag : liftRecordTag r ≤ 2 := by cases r <;> simp [liftRecordTag]
  rw [← hv]
  exact eval_read (eval_reg hstart (by omega)) hb (by rw [hv]; omega)

end GraphMinor.Compute.Crossing
