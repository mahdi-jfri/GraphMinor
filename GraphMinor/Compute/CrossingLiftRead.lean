module

public import GraphMinor.Compute.SpecsCrossingRec
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading lift records backwards

The record buffer stores the records oldest first. Each record ends with the length of its
body. Reading that length lets the lift program move to the start of the last record without
scanning the free part of the buffer. This file proves the memory bounds and the execution of
that move. The same step works for all three kinds of record.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Every encoded record has a nonempty body and a trailing body length. -/
theorem IsRecordEnc.exists_body {N : ℕ} {r : CrossRecord (Fin N)} {l : List ℕ}
    (h : IsRecordEnc r l) : ∃ body : List ℕ, body ≠ [] ∧ l = withLength body := by
  cases r with
  | repl r =>
    obtain ⟨B, R, E, _, _, _, _, _, _, hl⟩ := h
    exact ⟨_, by simp, hl⟩
  | contr r =>
    obtain ⟨Nv, _, _, hl⟩ := h
    exact ⟨_, by simp, hl⟩
  | del G S => exact ⟨[2], by simp, h⟩

/-- Every record uses at least two words, including its trailing length. -/
theorem IsRecordEnc.two_le_length {N : ℕ} {r : CrossRecord (Fin N)} {l : List ℕ}
    (h : IsRecordEnc r l) : 2 ≤ l.length := by
  obtain ⟨body, hne, rfl⟩ := h.exists_body
  have hb := List.length_pos_iff.mpr hne
  simp only [withLength, List.length_append, List.length_singleton]
  omega

/-- The active encoding pays for constant work at every record, including deletions. -/
theorem record_count_le_words {N : ℕ} {rs : List (CrossRecord (Fin N))}
    {ls : List (List ℕ)} (h : List.Forall₂ IsRecordEnc rs ls) :
    2 * rs.length ≤ ls.flatten.length := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    have hl := hr.two_le_length
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- Reading the record trailers costs at most six times the used prefix length. Free buffer
entries contribute nothing to this bound. -/
theorem record_reader_cost_le {N : ℕ} {a_rec r_rec k : ℕ}
    {rs : List (CrossRecord (Fin N))} {s : State}
    (h : IsRecBufAt a_rec r_rec rs k s) : 12 * rs.length ≤ 6 * s.regs r_rec := by
  obtain ⟨ls, hls, _, hreg⟩ := h
  have hc := record_count_le_words hls
  omega

/-- The trailing length of a record gives its starting offset in a buffer prefix. -/
theorem record_start_of_trailer (pre body spare : List ℕ) :
    let stop := (pre ++ withLength body).length
    (pre ++ withLength body ++ spare)[stop - 1]? = some body.length ∧
      stop - 1 - body.length = pre.length := by
  dsimp only
  constructor
  · simp only [withLength, List.length_append, List.length_singleton, List.append_assoc]
    have hi : pre.length + (body.length + 1) - 1 = pre.length + body.length := by omega
    rw [hi, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_right (by omega)]
    simp
  · simp only [withLength, List.length_append, List.length_singleton]
    omega

/-- Read the length before `r_stop`, then replace `r_stop` by the start of that record.
The body length is returned in `r_len`. Both registers are scratch registers. -/
def readLiftRecordProg (a_rec r_stop r_len : ℕ) : Cmd :=
  .seq (.assign r_len (.read a_rec (.op .sub (.reg r_stop) (.const 1))))
    (.assign r_stop (.op .sub (.op .sub (.reg r_stop) (.const 1)) (.reg r_len)))

/-- One reverse-record step uses constant time and does not change any array. Its bound depends
on the used prefix, so unused capacity need not fit in a word. -/
theorem readLiftRecordProg_exec {w : ℕ} (a_rec r_stop r_len : ℕ)
    (hne : r_stop ≠ r_len) (pre body spare : List ℕ) (s : State)
    (harr : s.arrs a_rec = pre ++ withLength body ++ spare)
    (hstop : s.regs r_stop = (pre ++ withLength body).length)
    (hw : (pre ++ withLength body).length < 2 ^ w) :
    ∃ s' t, Exec w (readLiftRecordProg a_rec r_stop r_len) s s' t ∧ t ≤ 12 ∧
      s'.regs r_stop = pre.length ∧ s'.regs r_len = body.length ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_stop → r ≠ r_len → s'.regs r = s.regs r) := by
  have hlength : (pre ++ withLength body).length = pre.length + body.length + 1 := by
    simp [withLength, Nat.add_assoc]
  have hw1 : 1 < 2 ^ w := by omega
  have hbw : body.length < 2 ^ w := by omega
  have hindex : (pre ++ withLength body).length - 1 < (s.arrs a_rec).length := by
    rw [harr]
    simp only [withLength, List.length_append, List.length_singleton]
    omega
  have hval : (s.arrs a_rec)[(pre ++ withLength body).length - 1]'hindex = body.length := by
    have ht := (record_start_of_trailer pre body spare).1
    rw [← harr, List.getElem?_eq_getElem hindex] at ht
    exact Option.some.inj ht
  have hread : (Expr.read a_rec (.op .sub (.reg r_stop) (.const 1))).eval w s =
      some body.length := by
    rw [← hval]
    exact eval_read (eval_sub (eval_reg hstop hw) (eval_const hw1)) hindex (by rw [hval]; exact hbw)
  have hsub : (pre ++ withLength body).length - 1 - body.length = pre.length := by omega
  have hmove : (Expr.op .sub (.op .sub (.reg r_stop) (.const 1)) (.reg r_len)).eval w
      (s.setReg r_len body.length) = some pre.length := by
    rw [← hsub]
    exact eval_sub
      (eval_sub (eval_reg (by simpa [hne] using hstop) hw) (eval_const hw1))
      (eval_reg (by simp) hbw)
  refine ⟨_, _, .seq (.assign hread) (.assign hmove), by simp [Expr.cost], ?_, ?_, ?_, ?_⟩
  · simp
  · simp [hne.symm]
  · intro a; rfl
  · intro r hrs hrl; simp [hrs, hrl]

/-- Read one field of a record body from its starting offset. Only the selected field needs a
word bound; neither the prefix nor the unused suffix is scanned. -/
theorem eval_lift_record_field {w a_rec r_start i value : ℕ} {pre body spare : List ℕ}
    {s : State} (harr : s.arrs a_rec = pre ++ body ++ spare)
    (hstart : s.regs r_start = pre.length) (hfield : body[i]? = some value)
    (hword : value < 2 ^ w) (hw : pre.length + body.length + 1 < 2 ^ w) :
    (Expr.read a_rec (.op .add (.reg r_start) (.const i))).eval w s = some value := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hfield
  have hbound : pre.length + i < (s.arrs a_rec).length := by
    rw [harr]; simp only [List.length_append]; omega
  have hval : (s.arrs a_rec)[pre.length + i]'hbound = value := by
    simp only [harr]
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using hget
  rw [← hval]
  exact eval_read (eval_add (eval_reg hstart (by omega)) (eval_const (by omega)) (by omega))
    hbound (by rw [hval]; exact hword)

end GraphMinor.Compute.Crossing
