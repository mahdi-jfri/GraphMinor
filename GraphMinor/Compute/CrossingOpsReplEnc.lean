module

public import GraphMinor.Compute.CrossingOpsReplPairs

/-!
# Writing the fields of a replacement record

The replacement record contains the boundary and recorded component as lists, followed by
ordered pairs of adjacent vertices. The programs here copy the list fields into a buffer
and replace the placeholder for the number of pairs after the pairs have been written.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Copy an array into the buffer, using three loop registers. -/
def emitArrayProg (src buf R : ℕ) : Cmd :=
  forArrProg src (R + 5) (R + 6) (R + 3) (emitProg buf (R + 4) (.reg (R + 3)))

/-- Copying a list field costs time proportional to its length and changes only the buffer
and its cursor and the three loop registers. -/
theorem emitArrayProg_exec {w : ℕ} (src buf R : ℕ) {s : State} {pre l : List ℕ} {k : ℕ}
    (hne : src ≠ buf) (hl : s.arrs src = l) (hb : IsBuf buf (R + 4) pre k s)
    (hk : l.length ≤ k) (hlt : ∀ x ∈ l, x < 2 ^ w)
    (hlen : l.length < 2 ^ w) (hw : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitArrayProg src buf R) s s' t ∧ t ≤ 7 + 17 * l.length ∧
      IsBuf buf (R + 4) (pre ++ l) (k - l.length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
        s'.regs r = s.regs r) := by
  let Q : ℕ → State → Prop := fun _ z =>
    (∀ a, a ≠ buf → z.arrs a = s.arrs a) ∧
    (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
      z.regs r = s.regs r)
  obtain ⟨s', t, hex, ht, hQ, hb'⟩ := forArrEmit_exec (w := w) src (R + 5) (R + 6) (R + 3)
    buf (R + 4) (emitProg buf (R + 4) (.reg (R + 3))) (fun x => [x]) Q 7
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa only [hl] using hlen) (by simpa only [hl] using hlt)
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hb (by simpa [hl] using hk)
    (fun j z z' h harr hreg => ⟨fun a ha => by rw [harr]; exact h.1 a ha,
      fun r h3 h4 h5 h6 => (hreg r h5 h6 h3).trans (h.2 r h3 h4 h5 h6)⟩)
    (fun _ z h => h.1 src hne)
    (fun j hj z pre' k' h hri hrn hry hb'' hk' hlen' => by
      have hkpos : k' = (k' - 1) + 1 := by
        simp only [List.length_singleton] at hk'
        omega
      obtain ⟨hex', hb'''⟩ := emitProg_exec (w := w) buf (R + 4) (.reg (R + 3))
        (by rw [← hkpos]; exact hb'')
        (eval_reg hry (hlt _ (by rw [← hl]; exact List.getElem_mem hj))) (by omega)
      refine ⟨_, 7, hex', le_rfl, ?_, ?_, ?_, hb'''⟩
      · exact ⟨fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha, h.1 a ha],
          fun r h3 h4 h5 h6 => by simp [State.setReg_regs, h4, h.2 r h3 h4 h5 h6]⟩
      · simpa using hri
      · simpa using hrn)
  refine ⟨s', t, hex, ?_, ?_, hQ.1, hQ.2⟩
  · simpa only [hl, Nat.mul_comm] using ht
  · simpa [hl] using hb'

/-- Emit the length of a list field, then all its entries. -/
def emitFieldProg (src buf R : ℕ) : Cmd :=
  .seq (emitProg buf (R + 4) (.len src)) (emitArrayProg src buf R)

/-- A list field uses one header word and one word for each entry. -/
theorem emitFieldProg_exec {w : ℕ} (src buf R : ℕ) {s : State} {pre l : List ℕ} {k : ℕ}
    (hne : src ≠ buf) (hl : s.arrs src = l) (hb : IsBuf buf (R + 4) pre k s)
    (hk : l.length + 1 ≤ k) (hlt : ∀ x ∈ l, x < 2 ^ w)
    (hw : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitFieldProg src buf R) s s' t ∧ t ≤ 14 + 17 * l.length ∧
      IsBuf buf (R + 4) (pre ++ l.length :: l) (k - (l.length + 1)) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 →
        s'.regs r = s.regs r) := by
  have hkpos : k = (k - 1) + 1 := by omega
  obtain ⟨hex, hb'⟩ := emitProg_exec (w := w) buf (R + 4) (.len src)
    (by rw [← hkpos]; exact hb) (eval_len hl (by omega)) (by omega)
  have harr : ∀ a, a ≠ buf →
      (((s.writeArr buf pre.length l.length).setReg (R + 4) (pre.length + 1)).arrs a) = s.arrs a :=
    fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha]
  obtain ⟨s', t, hex', ht, hb'', ha, hr⟩ := emitArrayProg_exec (w := w) src buf R hne
    ((harr src hne).trans hl) hb' (by omega) hlt (by omega) (by simp; omega)
  refine ⟨s', 7 + t, .seq hex hex', by omega, ?_,
    fun a h => (ha a h).trans (harr a h), fun r h3 h4 h5 h6 => ?_⟩
  · simpa [List.append_assoc, Nat.sub_sub, Nat.add_comm] using hb''
  · simpa [State.setReg_regs, h4] using hr r h3 h4 h5 h6

/-- Replace the pair-count placeholder using the start and end cursors. -/
def patchPairCountProg (buf r_cnt r_pos r_start : ℕ) : Cmd :=
  .write buf (.reg r_pos)
    (.op .div (.op .sub (.reg r_cnt) (.reg r_start)) (.const 2))

/-- The placeholder is replaced by half the number of emitted pair words. The buffer cursor
and all registers are preserved. -/
theorem patchPairCountProg_exec {w : ℕ} (buf r_cnt r_pos r_start : ℕ)
    {s : State} {head pairs : List ℕ} {k : ℕ}
    (hb : IsBuf buf r_cnt (head ++ 0 :: pairs) k s)
    (hp : s.regs r_pos = head.length) (hst : s.regs r_start = head.length + 1)
    (hw : head.length + pairs.length + 2 < 2 ^ w) :
    ∃ s', Exec w (patchPairCountProg buf r_cnt r_pos r_start) s s' 7 ∧
      IsBuf buf r_cnt (head ++ (pairs.length / 2) :: pairs) k s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧ s'.regs = s.regs := by
  have hcnt : s.regs r_cnt = head.length + 1 + pairs.length := by
    simpa only [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.2
  have hsub := eval_sub (eval_reg (w := w) hcnt (by omega))
    (eval_reg hst (by omega))
  have hval : (Expr.op .div (.op .sub (.reg r_cnt) (.reg r_start)) (.const 2)).eval w s =
      some (pairs.length / 2) := by
    have := eval_div hsub (eval_const (w := w) (c := 2) (by omega)) (by decide) (by
      have := Nat.div_le_self pairs.length 2
      omega)
    simpa only [Nat.add_sub_cancel_left] using this
  have hi : head.length < (s.arrs buf).length := by rw [hb.1]; simp
  have hex : Exec w (patchPairCountProg buf r_cnt r_pos r_start) s
      (s.writeArr buf head.length (pairs.length / 2)) 7 :=
    .write (eval_reg hp (by omega)) hval hi
  refine ⟨_, hex, ⟨?_, ?_⟩, fun a ha => State.writeArr_arrs_ne _ _ _ ha, rfl⟩
  · simp only [State.writeArr_arrs_self, hb.1]
    rw [List.append_assoc, List.set_append_right _ _ le_rfl, Nat.sub_self]
    simp
  · simpa only [State.writeArr_regs, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcnt

/-- Complete a record body by appending its length. -/
def emitLengthProg (buf r_cnt : ℕ) : Cmd := emitProg buf r_cnt (.reg r_cnt)

/-- The closing word is the length before the closing word itself. -/
theorem emitLengthProg_exec {w : ℕ} (buf r_cnt : ℕ) {s : State} {body : List ℕ} {k : ℕ}
    (hb : IsBuf buf r_cnt body k s) (hk : 1 ≤ k)
    (hw : body.length + 1 < 2 ^ w) :
    ∃ s', Exec w (emitLengthProg buf r_cnt) s s' 7 ∧
      IsBuf buf r_cnt (withLength body) (k - 1) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_cnt → s'.regs r = s.regs r) := by
  have hkpos : k = (k - 1) + 1 := by omega
  obtain ⟨hex, hb'⟩ := emitProg_exec buf r_cnt (.reg r_cnt)
    (by rw [← hkpos]; exact hb) (eval_reg hb.2 (by omega)) hw
  exact ⟨_, hex, hb', fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha],
    fun r hr => by simp [hr]⟩

/-- The replacement tag and its two list fields, before the pair count. -/
def replHead (bd rep : List ℕ) : List ℕ := [0, bd.length] ++ bd ++ [rep.length] ++ rep

/-- Write the tag, the two list fields, and a placeholder for the pair count. Save the
placeholder position in `R+9` and the start of the pairs in `R+10`. -/
def replHeaderProg (a_bd a_rep buf R : ℕ) : Cmd :=
  .seq (emitProg buf (R + 4) (.const 0))
    (.seq (emitFieldProg a_bd buf R)
      (.seq (emitFieldProg a_rep buf R)
        (.seq (.assign (R + 9) (.reg (R + 4)))
          (.seq (emitProg buf (R + 4) (.const 0))
            (.assign (R + 10) (.reg (R + 4)))))))

/-- The replacement header has the stated list fields and cursor positions. -/
theorem replHeaderProg_exec {w : ℕ} (a_bd a_rep buf R : ℕ)
    {s : State} {bd rep : List ℕ} {k : ℕ}
    (hbd : a_bd ≠ buf) (hrep : a_rep ≠ buf)
    (hB : s.arrs a_bd = bd) (hR : s.arrs a_rep = rep)
    (hb : IsBuf buf (R + 4) [] k s) (hk : bd.length + rep.length + 4 ≤ k)
    (hBw : ∀ x ∈ bd, x < 2 ^ w) (hRw : ∀ x ∈ rep, x < 2 ^ w)
    (hw : k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (replHeaderProg a_bd a_rep buf R) s s' t ∧
      t ≤ 46 + 17 * (bd.length + rep.length) ∧
      IsBuf buf (R + 4) (replHead bd rep ++ [0])
        (k - (bd.length + rep.length + 4)) s' ∧
      s'.regs (R + 9) = (replHead bd rep).length ∧
      s'.regs (R + 10) = (replHead bd rep).length + 1 ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) := by
  have hk0 : k = (k - 1) + 1 := by omega
  obtain ⟨hex0, hb0⟩ := emitProg_exec (w := w) buf (R + 4) (.const 0) (pre := []) (k := k - 1)
    (by rw [← hk0]; exact hb) (eval_const (by omega)) (by change 0 + 1 < 2 ^ w; omega)
  simp only [List.nil_append] at hb0
  let s0 := (s.writeArr buf 0 0).setReg (R + 4) 1
  have ha0 : ∀ a, a ≠ buf → s0.arrs a = s.arrs a := fun a ha => by
    simp [s0, State.writeArr_arrs_ne _ _ _ ha]
  obtain ⟨s1, t1, hex1, ht1, hb1, ha1, hr1⟩ := emitFieldProg_exec (w := w) a_bd buf R hbd
    ((ha0 a_bd hbd).trans hB) hb0 (by omega) hBw (by simp; omega)
  obtain ⟨s2, t2, hex2, ht2, hb2, ha2, hr2⟩ := emitFieldProg_exec (w := w) a_rep buf R hrep
    ((ha1 a_rep hrep).trans ((ha0 a_rep hrep).trans hR)) hb1 (by omega) hRw
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega)
  have hb2' : IsBuf buf (R + 4) (replHead bd rep)
      (k - (bd.length + rep.length + 3)) s2 := by
    simpa [replHead, List.append_assoc, Nat.sub_sub, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hb2
  let s3 := s2.setReg (R + 9) (replHead bd rep).length
  have hex3 : Exec w (.assign (R + 9) (.reg (R + 4))) s2 s3 2 :=
    .assign (eval_reg hb2'.2 (by simp [replHead]; omega))
  have hb3 : IsBuf buf (R + 4) (replHead bd rep)
      (k - (bd.length + rep.length + 3)) s3 := by
    exact ⟨hb2'.1, by simp [s3, hb2'.2]⟩
  have hk3 : k - (bd.length + rep.length + 3) =
      (k - (bd.length + rep.length + 4)) + 1 := by omega
  obtain ⟨hex4, hb4⟩ := emitProg_exec (w := w) buf (R + 4) (.const 0)
    (by rw [← hk3]; exact hb3) (eval_const (by omega)) (by simp [replHead]; omega)
  let s4 := (s3.writeArr buf (replHead bd rep).length 0).setReg (R + 4)
    ((replHead bd rep).length + 1)
  let s5 := s4.setReg (R + 10) ((replHead bd rep).length + 1)
  have hex5 : Exec w (.assign (R + 10) (.reg (R + 4))) s4 s5 2 :=
    .assign (eval_reg (by simp [s4]) (by simp [replHead]; omega))
  refine ⟨s5, _, .seq hex0 (.seq hex1 (.seq hex2 (.seq hex3 (.seq hex4 hex5)))),
    ?_, ⟨hb4.1, by simp [s5, s4, hb4.2]⟩, ?_, by simp [s5], ?_⟩
  · simp only [Expr.cost]
    omega
  · simp [s5, s4, s3]
  · intro a ha
    simp only [s5, s4, s3, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
    exact (ha2 a ha).trans ((ha1 a ha).trans (ha0 a ha))

end GraphMinor.Compute.Crossing
