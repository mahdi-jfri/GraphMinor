module

public import GraphMinor.Compute.CrossingOpsReplRecord

/-!
# Copying the used replacement record prefix

The encoder uses a buffer whose capacity is an upper bound on the record length.
The append routine takes an array containing exactly the record. The program here copies
only the used prefix and caps reads at a bound that contains every encoded word.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Copy the used record prefix to an exact-size array. Register `R+8` holds `N`. -/
def finishReplRecordProg (buf dst R : ℕ) : Cmd :=
  .seq (.assign (R + 11) (.op .add (.op .add (.reg (R + 8)) (.const 2)) (.reg (R + 4))))
    (.seq (.assign (R + 14) (.reg (R + 4)))
      (copyMinNProg buf dst (R + 11) (R + 12) (R + 14)))

/-- Copying the used prefix gives exactly the encoded record, since every encoded word
is at most `N+2+length`. Only the destination array and three scratch registers change. -/
theorem finishReplRecordProg_exec {w N : ℕ} (buf dst R : ℕ)
    {s : State} {words : List ℕ} {k : ℕ} {rec : GraphMinor.Crossing.CrossRecord (Fin N)}
    (hne : buf ≠ dst) (hN : s.regs (R + 8) = N)
    (hb : IsBuf buf (R + 4) words k s) (henc : IsRecordEnc rec words)
    (hw : N + 2 + words.length < 2 ^ w) :
    ∃ s' t, Exec w (finishReplRecordProg buf dst R) s s' t ∧
      t ≤ 15 * words.length + 14 ∧ s'.arrs dst = words ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 11 → r ≠ R + 12 → r ≠ R + 14 → s'.regs r = s.regs r) := by
  let cap := N + 2 + words.length
  let s1 := s.setReg (R + 11) cap
  have hex1 : Exec w (.assign (R + 11)
      (.op .add (.op .add (.reg (R + 8)) (.const 2)) (.reg (R + 4)))) s s1 6 :=
    .assign (eval_add (eval_add (eval_reg hN (by omega)) (eval_const (by omega)) (by omega))
      (eval_reg hb.2 (by omega)) hw)
  let s2 := s1.setReg (R + 14) words.length
  have hex2 : Exec w (.assign (R + 14) (.reg (R + 4))) s1 s2 2 :=
    .assign (eval_reg (by simp [s1, hb.2]) (by omega))
  obtain ⟨s3, t3, hex3, ht3, harr, ha3, hr3⟩ := copyMinNProg_exec (w := w)
    buf dst (R + 11) (R + 12) (R + 14) hne (by omega) (by omega) (by omega)
    (s := s2) (B := cap) (n := words.length) (by simp [s2, s1]) hw (by omega)
    (by simp [s2]) (by omega) (by simp [s2, s1, hb.1])
  refine ⟨s3, 6 + (2 + t3), .seq hex1 (.seq hex2 hex3), by omega, ?_,
    fun a ha => by simpa [s2, s1] using ha3 a ha,
    fun r h11 h12 h14 => by simpa [s2, s1, State.setReg_regs, h11, h14] using hr3 r h12⟩
  rw [harr]
  simp only [s2, s1, State.setReg_arrs, hb.1, List.take_left]
  have hm : words.map (fun x => min x cap) = words.map id :=
    List.map_congr_left (fun x hx => min_eq_left (le_of_isRecordEnc henc x hx))
  simpa only [List.map_id] using hm

end GraphMinor.Compute.Crossing
