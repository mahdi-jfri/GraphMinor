module

public import GraphMinor.Compute.GM02SavedFrameWords
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Locating the most recent saved parent frame

Read the last used stack word to recover the frame's starting offset.
Subtract it from the end cursor to obtain the frame length, then point
the read cursor at its eight-word header's successor. No stack word or
other array changes during this constant-time lookup.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Recover the frame start, total length, and first saved-array offset. -/
def gm02FindSavedFrameProg (stack : Arr) (r_pos r_start r_length r_read : Reg) : Cmd :=
  .seq (.assign r_start (.read stack (.op .sub (.reg r_pos) (.const 1))))
    (.seq (.assign r_length (.op .sub (.reg r_pos) (.reg r_start)))
      (.assign r_read (.op .add (.reg r_start) (.const 8))))

/-- Footer lookup recovers all frame offsets in constant time. -/
theorem gm02FindSavedFrameProg_exec {w cap : ℕ} (stack : Arr)
    (r_pos r_start r_length r_read : Reg)
    (hsp : r_start ≠ r_pos) (hls : r_length ≠ r_start)
    (hrs : r_read ≠ r_start) (hrl : r_read ≠ r_length)
    (P L R pref : List ℕ) (mode code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hlen : pref.length + 9 + P.length + L.length + R.length < 2 ^ w)
    (hstack : s.arrs stack = pref ++
      gm02SavedFrameWords P L R mode code aggregate leftAnswer catalogue pref.length ++
        List.replicate cap 0)
    (hpos : s.regs r_pos = pref.length + 9 + P.length + L.length + R.length) :
    ∃ s', Exec w (gm02FindSavedFrameProg stack r_pos r_start r_length r_read) s s' 13 ∧
      s'.regs r_start = pref.length ∧
      s'.regs r_length = 9 + P.length + L.length + R.length ∧
      s'.regs r_read = pref.length + 8 ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ r_start → r ≠ r_length → r ≠ r_read → s'.regs r = s.regs r) := by
  let H := gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue
  let pre := pref ++ H ++ P ++ L ++ R
  have hpre : pre.length = pref.length + 8 + P.length + L.length + R.length := by
    simp only [pre, List.length_append, H, gm02SavedFrameHeader_length]
  have harr : s.arrs stack = pre ++ pref.length :: List.replicate cap 0 := by
    simpa only [pre, H, gm02SavedFrameWords, List.append_assoc, List.singleton_append] using hstack
  have hpos' : s.regs r_pos = pre.length + 1 := by omega
  have hindex : pre.length < (s.arrs stack).length := by
    simp only [harr, List.length_append, List.length_cons, List.length_replicate]
    omega
  have hget : (s.arrs stack)[pre.length] = pref.length := by
    simp only [harr, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
  have hprefixw : pref.length < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h8 : 8 < 2 ^ w := by omega
  let s₁ := s.setReg r_start pref.length
  have he₁ : Exec w (.assign r_start (.read stack (.op .sub (.reg r_pos) (.const 1)))) s s₁ 5 := by
    apply Exec.assign
    have heidx := eval_sub (eval_reg hpos' (by omega : pre.length + 1 < 2 ^ w)) (eval_const h1)
    simp only [Nat.add_sub_cancel] at heidx
    have he := eval_read (a := stack) heidx hindex (by rw [hget]; exact hprefixw)
    simpa only [hget] using he
  let len := 9 + P.length + L.length + R.length
  let s₂ := s₁.setReg r_length len
  have he₂ : Exec w (.assign r_length (.op .sub (.reg r_pos) (.reg r_start))) s₁ s₂ 4 := by
    apply Exec.assign
    have hp₁ := (State.setReg_regs_ne s pref.length hsp.symm).trans hpos
    have hs₁ : s₁.regs r_start = pref.length := by simp [s₁]
    have he := eval_sub (eval_reg hp₁ hlen) (eval_reg hs₁ hprefixw)
    have hsub : pref.length + 9 + P.length + L.length + R.length - pref.length = len := by
      dsimp only [len]
      omega
    simpa only [hsub] using he

  let s₃ := s₂.setReg r_read (pref.length + 8)
  have he₃ : Exec w (.assign r_read (.op .add (.reg r_start) (.const 8))) s₂ s₃ 4 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₂, s₁, State.setReg_regs_ne _ _ hls.symm,
      checkWord_of_lt hprefixw, checkWord_of_lt h8,
      checkWord_of_lt (by omega : pref.length + 8 < 2 ^ w)]
  refine ⟨s₃, Exec.seq he₁ (Exec.seq he₂ he₃), ?_, ?_, by simp [s₃], rfl, ?_⟩
  · simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hrs.symm, State.setReg_regs_ne _ _ hls.symm]
  · simp [s₃, s₂, len, State.setReg_regs_ne _ _ hrl.symm]
  · intro r hrs' hrl' hrr'
    simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hrr', State.setReg_regs_ne _ _ hrl',
      State.setReg_regs_ne _ _ hrs']

end GraphMinor.Compute
