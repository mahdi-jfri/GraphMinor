module

public import GraphMinor.Compute.BitSet

/-!
# Restoring an array from a saved recursive frame

Read the next saved slice into a work array and advance the frame's
read cursor by the saved length. The saved-frame buffer itself stays
unchanged. The exact slice and cursor specification supports restoring
the parent input and both vertex-side arrays after a child returns.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restore a saved slice and advance its read cursor. -/
def gm02RestoreSavedArrayProg (stack dst : Arr) (r_off r_len r_base : Reg) : Cmd :=
  .seq (readSliceProg stack (.reg r_off) dst (.reg r_len) r_base)
    (.assign r_off (.op .add (.reg r_off) (.reg r_len)))

/-- Restoring a saved array writes exactly its words and advances past them. -/
theorem gm02RestoreSavedArrayProg_exec {w : ℕ} (stack dst : Arr)
    (r_off r_len r_base : Reg) (hsd : stack ≠ dst) (hob : r_off < r_base) (hlb : r_len < r_base)
    (pref words rest : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hwords : ∀ v ∈ words, v < 2 ^ w) (hlen : pref.length + words.length < 2 ^ w)
    (hstack : s.arrs stack = pref ++ words ++ rest)
    (hoff : s.regs r_off = pref.length) (hcount : s.regs r_len = words.length) :
    ∃ s' t, Exec w (gm02RestoreSavedArrayProg stack dst r_off r_len r_base) s s' t ∧
      t ≤ 16 * words.length + 13 ∧ s'.arrs dst = words ∧
      s'.regs r_off = pref.length + words.length ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_off → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ := readSliceProg_exec stack dst (.reg r_off)
    r_len r_base hsd hlb pref words rest rfl rfl hwords hw hlen
    (by simp [Expr.eval, hoff, checkWord_of_lt (by omega : pref.length < 2 ^ w)]) hstack hcount
  have ho₁ := (hr₁ r_off hob).trans hoff
  have hn₁ := (hr₁ r_len hlb).trans hcount
  let s₂ := s₁.setReg r_off (pref.length + words.length)
  have he₂ : Exec w (.assign r_off (.op .add (.reg r_off) (.reg r_len))) s₁ s₂ 4 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, ho₁, hn₁,
      checkWord_of_lt (by omega : pref.length < 2 ^ w),
      checkWord_of_lt (by omega : words.length < 2 ^ w), checkWord_of_lt hlen]
  refine ⟨s₂, t₁ + 4, Exec.seq he₁ he₂, ?_, hout, by simp [s₂], ha₁, ?_⟩
  · simp only [Expr.cost_reg] at ht₁
    omega
  · intro r hrb hro
    exact (State.setReg_regs_ne _ _ hro).trans (hr₁ r hrb)

end GraphMinor.Compute
