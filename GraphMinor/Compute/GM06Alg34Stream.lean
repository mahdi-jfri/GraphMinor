module

public import GraphMinor.Compute.GM06Alg34Input
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Reading past region boundaries in the disc input

The disc procedure first locates the supplied cuff and division lists.
Each region contributes two length-prefixed incidence lists. A RAM command
reads a list's length and advances the input cursor without copying its
entries. Its execution proof preserves the input and all other arrays.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a boundary-list length and move the cursor past that list. -/
def gm06SkipListProg (a : Arr) (r_pos r_len : Reg) : Cmd :=
  .seq (readStreamWordProg a r_pos r_len)
    (.assign r_pos (.op .add (.reg r_pos) (.reg r_len)))

/-- Skipping a supplied length-prefixed list costs at most twelve steps.
Only the cursor and length register change. The word-size conditions
bound the cursor and list length, not the entries being skipped. -/
theorem gm06SkipListProg_exec {w a off : ℕ} {mid tail : List ℕ} (r_pos r_len : ℕ)
    (hne : r_pos ≠ r_len) (hw : 1 < 2 ^ w)
    (hend : off + 1 + mid.length < 2 ^ w) {s : State}
    (hstream : AtStream a off (GM06DrawingData.listWords mid ++ tail) s)
    (hpos : s.regs r_pos = off) :
    ∃ s' t, Exec w (gm06SkipListProg a r_pos r_len) s s' t ∧ t ≤ 12 ∧
      s'.regs r_pos = off + 1 + mid.length ∧ s'.regs r_len = mid.length ∧
      AtStream a (off + 1 + mid.length) tail s' ∧
      (∀ b, s'.arrs b = s.arrs b) ∧
      (∀ r, r ≠ r_pos → r ≠ r_len → s'.regs r = s.regs r) := by
  have hoff : off + 1 < 2 ^ w := by omega
  have hlen : mid.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hlen₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    readStreamWordProg_exec r_pos r_len hne hw hoff hlen hstream hpos
  have heval : (Expr.op .add (.reg r_pos) (.reg r_len)).eval w s₁ =
      some (off + 1 + mid.length) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hpos₁, hlen₁, hoff, hlen, hend]
  let s₂ := s₁.setReg r_pos (off + 1 + mid.length)
  have hex₂ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.reg r_len))) s₁ s₂ 4 :=
    .assign heval
  refine ⟨s₂, t₁ + 4, .seq hex₁ hex₂, by omega, by simp [s₂], ?_, ?_, ?_, ?_⟩
  · simpa only [s₂, State.setReg_regs_ne _ _ hne.symm] using hlen₁
  · exact (hstream₁.append_advance (mid := mid)).of_arr_eq rfl
  · intro b
    exact harr₁ b
  · intro r hrp hrl
    rw [State.setReg_regs_ne _ _ hrp]
    exact hreg₁ r hrp hrl

end GraphMinor.Compute
