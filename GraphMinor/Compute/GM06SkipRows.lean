module

public import GraphMinor.Compute.GM06Alg34Stream
public import GraphMinor.Compute.GM06ListEncoding

/-!
# Locating a row in a cylinder field

Rotations and linkage paths are supplied as lists of rows. A counted
RAM loop skips the preceding rows by reading their length prefixes.
Its count is a register value, so the same fixed program can locate
any supplied row. The scan preserves all arrays and has a linear bound
in the number of rows skipped.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Skip the number of rows in the count register. -/
def gm06SkipRowsProg (a : Arr) (pos len count : Reg) : Cmd :=
  .while (.reg count)
    (.seq (gm06SkipListProg a pos len) (.assign count (.op .sub (.reg count) (.const 1))))

/-- The row-skipping loop stops at the following stream in at most `17 n + 1` steps. -/
theorem gm06SkipRowsProg_exec {w a off : ℕ} (pos len count : ℕ)
    (hpl : pos ≠ len) (hcp : count ≠ pos) (hcl : count ≠ len)
    (rows : List (List ℕ)) (tail : List ℕ) (hw : 1 < 2 ^ w)
    (hcw : rows.length < 2 ^ w) (hend : off + (gm06EncodeRowsPayload rows).length < 2 ^ w)
    {s : State} (hs : AtStream a off (gm06EncodeRowsPayload rows ++ tail) s)
    (hp : s.regs pos = off) (hc : s.regs count = rows.length) :
    ∃ s' t, Exec w (gm06SkipRowsProg a pos len count) s s' t ∧
      t ≤ 17 * rows.length + 1 ∧
      s'.regs pos = off + (gm06EncodeRowsPayload rows).length ∧ s'.regs count = 0 ∧
      AtStream a (off + (gm06EncodeRowsPayload rows).length) tail s' ∧
      (∀ b, s'.arrs b = s.arrs b) ∧
      (∀ r, r ≠ pos → r ≠ len → r ≠ count → s'.regs r = s.regs r) := by
  induction rows generalizing off s with
  | nil =>
    have hz : (Expr.reg count).eval w s = some 0 := by
      simp [Expr.eval, hc, checkWord, Nat.two_pow_pos w]
    refine ⟨s, 1, .while_false hz, by simp, ?_, hc, ?_, fun _ => rfl, ?_⟩
    · simpa [gm06EncodeRowsPayload] using hp
    · simpa [gm06EncodeRowsPayload] using hs
    · intro r _ _ _; rfl
  | cons row rows ih =>
    have htotal : off + 1 + row.length + (gm06EncodeRowsPayload rows).length < 2 ^ w := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
    have hs₀ : AtStream a off
        (GM06DrawingData.listWords row ++ (gm06EncodeRowsPayload rows ++ tail)) s := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, gm06EncodeNatList,
        GM06DrawingData.listWords, List.append_assoc] using hs
    obtain ⟨s₁, t₁, he₁, ht₁, hp₁, _, hs₁, ha₁, hr₁⟩ :=
      gm06SkipListProg_exec pos len hpl hw (by omega) hs₀ hp
    have hc₁ : s₁.regs count = rows.length + 1 := by
      rw [hr₁ count hcp hcl, hc, List.length_cons]
    have hsucc : rows.length + 1 < 2 ^ w := hcw
    have hrest : rows.length < 2 ^ w := (Nat.lt_succ_self _).trans hsucc
    have heval : (Expr.op .sub (.reg count) (.const 1)).eval w s₁ = some rows.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hsucc, hrest, hw]
    let s₂ := s₁.setReg count rows.length
    have he₂ : Exec w (.assign count (.op .sub (.reg count) (.const 1))) s₁ s₂ 4 :=
      .assign heval
    have hp₂ : s₂.regs pos = off + 1 + row.length := by
      simpa only [s₂, State.setReg_regs_ne _ _ hcp.symm] using hp₁
    have hs₂ : AtStream a (off + 1 + row.length)
        (gm06EncodeRowsPayload rows ++ tail) s₂ := hs₁.of_arr_eq rfl
    obtain ⟨s₃, t₃, he₃, ht₃, hp₃, hc₃, hs₃, ha₃, hr₃⟩ :=
      ih hrest htotal hs₂ hp₂ (State.setReg_regs_self _ _ _)
    have hcond : (Expr.reg count).eval w s = some (rows.length + 1) := by
      simp [Expr.eval, hc, checkWord, hsucc]
    have hoff : off + (gm06EncodeRowsPayload (row :: rows)).length =
        off + 1 + row.length + (gm06EncodeRowsPayload rows).length := by
      simp [gm06EncodeRowsPayload, gm06EncodeNatList]
      omega
    refine ⟨s₃, 1 + (t₁ + 4) + t₃,
      .while_true hcond (Nat.succ_ne_zero _) (.seq he₁ he₂) he₃, ?_,
      hp₃.trans hoff.symm, hc₃, hoff.symm ▸ hs₃, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro b
      exact (ha₃ b).trans (ha₁ b)
    · intro r hrp hrl hrc
      rw [hr₃ r hrp hrl hrc]
      change (s₁.setReg count rows.length).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ hrc, hr₁ r hrp hrl]

end GraphMinor.Compute
