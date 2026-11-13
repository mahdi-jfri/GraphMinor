module

public import GraphMinor.Compute.GM06Alg34MarkRegister
import GraphMinor.Compute.GM06Alg34RegionRow

/-!
# Starting a closure row with its own cell

Compute the row offset from the supplied cell count and current packed
label. Set the kind offset to zero and mark the cell itself. This is
the whole closure row for a vertex and the start of an edge row.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the current row offset and mark its own cell label. -/
def gm06StartClosureRowProg : Cmd :=
  .seq (.assign 173 (.op .mul (.reg 170) (.reg 171)))
    (.seq (.assign 174 (.const 0)) (gm06MarkRegisterProg 171))

/-- Starting a packed closure row writes exactly its diagonal incidence
in fifteen steps, preserving the input and both size/index registers. -/
theorem gm06StartClosureRowProg_exec {w N i : ℕ}
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hi : i < N) (hsquare : N * N < 2 ^ w)
    {s : State} (hNr : s.regs 170 = N) (hir : s.regs 171 = i)
    (hcap : (s.arrs 12).length = N * N) :
    ∃ s', Exec w gm06StartClosureRowProg s s' 15 ∧
      s'.arrs 12 = (s.arrs 12).set (N * i + i) 1 ∧
      s'.regs 173 = N * i ∧ s'.regs 174 = 0 ∧ s'.regs 109 = i ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 109 → q ≠ 173 → q ≠ 174 → s'.regs q = s.regs q) := by
  have hindex : N * i + i < N * N := gm06MatrixAddress_lt hi hi
  have hindexw := hindex.trans hsquare
  have hroww : N * i < 2 ^ w := by omega
  have hiw := hi.trans hN
  let s₁ := s.setReg 173 (N * i)
  have he₁ : Exec w (.assign 173 (.op .mul (.reg 170) (.reg 171))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hNr, hir, hN, hiw, hroww])
  let s₂ := s₁.setReg 174 0
  have he₂ : Exec w (.assign 174 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  obtain ⟨s₃, he₃, hbuf₃, hv₃, ha₃, hr₃⟩ :=
    gm06MarkRegisterProg_exec (s := s₂) (row := N * i) (shift := 0) (v := i) 171 hw
      (by simpa using hindexw) (by simp [s₂, s₁]) (by simp [s₂])
      (by simp [s₂, s₁, hir]) (by simpa [s₂, s₁, hcap] using hindex)
  have hex : Exec w gm06StartClosureRowProg s s₃ 15 := .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, hex, ?_, ?_, ?_, hv₃, ha₃, ?_⟩
  · simpa only [Nat.add_zero, s₂, s₁, State.setReg_arrs] using hbuf₃
  · rw [hr₃ 173 (by decide)]
    simp [s₂, s₁]
  · rw [hr₃ 174 (by decide)]
    simp [s₂]
  · intro q hqv hqr hqs
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06StartClosureRowProg, gm06MarkRegisterProg, gm06MarkCellProg, Cmd.writtenRegs, hqv, hqr, hqs])

end GraphMinor.Compute
