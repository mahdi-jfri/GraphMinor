module

public import GraphMinor.Compute.GM06Alg34MarkCell

/-!
# Marking a closure label held in a register

Copy the supplied label to the incidence-marker register and mark its
matrix position. Endpoint reads and row counters can therefore use the
same verified marker without changing their own registers.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Mark the closure label held in register `r`. -/
def gm06MarkRegisterProg (r : ℕ) : Cmd :=
  .seq (.assign 109 (.reg r)) gm06MarkCellProg

/-- Register-based incidence marking takes nine steps and changes only
the incidence matrix and the marker's label register. -/
theorem gm06MarkRegisterProg_exec {w row shift v : ℕ} (r : ℕ) (hw : 1 < 2 ^ w)
    (hword : row + shift + v < 2 ^ w) {s : State}
    (hrow : s.regs 173 = row) (hshift : s.regs 174 = shift) (hlabel : s.regs r = v)
    (hcap : row + shift + v < (s.arrs 12).length) :
    ∃ s', Exec w (gm06MarkRegisterProg r) s s' 9 ∧
      s'.arrs 12 = (s.arrs 12).set (row + shift + v) 1 ∧ s'.regs 109 = v ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 109 → s'.regs q = s.regs q) := by
  have hvw : v < 2 ^ w := by omega
  let s₁ := s.setReg 109 v
  have he₁ : Exec w (.assign 109 (.reg r)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hlabel, hvw])
  obtain ⟨s₂, he₂, hbuf₂, ha₂, hr₂⟩ := gm06MarkCellProg_exec (s := s₁) hw hword
    (by simpa [s₁] using hrow) (by simpa [s₁] using hshift) (by simp [s₁]) hcap
  have hex : Exec w (gm06MarkRegisterProg r) s s₂ 9 := .seq he₁ he₂
  refine ⟨s₂, hex, hbuf₂, ?_, ha₂, ?_⟩
  · rw [hr₂ 109]
    simp [s₁]
  · intro q hq
    exact (hr₂ q).trans (State.setReg_regs_ne _ _ hq)

end GraphMinor.Compute
