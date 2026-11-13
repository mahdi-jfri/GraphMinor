module

public import GraphMinor.Compute.GM02RecursiveEnterProgram

/-!
# Executing initialization of the crossing-scheme scan

Set the next code, accumulated feasibility bit, and saved left answer
to zero, then enter the scan state. Every array and every other register
is unchanged. This is the final constant-time action of non-base entry.
-/

public section
namespace GraphMinor.Compute

/-- Scheme-scan initialization sets exactly its four control words. -/
theorem gm02RecursiveScanInitProg_exec {w : ℕ} (q : ℕ) (s : State) (hw : 2 < 2 ^ w) :
    ∃ s', Exec w (gm02RecursiveScanInitProg q) s s' 8 ∧
      s'.regs (gm02RecursiveControlBase q + 4) = 0 ∧
      s'.regs (gm02RecursiveControlBase q + 5) = 0 ∧
      s'.regs (gm02RecursiveControlBase q + 6) = 0 ∧
      s'.regs (gm02RecursiveControlBase q + 18) = 2 ∧ s'.arrs = s.arrs ∧
      (∀ r, r ∉ [gm02RecursiveControlBase q + 4, gm02RecursiveControlBase q + 5,
        gm02RecursiveControlBase q + 6, gm02RecursiveControlBase q + 18] → s'.regs r = s.regs r) := by
  let b := gm02RecursiveControlBase q
  let s₁ := s.setReg (b + 4) 0
  have he₁ : Exec w (.assign (b + 4) (.const 0)) s s₁ 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  let s₂ := s₁.setReg (b + 5) 0
  have he₂ : Exec w (.assign (b + 5) (.const 0)) s₁ s₂ 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  let s₃ := s₂.setReg (b + 6) 0
  have he₃ : Exec w (.assign (b + 6) (.const 0)) s₂ s₃ 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  let s₄ := s₃.setReg (b + 18) 2
  have he₄ : Exec w (.assign (b + 18) (.const 2)) s₃ s₄ 2 := Exec.assign (checkWord_of_lt hw)
  refine ⟨s₄, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), ?_, ?_, ?_, by simp [s₄, b], rfl, ?_⟩
  · simp [s₄, s₃, s₂, s₁, b]
  · simp [s₄, s₃, s₂, b]
  · simp [s₄, s₃, b]
  · intro r hr
    have hn : r ≠ b + 4 ∧ r ≠ b + 5 ∧ r ≠ b + 6 ∧ r ≠ b + 18 := by simpa [b] using hr
    simp only [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hn.2.2.2,
      State.setReg_regs_ne _ _ hn.2.2.1, State.setReg_regs_ne _ _ hn.2.1,
      State.setReg_regs_ne _ _ hn.1]

end GraphMinor.Compute
