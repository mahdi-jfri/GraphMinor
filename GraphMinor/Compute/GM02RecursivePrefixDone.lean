module

public import GraphMinor.Compute.GM02RecursiveMachineProgram
public import GraphMinor.Compute.GM02RecursiveScanAdvance
public import GraphMinor.Compute.GM02LoopPrefix

/-!
# Ending the scheme scan inside the recursive loop

At the end of the fixed code range, one loop iteration copies the
accumulator into the output and enters the return state. Every array
and every other control word is unchanged. The exact cost includes both
state-dispatch tests and the loop guard.
-/

public section
namespace GraphMinor.Compute

/-- Finishing the actual loop's scan returns its accumulated bit in fourteen steps. -/
theorem gm02RecursivePrefix_scan_done {w : ℕ} (q : ℕ) (s : State) (answer : ℕ)
    (hstate : s.regs (gm02RecursiveControlBase q + 18) = 2)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) = gm02RecursiveCodeBound q)
    (hanswer : s.regs (gm02RecursiveControlBase q + 5) = answer)
    (hK : gm02RecursiveCodeBound q < 2 ^ w) (ha : answer < 2 ^ w) (hw : 3 < 2 ^ w) :
    ∃ s', GM02LoopPrefix w (.reg (gm02RecursiveControlBase q + 18))
        (gm02RecursiveMachineStepProg q) s s' 14 ∧
      s'.regs outReg = answer ∧ s'.regs (gm02RecursiveControlBase q + 18) = 3 ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ outReg → r ≠ gm02RecursiveControlBase q + 18 → s'.regs r = s.regs r) := by
  have hbg := gm02RecursiveControlBase_ge q
  let b := gm02RecursiveControlBase q
  let s₁ := s.setReg outReg answer
  let s₂ := s₁.setReg (b + 18) 3
  have he := gm02RecursiveScanProg_done_exec q s answer hcode hanswer hK ha hw
  have h1 : (.op .eq (.reg (b + 18)) (.const 1) : Expr).eval w s = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, b, hstate,
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w),
      checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have h2 : (.op .eq (.reg (b + 18)) (.const 2) : Expr).eval w s = some 1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, b, hstate,
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
  have heStep : Exec w (gm02RecursiveMachineStepProg q) s s₂ (3 + (3 + 7)) :=
    Exec.ite_false h1 (Exec.ite_true (v := 1) h2 (by decide) he)
  have hguard : (.reg (b + 18) : Expr).eval w s = some 2 := by
    simp [Expr.eval, b, hstate, checkWord_of_lt (by omega : 2 < 2 ^ w)]
  refine ⟨s₂, GM02LoopPrefix.single hguard (by decide) heStep, ?_, by simp [s₂, b], rfl, ?_⟩
  · exact (State.setReg_regs_ne _ _ (by dsimp only [b, outReg, Reg] at *; omega)).trans (by simp [s₁])
  · intro r hrout hrstate
    exact (State.setReg_regs_ne _ _ hrstate).trans (State.setReg_regs_ne _ _ hrout)

end GraphMinor.Compute
