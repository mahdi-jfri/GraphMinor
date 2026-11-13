module

public import GraphMinor.Compute.GM02RecursiveReturnProgram

/-!
# Returning at the root

With no saved parent, the return command stops the recursive loop. It
preserves the completed answer and every array, changing only the loop's
run-state word.
-/

public section
namespace GraphMinor.Compute

/-- An empty saved stack causes the recursive return command to halt. -/
theorem gm02RecursiveReturnProg_root_exec {w : ℕ} (q : ℕ) (s : State)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = 0) (hw : 1 < 2 ^ w) :
    Exec w (gm02RecursiveReturnProg q) s
      (s.setReg (gm02RecursiveControlBase q + 18) 0) 5 := by
  have hg : (.op .eq (.reg (gm02RecursiveControlBase q + 10)) (.const 0) : Expr).eval w s = some 1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hpos,
      checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt hw]
  have he : Exec w (.assign (gm02RecursiveControlBase q + 18) (.const 0)) s
      (s.setReg (gm02RecursiveControlBase q + 18) 0) 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  exact Exec.ite_true (v := 1) hg (by decide) he

end GraphMinor.Compute
