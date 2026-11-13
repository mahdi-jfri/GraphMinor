module

public import GraphMinor.Compute.GM02RecursiveMachineProgram
public import GraphMinor.Compute.GM02LoopPrefix

/-!
# Operational rules for the three recursive loop states

Lift an execution of an enter, scan, or return command through the
machine's fixed state dispatch and its loop guard. These are execution
composition rules, recording the exact constant dispatch cost. The
underlying command still has to be executed by its own proved rule.
-/

public section
namespace GraphMinor.Compute

private theorem control_eq_eval {w : ℕ} (q : ℕ) (s : State) (tag c : ℕ)
    (hs : s.regs (gm02RecursiveControlBase q + 18) = tag)
    (ht : tag < 2 ^ w) (hc : c < 2 ^ w) (hw : 1 < 2 ^ w) :
    (.op .eq (.reg (gm02RecursiveControlBase q + 18)) (.const c) : Expr).eval w s =
      some (if tag = c then 1 else 0) := by
  by_cases he : tag = c <;>
    simp [Expr.eval, BinOp.eval, BinOp.raw, hs, checkWord_of_lt ht, checkWord_of_lt hc,
      he, checkWord_of_lt hw, checkWord_of_lt (by omega : 0 < 2 ^ w)]

/-- Lift an enter-command execution to one guarded loop iteration. -/
theorem gm02RecursiveLoop_enter {w t : ℕ} (q : ℕ) {s s' : State}
    (hs : s.regs (gm02RecursiveControlBase q + 18) = 1) (hw : 3 < 2 ^ w)
    (he : Exec w (gm02RecursiveEnterProg q) s s' t) :
    GM02LoopPrefix w (.reg (gm02RecursiveControlBase q + 18)) (gm02RecursiveMachineStepProg q)
      s s' (4 + t) := by
  have h1 := control_eq_eval (w := w) q s 1 1 hs (by omega) (by omega) (by omega)
  have hguard : (.reg (gm02RecursiveControlBase q + 18) : Expr).eval w s = some 1 := by
    simp [Expr.eval, hs, checkWord_of_lt (by omega : 1 < 2 ^ w)]
  have hstep : Exec w (gm02RecursiveMachineStepProg q) s s' (3 + t) :=
    Exec.ite_true (v := 1) h1 (by decide) he
  simpa only [Expr.cost_reg, ← Nat.add_assoc] using GM02LoopPrefix.single hguard (by decide) hstep

/-- Lift a scan-command execution through both state-dispatch tests. -/
theorem gm02RecursiveLoop_scan {w t : ℕ} (q : ℕ) {s s' : State}
    (hs : s.regs (gm02RecursiveControlBase q + 18) = 2) (hw : 3 < 2 ^ w)
    (he : Exec w (gm02RecursiveScanProg q) s s' t) :
    GM02LoopPrefix w (.reg (gm02RecursiveControlBase q + 18)) (gm02RecursiveMachineStepProg q)
      s s' (7 + t) := by
  have h1 := control_eq_eval (w := w) q s 2 1 hs (by omega) (by omega) (by omega)
  have h2 := control_eq_eval (w := w) q s 2 2 hs (by omega) (by omega) (by omega)
  have hguard : (.reg (gm02RecursiveControlBase q + 18) : Expr).eval w s = some 2 := by
    simp [Expr.eval, hs, checkWord_of_lt (by omega : 2 < 2 ^ w)]
  have hstep : Exec w (gm02RecursiveMachineStepProg q) s s' (3 + (3 + t)) :=
    Exec.ite_false h1 (Exec.ite_true (v := 1) h2 (by decide) he)
  simpa only [Expr.cost_reg, ← Nat.add_assoc] using GM02LoopPrefix.single hguard (by decide) hstep

/-- Lift a return-command execution through both state-dispatch tests. -/
theorem gm02RecursiveLoop_return {w t : ℕ} (q : ℕ) {s s' : State}
    (hs : s.regs (gm02RecursiveControlBase q + 18) = 3) (hw : 3 < 2 ^ w)
    (he : Exec w (gm02RecursiveReturnProg q) s s' t) :
    GM02LoopPrefix w (.reg (gm02RecursiveControlBase q + 18)) (gm02RecursiveMachineStepProg q)
      s s' (7 + t) := by
  have h1 := control_eq_eval (w := w) q s 3 1 hs hw (by omega) (by omega)
  have h2 := control_eq_eval (w := w) q s 3 2 hs hw (by omega) (by omega)
  have hguard : (.reg (gm02RecursiveControlBase q + 18) : Expr).eval w s = some 3 := by
    simp [Expr.eval, hs, checkWord_of_lt hw]
  have hstep : Exec w (gm02RecursiveMachineStepProg q) s s' (3 + (3 + t)) :=
    Exec.ite_false h1 (Exec.ite_false h2 he)
  simpa only [Expr.cost_reg, ← Nat.add_assoc] using GM02LoopPrefix.single hguard (by decide) hstep

end GraphMinor.Compute
