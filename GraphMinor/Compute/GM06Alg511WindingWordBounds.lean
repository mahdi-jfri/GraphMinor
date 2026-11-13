module

public import GraphMinor.Compute.GM06Alg511WindingSetup
import Mathlib.Tactic

/-!
# Word bounds on the computed winding accumulators

The winding program of VI (5.11), page 134, clears both signed
accumulators before using them. Every later assignment is checked
by the RAM semantics. Therefore both final accumulators fit in a
word, even when the initial scratch registers were arbitrary. This
allows the scaled numerator to be formed with a fixed larger word
size without adding assumptions about computed values.
-/

public section
namespace GraphMinor.Compute

/-- A register that fits in a word continues to fit after any
successful RAM execution: every newly assigned word is checked. -/
theorem gm06Alg511Exec_reg_lt {w : ℕ} {c : Cmd} {s s' : State} {t r : ℕ}
    (he : Exec w c s s' t) (hr : s.regs r < 2 ^ w) : s'.regs r < 2 ^ w := by
  revert hr
  induction he with
  | skip => exact id
  | @assign target e st v hval =>
    intro hr
    by_cases h : r = target
    · subst r
      simpa using Expr.eval_lt hval
    · simpa only [State.setReg_regs_ne _ _ h] using hr
  | write _ _ _ => intro hr; simpa [State.writeArr] using hr
  | alloc _ => intro hr; simpa using hr
  | seq _ _ ih₁ ih₂ => intro hr; exact ih₂ (ih₁ hr)
  | ite_true _ _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_false _ => exact id
  | while_true _ _ _ _ ih₁ ih₂ => intro hr; exact ih₂ (ih₁ hr)

/-- Every value written by a successful assignment fits in its execution word. -/
theorem gm06Alg511Assigned_reg_lt {w r : ℕ} {e : Expr} {s s' : State} {t : ℕ}
    (he : Exec w (.assign r e) s s' t) : s'.regs r < 2 ^ w := by
  cases he with
  | assign hval => simpa using Expr.eval_lt hval

private theorem sum_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511TurnSumProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq hclear hrest =>
    have hp := gm06Alg511Assigned_reg_lt hclear
    have hpos := gm06Alg511Exec_reg_lt hrest (by simpa using hp)
    refine ⟨hpos, ?_⟩
    cases hrest with
    | seq hclear₂ hloop =>
      have hq := gm06Alg511Assigned_reg_lt hclear₂
      exact gm06Alg511Exec_reg_lt hloop (by simpa using hq)

private theorem path_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511PathTurnProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq _ hsuffix =>
    cases hsuffix with
    | seq _ hsum => exact sum_regs_lt hsum

private theorem trace_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511TraceTurnsProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq _ hsuffix =>
    cases hsuffix with
    | seq _ hpath => exact path_regs_lt hpath

/-- Both actual output accumulators of the complete winding phase
fit in its execution word size, without bounds on initial scratch. -/
theorem gm06Alg511InitialWindingProg_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511InitialWindingProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq _ hindex =>
    cases hindex with
    | seq htrace hscan =>
      obtain ⟨hp, hq⟩ := trace_regs_lt htrace
      exact ⟨gm06Alg511Exec_reg_lt hscan hp, gm06Alg511Exec_reg_lt hscan hq⟩

end GraphMinor.Compute
