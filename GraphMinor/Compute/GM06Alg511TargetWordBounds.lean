module

public import GraphMinor.Compute.GM06Alg511ReadNormalTarget
import GraphMinor.Compute.GM06Alg511WindingWordBounds

/-!
# Word bounds for the executed target reader

The orientation comparison of VI (5.11), page 134, multiplies the
normalized target words. Both numerator words are assigned in either
sign branch, and the denominator word is assigned before that branch.
Successful execution therefore bounds all three output words without
any assumptions about their old scratch contents.
-/

public section
namespace GraphMinor.Compute

private theorem pair_regs_lt {w : ℕ} {a b : Expr} {s s' : State} {t : ℕ}
    (he : Exec w (.seq (.assign 62 a) (.assign 63 b)) s s' t) :
    s'.regs 62 < 2 ^ w ∧ s'.regs 63 < 2 ^ w := by
  cases he with
  | seq hfirst hsecond =>
    exact ⟨gm06Alg511Exec_reg_lt hsecond (gm06Alg511Assigned_reg_lt hfirst),
      gm06Alg511Assigned_reg_lt hsecond⟩

private theorem branch_pair_regs_lt {w : ℕ} {cond a b c d : Expr}
    {s s' : State} {t : ℕ}
    (he : Exec w (.ite cond (.seq (.assign 62 a) (.assign 63 b))
      (.seq (.assign 62 c) (.assign 63 d))) s s' t) :
    s'.regs 62 < 2 ^ w ∧ s'.regs 63 < 2 ^ w := by
  cases he with
  | ite_true _ _ hbody => exact pair_regs_lt hbody
  | ite_false _ hbody => exact pair_regs_lt hbody

private theorem normalize_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511NormalizeTargetProg s s' t) :
    s'.regs 62 < 2 ^ w ∧ s'.regs 63 < 2 ^ w ∧ s'.regs 66 < 2 ^ w := by
  cases he with
  | seq hden hrest =>
    have hd := gm06Alg511Exec_reg_lt hrest (gm06Alg511Assigned_reg_lt hden)
    cases hrest with
    | seq hbranch hfinish =>
      have hpair := branch_pair_regs_lt hbranch
      exact ⟨gm06Alg511Exec_reg_lt hfinish hpair.1,
        gm06Alg511Exec_reg_lt hfinish hpair.2, hd⟩

/-- Every actual target-reader execution produces numerator and
denominator words that fit, irrespective of the initial scratch. -/
theorem gm06Alg511ReadNormalTargetProg_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511ReadNormalTargetProg s s' t) :
    s'.regs 62 < 2 ^ w ∧ s'.regs 63 < 2 ^ w ∧ s'.regs 66 < 2 ^ w := by
  cases he with
  | seq _ hrest =>
    cases hrest with
    | seq _ hrest₂ =>
      cases hrest₂ with
      | seq _ hnormalize => exact normalize_regs_lt hnormalize

end GraphMinor.Compute
