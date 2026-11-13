module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Retaining a candidate code's answer

An empty accumulated answer is zero. Read the candidate flag from
register 89. Retain a positive answer in register 192, and leave an
infeasible zero answer unchanged. The command computes the same flag in
either case and changes no other register or array.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Store a positive candidate answer in the previously empty accumulator. -/
@[expose] def gm02AccumulateCodeFlagProg : Cmd :=
  .ite (.op .lt (.const 0) (.reg 89)) (.assign 192 (.reg 89)) .skip

/-- Accumulation copies a candidate's zero, one, or two flag in at most five steps. -/
theorem gm02AccumulateCodeFlagProg_exec {w flag : ℕ} (s : State)
    (hflag : s.regs 89 = flag) (hbound : flag ≤ 2) (hzero : s.regs 192 = 0) (hw : 3 < 2 ^ w) :
    ∃ s' t, Exec w gm02AccumulateCodeFlagProg s s' t ∧ t ≤ 5 ∧
      s'.regs 192 = flag ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ 192 → s'.regs r = s.regs r) := by
  have hword : flag < 2 ^ w := by omega
  have hguard := eval_lt (eval_const (by omega : 0 < 2 ^ w)) (eval_reg hflag hword) (by omega)
  by_cases hpos : 0 < flag
  · let s₀ := s.setReg 192 flag
    have he : Exec w (.assign 192 (.reg 89)) s s₀ 2 := .assign (eval_reg hflag hword)
    have hg : (Expr.op .lt (.const 0) (.reg 89)).eval w s = some 1 := by
      simpa only [hpos, ↓reduceIte] using hguard
    exact ⟨s₀, 5, .ite_true hg (by decide) he, le_rfl, State.setReg_regs_self ..,
      rfl, fun r hr => State.setReg_regs_ne s flag hr⟩
  · have hf : flag = 0 := Nat.eq_zero_of_not_pos hpos
    have hg : (Expr.op .lt (.const 0) (.reg 89)).eval w s = some 0 := by
      simpa only [hpos, ↓reduceIte] using hguard
    exact ⟨s, 4, .ite_false hg (.skip s), by decide, hzero.trans hf.symm,
      rfl, fun _ _ => rfl⟩

end GraphMinor.Compute
