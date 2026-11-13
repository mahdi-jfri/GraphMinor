module

public import GraphMinor.Compute.GM02InjectionTests

/-!
# A RAM validator for decoded vertex injections

Combine the fixed bounds and distinctness tests into one Boolean
expression and store its value. The expression has fixed cost for a
fixed pattern, preserves every array, and changes only its result register.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- The fixed expression checking all decoded vertex choices. -/
@[expose] def gm02InjectionValidExpr (p : ℕ) : Expr :=
  gm02BooleanConjunction ((gm02InjectionTests p).map gm02InjectionTestExpr)

/-- Store the injection validity bit in register 193. -/
@[expose] def gm02ValidateInjectionProg (p : ℕ) : Cmd :=
  .assign 193 (gm02InjectionValidExpr p)

/-- The validator computes precisely code validity, at fixed cost and with complete array preservation. -/
theorem gm02ValidateInjectionProg_exec {W n code : ℕ} (p : ℕ) (s : State)
    (hw : 1 < 2 ^ W) (hn : n + 1 < 2 ^ W) (hrn : s.regs 40 = n)
    (hslots : ∀ i : Fin p, s.regs (200 + i.val) = gm02InjectionDigit n p code i) :
    ∃ s', Exec W (gm02ValidateInjectionProg p) s s' ((gm02InjectionValidExpr p).cost + 1) ∧
      s'.regs 193 = (if gm02InjectionCodeValid n p code then 1 else 0) ∧
      s'.arrs = s.arrs ∧ (∀ r, r ≠ 193 → s'.regs r = s.regs r) := by
  have hd (i : Fin p) : gm02InjectionDigit n p code i < 2 ^ W :=
    (gm02SeparatorDigit_le n code i.val).trans_lt (by omega)
  have he := gm02BooleanConjunction_eval s (gm02InjectionTests p) gm02InjectionTestExpr
    (gm02InjectionTestHolds n (gm02InjectionDigit n p code)) hw
    (fun t _ => gm02InjectionTestExpr_eval n _ s hw (by omega) hd hslots hrn t)
  have hv : (gm02InjectionValidExpr p).eval W s =
      some (if gm02InjectionCodeValid n p code then 1 else 0) := by
    simpa only [gm02InjectionValidExpr, gm02InjectionTests_iff] using he
  refine ⟨s.setReg 193 (if gm02InjectionCodeValid n p code then 1 else 0),
    Exec.assign hv, State.setReg_regs_self .., rfl, ?_⟩
  intro r hr
  exact State.setReg_regs_ne s _ hr

end GraphMinor.Compute
