module

public import GraphMinor.Compute.GM06Alg511OrientCompare
import Mathlib.Tactic

/-!
# The winding value in every executed orientation branch

For VI (5.11), page 134, the orientation branch either retains the
current signed pair or exchanges its two words. Invert successful
RAM executions to identify these scalar results without assumptions
on scratch contents. This lets a linkage already constructed by the
preceding program be retained through the orientation phase.
-/

public section
namespace GraphMinor.Compute

private theorem assign_reg_eq {w a b : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w (.assign a (.reg b)) s s' t) : s' = s.setReg a (s.regs b) := by
  cases he with
  | assign h =>
    have hv := (checkWord_eq_some.mp h).2
    rw [← hv]

private theorem assign_const_value {w a v : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w (.assign a (.const v)) s s' t) : s'.regs a = v := by
  cases he with
  | assign h =>
    have hv := (checkWord_eq_some.mp h).2
    simpa using hv.symm

private theorem swap_values {w a b tmp : ℕ} {s s' : State} {t : ℕ}
    (hab : a ≠ b) (hta : tmp ≠ a) (htb : tmp ≠ b)
    (he : Exec w (gm06Alg511SwapWordsProg a b tmp) s s' t) :
    s'.regs a = s.regs b ∧ s'.regs b = s.regs a := by
  cases he with
  | seq hfirst hrest =>
    cases hrest with
    | seq hsecond hthird =>
      have h₁ := assign_reg_eq hfirst
      have h₂ := assign_reg_eq hsecond
      have h₃ := assign_reg_eq hthird
      rw [h₂, h₁] at h₃
      rw [h₃]
      simp [hab, hta, htb.symm]

private theorem flip_values {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511FlipScalarsProg s s' t) :
    s'.regs 54 = s.regs 55 ∧ s'.regs 55 = s.regs 54 ∧ s'.regs 57 = 1 := by
  cases he with
  | seq hswap hrest =>
    obtain ⟨hp, hq⟩ := swap_values (by decide) (by decide) (by decide) hswap
    refine ⟨(hrest.regs_eq_of_not_mem_writtenRegs (by decide)).trans hp,
      (hrest.regs_eq_of_not_mem_writtenRegs (by decide)).trans hq, ?_⟩
    cases hrest with
    | seq _ hlast =>
      cases hlast with
      | seq _ hmode => exact assign_const_value hmode

private theorem keep_mode {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511KeepTablesProg s s' t) : s'.regs 57 = 0 := by
  cases he with
  | seq _ hrest =>
    cases hrest with
    | seq _ hrest =>
      cases hrest with
      | seq _ hscalars =>
        cases hscalars with
        | seq _ hmode => exact assign_const_value hmode

private theorem branch_values {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511OrientBranchProg s s' t) :
    ∃ flip : Bool, s'.regs 57 = (if flip then 1 else 0) ∧
      s'.regs 54 = (if flip then s.regs 55 else s.regs 54) ∧
      s'.regs 55 = (if flip then s.regs 54 else s.regs 55) := by
  cases he with
  | ite_true _ _ hflip =>
    cases hflip with
    | seq htables hscalars =>
      obtain ⟨hp, hq, hmode⟩ := flip_values hscalars
      refine ⟨true, hmode, ?_, ?_⟩
      · exact hp.trans (htables.regs_eq_of_not_mem_writtenRegs (by decide))
      · exact hq.trans (htables.regs_eq_of_not_mem_writtenRegs (by decide))
  | ite_false _ hkeep =>
    exact ⟨false, keep_mode hkeep,
      hkeep.regs_eq_of_not_mem_writtenRegs (by decide),
      hkeep.regs_eq_of_not_mem_writtenRegs (by decide)⟩

/-- Every successful orientation execution retains or negates the
current winding exactly as recorded by its actual output mode bit. -/
theorem gm06Alg511OrientCompareProg_value {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511OrientCompareProg s s' t) :
    ∃ flip : Bool, s'.regs 57 = (if flip then 1 else 0) ∧
      gm06Alg511CurrentValue s' =
        (if flip then -gm06Alg511CurrentValue s else gm06Alg511CurrentValue s) := by
  cases he with
  | seq hcompare hbranch =>
    obtain ⟨flip, hmode, hp, hq⟩ := branch_values hbranch
    have hk := (hbranch.regs_eq_of_not_mem_writtenRegs (by decide : 52 ∉
      gm06Alg511OrientBranchProg.writtenRegs)).trans
      (hcompare.regs_eq_of_not_mem_writtenRegs (by decide))
    have hp₀ := hcompare.regs_eq_of_not_mem_writtenRegs (by decide : 54 ∉
      gm06Alg511CompareWindingProg.writtenRegs)
    have hq₀ := hcompare.regs_eq_of_not_mem_writtenRegs (by decide : 55 ∉
      gm06Alg511CompareWindingProg.writtenRegs)
    refine ⟨flip, hmode, ?_⟩
    dsimp only [gm06Alg511CurrentValue]
    rw [hp, hq, hk, hp₀, hq₀]
    cases flip with
    | false => rfl
    | true =>
      change ((s.regs 55 : ℝ) - s.regs 54) / s.regs 52 =
        -(((s.regs 54 : ℝ) - s.regs 55) / s.regs 52)
      ring

end GraphMinor.Compute
