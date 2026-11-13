module

public import GraphMinor.Compute.GM02ChoicePairExpr
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Saving the first endpoint's validation data

Before checking the second endpoint, save the first incidence bit, chosen
host position, and required vertex in registers 47, 48, and 49. Three
assignments retain all arrays and every other register.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Preserve the first checked endpoint for the final pair test. -/
@[expose] def gm02SaveFirstChoiceProg : Cmd :=
  .seq (.assign 47 (.reg 46)) (.seq (.assign 48 (.reg 32)) (.assign 49 (.reg 45)))

/-- Saving the first endpoint takes exactly six steps and has an exact register frame. -/
theorem gm02SaveFirstChoiceProg_exec {w bit e v : ℕ} (s : State)
    (hb : s.regs 46 = bit) (he : s.regs 32 = e) (hv : s.regs 45 = v)
    (hbw : bit < 2 ^ w) (hew : e < 2 ^ w) (hvw : v < 2 ^ w) :
    ∃ s', Exec w gm02SaveFirstChoiceProg s s' 6 ∧
      s'.regs 47 = bit ∧ s'.regs 48 = e ∧ s'.regs 49 = v ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ 47 → r ≠ 48 → r ≠ 49 → s'.regs r = s.regs r) := by
  let s₁ := s.setReg 47 bit
  let s₂ := s₁.setReg 48 e
  let s₃ := s₂.setReg 49 v
  have he₁ : Exec w (.assign 47 (.reg 46)) s s₁ 2 := .assign (eval_reg hb hbw)
  have he₂ : Exec w (.assign 48 (.reg 32)) s₁ s₂ 2 :=
    .assign (eval_reg ((State.setReg_regs_ne s bit (by decide : (32 : Reg) ≠ 47)).trans he) hew)
  have he₃ : Exec w (.assign 49 (.reg 45)) s₂ s₃ 2 :=
    .assign (eval_reg (by simpa [s₂, s₁] using hv) hvw)
  refine ⟨s₃, .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, rfl, ?_⟩
  · simp [s₃, s₂, s₁]
  · simp [s₃, s₂]
  · exact State.setReg_regs_self ..
  · intro r hr47 hr48 hr49
    exact (State.setReg_regs_ne s₂ v hr49).trans
      ((State.setReg_regs_ne s₁ e hr48).trans (State.setReg_regs_ne s bit hr47))

end GraphMinor.Compute
