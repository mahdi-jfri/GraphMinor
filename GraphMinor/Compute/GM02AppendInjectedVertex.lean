module

public import GraphMinor.Compute.Basic
import GraphMinor.Compute.Algorithm44ModelBridge
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Appending one host vertex to the labelled input

The host-order scan stores its current vertex at the next unused buffer
position and advances that position. The buffer retains its fixed
capacity and all registers except the output position stay unchanged.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Append the host scan register to the vertex buffer and advance its used position. -/
@[expose] def gm02AppendInjectedVertexProg : Cmd :=
  .seq (.write 29 (.reg 195) (.reg 194))
    (.assign 195 (.op .add (.reg 195) (.const 1)))

/-- One vertex append takes seven steps and preserves the scan counter and decoded slots. -/
theorem gm02AppendInjectedVertexProg_exec {W : ℕ} (s : State) (pre : List ℕ) (rem v : ℕ)
    (hw : 1 < 2 ^ W) (hposw : pre.length + 1 < 2 ^ W) (hvw : v < 2 ^ W)
    (hbuf : s.arrs 29 = pre ++ List.replicate (rem + 1) 0)
    (hpos : s.regs 195 = pre.length) (hv : s.regs 194 = v) :
    ∃ s', Exec W gm02AppendInjectedVertexProg s s' 7 ∧
      s'.arrs 29 = (pre ++ [v]) ++ List.replicate rem 0 ∧
      s'.regs 195 = (pre ++ [v]).length ∧
      (∀ a, a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 195 → s'.regs r = s.regs r) := by
  let s₁ := s.writeArr 29 pre.length v
  have hi : pre.length < (s.arrs 29).length := by simp only [hbuf, List.length_append, List.length_replicate]; omega
  have he₁ : Exec W (.write 29 (.reg 195) (.reg 194)) s s₁ 3 :=
    .write (eval_reg hpos (by omega)) (eval_reg hv hvw) hi
  let s₂ := s₁.setReg 195 (pre.length + 1)
  have he₂ : Exec W (.assign 195 (.op .add (.reg 195) (.const 1))) s₁ s₂ 4 :=
    .assign (eval_add (eval_reg hpos (by omega)) (eval_const hw) hposw)
  refine ⟨s₂, .seq he₁ he₂, ?_, ?_, ?_, ?_⟩
  · change (s.arrs 29).set pre.length v = _
    rw [hbuf]
    exact set_append_replicate_succ pre rem v
  · simpa only [List.length_append, List.length_singleton] using State.setReg_regs_self s₁ 195 (pre.length + 1)
  · intro a ha
    exact State.writeArr_arrs_ne s pre.length v ha
  · intro r hr
    exact State.setReg_regs_ne s₁ (pre.length + 1) hr

end GraphMinor.Compute
