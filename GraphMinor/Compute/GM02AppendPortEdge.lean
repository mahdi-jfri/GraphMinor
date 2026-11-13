module

public import GraphMinor.Compute.MultiDigraph
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Appending one edge to the split graph buffer

Use the existing two-word buffer push to append the pair in registers
60 and 61. Increment the emitted edge count in register 68. The next
free word position in register 67 and the unused zero suffix give an
exact buffer invariant for the canonical pair scan.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Append one ordered edge and increment the emitted edge count. -/
@[expose] def gm02AppendPortEdgeProg : Cmd :=
  .seq (bufPush2 24 67 60 61) (.assign 68 (.op .add (.reg 68) (.const 1)))

/-- One emitted edge takes at most eighteen steps and preserves all unrelated state. -/
theorem gm02AppendPortEdgeProg_exec {w rem u v m : ℕ} (pre : List ℕ) (s : State)
    (hbuf : s.arrs 24 = pre ++ List.replicate (rem + 2) 0)
    (hpos : s.regs 67 = pre.length) (hu : s.regs 60 = u) (hv : s.regs 61 = v)
    (hm : s.regs 68 = m) (hw : 2 < 2 ^ w) (hposw : pre.length + 2 < 2 ^ w)
    (huw : u < 2 ^ w) (hvw : v < 2 ^ w) (hmw : m + 1 < 2 ^ w) :
    ∃ s' t, Exec w gm02AppendPortEdgeProg s s' t ∧ t ≤ 18 ∧
      s'.arrs 24 = (pre ++ [u, v]) ++ List.replicate rem 0 ∧
      s'.regs 67 = (pre ++ [u, v]).length ∧ s'.regs 68 = m + 1 ∧
      (∀ a, a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 67 → r ≠ 68 → s'.regs r = s.regs r) := by
  obtain ⟨s₀, t₀, he₀, ht₀, hbuf₀, hpos₀, ha₀, hr₀⟩ :=
    bufPush2_exec 24 67 60 61 pre rem u v hw hposw huw hvw hbuf hpos hu hv
  let s₁ := s₀.setReg 68 (m + 1)
  have he₁ : Exec w (.assign 68 (.op .add (.reg 68) (.const 1))) s₀ s₁ 4 :=
    .assign (eval_add (eval_reg ((hr₀ 68 (by decide)).trans hm) (by omega))
      (eval_const (by omega)) hmw)
  refine ⟨s₁, t₀ + 4, .seq he₀ he₁, by omega, hbuf₀, ?_, State.setReg_regs_self .., ha₀, ?_⟩
  · exact (State.setReg_regs_ne s₀ (m + 1) (by decide : (67 : Reg) ≠ 68)).trans hpos₀
  · intro r hr67 hr68
    exact (State.setReg_regs_ne s₀ (m + 1) hr68).trans (hr₀ r hr67)

end GraphMinor.Compute
