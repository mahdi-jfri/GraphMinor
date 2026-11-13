module

public import GraphMinor.Compute.GM02RecursiveComplexity
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Calling the proved path program in separate working memory

Shift the complete II (3.2) machine above the caller's arrays and decoded
slot registers. Run it on its ordinary encoded input and copy its
three-way answer into register 89. The shifted execution preserves all
low arrays and caller registers, including the outer candidate code.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Execute the actual path machine in shifted memory and return its flag in register 89. -/
@[expose] noncomputable def gm02ShiftedPathCallProg (q K : ℕ) : Cmd :=
  .seq ((gm02RecursiveMachineProg q).shift 1000 (1000 + 2 * K))
    (.assign 89 (.reg (outReg + (1000 + 2 * K))))

/-- The shifted call retains the complete path program's correctness and polynomial time. -/
theorem gm02ShiftedPathCallProg_exec {w : ℕ} (q K : ℕ) (hq : 1 ≤ q)
    (x : GM02SimpleTerminatedInput) (s : State)
    (hsrc : s.arrs (inArr + 1000) = x.enc) (hindex : x.A.index ≤ 3 * q)
    (hword : wordSize (gm02RecursiveWordConstant q) x.n ≤ w) (hw : 3 < 2 ^ w) :
    ∃ s' t, Exec w (gm02ShiftedPathCallProg q K) s s' t ∧
      t ≤ gm02RecursivePolynomialCoefficient q * (x.n + 1) ^ gm02RecursivePolynomialExponent q + 2 ∧
      ((s'.regs 89 = 1 ∧ x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
        (s'.regs 89 = 0 ∧ ¬x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
        (s'.regs 89 = 2 ∧ q ≤ x.width)) ∧
      (∀ a, a < 1000 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 1000 + 2 * K → r ≠ 89 → s'.regs r = s.regs r) := by
  obtain ⟨sub, t, he, ht, hcorrect⟩ := gm02RecursiveMachineProg_exec q x
    (s.unshift 1000 (1000 + 2 * K)) hsrc hindex hword
  let s₀ := s.applyShifted 1000 (1000 + 2 * K) sub
  have he₀ : Exec w ((gm02RecursiveMachineProg q).shift 1000 (1000 + 2 * K)) s s₀ t :=
    Exec.shift_from 1000 (1000 + 2 * K) he
  have hflag : sub.regs outReg ≤ 2 := by
    rcases hcorrect with h | h | h <;> omega
  let s₁ := s₀.setReg 89 (sub.regs outReg)
  have hreg : s₀.regs (outReg + (1000 + 2 * K)) = sub.regs outReg :=
    State.applyShifted_regs_add ..
  have he₁ : Exec w (.assign 89 (.reg (outReg + (1000 + 2 * K)))) s₀ s₁ 2 :=
    .assign (eval_reg hreg (by omega))
  refine ⟨s₁, t + 2, .seq he₀ he₁, ?_, ?_, ?_, ?_⟩
  · exact Nat.add_le_add_right (ht.trans (gm02RecursiveMachineTime_polynomial q hq x)) 2
  · have hret : s₁.regs 89 = sub.regs outReg := State.setReg_regs_self ..
    rcases hcorrect with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)
  · intro a ha
    exact State.applyShifted_arrs_lt 1000 (1000 + 2 * K) s sub ha
  · intro r hr hr89
    exact (State.setReg_regs_ne s₀ (sub.regs outReg) hr89).trans
      (State.applyShifted_regs_lt 1000 (1000 + 2 * K) s sub hr)

end GraphMinor.Compute
