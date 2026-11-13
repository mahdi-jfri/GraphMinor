module

public import GraphMinor.Compute.GM02CodeExpressions
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the complete code enumeration

Read the supplied host edge count as the digit base parameter. Compute
the fixed power giving the candidate range and store it in register 191.
Start the code counter and answer accumulator at zero. All arrays and
original input-header registers are preserved.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Compute the code limit and initialize the outer enumeration counters. -/
@[expose] def gm02InitPortCodeScanProg (K : ℕ) : Cmd :=
  .seq (.assign 40 (.reg 11))
    (.seq (.assign 191 (gm02PowerExpr gm02CodeBaseExpr (2 * K)))
      (.seq (.assign 190 (.const 0)) (.assign 192 (.const 0))))

/-- Code-scan initialization computes its exact fixed-power limit in time depending only on `K`. -/
theorem gm02InitPortCodeScanProg_exec {w m K : ℕ} (s : State)
    (hm : s.regs 11 = m) (hw : 1 < 2 ^ w) (hmw : m + 1 < 2 ^ w)
    (hpow : (m + 1) ^ (2 * K) < 2 ^ w) :
    ∃ s', Exec w (gm02InitPortCodeScanProg K) s s' (8 + 8 * K) ∧
      s'.regs 190 = 0 ∧ s'.regs 191 = (m + 1) ^ (2 * K) ∧ s'.regs 192 = 0 ∧
      s'.arrs = s.arrs ∧ (∀ r, r ∉ [40, 190, 191, 192] → s'.regs r = s.regs r) := by
  let s₀ := s.setReg 40 m
  have he₀ : Exec w (.assign 40 (.reg 11)) s s₀ 2 := .assign (eval_reg hm (by omega))
  have hbase : gm02CodeBaseExpr.eval w s₀ = some (m + 1) :=
    eval_add (eval_reg (State.setReg_regs_self ..) (by omega)) (eval_const hw) hmw
  have hpower := gm02PowerExpr_eval gm02CodeBaseExpr (2 * K) s₀ (by omega) hbase hpow
  let s₁ := s₀.setReg 191 ((m + 1) ^ (2 * K))
  have he₁ : Exec w (.assign 191 (gm02PowerExpr gm02CodeBaseExpr (2 * K))) s₀ s₁ (2 + 8 * K) := by
    convert (Exec.assign (r := 191) hpower) using 1
    simp only [gm02PowerExpr_cost, gm02CodeBaseExpr, Expr.cost]
    omega
  let s₂ := s₁.setReg 190 0
  let s₃ := s₂.setReg 192 0
  have he₂ : Exec w (.assign 190 (.const 0)) s₁ s₂ 2 := .assign (eval_const (by omega))
  have he₃ : Exec w (.assign 192 (.const 0)) s₂ s₃ 2 := .assign (eval_const (by omega))
  refine ⟨s₃, ?_, ?_, ?_, State.setReg_regs_self .., rfl, ?_⟩
  · convert (Exec.seq he₀ (.seq he₁ (.seq he₂ he₃))) using 1 <;> first | rfl | omega
  · simp [s₃, s₂]
  · simp [s₃, s₂, s₁]
  · intro r hrnot
    have hne (a : ℕ) (ha : a ∈ [40, 190, 191, 192]) : r ≠ a := fun h => hrnot (h.symm ▸ ha)
    simp only [s₃, s₂, s₁, s₀, State.setReg_regs_ne _ _ (hne 192 (by decide)),
      State.setReg_regs_ne _ _ (hne 190 (by decide)), State.setReg_regs_ne _ _ (hne 191 (by decide)),
      State.setReg_regs_ne _ _ (hne 40 (by decide))]

end GraphMinor.Compute
