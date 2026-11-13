module

public import GraphMinor.Compute.GM02EdgeListInput
public import GraphMinor.Compute.GM02CodeExpressions
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the injection search from the host encoding

Read the host vertex count directly from the first input word. Compute
the fixed power giving the injection-code range and clear the code
counter and result accumulator. The original graph array is unchanged.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read the host count and initialize the complete injection-code scan. -/
@[expose] def gm02InitInjectionScanProg (p : ℕ) : Cmd :=
  .seq (.assign 40 (.read inArr (.const 0)))
    (.seq (.assign 191 (gm02PowerExpr gm02CodeBaseExpr p))
      (.seq (.assign 190 (.const 0)) (.assign 192 (.const 0))))

/-- Initialization derives the exact scan controls from the plain graph input. -/
theorem gm02InitInjectionScanProg_exec {W : ℕ} (G : GM02EdgeListInput) (p : ℕ) (s : State)
    (hsrc : s.arrs inArr = G.enc) (hw : 1 < 2 ^ W)
    (hn : G.n + 1 < 2 ^ W) (hpow : (G.n + 1) ^ p < 2 ^ W) :
    ∃ s', Exec W (gm02InitInjectionScanProg p) s s' (9 + 4 * p) ∧
      s'.regs 190 = 0 ∧ s'.regs 191 = (G.n + 1) ^ p ∧ s'.regs 192 = 0 ∧
      s'.regs 40 = G.n ∧ s'.arrs = s.arrs := by
  let s₀ := s.setReg 40 G.n
  have he₀ : Exec W (.assign 40 (.read inArr (.const 0))) s s₀ 3 := by
    apply Exec.assign
    simp [Expr.eval, hsrc, GM02EdgeListInput.enc, checkWord_of_lt (by omega : 0 < 2 ^ W),
      checkWord_of_lt (by omega : G.n < 2 ^ W)]
  have hbase : gm02CodeBaseExpr.eval W s₀ = some (G.n + 1) :=
    eval_add (eval_reg (State.setReg_regs_self ..) (by omega)) (eval_const hw) hn
  have hpower := gm02PowerExpr_eval gm02CodeBaseExpr p s₀ (by omega) hbase hpow
  let s₁ := s₀.setReg 191 ((G.n + 1) ^ p)
  have he₁ : Exec W (.assign 191 (gm02PowerExpr gm02CodeBaseExpr p)) s₀ s₁ (2 + 4 * p) := by
    convert Exec.assign (r := 191) hpower using 1
    simp only [gm02PowerExpr_cost, gm02CodeBaseExpr, Expr.cost]
    omega
  let s₂ := s₁.setReg 190 0
  let s₃ := s₂.setReg 192 0
  have he₂ : Exec W (.assign 190 (.const 0)) s₁ s₂ 2 := .assign (eval_const (by omega))
  have he₃ : Exec W (.assign 192 (.const 0)) s₂ s₃ 2 := .assign (eval_const (by omega))
  refine ⟨s₃, ?_, ?_, ?_, State.setReg_regs_self .., ?_, rfl⟩
  · convert Exec.seq he₀ (.seq he₁ (.seq he₂ he₃)) using 1 <;> first | rfl | omega
  · simp [s₃, s₂]
  · simp [s₃, s₂, s₁]
  · simp [s₃, s₂, s₁, s₀]

end GraphMinor.Compute
