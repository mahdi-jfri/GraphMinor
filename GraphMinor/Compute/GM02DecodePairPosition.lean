module

public import GraphMinor.Compute.GM02RowMajorPairs
public import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Decoding a position of the canonical pair scan on the RAM

Divide the scan index by the numeric vertex count and take its
remainder. The canonical finite-product numbering identifies the two
results with the next ordered pair. A nonempty scan position guarantees
a nonzero divisor, including when the overall algorithm permits an empty
graph.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Decode pair position 64 using vertex count 66 into the pair registers. -/
@[expose] def gm02DecodePairPositionProg : Cmd :=
  .seq (.assign 60 (.op .div (.reg 64) (.reg 66)))
    (.assign 61 (.op .mod (.reg 64) (.reg 66)))

/-- The pair decoder executes in eight steps and returns the exact canonical pair. -/
theorem gm02DecodePairPositionProg_exec {w n : ℕ} (i : Fin (n * n)) (s : State)
    (hi : s.regs 64 = i.val) (hn : s.regs 66 = n)
    (hiw : i.val < 2 ^ w) (hnw : n < 2 ^ w) :
    ∃ s', Exec w gm02DecodePairPositionProg s s' 8 ∧
      s'.regs 60 = (finProdFinEquiv.symm i : Fin n × Fin n).1.val ∧
      s'.regs 61 = (finProdFinEquiv.symm i : Fin n × Fin n).2.val ∧
      s'.arrs = s.arrs ∧ (∀ r, r ≠ 60 → r ≠ 61 → s'.regs r = s.regs r) := by
  have hn0 : n ≠ 0 := by
    intro hz
    have hlt := i.isLt
    simp only [hz, Nat.mul_zero, Nat.not_lt_zero] at hlt
  have hdw : i.val / n < 2 ^ w := (finProdFinEquiv.symm i : Fin n × Fin n).1.isLt.trans hnw
  have hmw : i.val % n < 2 ^ w := (finProdFinEquiv.symm i : Fin n × Fin n).2.isLt.trans hnw
  let s₀ := s.setReg 60 (i.val / n)
  have he₀ : Exec w (.assign 60 (.op .div (.reg 64) (.reg 66))) s s₀ 4 :=
    .assign (eval_div (eval_reg hi hiw) (eval_reg hn hnw) hn0 hdw)
  let s₁ := s₀.setReg 61 (i.val % n)
  have hem : (Expr.op .mod (.reg 64) (.reg 66)).eval w s₀ = some (i.val % n) := by
    have hi₀ := eval_reg ((State.setReg_regs_ne s (i.val / n) (by decide : (64 : Reg) ≠ 60)).trans hi) hiw
    have hn₀ := eval_reg ((State.setReg_regs_ne s (i.val / n) (by decide : (66 : Reg) ≠ 60)).trans hn) hnw
    change (match (Expr.reg 64).eval w s₀, (Expr.reg 66).eval w s₀ with
      | some a, some b => BinOp.mod.eval w a b
      | _, _ => none) = _
    rw [hi₀, hn₀]
    simp only [BinOp.eval, BinOp.raw, hn0, ↓reduceIte, checkWord_of_lt hmw]
  have he₁ : Exec w (.assign 61 (.op .mod (.reg 64) (.reg 66))) s₀ s₁ 4 := .assign hem
  refine ⟨s₁, .seq he₀ he₁, ?_, State.setReg_regs_self .., rfl, ?_⟩
  · exact State.setReg_regs_ne s₀ (i.val % n) (by decide : (60 : Reg) ≠ 61) |>.trans (State.setReg_regs_self ..)
  · intro r hr60 hr61
    exact (State.setReg_regs_ne s₀ (i.val % n) hr61).trans (State.setReg_regs_ne s (i.val / n) hr60)

end GraphMinor.Compute
