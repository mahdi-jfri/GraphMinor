module

public import GraphMinor.Compute.GM06Alg34Between

/-!
# Cyclic intervals with computed position expressions

The dual division uses even positions for primal vertices and odd
positions for boundary gaps. Evaluate these positions directly in the
interval command, rather than storing extra position arrays. The proof
uses the two possible cyclic interval shapes and bounds the work by
the costs of the three supplied expressions.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test a cyclic interval whose three positions are computed expressions. -/
def gm06BetweenExpressionsProg (rd : ℕ) (ei ej et : Expr) : Cmd :=
  .ite (exprLt ei ej)
    (.assign rd (exprAnd (exprLt ei et) (exprLt et ej)))
    (.assign rd (exprOr (exprLt ei et) (exprLt et ej)))

/-- The expression-based interval test has the exact cyclic meaning
and costs at most twice the total position-expression cost plus seven. -/
theorem gm06BetweenExpressionsProg_exec {w rd i j k : ℕ} {s : State}
    (ei ej et : Expr) (hw : 2 < 2 ^ w)
    (hei : ei.eval w s = some i) (hej : ej.eval w s = some j) (het : et.eval w s = some k) :
    ∃ t, Exec w (gm06BetweenExpressionsProg rd ei ej et) s
      (s.setReg rd (if GM06DrawingData.cyclicBetween i j k then 1 else 0)) t ∧
      t ≤ 2 * (ei.cost + ej.cost + et.cost) + 7 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hc := eval_exprLt hw1 hei hej
  have ha := eval_exprLt hw1 hei het
  have hb := eval_exprLt hw1 het hej
  by_cases hij : i < j
  · have hflag : (if GM06DrawingData.cyclicBetween i j k then (1 : ℕ) else 0) =
        if i < k ∧ k < j then 1 else 0 := by
      simp [GM06DrawingData.cyclicBetween, hij]
    rw [hflag]
    refine ⟨_, .ite_true (by simpa only [if_pos hij] using hc) (by decide)
      (.assign (eval_exprAnd hw1 ha hb)), ?_⟩
    simp only [exprLt, exprAnd, Expr.cost]
    omega
  · have hflag : (if GM06DrawingData.cyclicBetween i j k then (1 : ℕ) else 0) =
        if i < k ∨ k < j then 1 else 0 := by
      simp [GM06DrawingData.cyclicBetween, hij]
    rw [hflag]
    refine ⟨_, .ite_false (by simpa only [if_neg hij] using hc)
      (.assign (eval_exprOr hw ha hb)), ?_⟩
    simp only [exprLt, exprOr, Expr.cost]
    omega

end GraphMinor.Compute
