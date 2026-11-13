module

public import GraphMinor.Compute.GM06Alg34CrossExpr

/-!
# Computing a cyclic interval flag

The crossing test in Graph Minors VI (3.4), page 121, compares two
positions with a cyclic interval. A conditional separates an interval
that wraps around the end of the cuff list from one that does not.
Only the destination register changes, and the cost is constant.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Store the cyclic-interval test for the three supplied position registers. -/
def gm06BetweenProg (rd ri rj rt : ℕ) : Cmd :=
  .ite (exprLt (.reg ri) (.reg rj))
    (.assign rd (exprAnd (exprLt (.reg ri) (.reg rt)) (exprLt (.reg rt) (.reg rj))))
    (.assign rd (exprOr (exprLt (.reg ri) (.reg rt)) (exprLt (.reg rt) (.reg rj))))

/-- The cyclic-interval command computes its flag in at most 13 steps.
Its exact final state also gives preservation of all other registers and arrays. -/
theorem gm06BetweenProg_exec {w : ℕ} (rd ri rj rt : ℕ) {s : State}
    (hw : 2 < 2 ^ w) (hi : s.regs ri < 2 ^ w)
    (hj : s.regs rj < 2 ^ w) (ht : s.regs rt < 2 ^ w) :
    ∃ t, Exec w (gm06BetweenProg rd ri rj rt) s
      (s.setReg rd (if GM06DrawingData.cyclicBetween
        (s.regs ri) (s.regs rj) (s.regs rt) then 1 else 0)) t ∧ t ≤ 13 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hei : (Expr.reg ri).eval w s = some (s.regs ri) := by
    simp [Expr.eval, checkWord, hi]
  have hej : (Expr.reg rj).eval w s = some (s.regs rj) := by
    simp [Expr.eval, checkWord, hj]
  have het : (Expr.reg rt).eval w s = some (s.regs rt) := by
    simp [Expr.eval, checkWord, ht]
  have hc := eval_exprLt hw1 hei hej
  have ha := eval_exprLt hw1 hei het
  have hb := eval_exprLt hw1 het hej
  by_cases hij : s.regs ri < s.regs rj
  · have hflag : (if GM06DrawingData.cyclicBetween
        (s.regs ri) (s.regs rj) (s.regs rt) then 1 else 0) =
        (if s.regs ri < s.regs rt ∧ s.regs rt < s.regs rj then 1 else 0) := by
      simp [GM06DrawingData.cyclicBetween, hij]
    rw [hflag]
    refine ⟨11, ?_, by decide⟩
    exact .ite_true (by simpa only [if_pos hij] using hc) (by decide)
      (.assign (eval_exprAnd hw1 ha hb))
  · have hflag : (if GM06DrawingData.cyclicBetween
        (s.regs ri) (s.regs rj) (s.regs rt) then 1 else 0) =
        (if s.regs ri < s.regs rt ∨ s.regs rt < s.regs rj then 1 else 0) := by
      simp [GM06DrawingData.cyclicBetween, hij]
    rw [hflag]
    refine ⟨13, ?_, by decide⟩
    exact .ite_false (by simpa only [if_neg hij] using hc)
      (.assign (eval_exprOr hw ha hb))

end GraphMinor.Compute
