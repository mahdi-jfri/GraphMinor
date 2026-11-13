module

public import GraphMinor.Compute.GM06Alg34CrossTest
public import GraphMinor.Compute.Algorithm77Prog
import GraphMinor.Compute.Algorithm77Prog73

/-!
# RAM expressions for one crossing comparison

Use the RAM's equality and multiplication operations for conjunctions of
Boolean tests. The expression checks distinct positions, distinct positive
block tags, and the two cyclic-interval flags. Its evaluation theorem is
exactly the finite comparison already proved correct for the division.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Check that the four supplied cuff positions are pairwise distinct. -/
def gm06DistinctExpr (i j k l : Expr) : Expr :=
  exprAnd (exprNe i j) (exprAnd (exprNe k l) (exprAnd (exprNe i k)
    (exprAnd (exprNe i l) (exprAnd (exprNe j k) (exprNe j l)))))

/-- Check that the two pairs have equal, positive, and different tags. -/
def gm06ColourExpr (a c b d : Expr) : Expr :=
  exprAnd (exprEq a c) (exprAnd (exprEq b d) (exprAnd (exprNe a b)
    (exprAnd (exprNe a (.const 0)) (exprNe b (.const 0)))))

/-- Combine the position, cyclic-interval, and block-tag comparisons. -/
def gm06QuadGuard (i j k l a c b d p q : Expr) : Expr :=
  exprAnd (exprAnd (gm06DistinctExpr i j k l) (exprNe p q)) (gm06ColourExpr a c b d)

private theorem gm06_eval_ne {w : ℕ} {s : State} {e f : Expr} {a b : ℕ}
    (hw : 1 < 2 ^ w) (he : e.eval w s = some a) (hf : f.eval w s = some b) :
    (exprNe e f).eval w s = some (if a ≠ b then 1 else 0) :=
  eval_exprNot hw (eval_exprEq hw he hf)

private theorem gm06_eval_xor {w : ℕ} {s : State} {e f : Expr} {a b : Bool}
    (hw : 1 < 2 ^ w) (he : e.eval w s = some (if a then 1 else 0))
    (hf : f.eval w s = some (if b then 1 else 0)) :
    (exprNe e f).eval w s = some (if a != b then 1 else 0) := by
  have ht := eval_exprNe hw he hf
  cases a <;> cases b <;> simpa using ht

/-- The expression for distinctness computes its six numeric comparisons. -/
theorem gm06DistinctExpr_eval {w : ℕ} {s : State} {ei ej ek el : Expr} {i j k l : ℕ}
    (hw : 1 < 2 ^ w) (hi : ei.eval w s = some i) (hj : ej.eval w s = some j)
    (hk : ek.eval w s = some k) (hl : el.eval w s = some l) :
    (gm06DistinctExpr ei ej ek el).eval w s =
      some (if i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l then 1 else 0) :=
  eval_exprAnd hw (gm06_eval_ne hw hi hj)
    (eval_exprAnd hw (gm06_eval_ne hw hk hl)
      (eval_exprAnd hw (gm06_eval_ne hw hi hk)
        (eval_exprAnd hw (gm06_eval_ne hw hi hl)
          (eval_exprAnd hw (gm06_eval_ne hw hj hk) (gm06_eval_ne hw hj hl)))))

/-- The tag expression computes exactly the two equalities, distinction,
and positivity conditions of the finite scan. -/
theorem gm06ColourExpr_eval {w : ℕ} {s : State} {ea ec eb ed : Expr} {a c b d : ℕ}
    (hw : 1 < 2 ^ w) (ha : ea.eval w s = some a) (hc : ec.eval w s = some c)
    (hb : eb.eval w s = some b) (hd : ed.eval w s = some d) :
    (gm06ColourExpr ea ec eb ed).eval w s =
      some (if a = c ∧ b = d ∧ a ≠ b ∧ a ≠ 0 ∧ b ≠ 0 then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have hz : (Expr.const 0).eval w s = some 0 := by simp [Expr.eval, checkWord, h0]
  exact eval_exprAnd hw (eval_exprEq hw ha hc)
    (eval_exprAnd hw (eval_exprEq hw hb hd)
      (eval_exprAnd hw (gm06_eval_ne hw ha hb)
        (eval_exprAnd hw (gm06_eval_ne hw ha hz) (gm06_eval_ne hw hb hz))))

/-- Once the two cyclic-interval flags have been computed, the RAM guard
is precisely the proved finite four-position comparison. -/
theorem gm06QuadGuard_eval {w : ℕ} {s : State} {ei ej ek el ea ec eb ed ep eq : Expr}
    {i j k l a c b d : ℕ} (hw : 1 < 2 ^ w)
    (hi : ei.eval w s = some i) (hj : ej.eval w s = some j)
    (hk : ek.eval w s = some k) (hl : el.eval w s = some l)
    (ha : ea.eval w s = some a) (hc : ec.eval w s = some c)
    (hb : eb.eval w s = some b) (hd : ed.eval w s = some d)
    (hp : ep.eval w s = some (if GM06DrawingData.cyclicBetween i j k then 1 else 0))
    (hq : eq.eval w s = some (if GM06DrawingData.cyclicBetween i j l then 1 else 0)) :
    (gm06QuadGuard ei ej ek el ea ec eb ed ep eq).eval w s =
      some (if gm06QuadPattern i j k l a c b d then 1 else 0) := by
  have hdis : (gm06DistinctExpr ei ej ek el).eval w s =
      some (if decide (i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l) then 1 else 0) := by
    simpa only [decide_eq_true_eq] using gm06DistinctExpr_eval hw hi hj hk hl
  have hcol : (gm06ColourExpr ea ec eb ed).eval w s =
      some (if decide (a = c ∧ b = d ∧ a ≠ b ∧ a ≠ 0 ∧ b ≠ 0) then 1 else 0) := by
    simpa only [decide_eq_true_eq] using gm06ColourExpr_eval hw ha hc hb hd
  have hx := gm06_eval_xor hw hp hq
  exact eval_exprAnd_bool hw (eval_exprAnd_bool hw hdis hx) hcol

end GraphMinor.Compute
