module

public import GraphMinor.Compute.GM06CutRotations
public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.GM06Alg34CrossExpr
import GraphMinor.Compute.CrossingOpsReplLists
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Word expressions for the cut interval table

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) uses open
cyclic intervals and signed cuff ends to assign each nonpath end. These
expressions implement the three interval cases with numeric zero/one
flags. The evaluation lemmas check all intermediate word bounds.
Copy labels retain the original direction and add the path-side tag.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Test an open cyclic interval, using its three position expressions. -/
def gm06CutBetweenExpr (a b d : Expr) : Expr :=
  gm13SelectExpr (exprLt a b)
    (exprAnd (exprLt a d) (exprLt d b)) (exprOr (exprLt a d) (exprLt d b))

/-- The expression implements the same open cyclic interval as the
pure rotation rule, including a wrapped interval. -/
theorem gm06CutBetweenExpr_eval {w a b d : ℕ} {s : State} {ea eb ed : Expr}
    (hw : 2 < 2 ^ w) (ha : ea.eval w s = some a) (hb : eb.eval w s = some b)
    (hd : ed.eval w s = some d) :
    (gm06CutBetweenExpr ea eb ed).eval w s =
      some (if GM06DrawingData.cyclicBetween a b d then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have he := gm13SelectExpr_eval hw1 (eval_exprLt hw1 ha hb)
    (eval_exprAnd hw1 (eval_exprLt hw1 ha hd) (eval_exprLt hw1 hd hb))
    (eval_exprOr hw (eval_exprLt hw1 ha hd) (eval_exprLt hw1 hd hb))
  by_cases hab : a < b <;>
    simpa only [gm06CutBetweenExpr, hab, ↓reduceIte, GM06DrawingData.cyclicBetween,
      decide_eq_true_eq] using he

/-- Form a copied directed-end label from its original label and side tag. -/
def gm06CutDartExpr (d tag : Expr) : Expr :=
  .op .add (.op .add (.op .mul (.const 4) (.op .div d (.const 2)))
    (.op .mul (.const 2) tag)) (.op .mod d (.const 2))

/-- A copied label stays within the four slots of its original edge. -/
theorem gm06CutDart_lt {m d tag : ℕ} (hd : d < 2 * m) (ht : tag < 2) :
    gm06CutDart d tag < 4 * m := by
  unfold gm06CutDart
  have hm := Nat.mod_lt d (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div d 2
  omega

/-- Copy-label arithmetic is exact, with every intermediate in range. -/
theorem gm06CutDartExpr_eval {w m d tag : ℕ} {s : State} {ed et : Expr}
    (hw : 4 < 2 ^ w) (hm : 4 * m < 2 ^ w) (hd : d < 2 * m) (ht : tag < 2)
    (he : ed.eval w s = some d) (hte : et.eval w s = some tag) :
    (gm06CutDartExpr ed et).eval w s = some (gm06CutDart d tag) := by
  have hw2 : 2 < 2 ^ w := by omega
  have hb := gm06CutDart_lt hd ht
  have hrem := Nat.mod_lt d (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div d 2
  exact GraphMinor.Compute.Crossing.eval_add
    (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
        (GraphMinor.Compute.Crossing.eval_div he (GraphMinor.Compute.Crossing.eval_const hw2)
          (by decide) (by have := Expr.eval_lt he; omega)) (by unfold gm06CutDart at hb; omega))
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw2) hte
        (by unfold gm06CutDart at hb; omega)) (by unfold gm06CutDart at hb; omega))
    (GraphMinor.Compute.Crossing.eval_mod he (GraphMinor.Compute.Crossing.eval_const hw2)
      (by decide)) (hb.trans hm)

/-- At a cuff the positive end overrides the interval test, followed
by the negative end. At an interior vertex only the interval is used. -/
def gm06CutSideExpr (cuffed d cp cn interval : Expr) : Expr :=
  gm13SelectExpr cuffed
    (gm13SelectExpr (exprEq d cp) (.const 1)
      (gm13SelectExpr (exprEq d cn) (.const 0) interval)) interval

/-- The override order agrees exactly with the finite cut rule.
No distinctness of the two cuff labels is needed for evaluation. -/
theorem gm06CutSideExpr_eval {w d cp cn : ℕ} {s : State}
    {cuffed inside : Bool} {ec ed ep en ei : Expr} (hw : 1 < 2 ^ w)
    (hc : ec.eval w s = some (if cuffed then 1 else 0))
    (hd : ed.eval w s = some d) (hp : ep.eval w s = some cp) (hn : en.eval w s = some cn)
    (hi : ei.eval w s = some (if inside then 1 else 0)) :
    (gm06CutSideExpr ec ed ep en ei).eval w s =
      some (if (if cuffed then (if d = cp then true else if d = cn then false else inside)
        else inside) then 1 else 0) := by
  have hz : (Expr.const 0).eval w s = some 0 :=
    GraphMinor.Compute.Crossing.eval_const (by omega)
  have ho : (Expr.const 1).eval w s = some 1 := GraphMinor.Compute.Crossing.eval_const hw
  have hneg := gm13SelectExpr_eval hw (eval_exprEq hw hd hn) hz hi
  have hpos := gm13SelectExpr_eval hw (eval_exprEq hw hd hp) ho hneg
  have he := gm13SelectExpr_eval hw hc hpos hi
  cases cuffed <;> by_cases hcp : d = cp <;> by_cases hcn : d = cn <;> cases inside <;>
    simpa [gm06CutSideExpr, hcp, hcn] using he

/-- Path membership uses the plus-one markers, so a zero sentinel
cannot match dart zero. -/
def gm06CutPathEndExpr (d incoming outgoing : Expr) : Expr :=
  exprOr (exprEq (.op .add d (.const 1)) incoming)
    (exprEq (.op .add d (.const 1)) outgoing)

/-- The path-end flag tests exactly the two stored plus-one marks. -/
theorem gm06CutPathEndExpr_eval {w d a b : ℕ} {s : State} {ed ea eb : Expr}
    (hw : 2 < 2 ^ w) (hd : d + 1 < 2 ^ w)
    (he : ed.eval w s = some d) (ha : ea.eval w s = some a) (hb : eb.eval w s = some b) :
    (gm06CutPathEndExpr ed ea eb).eval w s = some (if d + 1 = a ∨ d + 1 = b then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hplus := GraphMinor.Compute.Crossing.eval_add he (GraphMinor.Compute.Crossing.eval_const hw1) hd
  exact eval_exprOr hw (eval_exprEq hw1 hplus ha) (eval_exprEq hw1 hplus hb)

end GraphMinor.Compute
