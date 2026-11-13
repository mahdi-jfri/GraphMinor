module

public import GraphMinor.Compute.GM06Alg34CrossExpr
public import GraphMinor.Compute.GM06Alg34DualGapPositions

/-!
# The RAM guard for one dual gap separation test

Two primal positions witness a separation only if their labels have
the same positive division tag, the positions are distinct, and their
interval flags differ. This command expression combines exactly those
conditions. It uses the existing Boolean word-expression rules.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compare two primal positions, their block tags, and two interval-side flags. -/
def gm06GapPairGuard (ea eb eca ecb ep eq : Expr) : Expr :=
  exprAnd (exprAnd (exprEq eca ecb) (exprNe eca (.const 0)))
    (exprAnd (exprNe ea eb) (exprNe ep eq))

/-- The guard returns exactly the common-block and differing-side test. -/
theorem gm06GapPairGuard_eval {w : ℕ} {s : State} {ea eb eca ecb ep eq : Expr}
    {a b ca cb : ℕ} (p q : Bool) (hw : 1 < 2 ^ w)
    (ha : ea.eval w s = some a) (hb : eb.eval w s = some b)
    (hca : eca.eval w s = some ca) (hcb : ecb.eval w s = some cb)
    (hp : ep.eval w s = some (if p then 1 else 0))
    (hq : eq.eval w s = some (if q then 1 else 0)) :
    (gm06GapPairGuard ea eb eca ecb ep eq).eval w s =
      some (if decide (ca = cb ∧ ca ≠ 0) && (decide (a ≠ b) && (p != q)) then 1 else 0) := by
  have hz : (Expr.const 0).eval w s = some 0 := by
    simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]
  have hcn : (exprNe eca (.const 0)).eval w s = some (if ca ≠ 0 then 1 else 0) := by
    simpa only [ite_not] using eval_exprNe hw hca hz
  have hab : (exprNe ea eb).eval w s = some (if a ≠ b then 1 else 0) := by
    simpa only [ite_not] using eval_exprNe hw ha hb
  have hpq : (exprNe ep eq).eval w s =
      some (if (if p then 1 else 0) ≠ (if q then 1 else 0) then 1 else 0) := by
    simpa only [ite_not] using eval_exprNe hw hp hq
  have hc := eval_exprAnd hw (eval_exprEq hw hca hcb) hcn
  have hr := eval_exprAnd hw hab hpq
  have ht := eval_exprAnd hw hc hr
  cases p <;> cases q <;>
    simpa [gm06GapPairGuard, Bool.and_eq_true, decide_eq_true_eq] using ht

end GraphMinor.Compute
