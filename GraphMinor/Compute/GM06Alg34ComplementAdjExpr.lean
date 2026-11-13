module

public import GraphMinor.Compute.GM06Alg34ActiveCellRead

/-!
# Computing complement-cell adjacency

Two distinct packed cells are adjacent in the complement graph when
both are inactive and their supplied closures touch. Multiply these
zero-one tests. The expression reads the verified closure matrix and
the two active flags, with no geometric information in its state.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test complement adjacency of labels 180 and 181, whose active bits
are held in registers 182 and 183. -/
def gm06ComplementAdjExpr : Expr :=
  .op .mul (.op .sub (.const 1) (.op .eq (.reg 180) (.reg 181)))
    (.op .mul (.op .sub (.const 1) (.reg 182))
      (.op .mul (.op .sub (.const 1) (.reg 183)) (gm06CellTouchExpr 180 181)))

/-- The complement-adjacency expression computes exactly the finite
complement graph's edge bit. -/
theorem gm06ComplementAdjExpr_eval {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a b : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (ha : s.regs 180 = a.val) (hb : s.regs 181 = b.val)
    (hA : s.regs 182 = if x.activeCell vs (x.cellNumbering.symm a) then 1 else 0)
    (hB : s.regs 183 = if x.activeCell vs (x.cellNumbering.symm b) then 1 else 0) :
    gm06ComplementAdjExpr.eval w s = some (if (x.complementGraph vs).Adj a b then 1 else 0) := by
  have ht := gm06CellTouchExpr_eval x a b 180 181 hw hN hsquare hmat hc ha hb
  have haw := a.isLt.trans hN
  have hbw := b.isLt.trans hN
  simp only [gm06ComplementAdjExpr, Expr.eval, ht, BinOp.eval, BinOp.raw,
    hA, hB, ha, hb]
  cases hactA : x.activeCell vs (x.cellNumbering.symm a) <;>
    cases hactB : x.activeCell vs (x.cellNumbering.symm b) <;>
    cases htouch : x.cellTouch (x.cellNumbering.symm a) (x.cellNumbering.symm b) <;>
    by_cases heq : a.val = b.val
    <;> simp [hactA, hactB, htouch, heq, GM06DrawingData.complementGraph,
      checkWord, haw, hbw, hw, Nat.zero_lt_of_lt hw, Fin.ext_iff]

end GraphMinor.Compute
