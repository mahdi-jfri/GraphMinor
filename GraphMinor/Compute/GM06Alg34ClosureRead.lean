module

public import GraphMinor.Compute.GM06Alg34ClosureMatrixCorrect
public import GraphMinor.Compute.Basic

/-!
# RAM reads of closure and touching incidences

Read a closure bit using the packed row and column labels held in
registers. Two cells touch when either directional closure bit is one.
The Boolean union uses subtraction and multiplication on zero-one
words, so all its intermediate values fit even in small words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a closure incidence from matrix 12 using cell count 170. -/
def gm06ClosureReadExpr (row col : ℕ) : Expr :=
  .read 12 (.op .add (.op .mul (.reg 170) (.reg row)) (.reg col))

/-- Read the symmetric touching test from the two closure incidences. -/
def gm06CellTouchExpr (row col : ℕ) : Expr :=
  .op .sub (.const 1) (.op .mul
    (.op .sub (.const 1) (gm06ClosureReadExpr row col))
    (.op .sub (.const 1) (gm06ClosureReadExpr col row)))

/-- Reading the computed closure matrix returns exactly its cell
closure-membership bit. -/
theorem gm06ClosureReadExpr_eval {w : ℕ} (x : GM06DrawingData)
    (a b : Fin x.cellCount) (row col : ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (ha : s.regs row = a.val) (hb : s.regs col = b.val) :
    (gm06ClosureReadExpr row col).eval w s =
      some (if x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm a) then 1 else 0) := by
  have hidx : x.cellCount * a.val + b.val < (s.arrs 12).length := by
    rw [hmat, gm06ClosureMatrixData_length]
    exact (Nat.add_lt_add_left b.isLt _).trans_le (by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ a.isLt)
  have hidxw : x.cellCount * a.val + b.val < 2 ^ w := by
    rw [hmat, gm06ClosureMatrixData_length] at hidx
    exact hidx.trans hsquare
  have hmulw : x.cellCount * a.val < 2 ^ w := (Nat.le_add_right _ _).trans_lt hidxw
  have hget : (s.arrs 12)[x.cellCount * a.val + b.val]'hidx =
      if x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm a) then 1 else 0 := by
    simpa only [hmat] using gm06ClosureMatrixData_getElem_packed x a b
  have hav := a.isLt.trans hN
  have hbv := b.isLt.trans hN
  by_cases hmem : x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm a) <;>
    simp [gm06ClosureReadExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hc, ha, hb, hN, hav, hbv, hmulw, hidxw, hidx, hget, hmem, hw,
      Nat.zero_lt_of_lt hw]

/-- Symmetric closure reads compute exactly the supplied touching bit. -/
theorem gm06CellTouchExpr_eval {w : ℕ} (x : GM06DrawingData)
    (a b : Fin x.cellCount) (row col : ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (ha : s.regs row = a.val) (hb : s.regs col = b.val) :
    (gm06CellTouchExpr row col).eval w s =
      some (if x.cellTouch (x.cellNumbering.symm a) (x.cellNumbering.symm b) then 1 else 0) := by
  have hab := gm06ClosureReadExpr_eval x a b row col hw hN hsquare hmat hc ha hb
  have hba := gm06ClosureReadExpr_eval x b a col row hw hN hsquare hmat hc hb ha
  simp only [gm06CellTouchExpr, Expr.eval, hab, hba, BinOp.eval, BinOp.raw,
    GM06DrawingData.cellTouch, decide_eq_true_eq]
  by_cases h₁ : x.cellNumbering.symm a ∈ x.cellClosure (x.cellNumbering.symm b) <;>
    by_cases h₂ : x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm a) <;>
    simp [h₁, h₂, checkWord, hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
