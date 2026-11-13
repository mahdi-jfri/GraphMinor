module

public import GraphMinor.Compute.GM06Alg34ClosureMatrixCorrect
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading supplied closure incidence for the dual serializer

The prepared square closure matrix records all supplied region and
endpoint incidences. Read a row and column given by expressions, using
the saved cell count as the stride. The exact entry theorem turns the
RAM value into the finite closure-membership bit.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Read a prepared closure entry, with the cell stride in register 170. -/
def gm06DualMatrixExpr (row col : Expr) : Expr :=
  .read 12 (.op .add (.op .mul (.reg 170) row) col)

/-- Every prepared matrix read returns exactly its supplied closure bit. -/
theorem gm06DualMatrixExpr_eval {w : ℕ} (x : GM06DrawingData)
    (a b : GM06CellIndex x) (row col : Expr) {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hrow : row.eval w s = some (x.cellNumbering a).val)
    (hcol : col.eval w s = some (x.cellNumbering b).val) :
    (gm06DualMatrixExpr row col).eval w s = some (if b ∈ x.cellClosure a then 1 else 0) := by
  have haddr : x.cellCount * (x.cellNumbering a).val + (x.cellNumbering b).val <
      x.cellCount * x.cellCount := by
    exact (Nat.add_lt_add_left (x.cellNumbering b).isLt _).trans_le (by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (x.cellNumbering a).isLt)
  have hprod : x.cellCount * (x.cellNumbering a).val < 2 ^ w := by omega
  have hindex := eval_add (eval_mul (eval_reg hstride hN) hrow hprod) hcol
    (haddr.trans hsquare)
  have hbound : x.cellCount * (x.cellNumbering a).val + (x.cellNumbering b).val <
      (s.arrs 12).length := by rw [hmat, gm06ClosureMatrixData_length]; exact haddr
  have hentry : (s.arrs 12)[x.cellCount * (x.cellNumbering a).val + (x.cellNumbering b).val] =
      if b ∈ x.cellClosure a then 1 else 0 := by
    simpa only [hmat] using gm06ClosureMatrixData_getElem x a b
  have hbword : (s.arrs 12)[x.cellCount * (x.cellNumbering a).val + (x.cellNumbering b).val] < 2 ^ w := by
    rw [hentry]
    split_ifs <;> omega
  exact (eval_read hindex hbound hbword).trans (congrArg some hentry)

end GraphMinor.Compute
