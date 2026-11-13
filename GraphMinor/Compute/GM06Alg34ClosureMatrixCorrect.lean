module

public import GraphMinor.Compute.GM06Alg34ClosureRowCells

/-!
# Correctness of the supplied-cell closure matrix

The three supplied-data passes compute precisely the closure relation
on finite cells. Folded row marks give the numeric entry test, and the
row enumeration identifies that test with membership in the finite
cell closure. This also gives closure tests at arbitrary packed labels.
-/

public section
namespace GraphMinor.Compute

/-- Every entry computed by the closure-matrix passes is exactly the
incidence bit for the corresponding pair of finite input cells. -/
theorem gm06ClosureMatrixData_getElem (x : GM06DrawingData) (a b : GM06CellIndex x) :
    (gm06ClosureMatrixData x)[x.cellCount * (x.cellNumbering a).val +
      (x.cellNumbering b).val]'(by
        rw [gm06ClosureMatrixData_length]
        exact (Nat.add_lt_add_left (x.cellNumbering b).isLt _).trans_le (by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (x.cellNumbering a).isLt)) =
      if b ∈ x.cellClosure a then 1 else 0 := by
  have hh := gm06MatrixMarkRows_replicate_getElem x.cellCount (gm06ClosureRowLists x)
    (x.cellNumbering a).val (x.cellNumbering b).val
    (x.cellNumbering a).isLt (x.cellNumbering b).isLt (gm06ClosureRowLists_cols_lt x)
  simp only [gm06ClosureRowLists_incidence_iff] at hh
  simpa only [gm06ClosureMatrixData_eq_fold] using hh

/-- Packed labels read the closure relation after applying the inverse
of the input's explicit cell numbering. -/
theorem gm06ClosureMatrixData_getElem_packed (x : GM06DrawingData)
    (a b : Fin x.cellCount) :
    (gm06ClosureMatrixData x)[x.cellCount * a.val + b.val]'(by
      rw [gm06ClosureMatrixData_length]
      exact (Nat.add_lt_add_left b.isLt _).trans_le (by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ a.isLt)) =
      if x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm a) then 1 else 0 := by
  simpa only [Equiv.apply_symm_apply] using
    gm06ClosureMatrixData_getElem x (x.cellNumbering.symm a) (x.cellNumbering.symm b)

end GraphMinor.Compute
