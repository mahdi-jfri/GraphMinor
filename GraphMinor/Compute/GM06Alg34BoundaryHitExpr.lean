module

public import GraphMinor.Compute.GM06Alg34BoundaryHitData

/-!
# Reading one contribution to a new region boundary

A reached cell contributes a boundary label when the label belongs
to its supplied closure. Multiply the BFS mark by the corresponding
closure-matrix entry. Both operands are zero-one words and all labels
come from the finite input numbering.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test whether reached cell 204 contributes boundary label 205. -/
def gm06BoundaryHitExpr : Expr :=
  .op .mul (.read 33 (.reg 204)) (gm06ClosureReadExpr 204 205)

/-- The contribution expression reads exactly the conjunction of a
component mark and a supplied closure incidence. -/
theorem gm06BoundaryHitExpr_eval {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a c b : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hcell : s.regs 204 = c.val) (hboundary : s.regs 205 = b.val) :
    gm06BoundaryHitExpr.eval w s = some
      (if (x.complementGraph vs).Reachable a c ∧
        x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm c) then 1 else 0) := by
  have hclosure := gm06ClosureReadExpr_eval x c b 204 205 hw hN hsquare hmat hc hcell hboundary
  have hlen : c.val < (s.arrs 33).length := by
    rw [hmarks, gm06ComplementReachData_length]; exact c.isLt
  have hget : (s.arrs 33)[c.val]'hlen =
      if (x.complementGraph vs).Reachable a c then 1 else 0 := by
    simp only [hmarks, gm06ComplementReachData, List.getElem_ofFn]
  simp only [gm06BoundaryHitExpr, Expr.eval, hclosure, BinOp.eval, BinOp.raw]
  by_cases hreach : (x.complementGraph vs).Reachable a c <;>
    by_cases hinc : x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm c) <;>
    simp [Expr.eval, checkWord, hcell, c.isLt.trans hN, hlen, hget,
      hreach, hinc, hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
