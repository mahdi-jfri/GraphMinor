module

public import GraphMinor.Compute.GM06Alg34ClosureRead
public import GraphMinor.Compute.GM06Alg34ActiveEdgeExpr
public import GraphMinor.Compute.GM06Alg34EdgeMaskRead

/-!
# Reading the active flag of a packed cell

The packed vertex range reads the vertex mask, and the packed edge
range reads the edge mask after subtracting the vertex count. Region
cells have flag zero. The branches use only the supplied counts and
the masks already computed from the retained vertex labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read an active-cell bit at packed label `r` into register `out`. -/
def gm06ActiveCellReadProg (r out : ℕ) : Cmd :=
  .ite (.op .lt (.reg r) (.reg 100))
    (.assign out (.read 4 (.reg r)))
    (.ite (.op .lt (.reg r) (.op .add (.reg 100) (.reg 101)))
      (.assign out (.read 6 (.op .sub (.reg r) (.reg 100))))
      (.assign out (.const 0)))

/-- Packed active-cell reading returns the exact induced-drawing flag,
changes only its output register, and takes at most nineteen steps. -/
theorem gm06ActiveCellReadProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (c : GM06CellIndex x) (r out : ℕ)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w) {s : State}
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hr : s.regs r = (x.cellNumbering c).val)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ t, Exec w (gm06ActiveCellReadProg r out) s
      (s.setReg out (if x.activeCell vs c then 1 else 0)) t ∧ t ≤ 19 := by
  have hnw : x.n < 2 ^ w := (Nat.le_add_right _ _).trans_lt hN
  have hnmw : x.n + x.ends.length < 2 ^ w := by
    have hle : x.n + x.ends.length ≤ x.cellCount := by
      dsimp only [GM06DrawingData.cellCount]
      omega
    exact hle.trans_lt hN
  have hmw : x.ends.length < 2 ^ w := by omega
  have hcw : (x.cellNumbering c).val < 2 ^ w := (x.cellNumbering c).isLt.trans hN
  cases c with
  | inl v =>
    simp only [x.cellNumbering_vertex_val] at hr hcw
    have hvw := v.isLt.trans hnw
    have htest : (Expr.op .lt (.reg r) (.reg 100)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr,
        hn, hnw, hvw, v.isLt, hw]
    have hread := gm06ActiveVertexExpr_eval vs v r hw hnw hv hr
    refine ⟨_, Exec.ite_true htest (by omega) (Exec.assign ?_), by simp [Expr.cost]⟩
    simpa only [gm06ActiveVertexExpr, GM06DrawingData.activeCell, decide_eq_true_eq] using hread
  | inr c =>
    have hnot : ¬ (x.cellNumbering (.inr c)).val < x.n := by
      cases c <;> simp only [x.cellNumbering_edge_val, x.cellNumbering_region_val] <;> omega
    have htest : (Expr.op .lt (.reg r) (.reg 100)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hn, hnw, hcw,
        hnot, Nat.zero_lt_of_lt hw]
    cases c with
    | inl e =>
      simp only [x.cellNumbering_edge_val] at hcw
      have hlabel : s.regs r = x.n + e.val := hr
      have hlt : x.n + e.val < x.n + x.ends.length := Nat.add_lt_add_left e.isLt _
      have htest₂ : (Expr.op .lt (.reg r) (.op .add (.reg 100) (.reg 101))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlabel, hn, hm,
          hnw, hmw, hcw, hnmw, hlt, hw]
      have hlen : e.val < (s.arrs 6).length := by simp [he, gm06EdgeMask, e.isLt]
      have hget : (s.arrs 6)[e.val]'hlen =
          if x.activeCell vs (.inr (.inl e)) then 1 else 0 := by simp [he, gm06EdgeMask]
      have hread : (Expr.read 6 (.op .sub (.reg r) (.reg 100))).eval w s =
          some (if x.activeCell vs (.inr (.inl e)) then 1 else 0) := by
        cases hh : x.activeCell vs (.inr (.inl e)) <;>
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlabel, hn, hnw,
            hcw, e.isLt.trans hmw, hlen, hget, hh, hw, Nat.zero_lt_of_lt hw]
      refine ⟨_, Exec.ite_false htest (Exec.ite_true htest₂ (by omega) (Exec.assign hread)), by simp [Expr.cost]⟩
    | inr q =>
      simp only [x.cellNumbering_region_val] at hcw
      have hlabel : s.regs r = x.n + (x.ends.length + q.val) := hr
      have hnot₂ : ¬ x.n + (x.ends.length + q.val) < x.n + x.ends.length := by omega
      have htest₂ : (Expr.op .lt (.reg r) (.op .add (.reg 100) (.reg 101))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlabel, hn, hm,
          hnw, hmw, hcw, hnmw, hnot₂, Nat.zero_lt_of_lt hw]
      refine ⟨_, Exec.ite_false htest (Exec.ite_false htest₂ (Exec.assign ?_)), by simp [Expr.cost]⟩
      simp [Expr.eval, checkWord, GM06DrawingData.activeCell, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
