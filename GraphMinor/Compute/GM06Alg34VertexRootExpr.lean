module

public import GraphMinor.Compute.GM06Alg34VertexReachRanks
public import GraphMinor.Compute.GM06Alg34VertexComponents

/-!
# Reading a component root's prefix count

The source is the least label of its component exactly when its
exclusive component prefix count is zero. Reading that count from the
computed prefix array gives the canonical component-root bit.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test the prefix count at source label 187 for zero. -/
def gm06VertexRootExpr : Expr := .op .eq (.read 35 (.reg 187)) (.const 0)

/-- The computed zero-prefix test is exactly the least-label component-root test. -/
theorem gm06VertexRootExpr_eval {w : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (ha : s.regs 187 = a.val)
    (hranks : s.arrs 35 = List.ofFn (fun b : Fin x.n =>
      ((gm06VertexReachData x a).take b.val).sum)) :
    gm06VertexRootExpr.eval w s = some (if x.isComponentRoot a then 1 else 0) := by
  let p := ((gm06VertexReachData x a).take a.val).sum
  have hsum : p ≤ x.n :=
    ((List.take_sublist a.val (gm06VertexReachData x a)).sum_le_sum
      (fun _ _ => Nat.zero_le _)).trans (gm06VertexReachData_sum_le x a)
  have hpw := hsum.trans_lt hn
  have haw := a.isLt.trans hn
  have hlen : a.val < (s.arrs 35).length := by rw [hranks, List.length_ofFn]; exact a.isLt
  have hget : (s.arrs 35)[a.val]'hlen = p := by simp only [hranks, List.getElem_ofFn]; rfl
  have hroot : x.isComponentRoot a = true ↔ p = 0 := by
    simp only [GM06DrawingData.isComponentRoot, decide_eq_true_eq]
    exact (gm06VertexReachData_prefix_zero_iff x a).symm
  have hbit : (if x.isComponentRoot a then (1 : ℕ) else 0) = if p = 0 then 1 else 0 := by
    simp only [hroot]
  rw [hbit]
  by_cases hp : p = 0 <;>
    simp [gm06VertexRootExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord, ha,
      hlen, hget, haw, hpw, hp, hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
