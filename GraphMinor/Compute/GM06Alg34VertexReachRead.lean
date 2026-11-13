module

public import GraphMinor.Compute.GM06Alg34VertexBfs
public import GraphMinor.Compute.Algorithm77Prog

/-!
# Reading computed vertex reachability bits

A supplied vertex label indexes the visited array of a component search.
The resulting word is exactly its zero-one reachability indicator.
Comparing it with zero tests that the vertex is outside the component.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read whether the label in register 109 lies outside the searched component. -/
def gm06UnreachedExpr : Expr := exprEq (.read 33 (.reg 109)) (.const 0)

/-- Reading a component mark returns exactly the reachable-label indicator. -/
theorem gm06VertexReachRead_eval {w : ℕ} (x : GM06DrawingData) (a b : Fin x.n)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06VertexReachData x a) (hlabel : s.regs 109 = b.val) :
    (Expr.read 33 (.reg 109)).eval w s =
      some (if x.vertexGraph.Reachable a b then 1 else 0) := by
  have hlen : b.val < (s.arrs 33).length := by
    simp only [hmarks, gm06VertexReachData, List.length_ofFn]
    exact b.isLt
  have hget : (s.arrs 33)[b.val]'hlen = if x.vertexGraph.Reachable a b then 1 else 0 := by
    simp only [hmarks, gm06VertexReachData, List.getElem_ofFn]
  by_cases hr : x.vertexGraph.Reachable a b <;>
    simp [Expr.eval, checkWord, hlabel, b.isLt.trans hn, hlen, hget, hr, hw, Nat.zero_lt_of_lt hw]

/-- The zero test of a component mark is exactly non-reachability. -/
theorem gm06UnreachedExpr_eval {w : ℕ} (x : GM06DrawingData) (a b : Fin x.n)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06VertexReachData x a) (hlabel : s.regs 109 = b.val) :
    gm06UnreachedExpr.eval w s = some (if ¬ x.vertexGraph.Reachable a b then 1 else 0) := by
  have hread := gm06VertexReachRead_eval x a b hw hn hmarks hlabel
  have hz : (Expr.const 0).eval w s = some 0 := by
    simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]
  have he := eval_exprEq hw hread hz
  by_cases hr : x.vertexGraph.Reachable a b <;> simpa [gm06UnreachedExpr, hr] using he

end GraphMinor.Compute
