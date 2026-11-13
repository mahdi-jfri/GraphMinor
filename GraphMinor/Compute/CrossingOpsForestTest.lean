module

public import GraphMinor.Compute.CrossingOpsResidual
public import GraphMinor.Compute.CrossingOpsBool

/-!
# Testing the union of the computed forests

A forest edge is detected by either of its two parent comparisons. Taking the
Boolean union over the retained parent arrays tests the full certificate union.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Test whether either endpoint is the parent of the other. -/
def forestOneTest (a r_x r_y : ℕ) : Expr := boolNot (withoutParentTest a r_x r_y)

/-- Test membership in the union represented by a fixed list of parent arrays. -/
def forestListTest (parents : List ℕ) (r_x r_y : ℕ) : Expr :=
  parents.foldr (fun a rest => boolOr (forestOneTest a r_x r_y) rest) (.const 0)

/-- At distinct vertices, the parent comparisons detect exactly the discovery forest. -/
theorem eval_forestOneTest {w N a r_x r_y : ℕ} {s : State} {edges : List (Fin N × Fin N)}
    (hp : IsBfsParentsAt a edges s) (u v : Fin N) (hne : u ≠ v)
    [Decidable ((bfsDiscoveryForest edges).Adj u v)]
    (hx : s.regs r_x = u.val) (hy : s.regs r_y = v.val)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (forestOneTest a r_x r_y).eval w s =
      some (if (bfsDiscoveryForest edges).Adj u v then 1 else 0) := by
  classical
  have hh := eval_boolNot (eval_withoutParentTest hp u v hx hy hN hw) hw
  have hi : ¬ ((u, v) ∉ edges ∧ (v, u) ∉ edges) ↔ (bfsDiscoveryForest edges).Adj u v := by
    simp only [bfsDiscoveryForest, SimpleGraph.fromRel_adj, not_and_or, not_not]
    exact ⟨fun h => ⟨hne, h⟩, And.right⟩
  simpa only [forestOneTest, hi] using hh

/-- Combining stored parent arrays gives exactly their forest union. -/
theorem eval_forestListTest {w N r_x r_y : ℕ} {s : State} {parents : List ℕ}
    {ess : List (List (Fin N × Fin N))}
    (hp : List.Forall₂ (fun a edges => IsBfsParentsAt a edges s) parents ess)
    (u v : Fin N) (hne : u ≠ v)
    [hdec : Decidable ((forestUnion (ess.map bfsDiscoveryForest)).Adj u v)]
    (hx : s.regs r_x = u.val) (hy : s.regs r_y = v.val)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (forestListTest parents r_x r_y).eval w s =
      some (if (forestUnion (ess.map bfsDiscoveryForest)).Adj u v then 1 else 0) := by
  revert hdec
  induction hp with
  | nil =>
    intro hdec
    simp only [forestListTest, List.foldr_nil, List.map_nil, forestUnion, SimpleGraph.bot_adj, ite_false]
    exact eval_const (by omega)
  | cons hp hrest ih =>
    intro hdec
    classical
    have hh := eval_boolOr (eval_forestOneTest hp u v hne hx hy hN hw)
      (ih (hdec := Classical.propDecidable _)) hw
    simpa only [forestListTest, List.foldr_cons, List.map_cons, forestUnion,
      SimpleGraph.sup_adj] using hh

end GraphMinor.Compute.Crossing
