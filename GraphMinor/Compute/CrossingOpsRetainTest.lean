module

public import GraphMinor.Compute.CrossingOpsForestTest
public import GraphMinor.Compute.CrossingOpsCycleTest
public import GraphMinor.Compute.CrossingOpsEdgeTest
public import GraphMinor.Compute.CrossingOpsApexForests

/-!
# The sparsification retention test

An original edge is retained when it belongs to a computed forest, the cycle, or the
extra edge prefix. The word expression combines exactly those three tests. Every
intermediate Boolean word is zero or one.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The three tests of Section 7.2, evaluated on the two endpoint registers. -/
def retainedTest (parents : List ℕ) (a_pos a_mark r_cut r_len r_x r_y : ℕ) : Expr :=
  boolOr (forestListTest parents r_x r_y)
    (boolOr (cycleEdgeTest a_pos r_len r_x r_y) (edgePrefixTest a_mark r_cut r_x r_y))

/-- On an original edge, the retention expression is one exactly on the sparsified graph. -/
theorem eval_retainedTest {w N a_pos a_mark r_cut r_len r_x r_y : ℕ} {s : State}
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {D : List (Fin N)}
    {parents : List ℕ} {ess : List (List (Fin (N + 1) × Fin (N + 1)))}
    (h : IsAdjListFamily G lists) (hD : D.Nodup) (hDpos : 0 < D.length)
    (hp : List.Forall₂ (fun a edges => IsBfsParentsAt a edges s) parents ess)
    (cut u v : Fin N) (q k : ℕ)
    [DecidableRel (sparsifyGraph G D (apexForests ess) (edgePrefixSet lists k)).Adj]
    (hq : q ≤ (edgeRow lists cut).length) (hk : (edgeRowsBefore lists cut.val).length + q = k)
    (hadj : G.Adj u v)
    (hpos : s.arrs a_pos = cyclePositions D D.length)
    (hm : s.arrs a_mark = setAt (List.replicate N 0) (edgeBoundaryList lists cut q) 1)
    (hc : s.regs r_cut = cut.val) (hlen : s.regs r_len = D.length)
    (hx : s.regs r_x = u.val) (hy : s.regs r_y = v.val)
    (hN : N + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    (retainedTest parents a_pos a_mark r_cut r_len r_x r_y).eval w s =
      some (if (sparsifyGraph G D (apexForests ess) (edgePrefixSet lists k)).Adj u v then 1 else 0) := by
  classical
  have hcast : u.castSucc ≠ v.castSucc := fun he => hadj.ne (Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) he))
  have hf := eval_forestListTest hp u.castSucc v.castSucc hcast hx hy hN hw
  have hf' : (forestListTest parents r_x r_y).eval w s =
      some (if (forestUnion (apexForests ess)).Adj (some u) (some v) then 1 else 0) := by
    simpa only [apexForests, apex_forestUnion_adj] using hf
  have hcy := eval_cycleEdgeTest D hD hDpos u v hpos hx hy hlen (show N < 2 ^ w by omega) hw
  have he0 := eval_edgePrefixTest h cut u v q k hq hk hadj hm hc hx hy (show N < 2 ^ w by omega) hw
  have hh := eval_boolOr hf' (eval_boolOr hcy he0 hw) hw
  have hi : (forestUnion (apexForests ess)).Adj (some u) (some v) ∨
      (IsCycleEdge D u v ∨ s(u, v) ∈ edgePrefixSet lists k) ↔
      (sparsifyGraph G D (apexForests ess) (edgePrefixSet lists k)).Adj u v := by
    simp only [sparsifyGraph, hadj, true_and]
  simpa only [retainedTest, hi] using hh

/-- Four parent arrays give a fixed-cost retention expression. -/
theorem retainedTest_four_cost (p0 p1 p2 p3 a_pos a_mark r_cut r_len r_x r_y : ℕ) :
    (retainedTest [p0, p1, p2, p3] a_pos a_mark r_cut r_len r_x r_y).cost = 185 := by
  simp only [retainedTest, forestListTest, List.foldr_cons, List.foldr_nil, forestOneTest,
    withoutParentTest, cycleEdgeTest, cycleNextTestExpr, edgePrefixTest, orderedPrefixTest,
    boolOr, boolAnd, boolNot, Expr.cost]

end GraphMinor.Compute.Crossing
