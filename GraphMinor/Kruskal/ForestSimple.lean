module

public import GraphMinor.GM04.TopologicalContainment
public import Mathlib.Combinatorics.Graph.Simple

/-!
# A multigraph forest has no loops or parallel edges

The trees in Graph Minors IV, Section 2, page 230 have no circuits. A loop
would give a simple closed walk of length one. Two distinct parallel edges
would give one of length two. Thus these graphs satisfy Mathlib's `Simple`
condition, allowing the use of their underlying simple graphs.
-/

public section

namespace GraphMinor.Kruskal

open Graph Surface

/-- A loop gives a one-edge circuit, which a forest cannot contain. -/
theorem forest_loopless {α β : Type*} {G : Graph α β}
    (hforest : IsGraphForest G) : G.Loopless := by
  constructor
  intro e v hv
  let W : GraphWalk G v v := .cons hv (.nil hv.left_mem)
  have hW : W.IsSimpleClosed := by
    simp [W, GraphWalk.IsSimpleClosed, GraphWalk.support, GraphWalk.edges]
  have hlen := hforest v W hW
  exact Nat.one_ne_zero hlen

/-- Distinct parallel edges give a two-edge circuit. Together with the
absence of loops, this proves that every multigraph forest is simple. -/
theorem forest_simple {α β : Type*} {G : Graph α β}
    (hforest : IsGraphForest G) : G.Simple := by
  let := forest_loopless hforest
  refine { toLoopless := forest_loopless hforest, eq_of_isLink := ?_ }
  intro e f u v he hf
  by_contra hef
  have huv : u ≠ v := he.ne
  let W : GraphWalk G u u := .cons he (.cons hf.symm (.nil he.left_mem))
  have hW : W.IsSimpleClosed := by
    simp [W, GraphWalk.IsSimpleClosed, GraphWalk.support, GraphWalk.edges, hef, huv.symm]
  have hlen := hforest u W hW
  exact (by decide : (2 : ℕ) ≠ 0) hlen

end GraphMinor.Kruskal
