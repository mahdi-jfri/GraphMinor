module

import GraphMinor.Compute.Case3StepsLoopOwner

/-!
# Small edge-lift examples for steps (5)--(7)

The two-vertex example has parallel edges in both directions and loops at both
vertices. Assigning the loops at just one vertex keeps the full parallel
classes and exactly the assigned loops. The one-vertex example checks that
isolated member vertices survive even when none of their loops is assigned.
These examples check the edge lift, rather than the full Word RAM program.
-/

namespace Checks.Case3Steps

open GraphMinor.Compute Graph

private def parallelGraph : MultiDigraph 2 where
  edgeMult u v := if u = 0 then (if v = 0 then 4 else 2) else (if v = 0 then 3 else 5)

private def parallelMember : Alg86Subgraph parallelGraph.toSimpleGraph where
  verts := Finset.univ
  graph := parallelGraph.toSimpleGraph
  sub := le_rfl
  adj_verts _ _ _ := ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- Two forward copies, three reverse copies, and four loops at vertex zero
remain. The five loops at vertex one are omitted. -/
theorem parallel_lift_numEdges :
    (case3MemberMultiDigraph parallelGraph parallelMember {0}).numEdges = 9 := by
  classical
  simp [MultiDigraph.numEdges, Fin.sum_univ_two, case3MemberMultiDigraph,
    parallelMember, parallelGraph, MultiDigraph.toSimpleGraph_adj]

/-- The selected member retains both vertices and the original simple edge. -/
theorem parallel_lift_simpleGraph :
    (case3MemberMultiDigraph parallelGraph parallelMember {0}).toSimpleGraph =
      parallelGraph.toSimpleGraph := by
  exact case3MemberMultiDigraph_toSimpleGraph parallelGraph parallelMember {0}

private def loopGraph : MultiDigraph 1 where
  edgeMult _ _ := 3

private def loopMember : Alg86Subgraph loopGraph.toSimpleGraph where
  verts := Finset.univ
  graph := ⊥
  sub := bot_le
  adj_verts _ _ h := False.elim h

/-- Omitting every loop does not remove the member's sole vertex. -/
theorem isolated_lift_vertex :
    (0 : ℕ) ∈ V(case3LiftMember loopGraph loopMember ∅) := by
  exact ⟨(0 : Fin 1), Finset.mem_univ _, rfl⟩

/-- All three loops are kept when assigned, and none is kept when unassigned. -/
theorem one_vertex_loop_counts :
    (case3MemberMultiDigraph loopGraph loopMember {0}).numEdges = 3 ∧
      (case3MemberMultiDigraph loopGraph loopMember ∅).numEdges = 0 := by
  classical
  simp [MultiDigraph.numEdges, case3MemberMultiDigraph,
    loopMember, loopGraph]

end Checks.Case3Steps
