module

public import GraphMinor.Compute.Case3StepsBranchRecordWords
public import GraphMinor.Compute.Algorithm99TransportOrig

/-!
# The compass graph read from the final block

The compass section uses the same original-label vertex list and expanded
edge list as a renamed multigraph. The list decoder therefore restores
that graph exactly. No validity of a branch code is needed for this fact.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The parser's compass graph is the renamed compact compass when its
lists are the computed full vertex and copy lists. -/
theorem case3ParsedBlock_toCompassGraph {n N : ℕ} (D : MultiDigraph n)
    (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X)
    (e : Fin n ↪ Fin N)
    (hbase : relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph ≤ delGraph G X)
    (hv : p.K_vList = List.ofFn (fun u : Fin n => (e u).1))
    (he : p.K_eList = D.multiEdgeTriples.map (origEdgeEmb e e.injective)) :
    p.toCompassGraph = relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph := by
  let r := case3BranchRecord D (origVertexEmb e e.injective) (origEdgeEmb e e.injective) []
  have hrv : r.vList = List.ofFn (fun u : Fin n => (e u).1) :=
    case3BranchRecord_orig_vList D e e.injective []
  have hre : r.eList = D.multiEdgeTriples.map (origEdgeEmb e e.injective) := rfl
  change subgraphOfLists (delGraph G X) p.K_vList p.K_eList = _
  rw [hv, he, ← hrv, ← hre]
  exact case3BranchRecord_toSubgraph D _ _ [] (delGraph G X) hbase

end GraphMinor.Compute
