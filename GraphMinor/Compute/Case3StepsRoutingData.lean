module

public import GraphMinor.Compute.Case3StepsGroupingProg

/-!
# Contents of the division routing arrays

This finite array map names the graph, core, representative tables, selected
mask, loop owners, endpoint matrix, and ordered buckets kept in scratch
storage. It specifies data only. Execution theorems prove that the programs
write these exact values.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Scratch offsets containing retained input or routing data. -/
def case3RoutingArrayIndices : List ℕ := [3, 10, 16, 26, 27, 28, 29, 33, 34, 35, 36, 37]

/-- Exact contents at each retained graph, core, or routing-table offset. -/
noncomputable def case3RoutingArray (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) : ℕ → List ℕ
  | 3 => D.enc
  | 10 => bitSetList Z
  | 16 => encGraph x.G
  | 26 => case3AttachmentKeys x Z
  | 27 => case3ComponentRepList x Z
  | 28 => case3CoreEdgeRepList x Z
  | 29 => bitSetList (case3GroupLabelSet x Z)
  | 33 => List.ofFn (case3OrderedLoopLabel x Z)
  | 34 => case3EdgeMatrixPrefix x Z (case3InputEdges x).length
  | 35 => case3BucketHeads (case3ActivePairOwner x D Z) (x.n + (case3InputEdges x).length) 0
  | 36 => case3BucketNext (case3ActivePairOwner x D Z) 0
  | 37 => case3BucketCounts (case3ActivePairOwner x D Z) (x.n + (case3InputEdges x).length) 0
  | _ => []

/-- Scratch offsets containing the traversal sizes. -/
def case3RoutingRegIndices : List ℕ := [14, 17, 52, 64]

/-- Vertex, simple-edge, candidate, and positive-pair counts kept for later scans. -/
noncomputable def case3RoutingReg (x : Alg81Input) (D : MultiDigraph x.n) : ℕ → ℕ
  | 14 => x.n
  | 17 => (case3InputEdges x).length
  | 52 => x.n + (case3InputEdges x).length
  | 64 => D.numActivePairs
  | _ => 0

end GraphMinor.Compute
