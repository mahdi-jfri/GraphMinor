module

public import GraphMinor.Compute.GM06Alg34DualEnds

/-!
# The finite region-boundary operation for a disc dual

Dual regions correspond to primal vertices. Their boundary vertices
are the supplied primal regions incident with that vertex, and their
boundary edges correspond to primal edges with that end. All lists are
computed by finite scans. With a positive region count, the endpoint
list retains one slot per original edge. Invalid missing-side inputs
use label zero in that slot. Correctness excludes this default case.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- One endpoint pair per supplied edge, with a bounded default for invalid data. -/
def dualEndsOfNonempty (x : GM06DrawingData) (hR : 0 < x.regions.length) :
    List (Fin x.regions.length × Fin x.regions.length) :=
  (List.finRange x.ends.length).map (fun e =>
    (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩))

/-- The checked nonempty-region operation keeps every original edge slot. -/
theorem dualEndsOfNonempty_length (x : GM06DrawingData) (hR : 0 < x.regions.length) :
    (x.dualEndsOfNonempty hR).length = x.ends.length := by
  simp only [dualEndsOfNonempty, List.length_map, List.length_finRange]

/-- The supplied primal regions incident with one primal vertex. -/
def dualRegionVertices (x : GM06DrawingData) (v : Fin x.n) : List (Fin x.regions.length) :=
  (List.finRange x.regions.length).filter (fun r => decide (v ∈ x.regions[r].vertices))

/-- The supplied edges with the given primal end, in original edge order. -/
def dualRegionEdges (x : GM06DrawingData) (v : Fin x.n) : List (Fin x.ends.length) :=
  (List.finRange x.ends.length).filter (fun e => decide (x.ends[e].1 = v ∨ x.ends[e].2 = v))

/-- The finite region-boundary record corresponding to one primal vertex.
The boundary incidence transposes under disc duality, VI Section 3, pages 119–120. -/
def dualRegionBoundary (x : GM06DrawingData) (hR : 0 < x.regions.length) (v : Fin x.n) :
    GM06RegionBoundary x.regions.length (x.dualEndsOfNonempty hR).length where
  vertices := x.dualRegionVertices v
  edges := (x.dualRegionEdges v).map (Fin.cast (x.dualEndsOfNonempty_length hR).symm)

/-- Dual boundary vertices are exactly the region labels incident with the primal vertex. -/
theorem mem_dualRegionVertices_iff (x : GM06DrawingData) (v : Fin x.n)
    (r : Fin x.regions.length) :
    r ∈ x.dualRegionVertices v ↔ v ∈ x.regions[r].vertices := by
  simp only [dualRegionVertices, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- Dual boundary edge labels are exactly the edges with the primal vertex as an end. -/
theorem mem_dualRegionEdges_iff (x : GM06DrawingData) (v : Fin x.n)
    (e : Fin x.ends.length) :
    e ∈ x.dualRegionEdges v ↔ x.ends[e].1 = v ∨ x.ends[e].2 = v := by
  simp only [dualRegionEdges, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

end GraphMinor.Compute.GM06DrawingData
