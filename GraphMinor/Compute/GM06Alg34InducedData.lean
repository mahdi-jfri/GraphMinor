module

public import GraphMinor.Compute.GM06Alg34RelabelLists
public import GraphMinor.Compute.GM06Alg34RegionBoundary

/-!
# Finite drawing data after vertex deletion

Compute the new endpoint list from surviving edges. For regions, use
the least inactive-cell labels and their computed finite boundaries.
Filter and renumber each supplied cuff and division list, discarding
empty division blocks. Every value is computed from the old finite data
and the active label list, with no map from a geometric instance.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The renumbered finite boundary of a recomputed region. -/
def inducedRegionBoundary (x : GM06DrawingData) (vs : List (Fin x.n)) (r : Fin x.cellCount) :
    GM06RegionBoundary (x.activeVertices vs).length (x.activeEnds vs).length where
  vertices := x.relabelVertexList vs (x.regionBoundaryVertices vs r)
  edges := (x.relabelEdgeList vs (x.regionBoundaryEdges vs r)).map
    (Fin.cast (x.activeEnds_length vs).symm)

/-- All drawing data obtained by restricting to the supplied active
vertices. Division blocks are restricted and empty ones discarded. -/
def inducedData (x : GM06DrawingData) (vs : List (Fin x.n)) : GM06DrawingData where
  n := (x.activeVertices vs).length
  ends := x.activeEnds vs
  regions := (x.regionRoots vs).map (x.inducedRegionBoundary vs)
  cuffs := x.cuffs.map (x.relabelVertexList vs)
  division := (x.division.map (x.relabelVertexList vs)).filter (fun B => !B.isEmpty)

/-- The new vertex count is exactly the number of surviving labels. -/
theorem inducedData_n (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).n = (x.activeVertices vs).length := rfl

/-- The new edge count is exactly the number of surviving edges. -/
theorem inducedData_ends_length (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).ends.length = (x.activeEdges vs).length := x.activeEnds_length vs

/-- The new region count is the number of computed complement roots. -/
theorem inducedData_regions_length (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).regions.length = (x.regionRoots vs).length := by
  simp only [inducedData, List.length_map]

/-- Restricting vertices retains one cyclic list for each original cuff. -/
theorem inducedData_cuffs_length (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).cuffs.length = x.cuffs.length := by
  simp only [inducedData, List.length_map]

end GraphMinor.Compute.GM06DrawingData
