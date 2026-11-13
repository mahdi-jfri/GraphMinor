module

public import GraphMinor.Compute.GM06Alg34AppendBoundaryVertex
public import GraphMinor.Compute.GM06Alg34AppendBoundaryEdge

/-!
# New region records and their finite size bounds

A new region record consists of its length-prefixed vertex boundary
followed by its length-prefixed edge boundary. Each boundary uses at
most the original number of labels of its kind. Concatenating these
records in canonical root order is exactly the induced region section.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The exact two-field word record of one recomputed region. -/
def gm06RegionRecordWords (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : List ℕ :=
  GM06DrawingData.listWords (((x.inducedRegionBoundary vs a).vertices).map Fin.val) ++
    GM06DrawingData.listWords (((x.inducedRegionBoundary vs a).edges).map Fin.val)

/-- A new region's vertex boundary has at most the old vertex count. -/
theorem gm06RegionBoundaryVertices_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : (x.inducedRegionBoundary vs a).vertices.length ≤ x.n := by
  have hfit : 0 + x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hh := gm06BoundaryWords_length_le
    (gm06BoundarySelection x vs a 0 hfit (fun v => decide (v ∈ vs)))
    (fun v => ((gm06VertexMask vs).take v.val).sum) (List.finRange x.n)
  simpa only [gm06BoundaryVertexWords_eq, List.length_map, List.length_finRange] using hh

/-- A new region's edge boundary has at most the old edge count. -/
theorem gm06RegionBoundaryEdges_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : (x.inducedRegionBoundary vs a).edges.length ≤ x.ends.length := by
  have hfit : x.n + x.ends.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hh := gm06BoundaryWords_length_le
    (gm06BoundarySelection x vs a x.n hfit (fun e => x.activeCell vs (.inr (.inl e))))
    (fun e => ((gm06EdgeMask x vs).take e.val).sum) (List.finRange x.ends.length)
  simpa only [gm06BoundaryEdgeWords_eq, List.length_map, List.length_finRange] using hh

/-- A new region record has two count words and at most the old vertex
and edge counts in label words. -/
theorem gm06RegionRecordWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : (gm06RegionRecordWords x vs a).length ≤ 2 + x.n + x.ends.length := by
  have hv := gm06RegionBoundaryVertices_length_le x vs a
  have he := gm06RegionBoundaryEdges_length_le x vs a
  simp only [gm06RegionRecordWords, List.length_append, GM06DrawingData.listWords,
    List.length_cons, List.length_map]
  omega

private theorem records_map (x : GM06DrawingData) (vs : List (Fin x.n))
    (L : List (Fin x.cellCount)) :
    gm06RegionWords (L.map (fun a =>
      (((x.inducedRegionBoundary vs a).vertices).map Fin.val,
       ((x.inducedRegionBoundary vs a).edges).map Fin.val))) =
      L.flatMap (gm06RegionRecordWords x vs) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, gm06RegionWords, List.flatMap_cons, ih, gm06RegionRecordWords]

/-- The induced region section is exactly the records of canonical
roots in their finite increasing order. -/
theorem gm06Induced_regionWords_eq_records (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).regionWords = (x.regionRoots vs).flatMap (gm06RegionRecordWords x vs) := by
  simp only [GM06DrawingData.regionWords, GM06DrawingData.raw, GM06DrawingData.inducedData,
    List.map_map, Function.comp_def]
  exact records_map x vs (x.regionRoots vs)

end GraphMinor.Compute
