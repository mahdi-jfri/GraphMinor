module

public import GraphMinor.Compute.GM06Alg34CellGraph

/-!
# Numeric closure incidences for the region computation

The finite cell numbering puts vertices first, then edges, then
regions. Numbering each closure list therefore gives explicit rows
readable from the supplied endpoints and region boundary lists. These
identities connect those supplied lists to the region-incidence array.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Original vertex labels occupy the first packed range. -/
theorem cellNumbering_vertex_val (x : GM06DrawingData) (v : Fin x.n) :
    (x.cellNumbering (.inl v)).val = v.val := rfl

/-- Original edge labels occupy the range immediately after the vertices. -/
theorem cellNumbering_edge_val (x : GM06DrawingData) (e : Fin x.ends.length) :
    (x.cellNumbering (.inr (.inl e))).val = x.n + e.val := rfl

/-- Region labels occupy the last packed range. -/
theorem cellNumbering_region_val (x : GM06DrawingData) (r : Fin x.regions.length) :
    (x.cellNumbering (.inr (.inr r))).val = x.n + (x.ends.length + r.val) := rfl

/-- A vertex's numbered closure row contains just that vertex. -/
theorem numbered_cellClosure_vertex (x : GM06DrawingData) (v : Fin x.n) :
    (x.cellClosure (.inl v)).map (fun c => (x.cellNumbering c).val) = [v.val] := rfl

/-- An edge's numbered closure row contains its own cell and its supplied endpoints. -/
theorem numbered_cellClosure_edge (x : GM06DrawingData) (e : Fin x.ends.length) :
    (x.cellClosure (.inr (.inl e))).map (fun c => (x.cellNumbering c).val) =
      [x.n + e.val, x.ends[e].1.val, x.ends[e].2.val] := rfl

/-- A region's numbered closure row is precisely its supplied boundary lists,
preceded by the region's own packed label. -/
theorem numbered_cellClosure_region (x : GM06DrawingData) (r : Fin x.regions.length) :
    (x.cellClosure (.inr (.inr r))).map (fun c => (x.cellNumbering c).val) =
      (x.n + (x.ends.length + r.val)) ::
        (x.regions[r].vertices.map Fin.val ++ x.regions[r].edges.map (fun e => x.n + e.val)) := by
  simp only [cellClosure, List.map_cons, List.map_append, List.map_map, Function.comp_def,
    cellNumbering_vertex_val, cellNumbering_edge_val, cellNumbering_region_val]

/-- Every supplied numbered closure entry fits in the allocated cell range. -/
theorem numbered_cellClosure_lt (x : GM06DrawingData) (c : GM06CellIndex x)
    (a : ℕ) (ha : a ∈ (x.cellClosure c).map (fun d => (x.cellNumbering d).val)) :
    a < x.cellCount := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
  exact (x.cellNumbering d).isLt

end GraphMinor.Compute.GM06DrawingData
