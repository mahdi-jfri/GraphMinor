module

public import GraphMinor.GM06.Alg34InducedRep

/-!
# Canonical geometric labels for the induced gap input

Use the already proved induced vertex, edge, and region bijections to
interpret the computed base payload. Exposing these correctness maps
lets the gap-incidence proof identify its computed region labels with
their complement components. No geometric map is read by the program.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Interpret the computed induced payload using its canonical geometric
labels. This is a representation witness only, not a finite input encoder. -/
@[expose] noncomputable def inducedGapBaseRep (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) :
    GM06DrawingRep (x.inducedData vs) (induceDrawing G (h.vertexImage vs)) (h.inducedDivision vs) := by
  classical
  exact {
    vertex := Equiv.ofBijective (h.inducedVertex vs) (h.inducedVertex_bijective vs)
    edge := (finCongr (x.inducedData_ends_length vs)).trans
      (Equiv.ofBijective (h.inducedEdge vs) (h.inducedEdge_bijective vs))
    region := (finCongr (x.inducedData_regions_length vs)).trans
      (Equiv.ofBijective (h.inducedRegion vs) (h.inducedRegion_bijective vs))
    cuff := (finCongr (x.inducedData_cuffs_length vs)).trans h.cuff
    ends := by
      intro i
      exact h.inducedEdge_ends vs i
    boundary := by
      intro i
      have hget : (x.inducedData vs).regions[i] = x.inducedRegionBoundary vs
          ((x.regionRoots vs).get (Fin.cast (x.inducedData_regions_length vs) i)) := by
        change ((x.regionRoots vs).map (x.inducedRegionBoundary vs))[i.val] = _
        rw [List.getElem_map]
        rfl
      rw [hget]
      exact h.inducedRegionBoundary_eq vs ((x.regionRoots vs).get (Fin.cast (x.inducedData_regions_length vs) i))
    cuff_vertices := by
      intro i
      have hget : (x.inducedData vs).cuffs[i] = x.relabelVertexList vs
          x.cuffs[Fin.cast (x.inducedData_cuffs_length vs) i] := by
        change (x.cuffs.map (x.relabelVertexList vs))[i.val] = _
        rw [List.getElem_map]
        rfl
      rw [hget]
      exact h.induced_cuff_vertices vs (Fin.cast (x.inducedData_cuffs_length vs) i)
    cuff_nodup := h.induced_cuff_nodup vs
    order := by
      intro a b i j
      exact h.induced_crossing_order vs a b i j
    division := h.inducedData_division_image vs }

end GraphMinor.Compute.GM06DrawingRep
