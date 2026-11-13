module

public import GraphMinor.Compute.GM06Alg34BoundarySelectionCells

/-!
# Emitted boundary words agree with the induced drawing payload

The boundary selector keeps exactly the active old boundary labels.
Their prefix ranks equal their positions in the canonical surviving
vertex or edge list. Thus the generic filter's natural words are
precisely the finite labels stored by the induced region boundary.
-/

public section
namespace GraphMinor.Compute

/-- The selected vertex rank words are exactly the new region's vertex
boundary labels in the induced drawing payload. -/
theorem gm06BoundaryVertexWords_eq (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hfit : 0 + x.n ≤ x.cellCount) :
    gm06BoundaryWords
      (gm06BoundarySelection x vs a 0 hfit (fun v => decide (v ∈ vs)))
      (fun v => ((gm06VertexMask vs).take v.val).sum) (List.finRange x.n) =
      ((x.inducedRegionBoundary vs a).vertices).map Fin.val := by
  have hsel : gm06BoundarySelection x vs a 0 hfit (fun v => decide (v ∈ vs)) =
      (fun v => decide (v ∈ vs) && x.regionClosureHit vs a (.inl v)) :=
    funext (gm06BoundarySelection_vertex x vs a hfit)
  rw [gm06BoundaryWords, hsel]
  change (x.regionBoundaryVertices vs a).map (fun v => ((gm06VertexMask vs).take v.val).sum) =
    (x.relabelVertexList vs (x.regionBoundaryVertices vs a)).map Fin.val
  rw [← gm06RelabelVertexWords_eq]
  unfold gm06RelabelVertexWords
  have hkeep : (x.regionBoundaryVertices vs a).filter (fun v => decide (v ∈ vs)) =
      x.regionBoundaryVertices vs a := List.filter_eq_self.mpr (by
    intro v hv
    exact decide_eq_true ((x.mem_regionBoundaryVertices_iff vs a v).mp hv).1)
  rw [hkeep]
  apply List.map_congr_left
  intro v hv
  have hactive := ((x.mem_regionBoundaryVertices_iff vs a v).mp hv).1
  simpa only [gm06VertexRanks, List.getElem_ofFn, gm06ListIndex] using x.vertexRanks_get vs v hactive

private theorem relabelEdgeWords (x : GM06DrawingData) (vs : List (Fin x.n))
    (L : List (Fin x.ends.length)) :
    (x.relabelEdgeList vs L).map Fin.val =
      (L.filter (fun e => decide (e ∈ x.activeEdges vs))).map (fun e => (x.activeEdges vs).idxOf e) := by
  simp only [GM06DrawingData.relabelEdgeList, List.map_map, Function.comp_def, gm06ListIndex]
  exact List.attach_map_val (f := fun e : Fin x.ends.length => (x.activeEdges vs).idxOf e)

/-- The selected edge rank words are exactly the new region's edge
boundary labels in the induced drawing payload. -/
theorem gm06BoundaryEdgeWords_eq (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hfit : x.n + x.ends.length ≤ x.cellCount) :
    gm06BoundaryWords
      (gm06BoundarySelection x vs a x.n hfit (fun e => x.activeCell vs (.inr (.inl e))))
      (fun e => ((gm06EdgeMask x vs).take e.val).sum) (List.finRange x.ends.length) =
      ((x.inducedRegionBoundary vs a).edges).map Fin.val := by
  have hsel : gm06BoundarySelection x vs a x.n hfit (fun e => x.activeCell vs (.inr (.inl e))) =
      (fun e => x.activeCell vs (.inr (.inl e)) && x.regionClosureHit vs a (.inr (.inl e))) :=
    funext (gm06BoundarySelection_edge x vs a hfit)
  rw [gm06BoundaryWords, hsel]
  change (x.regionBoundaryEdges vs a).map (fun e => ((gm06EdgeMask x vs).take e.val).sum) =
    ((x.relabelEdgeList vs (x.regionBoundaryEdges vs a)).map
      (Fin.cast (x.activeEnds_length vs).symm)).map Fin.val
  have hcast : ((x.relabelEdgeList vs (x.regionBoundaryEdges vs a)).map
      (Fin.cast (x.activeEnds_length vs).symm)).map Fin.val =
      (x.relabelEdgeList vs (x.regionBoundaryEdges vs a)).map Fin.val := by
    simp only [List.map_map, Function.comp_def, Fin.coe_cast]
  rw [hcast, relabelEdgeWords]
  have hkeep : (x.regionBoundaryEdges vs a).filter (fun e => decide (e ∈ x.activeEdges vs)) =
      x.regionBoundaryEdges vs a := List.filter_eq_self.mpr (by
    intro e he
    have hactive := ((x.mem_regionBoundaryEdges_iff vs a e).mp he).1
    apply decide_eq_true
    simpa only [GM06DrawingData.activeEdges, List.mem_filter, List.mem_finRange, true_and] using hactive)
  rw [hkeep]
  apply List.map_congr_left
  intro e he
  have hactive := ((x.mem_regionBoundaryEdges_iff vs a e).mp he).1
  simpa only [gm06EdgeRanks, List.getElem_ofFn, gm06ListIndex] using x.edgeRanks_get vs e hactive

end GraphMinor.Compute
