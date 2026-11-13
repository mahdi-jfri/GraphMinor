module

public import GraphMinor.GM06.Alg34InducedEnds
public import GraphMinor.GM06.Alg34InducedBoundary
public import GraphMinor.GM06.Alg34InducedDivision
public import GraphMinor.GM06.Alg34InducedCuffs

/-!
# Correct representation of the finite deletion payload

Assemble the computed labels, endpoints, region boundaries, cuff orders,
and division lists into one representation of the actual induced
drawing. The payload is computed only from the old finite data and
active labels. This theorem constructs its geometric interpretation
and does not select any data for the program from an instance proof.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

private theorem alg34_fin_cast_bijective {n m : ℕ} (h : n = m) :
    Function.Bijective (Fin.cast h) := by
  cases h
  exact Function.bijective_id

private theorem alg34_get_map_cast {α β : Type*} (L : List α) (f : α → β)
    (i : Fin (L.map f).length) :
    (L.map f).get i = f (L.get (Fin.cast (List.length_map f) i)) := by
  simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]

/-- The finite payload produced from active vertex labels describes
exactly the induced drawing and its restricted division. All payload
fields are computed from finite input, independently of this proof. -/
theorem inducedData_rep (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    Nonempty (GM06DrawingRep (x.inducedData vs) (induceDrawing G (h.vertexImage vs))
      (h.inducedDivision vs)) := by
  classical
  let v := h.inducedVertex vs
  let e := fun i : Fin (x.inducedData vs).ends.length =>
    h.inducedEdge vs (Fin.cast (x.inducedData_ends_length vs) i)
  let r := fun i : Fin (x.inducedData vs).regions.length =>
    h.inducedRegion vs (Fin.cast (x.inducedData_regions_length vs) i)
  let c := fun i : Fin (x.inducedData vs).cuffs.length =>
    h.cuff (Fin.cast (x.inducedData_cuffs_length vs) i)
  have hv : Function.Bijective v := h.inducedVertex_bijective vs
  have he : Function.Bijective e := (h.inducedEdge_bijective vs).comp
    (alg34_fin_cast_bijective (x.inducedData_ends_length vs))
  have hr : Function.Bijective r := (h.inducedRegion_bijective vs).comp
    (alg34_fin_cast_bijective (x.inducedData_regions_length vs))
  have hc : Function.Bijective c := h.cuff.bijective.comp
    (alg34_fin_cast_bijective (x.inducedData_cuffs_length vs))
  refine ⟨{
    vertex := Equiv.ofBijective v hv
    edge := Equiv.ofBijective e he
    region := Equiv.ofBijective r hr
    ends := ?_
    boundary := ?_
    cuff := Equiv.ofBijective c hc
    cuff_vertices := ?_
    cuff_nodup := h.induced_cuff_nodup vs
    order := ?_
    division := ?_ }⟩
  · intro i
    exact h.inducedEdge_ends vs i
  · intro i
    have hget : (x.inducedData vs).regions[i] = x.inducedRegionBoundary vs
        ((x.regionRoots vs).get (Fin.cast (x.inducedData_regions_length vs) i)) := by
      exact alg34_get_map_cast (x.regionRoots vs) (x.inducedRegionBoundary vs) i
    rw [hget]
    exact h.inducedRegionBoundary_eq vs
        ((x.regionRoots vs).get (Fin.cast (x.inducedData_regions_length vs) i))
  · intro i
    have hget : (x.inducedData vs).cuffs[i] = x.relabelVertexList vs
        x.cuffs[Fin.cast (x.inducedData_cuffs_length vs) i] := by
      exact alg34_get_map_cast x.cuffs (x.relabelVertexList vs) i
    rw [hget]
    exact h.induced_cuff_vertices vs (Fin.cast (x.inducedData_cuffs_length vs) i)
  · intro a c' b d
    exact h.induced_crossing_order vs a c' b d
  · exact h.inducedData_division_image vs

end GraphMinor.Compute.GM06DrawingRep
