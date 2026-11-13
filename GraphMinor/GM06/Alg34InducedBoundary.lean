module

public import GraphMinor.GM06.Alg34InducedListImages
public import GraphMinor.GM06.Alg34UpdatedBoundary

/-!
# Boundary representation in the computed deletion payload

The canonical region boundary lists are already restricted to active
objects. Renumbering and reading them through the new object labels
therefore gives the same actual vertices and open edges. Combine these
identities with the exact recomputed region boundary theorem to verify
the boundary field of the updated input.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

private theorem alg34_cast_cancel {n m : ℕ} (h : n = m) (i : Fin m) :
    Fin.cast h (Fin.cast h.symm i) = i := by
  apply Fin.ext
  simp only [Fin.val_cast]

private theorem alg34_iUnion_cast {n m : ℕ} (h : n = m) (L : List (Fin m)) (F : Fin m → Set S) :
    (⋃ j ∈ L.map (Fin.cast h.symm), F (Fin.cast h j)) = ⋃ i ∈ L, F i := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [alg34_cast_cancel] at hpj
    exact mem_iUnion₂.mpr ⟨i, hi, hpj⟩
  · intro hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    refine mem_iUnion₂.mpr ⟨Fin.cast h.symm i, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    simpa only [alg34_cast_cancel] using hpi

/-- The computed relabelled region-boundary record denotes exactly
the topological boundary through the canonical new vertex and edge maps. -/
theorem inducedRegionBoundary_eq (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (r : Fin x.cellCount) :
    closure (h.regionClass vs r) \ h.regionClass vs r =
      {p | ∃ v ∈ (x.inducedRegionBoundary vs r).vertices, (h.inducedVertex vs v).val = p} ∪
      ⋃ e ∈ (x.inducedRegionBoundary vs r).edges,
        (h.inducedEdge vs (Fin.cast (x.activeEnds_length vs) e)).val := by
  have hVsub : ((fun v => (h.vertex v).val) '' GM06DrawingData.block (x.regionBoundaryVertices vs r)) ⊆
      h.vertexImage vs := by
    rintro p ⟨v, hv, rfl⟩
    exact (h.vertex_mem_image_iff vs v).mpr ((x.mem_regionBoundaryVertices_iff vs r v).mp hv).1
  have hV : (fun i => (h.inducedVertex vs i).val) ''
      GM06DrawingData.block (x.relabelVertexList vs (x.regionBoundaryVertices vs r)) =
      (fun v => (h.vertex v).val) '' GM06DrawingData.block (x.regionBoundaryVertices vs r) := by
    rw [h.image_relabelVertexList vs _, inter_eq_left.mpr hVsub]
  have hfilter : (x.regionBoundaryEdges vs r).filter (fun e => decide (e ∈ x.activeEdges vs)) =
      x.regionBoundaryEdges vs r := by
    apply List.filter_eq_self.mpr
    intro e he
    apply decide_eq_true
    apply (x.mem_activeEdges_iff vs e).mpr
    have heactive := ((x.mem_regionBoundaryEdges_iff vs r e).mp he).1
    simpa only [GM06DrawingData.activeCell, decide_eq_true_eq] using heactive
  have hE := h.iUnion_relabelEdgeList vs (x.regionBoundaryEdges vs r)
  rw [hfilter] at hE
  have hraw := h.regionClass_boundary_eq vs r
  change closure (h.regionClass vs r) \ h.regionClass vs r =
    ((fun i => (h.inducedVertex vs i).val) ''
      GM06DrawingData.block (x.relabelVertexList vs (x.regionBoundaryVertices vs r))) ∪
      (⋃ e ∈ (x.relabelEdgeList vs (x.regionBoundaryEdges vs r)).map
          (Fin.cast (x.activeEnds_length vs).symm),
        (h.inducedEdge vs (Fin.cast (x.activeEnds_length vs) e)).val)
  rw [alg34_iUnion_cast (x.activeEnds_length vs)
    (x.relabelEdgeList vs (x.regionBoundaryEdges vs r))
    (fun i => (h.inducedEdge vs i).val), hV, hE]
  exact hraw

end GraphMinor.Compute.GM06DrawingRep
