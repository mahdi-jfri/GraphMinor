module

public import GraphMinor.GM06.Alg34InducedLabels

/-!
# Geometric meaning of the filtered and renumbered lists

Read a computed vertex or edge list through the new object labels.
The resulting actual points or open edges are exactly the original
list restricted to surviving objects. In particular a vertex block
becomes its intersection with the surviving vertex set. These identities
verify cuff, boundary, and division lists in the updated representation.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The actual block denoted by a relabelled vertex list is the old
block intersected with the surviving vertex image. -/
theorem image_relabelVertexList (h : GM06DrawingRep x G Δ) (vs L : List (Fin x.n)) :
    (fun i => (h.inducedVertex vs i).val) '' GM06DrawingData.block (x.relabelVertexList vs L) =
      ((fun v => (h.vertex v).val) '' GM06DrawingData.block L) ∩ h.vertexImage vs := by
  apply Set.Subset.antisymm
  · rintro p ⟨i, hi, rfl⟩
    have hf : (x.activeVertices vs).get i ∈ L.filter (fun v => decide (v ∈ vs)) := by
      rw [← x.map_relabelVertexList vs L]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩
    obtain ⟨hL, hvs⟩ := List.mem_filter.mp hf
    have hvs' : (x.activeVertices vs).get i ∈ vs := of_decide_eq_true hvs
    exact ⟨⟨_, hL, rfl⟩, ⟨_, hvs', rfl⟩⟩
  · rintro p ⟨⟨v, hvL, hvp⟩, w, hw, hwp⟩
    have hvw : v = w := h.vertex.injective (Subtype.ext (hvp.trans hwp.symm))
    have hv : v ∈ vs := hvw.symm ▸ hw
    have hf : v ∈ L.filter (fun v => decide (v ∈ vs)) := List.mem_filter.mpr ⟨hvL, decide_eq_true hv⟩
    rw [← x.map_relabelVertexList vs L] at hf
    obtain ⟨i, hi, hiv⟩ := List.mem_map.mp hf
    refine ⟨i, hi, ?_⟩
    change (h.vertex ((x.activeVertices vs).get i)).val = p
    rw [hiv]
    exact hvp

/-- A relabelled edge list denotes exactly the old listed edges that survive. -/
theorem iUnion_relabelEdgeList (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (L : List (Fin x.ends.length)) :
    (⋃ i ∈ x.relabelEdgeList vs L, (h.inducedEdge vs i).val) =
      ⋃ e ∈ L.filter (fun e => decide (e ∈ x.activeEdges vs)), (h.edge e).val := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    have hf : (x.activeEdges vs).get i ∈ L.filter (fun e => decide (e ∈ x.activeEdges vs)) := by
      rw [← x.map_relabelEdgeList vs L]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩
    exact mem_iUnion₂.mpr ⟨_, hf, hpi⟩
  · intro hp
    obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
    rw [← x.map_relabelEdgeList vs L] at he
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp he
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    change p ∈ (h.edge ((x.activeEdges vs).get i)).val
    rw [hie]
    exact hpe

end GraphMinor.Compute.GM06DrawingRep
