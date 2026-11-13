module

public import GraphMinor.GM06.Alg34DualRegionIncidence
import GraphMinor.GM06.Alg34Boundary

/-!
# Exact boundaries of the computed dual regions

Use the boundary decomposition for a proper disc drawing. The dual
vertex and edge bijections turn its two parts into finite lists.
The incidence transposition identifies those lists with the computed
dual region record. Thus no boundary data are extracted from a proof
for use by the program.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- The computed dual region lists give exactly the topological boundary
of the actual dual region through the represented primal vertex. -/
theorem dualRegionBoundary_eq (h : GM06DrawingRep x G Δ) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D) (v : Fin x.n) :
    closure (h.dualRegionLabel hd v).val \ (h.dualRegionLabel hd v).val =
      {p | ∃ r ∈ x.dualRegionVertices v, (h.dualVertexLabel hd r).val = p} ∪
        ⋃ e ∈ x.dualRegionEdges v, (h.dualEdgeEquiv hd e).val := by
  rw [alg34_region_boundary_eq hS hd.2.1 (h.dualRegionLabel hd v).property]
  apply congrArg₂ (· ∪ ·)
  · ext p
    constructor
    · rintro ⟨hp, hcl⟩
      obtain ⟨r, hr⟩ := (h.dualVertexLabel_bijective hd).2 ⟨p, hp⟩
      have hrp : (h.dualVertexLabel hd r).val = p := congrArg Subtype.val hr
      exact ⟨r, (h.dualRegionVertices_iff hS hconn hd v r).mpr (hrp.symm ▸ hcl), hrp⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(h.dualVertexLabel hd r).property, (h.dualRegionVertices_iff hS hconn hd v r).mp hr⟩
  · ext p
    constructor
    · intro hp
      obtain ⟨f, ⟨hfE, hfcl⟩, hpf⟩ := mem_iUnion₂.mp hp
      obtain ⟨e, he⟩ := (h.dualEdgeEquiv hd).surjective ⟨f, hfE⟩
      have hef : (h.dualEdgeEquiv hd e).val = f := congrArg Subtype.val he
      obtain ⟨q, hq⟩ := ((h.dualEdgeEquiv hd e).property).2.2.1.nonempty
      have hi : D.EdgeRegionIncident (h.dualEdgeEquiv hd e).val (h.dualRegionLabel hd v).val :=
        ⟨(h.dualEdgeEquiv hd e).property, (h.dualRegionLabel hd v).property,
          q, hq, hfcl (hef ▸ hq)⟩
      exact mem_iUnion₂.mpr ⟨e, (h.dualRegionEdges_iff hS hd v e).mpr hi, hef.symm ▸ hpf⟩
    · intro hp
      obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
      have hi := (h.dualRegionEdges_iff hS hd v e).mp he
      exact mem_iUnion₂.mpr ⟨(h.dualEdgeEquiv hd e).val,
        ⟨(h.dualEdgeEquiv hd e).property,
          disc_edge_subset_closure_of_incident hS hd.2.1 (h.dualEdgeEquiv hd e).property
            (h.dualRegionLabel hd v).property hi.2.2⟩, hpe⟩

end GraphMinor.Compute.GM06DrawingRep
