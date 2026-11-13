module

public import GraphMinor.GM06.Alg34DualVertices
public import GraphMinor.GM06.Section3Main
import GraphMinor.GM11.Regions

/-!
# Boundary gaps and their primal regions

A boundary segment avoids a proper drawing and is connected, so it lies
in the region containing any one of its points. The dual point-set
condition places a dual vertex on that segment. Uniqueness of the dual
vertex in its primal region identifies it with the region's finite label.
These facts connect boundary gap incidence data to the dual payload.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 GM11

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- A segment of the disc boundary avoids every vertex and edge of a proper drawing. -/
theorem gap_subset_complement (hproper : G.IsProper) {seg : Set S}
    (hs : seg ∈ segmentsOf (bd S) (G.V ∩ bd S)) : seg ⊆ univ \ G.U := by
  intro z hz
  obtain ⟨⟨p, _, rfl⟩, _⟩ := hs
  have hz' : z ∈ bd S \ (G.V ∩ bd S) := connectedComponentIn_subset _ _ hz
  exact ⟨trivial, fun hU => hz'.2 ⟨hproper ⟨hz'.1, hU⟩, hz'.1⟩⟩

/-- The whole boundary segment lies in the region containing one of its points. -/
theorem gap_subset_region (hproper : G.IsProper) {seg r : Set S}
    (hs : seg ∈ segmentsOf (bd S) (G.V ∩ bd S)) (hr : r ∈ G.R)
    (hmeet : (r ∩ seg).Nonempty) : seg ⊆ r := by
  obtain ⟨p, hpr, hps⟩ := hmeet
  have hs' := hs
  obtain ⟨⟨q, _, rfl⟩, _⟩ := hs'
  exact subset_region hr isPreconnected_connectedComponentIn
    (disjoint_left.mpr fun z hz => (gap_subset_complement hproper hs hz).2) hps hpr

/-- The dual vertex of a region meeting a boundary segment lies on that segment.
This is the boundary placement in VI, Section 3, pages 119–120. -/
theorem dualVertexLabel_mem_gap (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    (r : Fin x.regions.length) {seg : Set S}
    (hs : seg ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hmeet : ((h.region r).val ∩ seg).Nonempty) :
    (h.dualVertexLabel hd r).val ∈ seg := by
  have hne := nonempty_of_mem_segmentsOf hS.isOArc_bd hs
  have hcard := (hd.2.2.2.2.1.2 hne).2 seg hs
  have hp : 0 < ((D.V ∩ bd S) ∩ seg).ncard := by omega
  obtain ⟨w, hw, hws⟩ := (Set.ncard_pos (D.finite_V.subset (fun _ hz => hz.1.1))).mp hp
  have hwr : w ∈ (h.region r).val :=
    gap_subset_region hd.1 hs (h.region r).property hmeet hws
  have heq : (h.dualVertexLabel hd r).val = w :=
    (hd.2.2.1 (h.region r).val (h.region r).property).unique
      ⟨h.dualVertexLabel_mem_region hd r, (h.dualVertexLabel hd r).property⟩ ⟨hwr, hw.1⟩
  exact heq.symm ▸ hws

/-- Distinct segments belong to distinct primal regions in a connected drawing. -/
theorem gap_region_labels_injective (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper)
    (hconn : IsGraphConnected G.toGraph) {k : ℕ} (segs : Fin k → Set S)
    (hsegs : Function.Injective segs) (g : Fin k → Fin x.regions.length)
    (hs : ∀ i, segs i ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hmeet : ∀ i, ((h.region (g i)).val ∩ segs i).Nonempty) : Function.Injective g := by
  intro i j hij
  apply hsegs
  apply region_inter_segmentsOf_subsingleton hS hproper hconn
    (h.region (g i)).property (hs i) (hs j) (hmeet i)
  simpa only [hij] using hmeet j

end GraphMinor.Compute.GM06DrawingRep
