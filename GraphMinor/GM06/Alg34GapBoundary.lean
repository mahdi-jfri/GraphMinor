module

public import GraphMinor.GM06.Alg34GapRegions

/-!
# Boundary vertices of the dual from gap region labels

A supplied enumeration of the boundary segments labels every peripheral
region. The dual point-set condition places exactly its region vertex
on each segment. Conversely every dual boundary vertex belongs to a
segment, so the finite gap region list covers the whole dual boundary.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- Every point of a boundary segment is on the boundary and outside the primal vertices. -/
theorem gap_subset_boundary_diff {seg : Set S}
    (hs : seg ∈ segmentsOf (bd S) (G.V ∩ bd S)) :
    seg ⊆ bd S \ (G.V ∩ bd S) := by
  obtain ⟨⟨p, _, rfl⟩, _⟩ := hs
  exact connectedComponentIn_subset _ _

/-- Any actual dual boundary vertex belongs to a boundary segment of the primal drawing. -/
theorem dual_boundary_vertex_mem_gap (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) {w : S} (hw : w ∈ D.V ∩ bd S) :
    ∃ seg ∈ segmentsOf (bd S) (G.V ∩ bd S), w ∈ seg := by
  have hnV : w ∉ G.V := by
    intro hV
    have hp : w ∈ G.V ∩ D.V := ⟨hV, hw.1⟩
    rw [hd.V_inter_dual_V_eq_empty] at hp
    exact hp
  have hw' : w ∈ bd S \ (G.V ∩ bd S) := ⟨hw.2, fun hh => hnV hh.1⟩
  have hne : (G.V ∩ bd S).Nonempty := by
    by_contra hn
    have he : G.V ∩ bd S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hempty := hd.2.2.2.2.1.1 he
    rw [hempty] at hw
    exact hw
  exact ⟨connectedComponentIn (bd S \ (G.V ∩ bd S)) w,
    connectedComponentIn_mem_segmentsOf hS.isOArc_bd
      (G.finite_V.subset inter_subset_left) inter_subset_right hne hw',
    mem_connectedComponentIn hw'⟩

/-- An exhaustive finite boundary-gap list gives exactly the actual dual boundary vertices. -/
theorem gap_region_labels_boundary (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    {k : ℕ} (segs : Fin k → Set S) (g : Fin k → Fin x.regions.length)
    (hs : ∀ i, segs i ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hcover : ∀ seg ∈ segmentsOf (bd S) (G.V ∩ bd S), ∃ i, segs i = seg)
    (hmeet : ∀ i, ((h.region (g i)).val ∩ segs i).Nonempty) :
    Set.range (fun i => (h.dualVertexLabel hd (g i)).val) = D.V ∩ bd S := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(h.dualVertexLabel hd (g i)).property,
      (gap_subset_boundary_diff (hs i) (h.dualVertexLabel_mem_gap hS hd (g i) (hs i) (hmeet i))).1⟩
  · intro hw
    obtain ⟨seg, hseg, hwseg⟩ := dual_boundary_vertex_mem_gap hS hd hw
    obtain ⟨i, hi⟩ := hcover seg hseg
    have hwsi : w ∈ segs i := hi.symm ▸ hwseg
    have hwr : w ∈ (h.region (g i)).val :=
      gap_subset_region hd.1 (hs i) (h.region (g i)).property (hmeet i) hwsi
    refine ⟨i, ?_⟩
    exact (hd.2.2.1 (h.region (g i)).val (h.region (g i)).property).unique
      ⟨h.dualVertexLabel_mem_region hd (g i), (h.dualVertexLabel hd (g i)).property⟩ ⟨hwr, hw.1⟩

/-- The finite list of gap region labels gives the required cuff vertex image. -/
theorem gap_region_labels_cuff (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    {k : ℕ} (segs : Fin k → Set S) (g : Fin k → Fin x.regions.length)
    (hs : ∀ i, segs i ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hcover : ∀ seg ∈ segmentsOf (bd S) (G.V ∩ bd S), ∃ i, segs i = seg)
    (hmeet : ∀ i, ((h.region (g i)).val ∩ segs i).Nonempty) :
    (fun r => (h.dualVertexLabel hd r).val) '' GM06DrawingData.block (List.ofFn g) =
      D.V ∩ bd S := by
  rw [← h.gap_region_labels_boundary hS hd segs g hs hcover hmeet]
  ext w
  simp only [mem_image, GM06DrawingData.block, mem_ofPred_eq, List.mem_ofFn, mem_range]
  constructor
  · rintro ⟨r, ⟨i, rfl⟩, hw⟩
    exact ⟨i, hw⟩
  · rintro ⟨i, rfl⟩
    exact ⟨g i, ⟨i, rfl⟩, rfl⟩

end GraphMinor.Compute.GM06DrawingRep
