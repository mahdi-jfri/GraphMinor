module

public import GraphMinor.GM06.Alg34DualEdgeLabels

/-!
# Boundary incidences of the computed dual regions

Vertex-region incidence transposes under the proved double-dual
correspondence. Edge-region incidence transposes with the ends of the
primal edge. These two facts identify the finite boundary lists used
for the dual region corresponding to each primal vertex.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- The supplied primal vertex-region incidence is exactly closure membership. -/
theorem vertex_mem_region_closure_iff (h : GM06DrawingRep x G Δ)
    (v : Fin x.n) (r : Fin x.regions.length) :
    (h.vertex v).val ∈ closure (h.region r).val ↔ v ∈ x.regions[r].vertices := by
  have ht := h.mem_closure_cell_iff (Sum.inr (Sum.inr r)) (Sum.inl v)
    (show (h.vertex v).val ∈ h.cell (Sum.inl v) from Set.mem_singleton _)
  simpa [cell, GM06DrawingData.cellClosure, Function.comp_def] using ht

/-- The computed dual region vertex list is exactly its actual incident dual vertices. -/
theorem dualRegionVertices_iff (h : GM06DrawingRep x G Δ) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (v : Fin x.n) (r : Fin x.regions.length) :
    r ∈ x.dualRegionVertices v ↔
      (h.dualVertexLabel hd r).val ∈ closure (h.dualRegionLabel hd v).val := by
  obtain ⟨_, _, _, _, _, _, _, hinc, _, _, _⟩ := hd.to_pair hS hconn
  rw [x.mem_dualRegionVertices_iff, ← h.vertex_mem_region_closure_iff]
  exact hinc (h.vertex v).val (h.vertex v).property (h.region r).val (h.region r).property
    (h.dualVertexLabel hd r).val ⟨h.dualVertexLabel_mem_region hd r, (h.dualVertexLabel hd r).property⟩
    (h.dualRegionLabel hd v).val (h.dualRegionLabel hd v).property (h.vertex_mem_dualRegionLabel hd v)

/-- The computed dual region edge list consists precisely of the actual
corresponding dual edges incident with that region. -/
theorem dualRegionEdges_iff (h : GM06DrawingRep x G Δ) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) (v : Fin x.n) (e : Fin x.ends.length) :
    e ∈ x.dualRegionEdges v ↔
      D.EdgeRegionIncident (h.dualEdgeEquiv hd e).val (h.dualRegionLabel hd v).val := by
  obtain ⟨_, he2, he3, he4, _⟩ := h.dualEdgeEquiv_spec hd e
  obtain ⟨⟨a, ha, b, hb, hab, _, hia, hib, hall⟩, _⟩ :=
    hd.edge_half_regions hS (h.edge e).property (h.dualEdgeEquiv hd e).property he2 he3 he4
  have hpair : (h.vertex v).val ∈ closure (h.edge e).val ∩ G.V ↔
      x.ends[e].1 = v ∨ x.ends[e].2 = v := by
    rw [h.ends e]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hv | hv)
      · exact Or.inl (h.vertex.injective (Subtype.ext hv)).symm
      · exact Or.inr (h.vertex.injective (Subtype.ext hv)).symm
    · rintro (he | he)
      · rw [he]; exact Or.inl rfl
      · rw [he]; exact Or.inr rfl
  rw [x.mem_dualRegionEdges_iff, ← hpair]
  constructor
  · intro hv
    rw [hab.2.2.2] at hv
    rcases Set.mem_insert_iff.mp hv with hv | hv
    · change (h.vertex v).val = a at hv
      simpa only [dualRegionLabel, hv] using hia
    · change (h.vertex v).val = b at hv
      simpa only [dualRegionLabel, hv] using hib
  · intro hi
    have hr := hall (h.dualRegionLabel hd v).val (h.dualRegionLabel hd v).property hi
    rcases hr with hr | hr
    · have hv : (h.vertex v).val = a := hd.2.2.2.2.2.1 _ (h.vertex v).property _ ha hr
      rw [hab.2.2.2, hv]
      exact Or.inl rfl
    · have hv : (h.vertex v).val = b := hd.2.2.2.2.2.1 _ (h.vertex v).property _ hb hr
      rw [hab.2.2.2, hv]
      exact Or.inr rfl

end GraphMinor.Compute.GM06DrawingRep
