module

public import GraphMinor.Compute.GM06Alg34DualEnds
public import GraphMinor.GM06.Alg34CellPartition

/-!
# Interpreting the incident-region scan for dual endpoints

At a point of a supplied cell, closure membership is exactly membership
of its label in the supplied closure list. Apply this to an edge point
and a region. The finite incident-region list is therefore precisely
the actual edge-region incidence relation used in the disc dual.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- At a point of one labelled cell, another cell's closure is read
exactly from the supplied finite closure list. -/
theorem mem_closure_cell_iff (h : GM06DrawingRep x G Δ)
    (a b : GM06CellIndex x) {p : S} (hp : p ∈ h.cell b) :
    p ∈ closure (h.cell a) ↔ b ∈ x.cellClosure a := by
  rw [h.closure_cell a]
  constructor
  · intro hcl
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp hcl
    exact h.cell_index_eq_of_mem hp hpc ▸ hc
  · intro hb
    exact mem_iUnion₂.mpr ⟨b, hb, hp⟩

/-- The incident-region labels are exactly the actual regions incident
with the represented edge, as required for the dual endpoint operation. -/
theorem incidentRegions_iff (h : GM06DrawingRep x G Δ) (e : Fin x.ends.length)
    (r : Fin x.regions.length) :
    r ∈ x.incidentRegions e ↔ G.EdgeRegionIncident (h.edge e).val (h.region r).val := by
  rw [x.mem_incidentRegions_iff]
  have hlabels : Sum.inr (Sum.inl e) ∈ x.cellClosure (Sum.inr (Sum.inr r)) ↔
      e ∈ x.regions[r].edges := by
    simp [GM06DrawingData.cellClosure, Function.comp_def]
  constructor
  · intro he
    obtain ⟨p, hp⟩ := (h.cell_isConnected (Sum.inr (Sum.inl e))).nonempty
    exact ⟨(h.edge e).property, (h.region r).property, p, hp,
      (h.mem_closure_cell_iff (Sum.inr (Sum.inr r)) (Sum.inr (Sum.inl e)) hp).mpr (hlabels.mpr he)⟩
  · rintro ⟨_, _, p, hpe, hpr⟩
    exact hlabels.mp ((h.mem_closure_cell_iff (Sum.inr (Sum.inr r))
      (Sum.inr (Sum.inl e)) hpe).mp hpr)

end GraphMinor.Compute.GM06DrawingRep
