module

public import GraphMinor.Compute.GM06Alg34ComponentInputs
public import GraphMinor.GM06.Alg34ComponentRep
public import GraphMinor.GM06.Alg34InducedRep

/-!
# The division on a computed component input

If no block meets two components, every block that survives restriction
to one component is wholly in that component. Thus the induced payload
represents exactly the component's part of the old division, rather
than just its intersections. This identifies the branch inputs in
VI (3.3)(iv), page 121.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- An unsplit represented block meeting a computed component lies wholly
inside that component's represented vertex set. -/
theorem block_subset_componentImage (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (a : Fin x.n) {δ : Set S} (hδ : δ ∈ Δ)
    (hmeet : (δ ∩ h.vertexImage (x.componentVertices a)).Nonempty) :
    δ ⊆ h.vertexImage (x.componentVertices a) := by
  obtain ⟨L, hL, hLδ⟩ := h.division.subset hδ
  obtain ⟨p, hpδ, hpC⟩ := hmeet
  obtain ⟨b, hb, hbp⟩ := hLδ.symm ▸ hpδ
  obtain ⟨c, hc, hcp⟩ := hpC
  have hbc : b = c := h.vertex.injective (Subtype.ext (hbp.trans hcp.symm))
  have hsub := x.block_subset_component_of_meets hs hL a ⟨b, hb, hbc.symm ▸ hc⟩
  intro q hq
  obtain ⟨d, hd, hdq⟩ := hLδ.symm ▸ hq
  exact ⟨d, hsub hd, hdq⟩

/-- Restricting an unsplit division to a component gives exactly the
blocks contained in that component, as in VI (3.3)(iv). -/
theorem component_inducedDivision (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ) (a : Fin x.n) :
    h.inducedDivision (x.componentVertices a) =
      {δ ∈ Δ | δ ⊆ (GM06.compOf G.toGraph (h.vertex a).val).vertexSet} := by
  apply Set.Subset.antisymm
  · rintro δ ⟨B, ⟨hB, hmeet⟩, rfl⟩
    have hsub := h.block_subset_componentImage hs a hB hmeet
    have heq : B ∩ h.vertexImage (x.componentVertices a) = B := inter_eq_left.mpr hsub
    change B ∩ h.vertexImage (x.componentVertices a) ∈
      {δ ∈ Δ | δ ⊆ (GM06.compOf G.toGraph (h.vertex a).val).vertexSet}
    rw [heq]
    exact ⟨hB, (h.component_vertexImage a) ▸ hsub⟩
  · rintro δ ⟨hδ, hsub⟩
    have hsub' : δ ⊆ h.vertexImage (x.componentVertices a) :=
      (h.component_vertexImage a).symm ▸ hsub
    have heq : δ ∩ h.vertexImage (x.componentVertices a) = δ := inter_eq_left.mpr hsub'
    exact ⟨δ, ⟨hδ, heq.symm ▸ hD.2.1 δ hδ⟩, heq⟩

/-- The computed branch payload describes the actual induced component
and the paper's corresponding part of the division. -/
theorem componentData_rep (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ) (a : Fin x.n) :
    Nonempty (GM06DrawingRep (x.componentData a)
      (induceDrawing G (GM06.compOf G.toGraph (h.vertex a).val).vertexSet)
      {δ ∈ Δ | δ ⊆ (GM06.compOf G.toGraph (h.vertex a).val).vertexSet}) := by
  have hr := h.inducedData_rep (x.componentVertices a)
  rw [h.component_vertexImage a, h.component_inducedDivision hs hD a] at hr
  exact hr

end GraphMinor.Compute.GM06DrawingRep
