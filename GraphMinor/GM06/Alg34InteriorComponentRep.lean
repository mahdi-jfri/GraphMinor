module

public import GraphMinor.GM06.Alg34ComponentRep

/-!
# The represented payload after deleting a cuff-disjoint component

The surviving finite labels denote the original vertex set minus the
selected actual component. Since every division vertex is on the
boundary, every division block survives in full. The computed induced
payload therefore represents exactly the drawing deletion and unchanged
division in VI (3.3)(ii), page 120.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Surviving finite labels denote exactly deletion of the actual component. -/
theorem interiorComponent_vertexImage (h : GM06DrawingRep x G Δ) (a : Fin x.n) :
    h.vertexImage (x.interiorComponentSurvivors a) =
      G.V \ (GM06.compOf G.toGraph (h.vertex a).val).vertexSet := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨(h.vertex b).property, ?_⟩
    intro hp
    rw [← h.component_vertexImage a] at hp
    have hbc := (h.vertex_mem_image_iff (x.componentVertices a) b).mp hp
    exact (x.mem_interiorComponentSurvivors_iff a b).mp hb
      ((x.mem_componentVertices_iff a b).mp hbc)
  · rintro ⟨hpG, hpC⟩
    obtain ⟨b, hb⟩ := h.vertex.surjective ⟨p, hpG⟩
    have hbp : (h.vertex b).val = p := congrArg Subtype.val hb
    refine ⟨b, (x.mem_interiorComponentSurvivors_iff a b).mpr ?_, hbp⟩
    intro hab
    apply hpC
    exact ⟨hpG, by simpa only [hbp] using (h.vertex_reachable_iff a b).mp hab⟩

/-- Boundary division blocks lie entirely outside a component selected
by the finite interior-component test. -/
theorem interiorComponent_block_subset (h : GM06DrawingRep x G Δ) (a : Fin x.n)
    (ha : x.isInteriorComponent a = true) (hbd : divisionUnion Δ ⊆ G.V ∩ bd S)
    {δ : Set S} (hδ : δ ∈ Δ) : δ ⊆ h.vertexImage (x.interiorComponentSurvivors a) := by
  rw [h.interiorComponent_vertexImage a]
  intro p hp
  have hpb := hbd ⟨δ, hδ, hp⟩
  refine ⟨hpb.1, ?_⟩
  intro hpC
  exact Set.disjoint_left.mp ((h.isInteriorComponent_iff a).mp ha) hpC hpb.2

/-- The actual division remains unchanged when the selected interior
component is deleted. -/
theorem interiorComponent_inducedDivision (h : GM06DrawingRep x G Δ) (a : Fin x.n)
    (ha : x.isInteriorComponent a = true) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    h.inducedDivision (x.interiorComponentSurvivors a) = Δ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨δ, ⟨hδ, _⟩, rfl⟩
    change δ ∩ h.vertexImage (x.interiorComponentSurvivors a) ∈ Δ
    rw [inter_eq_left.mpr (h.interiorComponent_block_subset a ha hbd hδ)]
    exact hδ
  · intro δ hδ
    have hsub := h.interiorComponent_block_subset a ha hbd hδ
    have heq : δ ∩ h.vertexImage (x.interiorComponentSurvivors a) = δ := inter_eq_left.mpr hsub
    exact ⟨δ, ⟨hδ, heq.symm ▸ hD.2.1 δ hδ⟩, heq⟩

/-- The computed interior-component payload represents exactly the
vertex deletion and unchanged division of VI (3.3)(ii). -/
theorem interiorComponentData_rep (h : GM06DrawingRep x G Δ) (a : Fin x.n)
    (ha : x.isInteriorComponent a = true) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    Nonempty (GM06DrawingRep (x.interiorComponentData a)
      (induceDrawing G (G.V \ (GM06.compOf G.toGraph (h.vertex a).val).vertexSet)) Δ) := by
  have hr := h.inducedData_rep (x.interiorComponentSurvivors a)
  rw [h.interiorComponent_vertexImage a, h.interiorComponent_inducedDivision a ha hD hbd] at hr
  exact hr

end GraphMinor.Compute.GM06DrawingRep
