module

public import GraphMinor.GM06.Alg34DualVertices

/-!
# A primal edge has one or two supplied incident regions

Take the ends of its corresponding actual dual edge. Their unique
primal regions are exactly all incident regions, by the disc-dual
incidence condition. The supplied region bijection transfers this to
the finite incident list. Thus the computed endpoint selection never
drops an edge of a represented disc dual.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- Every primal edge's supplied incident regions are exactly the one
or two regions represented by the ends of its actual dual edge. -/
theorem incidentRegions_eq_pair (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (e : Fin x.ends.length) :
    ∃ r s : Fin x.regions.length,
      ∀ a : Fin x.regions.length, a ∈ x.incidentRegions e ↔ a = r ∨ a = s := by
  classical
  obtain ⟨ee, hee⟩ := hd.2.2.2.2.2.2
  obtain ⟨u, v, huv⟩ := (D.toGraph.edge_mem_iff_exists_isLink (ee (h.edge e)).val).mp
    (ee (h.edge e)).property
  obtain ⟨r, hr⟩ := (h.dualVertexLabel_bijective hd).2 ⟨u, huv.left_mem⟩
  obtain ⟨s, hs⟩ := (h.dualVertexLabel_bijective hd).2 ⟨v, huv.right_mem⟩
  have hru : (h.dualVertexLabel hd r).val = u := congrArg Subtype.val hr
  have hsv : (h.dualVertexLabel hd s).val = v := congrArg Subtype.val hs
  obtain ⟨_, _, _, _, hlink⟩ := hee (h.edge e)
  have hends := (hlink (h.region r).val (h.region r).property
    (h.region s).val (h.region s).property (h.dualVertexLabel hd r).val
    ⟨h.dualVertexLabel_mem_region hd r, (h.dualVertexLabel hd r).property⟩
    (h.dualVertexLabel hd s).val
    ⟨h.dualVertexLabel_mem_region hd s, (h.dualVertexLabel hd s).property⟩).mp
      (by simpa only [hru, hsv] using huv)
  refine ⟨r, s, fun a => ?_⟩
  rw [h.incidentRegions_iff]
  constructor
  · intro ha
    rcases hends.2.2 (h.region a).val (h.region a).property ha with har | has
    · exact Or.inl (h.region.injective (Subtype.ext har))
    · exact Or.inr (h.region.injective (Subtype.ext has))
  · rintro (rfl | rfl)
    · exact hends.1
    · exact hends.2.1

/-- Every represented primal edge has a nonempty incident-region list,
and that list contains at most two labels. -/
theorem incidentRegions_nonempty_length_le_two (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) (e : Fin x.ends.length) :
    x.incidentRegions e ≠ [] ∧ (x.incidentRegions e).length ≤ 2 := by
  obtain ⟨r, s, hrs⟩ := h.incidentRegions_eq_pair hd e
  have hr : r ∈ x.incidentRegions e := (hrs r).mpr (Or.inl rfl)
  have hsub : (x.incidentRegions e).toFinset ⊆ ({r, s} : Finset (Fin x.regions.length)) := by
    intro a ha
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (hrs a).mp (List.mem_toFinset.mp ha)
  have hcard : ({r, s} : Finset (Fin x.regions.length)).card ≤ 2 := by
    by_cases heq : r = s
    · subst s; simp
    · simp [heq]
  refine ⟨?_, ?_⟩
  · intro hh
    rw [hh] at hr
    cases hr
  · rw [← List.toFinset_card_of_nodup (x.incidentRegions_nodup e)]
    exact (Finset.card_le_card hsub).trans hcard

/-- The computed dual endpoint selection returns a pair for every edge
and its ends are exactly the actual incident primal regions. -/
theorem dualEdgeEnds_complete (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (e : Fin x.ends.length) :
    ∃ p, x.dualEdgeEnds e = some p ∧
      ∀ r : Fin x.regions.length,
        G.EdgeRegionIncident (h.edge e).val (h.region r).val ↔ r = p.1 ∨ r = p.2 := by
  obtain ⟨hne, htwo⟩ := h.incidentRegions_nonempty_length_le_two hd e
  obtain ⟨p, hp, hs⟩ := x.dualEdgeEnds_spec e hne htwo
  exact ⟨p, hp, fun r => (h.incidentRegions_iff e r).symm.trans (hs r)⟩

end GraphMinor.Compute.GM06DrawingRep
