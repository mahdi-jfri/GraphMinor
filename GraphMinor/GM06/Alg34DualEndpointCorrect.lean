module

public import GraphMinor.GM06.Alg34DualEdgeLabels
public import GraphMinor.GM06.Alg34DualSides

/-!
# Exact ends of the computed dual edges

The finite selection returns precisely the incident primal regions.
Interpret its two labels through the region-to-dual-vertex bijection.
The defining dual incidence condition then gives the actual ends of
the corresponding dual edge. The bounded default for invalid inputs
is never used for a represented disc dual.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- The computed endpoint pair denotes exactly the two actual ends of
the corresponding dual edge, including the loop case. -/
theorem dualEndsOfNonempty_ends (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length) (e : Fin x.ends.length) :
    let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩)
    closure (h.dualEdgeEquiv hd e).val ∩ D.V =
      {(h.dualVertexLabel hd p.1).val, (h.dualVertexLabel hd p.2).val} := by
  obtain ⟨p, hp, hs⟩ := h.dualEdgeEnds_complete hd e
  simp only [hp, Option.getD_some]
  obtain ⟨_, _, _, _, hlink⟩ := h.dualEdgeEquiv_spec hd e
  have hfirst := (hs p.1).mpr (Or.inl rfl)
  have hsecond := (hs p.2).mpr (Or.inr rfl)
  have hall : ∀ r ∈ G.R, G.EdgeRegionIncident (h.edge e).val r →
      r = (h.region p.1).val ∨ r = (h.region p.2).val := by
    intro r hr hi
    obtain ⟨a, ha⟩ := h.region.surjective ⟨r, hr⟩
    have har : (h.region a).val = r := congrArg Subtype.val ha
    rcases (hs a).mp (har.symm ▸ hi) with hpa | hpa
    · exact Or.inl (har.symm.trans (congrArg (fun a => (h.region a).val) hpa))
    · exact Or.inr (har.symm.trans (congrArg (fun a => (h.region a).val) hpa))
  have hed := (hlink (h.region p.1).val (h.region p.1).property
    (h.region p.2).val (h.region p.2).property
    (h.dualVertexLabel hd p.1).val
    ⟨h.dualVertexLabel_mem_region hd p.1, (h.dualVertexLabel hd p.1).property⟩
    (h.dualVertexLabel hd p.2).val
    ⟨h.dualVertexLabel_mem_region hd p.2, (h.dualVertexLabel hd p.2).property⟩).mpr
      ⟨hfirst, hsecond, hall⟩
  exact hed.2.2.2

end GraphMinor.Compute.GM06DrawingRep
