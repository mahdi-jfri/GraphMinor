module

public import GraphMinor.GM06.Alg34RegionIncidentEdge
public import GraphMinor.GM06.Alg34DualDataLabels
public import GraphMinor.Compute.GM06Alg34SingletonEdgeLoss

/-!
# Every dual singleton deletion loses an edge

A dual vertex labels a primal region. If the primal has an edge, every
region is incident with some edge. The computed dual endpoint pair
contains exactly those incident region labels. Hence every computed
dual vertex has an incident edge, and its singleton deletion strictly
lowers the edge count. No connectivity of the dual is assumed.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- Every computed dual vertex has an incident edge when the primal has an edge. -/
theorem dualData_exists_incident (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length) (hE : 0 < x.ends.length)
    (v : Fin (x.dualData L hR g).n) :
    ∃ e : Fin (x.dualData L hR g).ends.length,
      v = (x.dualData L hR g).ends[e].1 ∨ v = (x.dualData L hR g).ends[e].2 := by
  have hGE : G.E.Nonempty := ⟨(h.edge ⟨0, hE⟩).val, (h.edge ⟨0, hE⟩).property⟩
  obtain ⟨es, hes, hi⟩ := alg34_region_incident_edge hS hGE (h.region v).property
  let e := h.edge.symm ⟨es, hes⟩
  have hev : (h.edge e).val = es := congrArg Subtype.val (h.edge.apply_symm_apply ⟨es, hes⟩)
  have hi' : G.EdgeRegionIncident (h.edge e).val (h.region v).val := hev.symm ▸ hi
  obtain ⟨p, hp, hs⟩ := h.dualEdgeEnds_complete hd e
  let e' := (finCongr (x.dualData_edges_length L hR g)).symm e
  have hep : (x.dualData L hR g).ends[e'] = p := by
    rw [dualData_ends_get]
    change (x.dualEdgeEnds ((finCongr (x.dualData_edges_length L hR g))
      ((finCongr (x.dualData_edges_length L hR g)).symm e))).getD _ = p
    rw [Equiv.apply_symm_apply, hp]
    rfl
  refine ⟨e', ?_⟩
  rw [hep]
  exact (hs v).mp hi'

/-- A singleton deletion in the computed dual strictly loses edges. -/
theorem dualData_singleton_edges_lt (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length) (hE : 0 < x.ends.length)
    (v : Fin (x.dualData L hR g).n) :
    ((x.dualData L hR g).singletonData v).ends.length < x.ends.length := by
  obtain ⟨e, he⟩ := h.dualData_exists_incident hS hd L hR g hE v
  exact ((x.dualData L hR g).singletonData_edges_lt_of_incident v e he).trans_eq
    (x.dualData_edges_length L hR g)

/-- The dual transition and its following singleton deletion strictly
lower the queue charge, using the fixed bound on primal regions. -/
theorem dualData_singleton_workWeight_lt (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D)
    (M : ℕ) (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length) (hn : 0 < x.n)
    (hr : x.regions.length ≤ M) (hE : 0 < x.ends.length)
    (v : Fin (x.dualData L hR g).n) :
    ((x.dualData L hR g).singletonData v).workWeight (M + 1) < x.workWeight (M + 1) := by
  have he := h.dualData_singleton_edges_lt hS hd L hR g hE v
  have hv := gm06SingletonData_n_lt (x.dualData L hR g) v
  have hy : (x.dualData L hR g).n = x.regions.length := rfl
  apply x.workWeight_lt_of_mass (M + 1) _ hn
  exact x.workMass_lt_of_edges M _ (by omega) he

end GraphMinor.Compute.GM06DrawingRep
