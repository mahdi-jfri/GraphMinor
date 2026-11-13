module

public import GraphMinor.GM11.LocalCone
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.Regions

/-!
# Polar rays stay in a region of a subdrawing

For the local seed in VI (5.5), page 130, the polar chart belongs
to the full drawing, but the corner belongs to a retained subdrawing.
That subdrawing is a union of full-drawing atoms. A polar ray whose
rim point misses it therefore stays in one complementary region.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A polar ray starting in a region of a subdrawing stays in that
region at every positive radial scale. -/
theorem polar_ray_mem_region_of_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {r : Set S} (hr : r ∈ T.R) {x : ClosedUnitDisc}
    (hx : x ≠ polarCentre) (hxr : Φ x ∈ r)
    (c : I) (hc : 0 < c) : Φ (discScale c x) ∈ r := by
  have hn : IsGammaNice Γ T.U := isGammaNice_of_frontier hT subset_rfl
    (frontier_subset_closure.trans (by rw [T.isClosed_U.closure_eq]))
  obtain ⟨a, ha, hxa, hca⟩ := hp.ray x hx c hc
  have hd : Disjoint a T.U := by
    apply disjoint_left.mpr
    intro y hya hyT
    exact region_subset hr hxr (nice_atom hn ha ⟨y, hya, hyT⟩ hxa)
  exact subset_region hr (isPreconnected_atom ha) hd hxa hxr hca

/-- At positive radial scales, membership in a retained region is
unchanged in either direction along a polar ray. -/
theorem polar_ray_mem_region_of_subdrawing_iff
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {r : Set S} (hr : r ∈ T.R) {x : ClosedUnitDisc}
    (hx : x ≠ polarCentre) (c : I) (hc : 0 < c) :
    Φ x ∈ r ↔ Φ (discScale c x) ∈ r := by
  refine ⟨fun hxr => polar_ray_mem_region_of_subdrawing hT hp hr hx hxr c hc, ?_⟩
  intro hcr
  have hn : IsGammaNice Γ T.U := isGammaNice_of_frontier hT subset_rfl
    (frontier_subset_closure.trans (by rw [T.isClosed_U.closure_eq]))
  obtain ⟨a, ha, hxa, hca⟩ := hp.ray x hx c hc
  have hd : Disjoint a T.U := by
    apply disjoint_left.mpr
    intro y hya hyT
    exact region_subset hr hcr (nice_atom hn ha ⟨y, hya, hyT⟩ hca)
  exact subset_region hr (isPreconnected_atom ha) hd hca hcr hxa

end GraphMinor.GM06
