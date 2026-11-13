module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarDiscInterior
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section5PolarSubdrawingRegions
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.Regions

/-!
# Local discarded points come from discarded rim directions

For VI (5.5), page 130, both sides of the separation are subdrawings
of the full polar drawing. Radial normalization preserves the
subdrawing atom containing a point. It also preserves its retained
region. Thus a local discarded point in that region lies at a
strictly smaller positive radius along one of its discarded rim
directions.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A local point of one subdrawing in a region of another has a
direction on the rim belonging to that same subdrawing and region. -/
theorem exists_rim_direction_of_local_subdrawing_region_point
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    (hS : IsClosedSurface S) {Γ T H : Drawing S}
    (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ) (hsT : s ∈ T.U)
    {r : Set S} (hr : r ∈ T.R) {y : S}
    (hy : y ∈ interior (range Φ)) (hyH : y ∈ H.U) (hyr : y ∈ r) :
    ∃ (c : I) (w : Circle), 0 < c ∧ c < 1 ∧
      Φ (polarDiscPoint c w) = y ∧ polarRimMap Φ w ∈ H.U ∩ r := by
  have hys : y ≠ s := fun he => region_subset hr (he ▸ hyr) hsT
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  obtain ⟨c, hc, he⟩ := hrepr y ⟨interior_subset hy, hys⟩
  have hc1 : c < 1 := by
    have hh := norm_lt_one_of_mem_interior_polar_disc hS hp (he.symm ▸ hy)
    rwa [norm_polarDiscPoint] at hh
  have hn : IsGammaNice Γ H.U := isGammaNice_of_frontier hH subset_rfl
    (frontier_subset_closure.trans (by rw [H.isClosed_U.closure_eq]))
  obtain ⟨a, ha, hwa, hca⟩ := hp.ray (polarDiscPoint 1 (q y))
    (polarDiscPoint_one_ne_centre (q y)) c hc
  rw [discScale_polarDiscPoint_one, he] at hca
  have hwH : polarRimMap Φ (q y) ∈ H.U := nice_atom hn ha ⟨y, hca, hyH⟩ hwa
  have hwr : polarRimMap Φ (q y) ∈ r := by
    apply (polar_ray_mem_region_of_subdrawing_iff hT hp hr
      (polarDiscPoint_one_ne_centre (q y)) c hc).mpr
    rw [discScale_polarDiscPoint_one, he]
    exact hyr
  exact ⟨c, q y, hc, hc1, he, hwH, hwr⟩

end GraphMinor.GM06
