module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section5PolarSubdrawingRegions
import GraphMinor.GM11.Regions

/-!
# Projecting a retained region onto the polar rim

In VI (5.5), page 130, the angular projection of a punctured local
piece of a retained region remains in that region on the rim.
Represent each point at its positive radial scale and use the fact
that retained-region membership is unchanged along a polar ray.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The polar angular projection is continuous on the punctured
disc and takes every local point of a retained region back to
that same region on the rim. -/
theorem exists_region_preserving_polar_angular_projection
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {r : Set S} (hr : r ∈ T.R) (hsT : s ∈ T.U) :
    ∃ q : S → Circle, ContinuousOn q (range Φ \ {s}) ∧
      (∀ (c : I), 0 < c → ∀ w : Circle, q (Φ (polarDiscPoint c w)) = w) ∧
      ∀ y ∈ range Φ ∩ r, polarRimMap Φ (q y) ∈ r := by
  obtain ⟨q, hqc, hqr, hrepr⟩ := exists_polar_angular_projection hp
  refine ⟨q, hqc, hqr, ?_⟩
  intro y hy
  have hys : y ≠ s := fun he => region_subset hr (he ▸ hy.2) hsT
  obtain ⟨c, hc, he⟩ := hrepr y ⟨hy.1, hys⟩
  have hi : Φ (discScale c (polarDiscPoint 1 (q y))) ∈ r := by
    rw [discScale_polarDiscPoint_one, he]
    exact hy.2
  exact (polar_ray_mem_region_of_subdrawing_iff hT hp hr
    (polarDiscPoint_one_ne_centre (q y)) c hc).mpr hi

end GraphMinor.GM06
