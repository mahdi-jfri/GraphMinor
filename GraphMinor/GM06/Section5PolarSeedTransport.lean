module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5PolarChartPlaneMap
import GraphMinor.Surface.Wedge

/-!
# Transporting plane seed discs to a polar chart

For VI (5.5), page 130, an angular seed is constructed in the
complex unit disc. The plane map of the polar chart carries it
to a closed disc in the surface. Injectivity preserves both the
boundary and the interior, so the attachment and the enclosed
local drawing pieces keep their required positions.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

/-- A plane seed inside the unit ball transfers to the polar chart,
with its boundary and interior given by the same coordinate map. -/
theorem exists_seed_disc_image_in_polar_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {s : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {D : Set ℂ} (hD : IsClosedDisc D) (hDb : D ⊆ closedBall 0 1) :
    ∃ F : ℂ → S, F 0 = s ∧ IsClosedDisc (F '' D) ∧
      discBd (F '' D) = F '' discBd D ∧
      discInt (F '' D) = F '' discInt D ∧
      ∀ (z : ℂ) (hz : z ∈ closedBall 0 1),
        F z = Φ ⟨planeOf z, by
          simpa only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
            using mem_closedBall_zero_iff.mp hz⟩ := by
  obtain ⟨F, hFc, hFi, hF0, hF⟩ := exists_plane_map_of_polar_chart hp
  have hi : InjOn F D := hFi.mono hDb
  obtain ⟨hE, hEb⟩ := isClosedDisc_image_injOn hD hD.isCompact (hFc.mono hDb) hi
  refine ⟨F, hF0, hE, hEb, ?_, hF⟩
  change F '' D \ discBd (F '' D) = F '' (D \ discBd D)
  rw [hEb, hi.image_sdiff_subset (GraphMinor.Surface.discBd_subset D)]

end GraphMinor.GM06
