module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5CompactAngularCoordinates
import GraphMinor.GM06.Section5AngularSeedDisc
import GraphMinor.GM06.Section5PolarSeedTransport
import GraphMinor.GM06.Section5PolarSubdrawingRegions
import GraphMinor.Surface.DiscTwist

/-!
# A seed disc around a compact set of rim directions

For the enclosure in VI (5.5), page 130, take a compact set of
discarded directions within an open arc belonging to one retained
region. Choose angular coordinates enclosing those directions and
transport the resulting half-disc into the polar chart. Ray
containment puts the whole disc in that region with its attachment
added. Every discarded direction lies in its interior at smaller
positive radii.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A compact set of rim directions inside an open region arc has
an attached seed disc enclosing every smaller positive radial point. -/
theorem exists_seed_for_compact_rim_arc
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {r : Set S} (hr : r ∈ T.R)
    {a : I → Circle} (ha : IsArcMap a)
    (har : ∀ w ∈ range a \ {a 0, a 1}, polarRimMap Φ w ∈ r)
    {K : Set Circle} (hK : IsCompact K) (hne : K.Nonempty)
    (hKa : K ⊆ range a) (h0 : a 0 ∉ K) (h1 : a 1 ∉ K) :
    ∃ E : Set S, IsClosedDisc E ∧ s ∈ discBd E ∧ E ⊆ r ∪ {s} ∧
      ∀ c : I, 0 < c → c < 1 → ∀ w ∈ K,
        Φ (polarDiscPoint c w) ∈ discInt E := by
  obtain ⟨h, hKh, hh⟩ := exists_angular_coordinates_enclosing_compact_arc_part ha hK hne hKa h0 h1
  obtain ⟨D, hD, h0D, hDn, hDm, hDi⟩ := exists_angular_seed_disc h
  have hDb : D ⊆ closedBall 0 1 := fun z hz => mem_closedBall_zero_iff.mpr (hDn z hz)
  obtain ⟨F, hF0, hE, hEb, hEi, hF⟩ := exists_seed_disc_image_in_polar_chart hp hD hDb
  have hrad (c : I) (w : Circle) : F ((c : ℂ) * w) = Φ (polarDiscPoint c w) := by
    have hz : (c : ℂ) * w ∈ closedBall 0 1 := by
      apply mem_closedBall_zero_iff.mpr
      simpa [norm_mul, Complex.norm_real, Real.norm_of_nonneg c.2.1] using c.2.2
    exact hF _ hz
  refine ⟨F '' D, hE, ?_, ?_, ?_⟩
  · rw [hEb]
    exact ⟨0, h0D, hF0⟩
  · rintro y ⟨z, hzD, rfl⟩
    by_cases hz0 : z = 0
    · exact Or.inr (by rw [hz0, hF0]; rfl)
    · let w := unitOf z hz0
      let c : I := ⟨‖z‖, norm_nonneg _, hDn z hzD⟩
      have hc : 0 < c := norm_pos_iff.mpr hz0
      have he : (c : ℂ) * w = z := norm_mul_unitOf z hz0
      have hm : 0 ≤ ((h.symm w : Circle) : ℂ).im := by
        apply (hDm ‖z‖ hc (hDn z hzD) (h.symm w)).mp
        change (c : ℂ) * h (h.symm w) ∈ D
        rw [h.apply_symm_apply, he]
        exact hzD
      have hrim : polarRimMap Φ w ∈ r := by
        have hew := hh (h.symm w) hm
        rw [h.apply_symm_apply] at hew
        exact har w hew
      have hray := polar_ray_mem_region_of_subdrawing hT hp hr
        (polarDiscPoint_one_ne_centre w) hrim c hc
      rw [discScale_polarDiscPoint_one] at hray
      exact Or.inl (by rw [← he, hrad]; exact hray)
  · intro c hc hc1 w hw
    rw [hEi]
    refine ⟨(c : ℂ) * w, ?_, hrad c w⟩
    have hi := hDi (c : ℝ) hc hc1 (h.symm w) (hKh w hw)
    simpa only [h.apply_symm_apply] using hi

end GraphMinor.GM06
