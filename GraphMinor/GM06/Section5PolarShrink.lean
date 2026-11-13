module

public import GraphMinor.GM06.Section5PolarRay
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM06.Section5PolarInitialArc

/-!
# Keeping rim labels when a polar chart is shrunk

The rotation rows used in VI (5.7), page 133, label the directions
of one given vertex chart. Positive radial restriction preserves
membership in every nice set. Thus the local clockwise test can
use a smaller chart without changing the labels in the input row.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Radial scaling multiplies the radius without changing its direction. -/
theorem discScale_polarDiscPoint (a r : I) (w : Circle) :
    discScale a (polarDiscPoint r w) = polarDiscPoint (a * r) w := by
  rw [← discScale_polarDiscPoint_one r w, ← discScale_polarDiscPoint_one (a * r) w]
  apply Subtype.ext
  simp only [discScale, smul_smul, Set.Icc.coe_mul]

/-- Restricting a chart radially keeps each ray inside its original ray. -/
theorem polar_ray_range_subset_of_radial_restriction
    {S : Type u} [TopologicalSpace S] {Φ Ψ : C(ClosedUnitDisc, S)}
    (a : I) (hscale : ∀ x, Ψ x = Φ (discScale a x)) (w : Circle) :
    range (polarRayMap Ψ w) ⊆ range (polarRayMap Φ w) := by
  rintro _ ⟨r, rfl⟩
  refine ⟨a * r, ?_⟩
  change Φ (polarDiscPoint (a * r) w) = Ψ (polarDiscPoint r w)
  rw [hscale, discScale_polarDiscPoint]

/-- An arc carrying a direction in the input chart and a direction
in its restriction identifies those two direction labels. -/
theorem polar_direction_eq_of_radial_restriction_in_arc
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {v : S}
    {Φ Ψ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Ψ)
    (a : I) (hscale : ∀ x, Ψ x = Φ (discScale a x))
    (f : C(I, S)) (hf : IsArcMap f) (hf0 : f 0 = v) {w z : Circle}
    (hw : range (polarRayMap Ψ w) ⊆ range f)
    (hz : range (polarRayMap Φ z) ⊆ range f) : w = z := by
  exact polar_direction_eq_of_same_initial_arc hp f hf hf0 hw
    ((polar_ray_range_subset_of_radial_restriction a hscale z).trans hz)

/-- Positive radial restriction preserves membership in a nice set. -/
theorem polar_ray_mem_nice_iff
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {v : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {Z : Set S} (hn : IsGammaNice Γ Z) {x : ClosedUnitDisc} (hx : x ≠ polarCentre)
    (a : I) (ha : 0 < a) : Φ x ∈ Z ↔ Φ (discScale a x) ∈ Z := by
  obtain ⟨b, hb, hxb, hab⟩ := hp.ray x hx a ha
  exact ⟨fun h => nice_atom hn hb ⟨_, hxb, h⟩ hab,
    fun h => nice_atom hn hb ⟨_, hab, h⟩ hxb⟩

/-- A smaller chart with the same directions has the same nice-set rim labels. -/
theorem polar_rim_mem_nice_iff_of_radial_restriction
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {v : S}
    {Φ Ψ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (a : I) (ha : 0 < a) (hscale : ∀ x, Ψ x = Φ (discScale a x))
    {Z : Set S} (hn : IsGammaNice Γ Z) (w : Circle) :
    polarRimMap Φ w ∈ Z ↔ polarRimMap Ψ w ∈ Z := by
  change Φ (polarDiscPoint 1 w) ∈ Z ↔ Ψ (polarDiscPoint 1 w) ∈ Z
  rw [hscale]
  exact polar_ray_mem_nice_iff hp hn (polarDiscPoint_one_ne_centre w) a ha

end GraphMinor.GM06
