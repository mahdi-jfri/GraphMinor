module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRay
import GraphMinor.GM06.Section5InitialSubarcsMeet

/-!
# A single initial arc carries at most one polar direction

For the cuff sides in VI (5.7), page 133, each of the two arcs
from the initial vertex to a second cuff point carries one local
direction. Uniqueness uses only injectivity of the arc: two radial
segments on it would be initial subarcs of the same arc, hence
would meet away from the centre and have the same direction.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Two positive polar rays carried by the same arc starting at
the centre have the same direction. -/
theorem polar_direction_eq_of_same_initial_arc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (f : C(I, S)) (hf : IsArcMap f) (hf0 : f 0 = v) {w z : Circle}
    (hw : range (polarRayMap Φ w) ⊆ range f)
    (hz : range (polarRayMap Φ z) ⊆ range f) : w = z := by
  have hstart (d : Circle) : polarRayMap Φ d 0 = f 0 := by
    rw [polarRayMap_zero, hp.centre, hf0]
  obtain ⟨r, s, hr, _, hrs⟩ := exists_positive_meeting_of_initial_subarcs f
    (polarRayMap Φ w) (polarRayMap Φ z) hf
    (isArcMap_polarRayMap hp.inj w) (isArcMap_polarRayMap hp.inj z)
    hw hz (hstart w) (hstart z)
  exact polarDiscPoint_direction_eq hr (hp.inj hrs)

end GraphMinor.GM06
