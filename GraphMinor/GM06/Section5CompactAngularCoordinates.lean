module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5CompactArcInterval
import GraphMinor.GM06.Section5CircleArcCoordinates
import GraphMinor.Surface.PushOff
import GraphMinor.GM11.RadialCorners

/-!
# Angular coordinates enclosing a compact part of a corner

In VI (5.5), page 130, the discarded drawing on the rim lies in
an open corner arc. A smaller closed subarc contains this compact
set away from its ends. Complete that subarc to the circle and
choose coordinates in which it is the upper half-circle. The
compact set then has strictly positive imaginary coordinate.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A compact subset of the open part of a circle arc admits angular
coordinates putting it strictly above the real axis, while the
whole upper half-circle remains in that open arc. -/
theorem exists_angular_coordinates_enclosing_compact_arc_part
    {a : unitInterval → Circle} (ha : IsArcMap a)
    {K : Set Circle} (hK : IsCompact K) (hne : K.Nonempty)
    (hKa : K ⊆ range a) (h0 : a 0 ∉ K) (h1 : a 1 ∉ K) :
    ∃ h : Circle ≃ₜ Circle,
      (∀ z ∈ K, 0 < ((h.symm z : Circle) : ℂ).im) ∧
      ∀ w : Circle, 0 ≤ (w : ℂ).im → h w ∈ range a \ {a 0, a 1} := by
  obtain ⟨l, r, hl0, hlr, hr1, hKlr, hlrsub⟩ :=
    exists_closed_subinterval_enclosing_compact_arc_part ha hK hne hKa h0 h1
  have hline := GraphMinor.GM11.isLine_piece ha.1 ha.2 hlr
  have hcircle : IsOArc (univ : Set Circle) := ⟨(Homeomorph.Set.univ Circle).symm⟩
  obtain ⟨u, v, huv, huL, hu0, hu1, huvR⟩ :=
    exists_arcs_of_line hcircle hline (subset_univ _)
  obtain ⟨j, hj, hjends⟩ := exists_circle_homeomorph_respecting_two_arcs
    huv.arc_left huv.arc_right huv.zero.symm huv.one.symm huv.meet
  let e : (range u ∪ range v : Set Circle) ≃ₜ Circle :=
    (Homeomorph.setCongr huvR).trans (Homeomorph.Set.univ Circle)
  let h := j.trans e
  have hh (w : Circle) : h w = (j w).1 := rfl
  have hKu : K ⊆ range u := by
    intro z hz
    rw [huL]
    obtain ⟨t, ht, he⟩ := hKlr hz
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, he⟩
  have hK0 : u 0 ∉ K := by
    rw [hu0]
    intro hz
    obtain ⟨t, ht, he⟩ := hKlr hz
    have htl := ha.2 he
    exact ht.1.ne' htl
  have hK1 : u 1 ∉ K := by
    rw [hu1]
    intro hz
    obtain ⟨t, ht, he⟩ := hKlr hz
    have htr := ha.2 he
    exact ht.2.ne htr
  refine ⟨h, ?_, ?_⟩
  · intro z hz
    let w := h.symm z
    have hw : (j w).1 = z := (hh w).symm.trans (h.apply_symm_apply z)
    have hnonneg : 0 ≤ (w : ℂ).im := (hj w).mp (hw.symm ▸ hKu hz)
    apply lt_of_le_of_ne hnonneg
    intro he
    rcases hjends w he.symm with hleft | hright
    · exact hK0 ((hw.symm.trans hleft) ▸ hz)
    · exact hK1 ((hw.symm.trans hright) ▸ hz)
  · intro w hw
    rw [hh]
    apply hlrsub
    rw [← huL]
    exact (hj w).mpr hw

end GraphMinor.GM06
