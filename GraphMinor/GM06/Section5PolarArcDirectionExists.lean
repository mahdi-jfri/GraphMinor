module

public import GraphMinor.GM06.Section5PolarTwoArcChoice
import GraphMinor.GM06.Section5PolarAngularProjection

/-!
# Each cuff arc supplies a polar direction

For VI (5.7), page 133, each of the two cuff arcs has a positive
point inside the polar chart. Move that point radially to the rim.
The ray stays in the cuff and must choose one of the two arcs.
It cannot choose the other arc, since their only common points
are the two ends and the chosen point is an interior arc point.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Each initial arc in a two-arc closed nice circle has a polar
rim direction carried by that arc, when the chart misses the far end. -/
theorem exists_polar_direction_on_first_of_two_arcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (f g : I → S) (hfg : IsTwoArcs f g) (hf0 : f 0 = v)
    (hfar : f 1 ∉ range Φ)
    (hCclosed : IsClosed (range f ∪ range g))
    (hCnice : IsGammaNice Γ (range f ∪ range g)) :
    ∃ w : Circle, range (polarRayMap Φ w) ⊆ range f := by
  let V := f ⁻¹' interior (range Φ)
  have hVo : IsOpen V := isOpen_interior.preimage hfg.arc_left.1
  have h0V : (0 : I) ∈ V := by
    change f 0 ∈ interior (range Φ)
    rw [hf0]
    exact hp.nhd
  have h0cl : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
    rw [closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨a, haV, ha⟩ := mem_closure_iff.mp h0cl V hVo h0V
  have ha0 : a ≠ 0 := unitInterval.pos_iff_ne_zero.mp ha.1
  have ha1 : a ≠ 1 := unitInterval.lt_one_iff_ne_one.mp ha.2
  have hay : f a ≠ v := fun hh => ha0 (hfg.arc_left.2 (hh.trans hf0.symm))
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  obtain ⟨c, hc, hcy⟩ := hrepr (f a) ⟨interior_subset haV, hay⟩
  let w := q (f a)
  have hw : polarRimMap Φ w ∈ range f ∪ range g := by
    obtain ⟨b, hb, hwb, hcb⟩ := hp.ray (polarDiscPoint 1 w)
      (polarDiscPoint_one_ne_centre w) c hc
    rw [discScale_polarDiscPoint_one, hcy] at hcb
    exact nice_atom hCnice hb ⟨f a, hcb, Or.inl (mem_range_self a)⟩ hwb
  rcases polar_ray_subset_one_of_two_arcs hp f g hfg hf0 hfar hCclosed hCnice hw with hf | hg
  · exact ⟨w, hf⟩
  · obtain ⟨r, hr⟩ := hg (mem_range_self c)
    have hfr : f a = g r := hcy.symm.trans hr.symm
    rcases hfg.meet a r hfr with h0 | h1
    · exact (ha0 h0.1).elim
    · exact (ha1 h1.1).elim

end GraphMinor.GM06
