module

public import GraphMinor.GM06.Section5PolarArcDirectionExists
public import GraphMinor.GM06.Section5PolarInitialArc

/-!
# The two polar directions of a cuff

For VI (5.7), page 133, split a cuff into two arcs with the
initial vertex as one common end. A polar chart missing the other
end has one direction on each arc. The directions are distinct,
since a radial segment cannot meet either common end positively.
Every cuff ray chooses one arc, so these are all its directions.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A closed nice circle split into two arcs has exactly two polar
rim directions, one carried by each arc, if the chart misses the far end. -/
theorem exists_two_polar_rim_directions_of_two_arcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (f g : I → S) (hfg : IsTwoArcs f g) (hf0 : f 0 = v)
    (hfar : f 1 ∉ range Φ)
    (hCclosed : IsClosed (range f ∪ range g))
    (hCnice : IsGammaNice Γ (range f ∪ range g)) :
    ∃ p c : Circle, p ≠ c ∧
      range (polarRayMap Φ p) ⊆ range f ∧
      range (polarRayMap Φ c) ⊆ range g ∧
      ∀ w : Circle, polarRimMap Φ w ∈ range f ∪ range g ↔ w = p ∨ w = c := by
  have hgf : IsTwoArcs g f := by
    refine ⟨hfg.arc_right, hfg.arc_left, hfg.zero.symm, hfg.one.symm, ?_⟩
    intro r s hrs
    rcases hfg.meet s r hrs.symm with h0 | h1
    · exact Or.inl ⟨h0.2, h0.1⟩
    · exact Or.inr ⟨h1.2, h1.1⟩
  obtain ⟨p, hpf⟩ := exists_polar_direction_on_first_of_two_arcs hp f g hfg hf0 hfar hCclosed hCnice
  obtain ⟨c, hcg⟩ := exists_polar_direction_on_first_of_two_arcs hp g f hgf
    (hfg.zero.trans hf0) (hfg.one ▸ hfar)
    (by simpa only [union_comm] using hCclosed) (by simpa only [union_comm] using hCnice)
  have hpc : p ≠ c := by
    intro hh
    obtain ⟨r, hr⟩ := hpf (mem_range_self 1)
    have hpg : polarRayMap Φ p 1 ∈ range g := by rw [hh]; exact hcg (mem_range_self 1)
    obtain ⟨s, hs⟩ := hpg
    rcases hfg.meet r s (hr.trans hs.symm) with h0 | h1
    · have h10 : polarRayMap Φ p 1 = polarRayMap Φ p 0 := by
        rw [← hr, h0.1, hf0, polarRayMap_zero, hp.centre]
      exact one_ne_zero ((isArcMap_polarRayMap hp.inj p).2 h10)
    · rw [h1.1] at hr
      exact hfar ⟨polarDiscPoint 1 p, hr.symm⟩
  refine ⟨p, c, hpc, hpf, hcg, ?_⟩
  intro w
  constructor
  · intro hw
    rcases polar_ray_subset_one_of_two_arcs hp f g hfg hf0 hfar hCclosed hCnice hw with hwf | hwg
    · exact Or.inl (polar_direction_eq_of_same_initial_arc hp ⟨f, hfg.arc_left.1⟩
        hfg.arc_left hf0 hwf hpf)
    · exact Or.inr (polar_direction_eq_of_same_initial_arc hp ⟨g, hfg.arc_right.1⟩
        hfg.arc_right (hfg.zero.trans hf0) hwg hcg)
  · rintro (rfl | rfl)
    · exact Or.inl (hpf (mem_range_self 1))
    · exact Or.inr (hcg (mem_range_self 1))

end GraphMinor.GM06
