module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRay
public import GraphMinor.Surface.DiscGrow

/-!
# A polar cuff ray chooses one of two cuff arcs

For the side test in VI (5.7), page 133, split the initial cuff
into two arcs from its initial vertex to a second point. Choose
the polar chart to miss that second point. A positive cuff ray
misses both common ends and is connected, so it lies entirely in
one of the two arcs. Its centre then lies in that same arc.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

private theorem subset_one_of_two_closed
    {X : Type*} [TopologicalSpace X] {B A C : Set X}
    (hB : IsPreconnected B) (hAc : IsClosed A) (hCc : IsClosed C)
    (hcover : B ⊆ A ∪ C) (hno : B ∩ (A ∩ C) = ∅) : B ⊆ A ∨ B ⊆ C := by
  by_cases hBA : B ⊆ A
  · exact Or.inl hBA
  right
  obtain ⟨x, hxB, hxA⟩ := not_subset.mp hBA
  have hxC : x ∈ C := (hcover hxB).resolve_left hxA
  intro y hyB
  by_contra hyC
  have hyA : y ∈ A := (hcover hyB).resolve_right hyC
  obtain ⟨z, hz⟩ := isPreconnected_closed_iff.mp hB _ _ hAc hCc hcover
    ⟨y, hyB, hyA⟩ ⟨x, hxB, hxC⟩
  rw [hno] at hz
  exact hz

/-- If a polar chart misses the far common endpoint of two arcs,
a ray on their closed nice union uses exactly one of those arcs. -/
theorem polar_ray_subset_one_of_two_arcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (f g : I → S) (hfg : IsTwoArcs f g) (hf0 : f 0 = v)
    (hfar : f 1 ∉ range Φ)
    (hCclosed : IsClosed (range f ∪ range g))
    (hCnice : IsGammaNice Γ (range f ∪ range g))
    {w : Circle} (hw : polarRimMap Φ w ∈ range f ∪ range g) :
    range (polarRayMap Φ w) ⊆ range f ∨ range (polarRayMap Φ w) ⊆ range g := by
  let ray := polarRayMap Φ w
  let B := ray '' Ioi (0 : I)
  have hBcover : B ⊆ range f ∪ range g := by
    rintro _ ⟨t, _, rfl⟩
    have hh := hp.star hCclosed hCnice hw t
    rwa [discScale_polarDiscPoint_one] at hh
  have hBno : B ∩ (range f ∩ range g) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨t, ht, hty⟩, ⟨r, hry⟩, ⟨s, hsy⟩⟩
    rcases hfg.meet r s (hry.trans hsy.symm) with h0 | h1
    · have hy0 : y = v := by rw [← hry, h0.1, hf0]
      have hray0 : ray t = ray 0 := by
        rw [hty, hy0, polarRayMap_zero, hp.centre]
      have ht0 : t ≠ 0 := unitInterval.pos_iff_ne_zero.mp ht
      exact ht0 ((isArcMap_polarRayMap hp.inj w).2 hray0)
    · have hy1 : y = f 1 := by rw [← hry, h1.1]
      exact hfar (hy1 ▸ hty ▸ mem_range_self (polarDiscPoint t w))
  have hchoice : B ⊆ range f ∨ B ⊆ range g :=
    subset_one_of_two_closed (isPreconnected_Ioi.image ray ray.continuous.continuousOn)
      (isCompact_range hfg.arc_left.1).isClosed (isCompact_range hfg.arc_right.1).isClosed
      hBcover hBno
  have hzero : ray 0 = v := (polarRayMap_zero Φ w).trans hp.centre
  have hpromote (A : Set S) (hvA : v ∈ A) (hBA : B ⊆ A) : range ray ⊆ A := by
    rintro _ ⟨t, rfl⟩
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht | ht
    · have ht0 : t = 0 := Subtype.ext ht.symm
      rwa [ht0, hzero]
    · exact hBA (mem_image_of_mem ray ht)
  rcases hchoice with hh | hh
  · exact Or.inl (hpromote _ ⟨0, hf0⟩ hh)
  · exact Or.inr (hpromote _ ⟨0, hfg.zero.trans hf0⟩ hh)

end GraphMinor.GM06
