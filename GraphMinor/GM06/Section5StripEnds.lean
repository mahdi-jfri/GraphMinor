module

public import GraphMinor.Surface.Defs
import Mathlib.Topology.UnitInterval

/-!
# The ends of a proper strip curve

The lifted paths used in VI (5.1), page 129, have radial coordinate
1 at the start, 2 at the end, and strictly intermediate coordinates
elsewhere. Thus they meet either radial boundary line only at its
specified end. This ensures that joining consecutive lifted paths
by their two boundary intervals introduces no other intersections.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- A proper curve across the radial strip meets its first boundary
line only at its initial parameter. -/
theorem eq_zero_of_strip_radius_one
    {f : unitInterval → ℝ × ℝ} (h1 : (f 1).1 = 2)
    (hmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).1 ∧ (f t).1 < 2)
    {t : unitInterval} (ht : (f t).1 = 1) : t = 0 := by
  by_contra ht0
  by_cases ht1 : t = 1
  · subst t
    rw [h1] at ht
    norm_num at ht
  · have hI : t ∈ Ioo (0 : unitInterval) 1 :=
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
    have hlt := (hmid t hI).1
    rw [ht] at hlt
    exact lt_irrefl _ hlt

/-- A proper curve across the radial strip meets its second boundary
line only at its terminal parameter. -/
theorem eq_one_of_strip_radius_two
    {f : unitInterval → ℝ × ℝ} (h0 : (f 0).1 = 1)
    (hmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).1 ∧ (f t).1 < 2)
    {t : unitInterval} (ht : (f t).1 = 2) : t = 1 := by
  by_contra ht1
  by_cases ht0 : t = 0
  · subst t
    rw [h0] at ht
    norm_num at ht
  · have hI : t ∈ Ioo (0 : unitInterval) 1 :=
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
    have hlt := (hmid t hI).2
    rw [ht] at hlt
    exact lt_irrefl _ hlt

/-- The first radial boundary line meets a proper strip curve exactly
at its initial point. -/
theorem inter_range_strip_curve_radius_one
    {f : unitInterval → ℝ × ℝ} (h0 : (f 0).1 = 1) (h1 : (f 1).1 = 2)
    (hmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).1 ∧ (f t).1 < 2) :
    {p : ℝ × ℝ | p.1 = 1} ∩ range f = {f 0} := by
  ext p
  constructor
  · rintro ⟨hp, t, rfl⟩
    exact mem_singleton_iff.mpr (congrArg f (eq_zero_of_strip_radius_one h1 hmid hp))
  · intro hp
    have hp0 : p = f 0 := mem_singleton_iff.mp hp
    subst p
    exact ⟨h0, mem_range_self 0⟩

/-- The second radial boundary line meets a proper strip curve exactly
at its terminal point. -/
theorem inter_range_strip_curve_radius_two
    {f : unitInterval → ℝ × ℝ} (h0 : (f 0).1 = 1) (h1 : (f 1).1 = 2)
    (hmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).1 ∧ (f t).1 < 2) :
    {p : ℝ × ℝ | p.1 = 2} ∩ range f = {f 1} := by
  ext p
  constructor
  · rintro ⟨hp, t, rfl⟩
    exact mem_singleton_iff.mpr (congrArg f (eq_one_of_strip_radius_two h0 hmid hp))
  · intro hp
    have hp1 : p = f 1 := mem_singleton_iff.mp hp
    subst p
    exact ⟨h1, mem_range_self 1⟩

end GraphMinor.GM06
