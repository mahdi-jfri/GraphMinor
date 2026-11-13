module

public import GraphMinor.GM06.Section5StripQuad
import GraphMinor.Surface.Cap
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# The straight strip used for contraction coordinates

For Reduction 3 of VI, page 129, a linkage strip is matched to a
rectangle. The straight radial paths and the two angular intervals
form its four parametrized sides. Their union is exactly the disc
boundary, so the four-side extension lemma gives the needed model.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface Complex

/-- A straight radial path from radius one to radius two. -/
@[expose] noncomputable def section5RadialSegment (a : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => ⟨1 + t.1, a⟩,
    Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_const.add continuous_subtype_val).prodMk continuous_const)⟩

private theorem radialSegment_isArc (a : ℝ) : IsArcMap (section5RadialSegment a) := by
  refine ⟨(section5RadialSegment a).continuous, ?_⟩
  intro s t he
  have hr := congrArg Complex.re he
  change 1 + s.1 = 1 + t.1 at hr
  exact Subtype.ext (add_left_cancel hr)

/-- The straight rectangle satisfies the four-side corner conditions. -/
theorem isQuad_straight_strip :
    IsQuad (section5AngularSegment 1 0 1) (section5RadialSegment 0)
      (section5RadialSegment 1) (section5AngularSegment 2 0 1) := by
  apply isQuad_of_proper_strip_arcs (section5RadialSegment 0) (section5RadialSegment 1)
    (radialSegment_isArc 0) (radialSegment_isArc 1)
  · change 1 + (0 : ℝ) = 1
    ring
  · change 1 + (0 : ℝ) = 1
    ring
  · change 1 + (1 : ℝ) = 2
    norm_num
  · change 1 + (1 : ℝ) = 2
    norm_num
  · intro t ht
    change 1 < 1 + t.1 ∧ 1 + t.1 < 2
    have h0 : (0 : ℝ) < t.1 := ht.1
    have h1 : t.1 < 1 := ht.2
    constructor <;> linarith only [h0, h1]
  · intro t ht
    change 1 < 1 + t.1 ∧ 1 + t.1 < 2
    have h0 : (0 : ℝ) < t.1 := ht.1
    have h1 : t.1 < 1 := ht.2
    constructor <;> linarith only [h0, h1]
  · apply disjoint_left.mpr
    rintro z ⟨s, rfl⟩ ⟨t, he⟩
    have hh : (1 : ℝ) = 0 := congrArg Complex.im he
    norm_num at hh
  · change (0 : ℝ) < 1
    norm_num
  · change (0 : ℝ) < 1
    norm_num

/-- The points of a straight radial side are exactly its vertical interval. -/
theorem range_section5RadialSegment (a : ℝ) :
    range (section5RadialSegment a) = Icc (1 : ℝ) 2 ×ℂ {a} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    change (1 ≤ 1 + t.1 ∧ 1 + t.1 ≤ 2) ∧ a ∈ ({a} : Set ℝ)
    exact ⟨⟨by linarith only [t.2.1], by linarith only [t.2.2]⟩, rfl⟩
  · intro hz
    obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.mp hz
    have hzi' : z.im = a := mem_singleton_iff.mp hzi
    refine ⟨⟨z.re - 1, ⟨by linarith only [hzr.1], by linarith only [hzr.2]⟩⟩, ?_⟩
    apply Complex.ext
    · change 1 + (z.re - 1) = z.re
      ring
    · exact hzi'.symm

/-- The angular sides of the model rectangle use their interval coordinate. -/
theorem range_section5AngularSegment_zero_one (r : ℝ) :
    range (section5AngularSegment r 0 1) = ({r} : Set ℝ) ×ℂ Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    apply Complex.mem_reProdIm.mpr
    refine ⟨rfl, ?_⟩
    change (1 - t.1) * 0 + t.1 * 1 ∈ Icc (0 : ℝ) 1
    simpa only [mul_zero, mul_one, zero_add] using t.2
  · intro hz
    obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.mp hz
    refine ⟨⟨z.im, hzi⟩, ?_⟩
    apply Complex.ext
    · exact (mem_singleton_iff.mp hzr).symm
    · change (1 - z.im) * 0 + z.im * 1 = z.im
      ring

/-- The four straight sides form exactly the boundary of a closed rectangle. -/
theorem straight_strip_disc_and_boundary :
    IsClosedDisc (Icc (1 : ℝ) 2 ×ℂ Icc (0 : ℝ) 1) ∧
      discBd (Icc (1 : ℝ) 2 ×ℂ Icc (0 : ℝ) 1) =
        quadSet (section5AngularSegment 1 0 1) (section5RadialSegment 0)
          (section5RadialSegment 1) (section5AngularSegment 2 0 1) := by
  obtain ⟨hD, hDb⟩ := isClosedDisc_rect (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨hD, ?_⟩
  rw [hDb, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
    frontier_Icc (by norm_num : (1 : ℝ) ≤ 2), frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  rw [quadSet, range_section5RadialSegment, range_section5RadialSegment,
    range_section5AngularSegment_zero_one, range_section5AngularSegment_zero_one]
  ext z
  simp only [Complex.mem_reProdIm, mem_union, mem_insert_iff, mem_singleton_iff]
  tauto

end GraphMinor.GM06
