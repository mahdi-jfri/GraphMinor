module

public import GraphMinor.GM06.Section5QuadChart
public import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# The four parametrized sides of a strip

For Reduction 3 of VI, page 129, two proper disjoint lifted paths
and the straight intervals between their cuff ends form the four
sides of a disc. Their intersections are exactly the four corners.
The ordered angular endpoints make the interval parametrizations
injective, so the four-side extension lemma applies.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Parametrize an interval on a line of constant radius in the
angular cover, viewed as the complex plane. -/
@[expose] noncomputable def section5AngularSegment (r a b : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => ⟨r, (1 - t.1) * a + t.1 * b⟩,
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk
        (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
          (continuous_subtype_val.mul continuous_const)))⟩

private theorem angularSegment_isArc {r a b : ℝ} (hab : a < b) :
    IsArcMap (section5AngularSegment r a b) := by
  refine ⟨(section5AngularSegment r a b).continuous, ?_⟩
  intro s t he
  have hi := congrArg Complex.im he
  change (1 - s.1) * a + s.1 * b = (1 - t.1) * a + t.1 * b at hi
  apply Subtype.ext
  nlinarith only [hi, hab]

private theorem eq_zero_of_re_one {f : C(unitInterval, ℂ)}
    (h1 : (f 1).re = 2)
    (hm : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).re ∧ (f t).re < 2)
    {t : unitInterval} (ht : (f t).re = 1) : t = 0 := by
  by_contra hn
  by_cases ht1 : t = 1
  · rw [ht1, h1] at ht
    norm_num at ht
  · have hmid := hm t ⟨unitInterval.pos_iff_ne_zero.mpr hn,
      unitInterval.lt_one_iff_ne_one.mpr ht1⟩
    linarith only [hmid.1, ht]

private theorem eq_one_of_re_two {f : C(unitInterval, ℂ)}
    (h0 : (f 0).re = 1)
    (hm : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).re ∧ (f t).re < 2)
    {t : unitInterval} (ht : (f t).re = 2) : t = 1 := by
  by_contra hn
  by_cases ht0 : t = 0
  · rw [ht0, h0] at ht
    norm_num at ht
  · have hmid := hm t ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
      unitInterval.lt_one_iff_ne_one.mpr hn⟩
    linarith only [hmid.2, ht]

/-- Two proper lifted linkage paths, together with the intervals
between their ends, satisfy the four-side matching conditions. -/
theorem isQuad_of_proper_strip_arcs (f g : C(unitInterval, ℂ))
    (hf : IsArcMap f) (hg : IsArcMap g)
    (hf0 : (f 0).re = 1) (hg0 : (g 0).re = 1)
    (hf1 : (f 1).re = 2) (hg1 : (g 1).re = 2)
    (hfmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).re ∧ (f t).re < 2)
    (hgmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (g t).re ∧ (g t).re < 2)
    (hdis : Disjoint (range f) (range g))
    (ho0 : (f 0).im < (g 0).im) (ho1 : (f 1).im < (g 1).im) :
    IsQuad (section5AngularSegment 1 (f 0).im (g 0).im) f g
      (section5AngularSegment 2 (f 1).im (g 1).im) := by
  have haff {a b : ℝ} (hab : a < b) {t : unitInterval}
      (he : (1 - t.1) * a + t.1 * b = a) : t = 0 := by
    apply Subtype.ext
    change t.1 = 0
    nlinarith only [hab, he]
  have baff {a b : ℝ} (hab : a < b) {t : unitInterval}
      (he : (1 - t.1) * a + t.1 * b = b) : t = 1 := by
    apply Subtype.ext
    change t.1 = 1
    nlinarith only [hab, he]
  refine ⟨angularSegment_isArc ho0, hf, hg, angularSegment_isArc ho1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Complex.ext
    · exact hf0.symm
    · change (1 - (0 : ℝ)) * (f 0).im + 0 * (g 0).im = (f 0).im
      ring
  · apply Complex.ext
    · exact hg0.symm
    · change (1 - (1 : ℝ)) * (f 0).im + 1 * (g 0).im = (g 0).im
      ring
  · apply Complex.ext
    · exact hf1
    · change (f 1).im = (1 - (0 : ℝ)) * (f 1).im + 0 * (g 1).im
      ring
  · apply Complex.ext
    · exact hg1
    · change (g 1).im = (1 - (1 : ℝ)) * (f 1).im + 1 * (g 1).im
      ring
  · intro s t he
    have ht := eq_zero_of_re_one hf1 hfmid (congrArg Complex.re he).symm
    subst t
    exact ⟨haff ho0 (congrArg Complex.im he), rfl⟩
  · intro s t he
    have ht := eq_zero_of_re_one hg1 hgmid (congrArg Complex.re he).symm
    subst t
    exact ⟨baff ho0 (congrArg Complex.im he), rfl⟩
  · intro s t he
    exact disjoint_left.mp hdis (mem_range_self s) ⟨t, he.symm⟩
  · intro s t he
    have hs := eq_one_of_re_two hf0 hfmid (congrArg Complex.re he)
    subst s
    exact ⟨rfl, haff ho1 (congrArg Complex.im he).symm⟩
  · intro s t he
    have hs := eq_one_of_re_two hg0 hgmid (congrArg Complex.re he)
    subst s
    exact ⟨rfl, baff ho1 (congrArg Complex.im he).symm⟩
  · intro s t he
    have hr : (1 : ℝ) = 2 := congrArg Complex.re he
    norm_num at hr

/-- The parametrized angular side has exactly the interval between
its ordered endpoints as its range. -/
theorem range_section5AngularSegment {r a b : ℝ} (hab : a < b) :
    range (section5AngularSegment r a b) = ({r} : Set ℝ) ×ℂ Icc a b := by
  have hc : Continuous (fun t : unitInterval => (section5AngularSegment r a b t).im) :=
    Complex.continuous_im.comp (section5AngularSegment r a b).continuous
  have h0 : (section5AngularSegment r a b 0).im = a := by
    change (1 - (0 : ℝ)) * a + 0 * b = a
    ring
  have h1 : (section5AngularSegment r a b 1).im = b := by
    change (1 - (1 : ℝ)) * a + 1 * b = b
    ring
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    apply Complex.mem_reProdIm.mpr
    refine ⟨rfl, ?_⟩
    change a ≤ (1 - t.1) * a + t.1 * b ∧ (1 - t.1) * a + t.1 * b ≤ b
    constructor <;> nlinarith only [hab, t.2.1, t.2.2]
  · intro hz
    obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.mp hz
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (zero_le_one' unitInterval) hc.continuousOn
      (show z.im ∈ Icc (section5AngularSegment r a b 0).im
        (section5AngularSegment r a b 1).im by rwa [h0, h1])
    exact ⟨t, Complex.ext (mem_singleton_iff.mp hzr).symm ht⟩

end GraphMinor.GM06
