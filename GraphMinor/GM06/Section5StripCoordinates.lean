module

public import GraphMinor.GM06.Section5StraightStrip
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# Coordinates agreeing on the linkage paths

For Reduction 3 of VI, page 129, map a straight rectangle onto the
disc between two proper strip arcs. The four-side extension theorem
prescribes both linkage curves and the cuff intervals. Its inverse
proves injectivity, and its surjectivity gives the entire strip disc.
Thus adjacent strip charts use the same parameter on a shared path.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface Complex

/-- A closed disc between two proper strip arcs admits square
coordinates matching both path parameters and the cuff intervals.
These are the compatible strip charts used for Reduction 3. -/
theorem exists_coordinates_of_proper_strip_arcs
    (f g : C(unitInterval, ℂ)) (hf : IsArcMap f) (hg : IsArcMap g)
    (hf0 : (f 0).re = 1) (hg0 : (g 0).re = 1)
    (hf1 : (f 1).re = 2) (hg1 : (g 1).re = 2)
    (hfmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).re ∧ (f t).re < 2)
    (hgmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (g t).re ∧ (g t).re < 2)
    (hdis : Disjoint (range f) (range g))
    (ho0 : (f 0).im < (g 0).im) (ho1 : (f 1).im < (g 1).im)
    {D : Set ℂ} (hD : IsClosedDisc D)
    (hDb : discBd D = range f ∪ range g ∪
      (({1} : Set ℝ) ×ℂ Icc (f 0).im (g 0).im) ∪
      (({2} : Set ℝ) ×ℂ Icc (f 1).im (g 1).im)) :
    ∃ F : C(unitInterval × unitInterval, ℂ),
      Function.Injective F ∧ range F = D ∧
      (∀ t, F (0, t) = f t) ∧ (∀ t, F (1, t) = g t) ∧
      (∀ u, F (u, 0) = section5AngularSegment 1 (f 0).im (g 0).im u) ∧
      (∀ u, F (u, 1) = section5AngularSegment 2 (f 1).im (g 1).im u) := by
  let W := Icc (1 : ℝ) 2 ×ℂ Icc (0 : ℝ) 1
  have hW := straight_strip_disc_and_boundary
  have hquad := isQuad_of_proper_strip_arcs f g hf hg hf0 hg0 hf1 hg1 hfmid hgmid hdis ho0 ho1
  have hb : discBd D = quadSet (section5AngularSegment 1 (f 0).im (g 0).im) f g
      (section5AngularSegment 2 (f 1).im (g 1).im) := by
    rw [hDb, quadSet, range_section5AngularSegment ho0, range_section5AngularSegment ho1]
    ext z
    simp only [mem_union]
    tauto
  obtain ⟨h, k, hm, hbot, hleft, hright, htop⟩ := exists_closed_disc_match_of_quads
    hW.1 hD isQuad_straight_strip hquad hW.2 hb
  let ψ : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun q => ⟨1 + q.2.1, q.1.1⟩,
      Complex.equivRealProdCLM.symm.continuous.comp
        ((continuous_const.add (continuous_subtype_val.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp continuous_fst))⟩
  have hψW (q : unitInterval × unitInterval) : ψ q ∈ W := by
    apply Complex.mem_reProdIm.mpr
    exact ⟨⟨by change 1 ≤ 1 + q.2.1; linarith only [q.2.2.1],
      by change 1 + q.2.1 ≤ 2; linarith only [q.2.2.2]⟩, q.1.2⟩
  have hψonto : SurjOn ψ univ W := by
    intro z hz
    obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.mp hz
    refine ⟨(⟨z.im, hzi⟩, ⟨z.re - 1, ⟨by linarith only [hzr.1], by linarith only [hzr.2]⟩⟩),
      mem_univ _, ?_⟩
    apply Complex.ext
    · change 1 + (z.re - 1) = z.re
      ring
    · rfl
  let F : C(unitInterval × unitInterval, ℂ) :=
    ⟨h ∘ ψ, hm.2.2.2.2.1.comp_continuous ψ.continuous hψW⟩
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b he
    have hab : ψ a = ψ b := hm.2.2.1.injOn (hψW a) (hψW b) he
    apply Prod.ext
    · exact Subtype.ext (congrArg Complex.im hab)
    · apply Subtype.ext
      have hr : 1 + a.2.1 = 1 + b.2.1 := congrArg Complex.re hab
      exact add_left_cancel hr
  · ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact hm.1 (hψW q)
    · intro hz
      obtain ⟨q, _, hq⟩ := hψonto (hm.2.1 hz)
      refine ⟨q, ?_⟩
      change h (ψ q) = z
      rw [hq]
      exact hm.2.2.2.1 hz
  · intro t
    exact hleft t
  · intro t
    exact hright t
  · intro u
    change h (ψ (u, 0)) = _
    have he : ψ (u, 0) = section5AngularSegment 1 0 1 u := by
      apply Complex.ext
      · change 1 + (0 : ℝ) = 1
        ring
      · change u.1 = (1 - u.1) * 0 + u.1 * 1
        ring
    rw [he]
    exact hbot u
  · intro u
    change h (ψ (u, 1)) = _
    have he : ψ (u, 1) = section5AngularSegment 2 0 1 u := by
      apply Complex.ext
      · change 1 + (1 : ℝ) = 2
        norm_num
      · change u.1 = (1 - u.1) * 0 + u.1 * 1
        ring
    rw [he]
    exact htop u

end GraphMinor.GM06
