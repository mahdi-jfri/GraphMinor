module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Coordinates for contracting a boundary edge

Reduction 3 of VI, page 129, contracts an edge from the boundary to
an interior vertex. In a rectangular chart the edge is the segment
from (0,0) to (0,1). The map below collapses that segment and fixes
the rectangle boundary. Away from the segment it is injective.
-/

public section

namespace GraphMinor.GM06

open Set

/-- The height coordinate of the local edge contraction. -/
@[expose] noncomputable def section5CollapseHeight (x y : ℝ) : ℝ :=
  max (2 * |x| * y / (1 + |x|)) (2 * y - 2)

/-- The coordinate formula for Reduction 3 is continuous. -/
theorem continuous_section5CollapseHeight :
    Continuous (fun p : ℝ × ℝ => section5CollapseHeight p.1 p.2) := by
  unfold section5CollapseHeight
  have hn : Continuous (fun p : ℝ × ℝ => 2 * |p.1| * p.2) :=
    (continuous_const.mul continuous_fst.abs).mul continuous_snd
  have hd : Continuous (fun p : ℝ × ℝ => 1 + |p.1|) :=
    continuous_const.add continuous_fst.abs
  have hh : ∀ p : ℝ × ℝ, 1 + |p.1| ≠ 0 :=
    fun p => ne_of_gt (by positivity)
  exact (hn.div hd hh).max ((continuous_const.mul continuous_snd).sub continuous_const)

/-- The contraction height stays inside the rectangle. -/
theorem section5CollapseHeight_mem {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 2) : section5CollapseHeight x y ∈ Icc (0 : ℝ) 2 := by
  have ha : |x| ≤ 1 := abs_le.mpr hx
  have hd : 0 < 1 + |x| := by positivity
  have hf : 0 ≤ 2 * |x| * y / (1 + |x|) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg x)) hy.1) hd.le
  have hf2 : 2 * |x| * y / (1 + |x|) ≤ 2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [abs_nonneg x, mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hy.2)]
  exact ⟨hf.trans (le_max_left _ _), max_le hf2 (by linarith only [hy.2])⟩

/-- The four boundary sides are fixed by the contraction. -/
theorem section5CollapseHeight_boundary {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 2)
    (hb : x = -1 ∨ x = 1 ∨ y = 0 ∨ y = 2) :
    section5CollapseHeight x y = y := by
  rcases hb with rfl | rfl | rfl | rfl
  · simp only [section5CollapseHeight, abs_neg, abs_one]
    rw [show 2 * (1 : ℝ) * y / (1 + 1) = y by ring]
    exact max_eq_left (by linarith only [hy.2])
  · simp only [section5CollapseHeight, abs_one]
    rw [show 2 * (1 : ℝ) * y / (1 + 1) = y by ring]
    exact max_eq_left (by linarith only [hy.2])
  · simp [section5CollapseHeight]
  · have hd : 0 < 1 + |x| := by positivity
    have ha : |x| ≤ 1 := abs_le.mpr hx
    unfold section5CollapseHeight
    norm_num only
    exact max_eq_right ((div_le_iff₀ hd).mpr (by linarith))

/-- Exactly the distinguished segment is mapped to height zero. -/
theorem section5CollapseHeight_eq_zero_iff {x y : ℝ} (hy : 0 ≤ y) :
    section5CollapseHeight x y = 0 ↔ y = 0 ∨ x = 0 ∧ y ≤ 1 := by
  have hd : 0 < 1 + |x| := by positivity
  constructor
  · intro he
    have hf : 2 * |x| * y / (1 + |x|) ≤ 0 := by
      rw [← he]
      exact le_max_left _ _
    have hm : 2 * |x| * y ≤ 0 := by simpa only [zero_mul] using (div_le_iff₀ hd).mp hf
    have hh : 2 * y - 2 ≤ 0 := by
      rw [← he]
      exact le_max_right _ _
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · have ha : |x| = 0 := by
        have hp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
        have hle : |x| ≤ 0 := by nlinarith
        exact le_antisymm hle (abs_nonneg x)
      exact Or.inr ⟨abs_eq_zero.mp ha, by linarith only [hh]⟩
  · rintro (rfl | ⟨rfl, hy1⟩)
    · simp [section5CollapseHeight]
    · simp only [section5CollapseHeight, abs_zero, mul_zero, zero_mul, zero_div]
      exact max_eq_left (by linarith only [hy1])

/-- Off the collapsed segment, two equal heights with the same
horizontal coordinate have the same original height. -/
theorem section5CollapseHeight_injective_off_segment {x y z : ℝ}
    (hy : x ≠ 0 ∨ 1 < y) (hz : x ≠ 0 ∨ 1 < z)
    (he : section5CollapseHeight x y = section5CollapseHeight x z) : y = z := by
  by_cases hx : x = 0
  · subst x
    have hy1 : 1 < y := hy.resolve_left (not_ne_iff.mpr rfl)
    have hz1 : 1 < z := hz.resolve_left (not_ne_iff.mpr rfl)
    simp only [section5CollapseHeight, abs_zero, mul_zero, zero_mul, zero_div,
      max_eq_right (by linarith only [hy1] : 0 ≤ 2 * y - 2),
      max_eq_right (by linarith only [hz1] : 0 ≤ 2 * z - 2)] at he
    linarith only [he]
  · have ha : 0 < |x| := abs_pos.mpr hx
    have hc : 0 < 2 * |x| / (1 + |x|) := by positivity
    have hstrict : StrictMono (fun t : ℝ => section5CollapseHeight x t) := by
      intro a b hab
      unfold section5CollapseHeight
      apply max_lt_max
      · rw [show 2 * |x| * a / (1 + |x|) = (2 * |x| / (1 + |x|)) * a by ring,
          show 2 * |x| * b / (1 + |x|) = (2 * |x| / (1 + |x|)) * b by ring]
        exact mul_lt_mul_of_pos_left hab hc
      · linarith only [hab]
    exact hstrict.injective he

/-- Every height in the rectangle has a preimage at the same horizontal
coordinate. This follows from continuity and the fixed top and bottom. -/
theorem section5CollapseHeight_surjOn {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    SurjOn (section5CollapseHeight x) (Icc (0 : ℝ) 2) (Icc (0 : ℝ) 2) := by
  have hc : Continuous (section5CollapseHeight x) :=
    continuous_section5CollapseHeight.comp (continuous_const.prodMk continuous_id)
  have h0 := section5CollapseHeight_boundary hx (show (0 : ℝ) ∈ Icc 0 2 by norm_num)
    (Or.inr (Or.inr (Or.inl rfl)))
  have h2 := section5CollapseHeight_boundary hx (show (2 : ℝ) ∈ Icc 0 2 by norm_num)
    (Or.inr (Or.inr (Or.inr rfl)))
  intro z hz
  apply intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hc.continuousOn
  simpa only [h0, h2] using hz

end GraphMinor.GM06
