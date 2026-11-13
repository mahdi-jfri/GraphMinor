module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Retraction away from a disc boundary attachment

In the attached-side case of VI (5.5), page 130, a curve missing
the attachment can be detoured onto the remaining disc boundary.
In unit-disc coordinates with attachment 1, the formula
`-(w - 1) / (conj w - 1)` is continuous away from 1 and has norm 1.
It fixes the punctured unit circle and never takes the value 1
on the closed unit disc minus that point.
-/

public section
namespace GraphMinor.GM06
open Set Metric
open scoped ComplexConjugate

/-- The closed unit disc punctured at 1 retracts onto its unit
circle punctured at 1, keeping all other boundary points fixed. -/
theorem exists_boundary_punctured_disc_retraction :
    ∃ r : ℂ → ℂ, ContinuousOn r (closedBall 0 1 \ {1}) ∧
      (∀ w ∈ closedBall (0 : ℂ) 1 \ {1}, ‖r w‖ = 1 ∧ r w ≠ 1) ∧
      ∀ w : ℂ, ‖w‖ = 1 → w ≠ 1 → r w = w := by
  let r : ℂ → ℂ := fun w => -(w - 1) / (conj w - 1)
  have hden {w : ℂ} (hw : w ≠ 1) : conj w - 1 ≠ 0 := by
    intro he
    have he' := congrArg conj (sub_eq_zero.mp he)
    simp only [map_one, Complex.conj_conj] at he'
    exact hw he'
  refine ⟨r, ?_, ?_, ?_⟩
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun w hw => hden hw.2)
  · intro w hw
    have hn : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw.1
    constructor
    · change ‖-(w - 1) / (conj w - 1)‖ = 1
      rw [norm_div, norm_neg, show conj w - 1 = conj (w - 1) by simp,
        Complex.norm_conj, div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw.2))]
    · intro he
      have heq : -(w - 1) = conj w - 1 := (div_eq_one_iff_eq (hden hw.2)).mp he
      have hre : w.re = 1 := by
        have h := congrArg Complex.re heq
        simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.conj_re] at h
        linarith only [h]
      have hsq : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
        have hnorm : ‖w‖ ^ 2 ≤ (1 : ℝ) := by nlinarith [norm_nonneg w]
        calc
          w.re ^ 2 + w.im ^ 2 = Complex.normSq w := by rw [Complex.normSq_apply]; ring
          _ = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
          _ ≤ 1 := hnorm
      have him : w.im = 0 := by rw [hre] at hsq; nlinarith [sq_nonneg w.im]
      exact hw.2 (Complex.ext hre (by simpa using him))
  · intro w hw hne
    change -(w - 1) / (conj w - 1) = w
    apply (div_eq_iff (hden hne)).mpr
    have hmul : w * conj w = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
      norm_num
    linear_combination -hmul

/-- The boundary-puncture retraction with an arbitrary unit-circle
attachment, obtained by rotating the attachment to 1 and back. -/
theorem exists_boundary_punctured_disc_retraction_at
    {s : ℂ} (hs : ‖s‖ = 1) :
    ∃ r : ℂ → ℂ, ContinuousOn r (closedBall 0 1 \ {s}) ∧
      (∀ w ∈ closedBall (0 : ℂ) 1 \ {s}, ‖r w‖ = 1 ∧ r w ≠ s) ∧
      ∀ w : ℂ, ‖w‖ = 1 → w ≠ s → r w = w := by
  obtain ⟨r, hc, hr, hfix⟩ := exists_boundary_punctured_disc_retraction
  have hmul : s * conj s = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hs]
    norm_num
  have hinv (w : ℂ) : s * (conj s * w) = w := by rw [← mul_assoc, hmul, one_mul]
  have hnorm (w : ℂ) : ‖conj s * w‖ = ‖w‖ := by rw [norm_mul, Complex.norm_conj, hs, one_mul]
  have hne (w : ℂ) (hw : w ≠ s) : conj s * w ≠ 1 := by
    intro he
    exact hw ((hinv w).symm.trans (by rw [he, mul_one]))
  have hmaps : MapsTo (fun w : ℂ => conj s * w)
      (closedBall 0 1 \ {s}) (closedBall 0 1 \ {1}) := by
    intro w hw
    exact ⟨mem_closedBall_zero_iff.mpr (by rw [hnorm]; exact mem_closedBall_zero_iff.mp hw.1), hne w hw.2⟩
  refine ⟨fun w => s * r (conj s * w), continuousOn_const.mul
    (hc.comp (by fun_prop) hmaps), ?_, ?_⟩
  · intro w hw
    obtain ⟨hn, hnot⟩ := hr _ (hmaps hw)
    constructor
    · rw [norm_mul, hs, hn, one_mul]
    · intro he
      have hsne : s ≠ 0 := norm_ne_zero_iff.mp (by rw [hs]; norm_num)
      exact hnot ((mul_left_cancel₀ hsne (he.trans (mul_one s).symm)))
  · intro w hw hws
    change s * r (conj s * w) = w
    rw [hfix _ ((hnorm w).trans hw) (hne w hws), hinv]

end GraphMinor.GM06
