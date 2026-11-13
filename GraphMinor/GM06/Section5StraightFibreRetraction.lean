module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
import GraphMinor.GM06.Section5RadialDiscPush
import GraphMinor.Surface.Gluing

/-!
# Disc retractions with straight attachment fibres

For the attachment-visit count in VI (5.5), page 130, undo the
radial disc push, then normalize to the unit circle. The resulting
retraction fixes the boundary. A point mapped to a boundary vertex
lies on the straight segment from the omitted centre to that vertex.
Choosing the centre near the attachment therefore confines every
new attachment contact to a small neighbourhood of the old ones.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- An interior-puncture retraction whose fibre over every boundary
point stays on the straight segment from its omitted centre. -/
theorem exists_disc_retraction_with_straight_fibres
    {a : ℂ} (ha : ‖a‖ < 1) :
    ∃ r : ℂ → ℂ, ContinuousOn r (closedBall 0 1 \ {a}) ∧
      (∀ w ∈ closedBall (0 : ℂ) 1 \ {a}, ‖r w‖ = 1) ∧
      (∀ w : ℂ, ‖w‖ = 1 → r w = w) ∧
      ∀ w ∈ closedBall (0 : ℂ) 1 \ {a}, ∀ s : ℂ, r w = s → w ∈ segment ℝ a s := by
  obtain ⟨θ, hθc, hθ, hθ0, hfix, hformula⟩ := exists_radial_disc_push ha
  obtain ⟨ρ, hρc, hρ⟩ := exists_inv_of_compactOn (isCompact_closedBall (0 : ℂ) 1)
    hθc.continuousOn hθ.2.1
  have him : θ '' closedBall (0 : ℂ) 1 = closedBall 0 1 := hθ.image_eq
  rw [him] at hρc
  have hρD (w) (hw : w ∈ closedBall (0 : ℂ) 1) :
      ρ w ∈ closedBall (0 : ℂ) 1 ∧ θ (ρ w) = w := by
    obtain ⟨z, hz, hzw⟩ := hθ.2.2 hw
    rw [← hzw, hρ hz]
    exact ⟨hz, rfl⟩
  have hρne (w) (hw : w ∈ closedBall (0 : ℂ) 1 \ {a}) : ρ w ≠ 0 := by
    intro he
    have h := (hρD w hw.1).2
    rw [he, hθ0] at h
    exact hw.2 h.symm
  let r : ℂ → ℂ := fun w => ρ w / ‖ρ w‖
  have hn (w) (hw : w ∈ closedBall (0 : ℂ) 1 \ {a}) : ‖r w‖ = 1 := by
    change ‖ρ w / (‖ρ w‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr (hρne w hw))]
  refine ⟨r, ?_, hn, ?_, ?_⟩
  · exact (hρc.mono sdiff_subset).div
      (Complex.continuous_ofReal.comp_continuousOn (hρc.mono sdiff_subset).norm)
      (fun w hw => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hρne w hw)))
  · intro w hw
    have hwD : w ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hw.le
    have hρw : ρ w = w := by
      have hleft := hρ hwD
      rwa [hfix w (mem_sphere_zero_iff_norm.mpr hw)] at hleft
    change ρ w / (‖ρ w‖ : ℂ) = w
    rw [hρw, hw]
    simp
  · intro w hw s he
    have hnorm : ‖ρ w‖ ≤ 1 := mem_closedBall_zero_iff.mp (hρD w hw.1).1
    have hne : (‖ρ w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hρne w hw))
    have hqs : ρ w = (‖ρ w‖ : ℂ) * s := by
      have h := (div_eq_iff hne).mp he
      exact h.trans (mul_comm _ _)
    refine ⟨1 - ‖ρ w‖, ‖ρ w‖, sub_nonneg.mpr hnorm, norm_nonneg _, sub_add_cancel 1 _, ?_⟩
    have hθq := (hρD w hw.1).2
    rw [hformula] at hθq
    rw [Complex.real_smul, Complex.real_smul, ← hqs]
    exact (add_comm _ _).trans hθq

end GraphMinor.GM06
