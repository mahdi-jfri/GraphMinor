module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GraphMinor.Surface.DiscTwist

/-!
# Extending angular coordinates along straight rays

For the local seed discs of VI (5.5), page 130, angular changes
must preserve the straight rays of a polar chart. Extend a circle
homeomorphism radially over the plane. The norm stays unchanged,
and extending the inverse circle map gives the inverse plane map.
This carries a half-disc to an angular seed disc without changing
which drawing rays lie in its interior.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Every circle homeomorphism extends radially to a plane
homeomorphism fixing the origin and preserving each radial parameter. -/
theorem exists_radial_circle_homeomorph (h : Circle ≃ₜ Circle) :
    ∃ R : ℂ ≃ₜ ℂ, R 0 = 0 ∧ (∀ z, ‖R z‖ = ‖z‖) ∧
      ∀ (r : ℝ), 0 ≤ r → ∀ w : Circle, R ((r : ℂ) * w) = (r : ℂ) * h w := by
  let μ : unitInterval × Circle → Circle := fun p => h p.2
  let ν : unitInterval × Circle → Circle := fun p => h.symm p.2
  let F := twistMap μ
  let K := twistMap ν
  have hF0 : F 0 = 0 := by simp [F, twistMap]
  have hK0 : K 0 = 0 := by simp [K, twistMap]
  have hFn (z) : ‖F z‖ = ‖z‖ := norm_twistMap μ z
  have hKn (z) : ‖K z‖ = ‖z‖ := norm_twistMap ν z
  have hF (z) (hz : z ≠ 0) : F z = (‖z‖ : ℂ) * h (unitOf z hz) := by simp [F, twistMap, μ, hz]
  have hK (z) (hz : z ≠ 0) : K z = (‖z‖ : ℂ) * h.symm (unitOf z hz) := by simp [K, twistMap, ν, hz]
  have hFKne (z) (hz : z ≠ 0) : F z ≠ 0 ∧ K z ≠ 0 := by
    constructor
    · intro he
      have hn := hFn z
      rw [he, norm_zero] at hn
      exact hz (norm_eq_zero.mp hn.symm)
    · intro he
      have hn := hKn z
      rw [he, norm_zero] at hn
      exact hz (norm_eq_zero.mp hn.symm)
  have hKF (z) : K (F z) = z := by
    by_cases hz : z = 0
    · simp [hz, hF0, hK0]
    · have hfne := (hFKne z hz).1
      have hu : unitOf (F z) hfne = h (unitOf z hz) := by
        apply Circle.ext
        rw [coe_unitOf, hFn, hF z hz, ← mul_assoc,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)), one_mul]
      rw [hK _ hfne, hFn, hu, h.symm_apply_apply]
      exact norm_mul_unitOf z hz
  have hFK (z) : F (K z) = z := by
    by_cases hz : z = 0
    · simp [hz, hF0, hK0]
    · have hkne := (hFKne z hz).2
      have hu : unitOf (K z) hkne = h.symm (unitOf z hz) := by
        apply Circle.ext
        rw [coe_unitOf, hKn, hK z hz, ← mul_assoc,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)), one_mul]
      rw [hF _ hkne, hKn, hu, h.apply_symm_apply]
      exact norm_mul_unitOf z hz
  let R : ℂ ≃ₜ ℂ :=
    { toFun := F
      invFun := K
      left_inv := hKF
      right_inv := hFK
      continuous_toFun := continuous_twistMap (h.continuous.comp continuous_snd)
      continuous_invFun := continuous_twistMap (h.symm.continuous.comp continuous_snd) }
  refine ⟨R, hF0, hFn, ?_⟩
  intro r hr w
  by_cases hr0 : r = 0
  · simp [hr0, show R 0 = 0 from hF0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hzne : (r : ℂ) * w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0) (Circle.coe_ne_zero w)
    change F ((r : ℂ) * w) = _
    rw [hF _ hzne, unitOf_mul r hrpos w hzne, norm_mul, Complex.norm_real, Circle.norm_coe,
      mul_one, Real.norm_of_nonneg hr]

end GraphMinor.GM06
