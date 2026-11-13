module

public import GraphMinor.GM06.Alg57SourceChartOrientation
import GraphMinor.GM06.Alg57PolarStar
import GraphMinor.Surface.PlaneOrientation

/-!
# The surviving rays in the source quotient coordinates

For Lemma 8 in the implementation of VI (5.7), page 133, rotate
the incoming target direction to angle zero. The explicit radius
quotient sends angle θ, with 0 < θ < 2π, to angle θ/2 and shortens
its radius by sin(θ/2). This factor is positive. Consequently the
surviving target germs fill the upper half of the source chart in
the old order starting just after the incoming end. The pointwise
chart equation carries this calculation to the actual collapse.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The explicit quotient halves a surviving ray's angle. -/
theorem section5RadiusCollapse_exp (θ : ℝ) :
    section5RadiusCollapse (Circle.exp θ : ℂ) =
      (Real.sin (θ / 2) : ℂ) * (Circle.exp (θ / 2) : ℂ) := by
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    simpa only [mul_div_cancel₀ θ (by norm_num : (2 : ℝ) ≠ 0)] using
      Real.sin_two_mul (θ / 2)
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    simpa only [mul_div_cancel₀ θ (by norm_num : (2 : ℝ) ≠ 0)] using
      Real.cos_two_mul_eq_one_sub (θ / 2)
  apply Complex.ext
  · change (Circle.exp θ : ℂ).im / 2 = _
    simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [hsin]
    ring
  · change (‖(Circle.exp θ : ℂ)‖ - (Circle.exp θ : ℂ).re) / 2 = _
    rw [Circle.norm_coe]
    simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [hcos]
    ring

/-- Every surviving direction has a positive shortening factor
and a new angle strictly between zero and π. -/
theorem section5RadiusCollapse_half_angle_bounds {θ : ℝ}
    (hθ0 : 0 < θ) (hθP : θ < 2 * Real.pi) :
    0 < θ / 2 ∧ θ / 2 < Real.pi ∧ 0 < Real.sin (θ / 2) := by
  have hhalf0 : 0 < θ / 2 := half_pos hθ0
  have hhalfP : θ / 2 < Real.pi := by linarith only [hθP]
  exact ⟨hhalf0, hhalfP, Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfP⟩

/-- The entire retained radial segment is shortened by the same
positive factor, without changing its parameter order. -/
theorem section5RadiusCollapse_radial_exp (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
    section5RadiusCollapse ((r : ℂ) * Circle.exp θ) =
      ((r * Real.sin (θ / 2) : ℝ) : ℂ) * (Circle.exp (θ / 2) : ℂ) := by
  rw [section5RadiusCollapse_nonneg_smul r hr, section5RadiusCollapse_exp]
  push_cast
  ring

/-- The old order after the incoming direction is the strict
half-angle order of the surviving rays. -/
theorem circleCyclic_half_angles {θ₁ θ₂ θ₃ : ℝ}
    (h0 : 0 < θ₁) (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (hP : θ₃ < 2 * Real.pi) :
    CircleCyclic (Circle.exp (θ₁ / 2)) (Circle.exp (θ₂ / 2))
      (Circle.exp (θ₃ / 2)) := by
  apply circleCyclic_exp_of_lt (div_lt_div_of_pos_right h12 (by norm_num)) (div_lt_div_of_pos_right h23 (by norm_num))
  have hpi := Real.pi_pos
  linarith only [h0, hP, hpi]

/-- The explicit model point of a surviving target ray has its
half-angle direction in the unit source parameter disc. -/
theorem section5CollapsedRadiusDiscPoint_ray (r : I) (θ : ℝ)
    (hθ0 : 0 < θ) (hθP : θ < 2 * Real.pi) :
    section5CollapsedRadiusDiscPoint (polarDiscPoint r (Circle.exp θ)) =
      polarDiscPoint
        ⟨(r : ℝ) * Real.sin (θ / 2),
          mul_nonneg r.property.1 (section5RadiusCollapse_half_angle_bounds hθ0 hθP).2.2.le,
          (mul_le_mul_of_nonneg_left (Real.sin_le_one _) r.property.1).trans
            (by simpa only [mul_one] using r.property.2)⟩
        (Circle.exp (θ / 2)) := by
  apply Subtype.ext
  change planeOf (section5RadiusCollapse (planeOf.symm (planeOf ((r : ℂ) * Circle.exp θ)))) = _
  rw [planeOf.symm_apply_apply, section5RadiusCollapse_radial_exp _ r.property.1]
  rfl

/-- The full source chart's actual collapse equation gives the
retained target rays exactly at their half-angle coordinates. -/
theorem source_chart_collapsed_ray
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hmap : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    (r : I) (θ : ℝ) (hθ0 : 0 < θ) (hθP : θ < 2 * Real.pi) :
    Ψ (polarDiscPoint
        ⟨(r : ℝ) * Real.sin (θ / 2),
          mul_nonneg r.property.1 (section5RadiusCollapse_half_angle_bounds hθ0 hθP).2.2.le,
          (mul_le_mul_of_nonneg_left (Real.sin_le_one _) r.property.1).trans
            (by simpa only [mul_one] using r.property.2)⟩
        (Circle.exp (θ / 2))) =
      π (Φ (polarDiscPoint r (w * Circle.exp θ))) := by
  rw [← section5CollapsedRadiusDiscPoint_ray r θ hθ0 hθP, hmap,
    section5RotateDisc_polarDiscPoint]

end GraphMinor.GM06
