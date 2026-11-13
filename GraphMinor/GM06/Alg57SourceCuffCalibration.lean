module

public import GraphMinor.GM06.Alg57SourceGermContacts
public import GraphMinor.GM06.Alg57ExpChart
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Alg57CuffFace
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The two signed source cuff ends

The source splice in Lemma 8 of the implementation of VI (5.7),
page 133, retains the two cuff ends in their old order. Read them
in the explicit positive exponential chart at the source. Its
negative and positive imaginary radii run along the negative and
positive cuff half-spokes. Every ordinary edge point is outside
the inner cuff circle, so its inverse coordinate has positive real
part. Positive coordinate winding transfers that signed order to
the actual new polar chart.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The explicit exponential neighbourhood is positive in the
same plane orientation as the input rows. -/
theorem positive_expChart {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    GM06PositivePolar (expChart q l) := by
  refine ⟨expChartΨ q l, expChart_eq q l, ?_⟩
  rw [← wind_chartC]
  exact wind_expChartΨ_pos hq hl hl1

/-- A short exponential radius lies strictly before the midpoint
of a half-spoke whose angular parameter has a larger scale. -/
theorem expChart_ray_mem_short_curve
    {q : ℂ} {l d : ℝ} (hl : 0 < l) (hld : l < d)
    (u : Circle) {g : I → OnePoint EuclideanPlane}
    (hg : ∀ t, g t = toSph (q * Complex.exp ((d : ℂ) * (t : ℂ) * u)))
    (r : I) (hr : 0 < (r : ℝ)) :
    expChart q l (polarDiscPoint r u) ∈ g '' Ioo (0 : I) 1 := by
  have hd : 0 < d := hl.trans hld
  let t : I := ⟨l * (r : ℝ) / d, (div_pos (mul_pos hl hr) hd).le,
    (div_le_one hd).mpr ((mul_le_of_le_one_right hl.le r.property.2).trans hld.le)⟩
  have ht0 : 0 < t := div_pos (mul_pos hl hr) hd
  have ht1 : t < 1 := (div_lt_one hd).mpr
    ((mul_le_of_le_one_right hl.le r.property.2).trans_lt hld)
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  rw [hg, expChart_apply]
  change toSph (q * Complex.exp ((d : ℂ) * (t : ℂ) * u)) =
    toSph (expMap q l (planeOf.symm (planeOf ((r : ℂ) * u))))
  rw [planeOf.symm_apply_apply]
  apply congrArg toSph
  unfold expMap
  congr 2
  have htval : d * (t : ℝ) = l * (r : ℝ) := by
    change d * (l * (r : ℝ) / d) = _
    field_simp
  have hc := congrArg (fun x : ℝ => (x : ℂ)) htval
  push_cast at hc
  rw [hc]
  ring

/-- A rightward direction lies positively between the negative
and positive imaginary directions. -/
theorem circleCyclic_imaginary_of_re_pos {u : Circle} (hu : 0 < (u : ℂ).re) :
    CircleCyclic (Circle.exp (-(Real.pi / 2))) u (Circle.exp (Real.pi / 2)) := by
  have hlo : -(Real.pi / 2) < Complex.arg (u : ℂ) :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hu)
  have hhi : Complex.arg (u : ℂ) < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hh := circleCyclic_exp_of_lt hlo hhi
    (show Real.pi / 2 < -(Real.pi / 2) + 2 * Real.pi by linarith [Real.pi_pos])
  simpa only [Circle.exp_arg] using hh

/-- An ordinary point outside the cuff circle has positive real
inverse coordinate in the source exponential chart. -/
theorem re_pos_of_expChart_coordinate_outside_circle
    {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l)
    {z y : ℂ} (hz : ‖z‖ ≤ 1)
    (heq : expChart q l (discPt z) = toSph y) (hy : ‖q‖ < ‖y‖) : 0 < z.re := by
  have hvalue : expMap q l z = y := by
    rw [expChart_apply] at heq
    change toSph (expMap q l (planeOf.symm (planeOf (ballClamp z)))) = toSph y at heq
    rw [planeOf.symm_apply_apply, ballClamp_of_norm_le hz] at heq
    exact toSph_injective heq
  have hnorm : ‖y‖ = ‖q‖ * Real.exp (l * z.re) := by
    rw [← hvalue, norm_expMap]
  by_contra hh
  have hr : l * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl.le (le_of_not_gt hh)
  have he : Real.exp (l * z.re) ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hr
  have hn := mul_le_of_le_one_right (norm_nonneg q) he
  rw [← hnorm] at hn
  exact hy.not_ge hn


/-- The two actual signed cuff half-spokes bracket every ordinary
source end outside the inner cuff circle. The comparison reads
the new positive chart through the explicit exponential chart. -/
theorem source_signed_cuff_order_of_expChart
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {q : ℂ} (hq : q ≠ 0)
    {p : OnePoint EuclideanPlane} (hpc : p = toSph q) (hpV : p ∈ Γ.V) {l scale : ℝ} (hl : 0 < l) (hl1 : l < 1) (hls : l < scale)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (hpos : GM06PositivePolar Φ) (hsub : range Φ ⊆ range (expChart q l))
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.val))
    (minus plus a : halfEdges Γ γ p)
    (hmp : minus ≠ plus) (hma : minus ≠ a) (hpa : plus ≠ a)
    (hminus : ∀ t, spoke γ minus.val t = toSph (q * Complex.exp
      ((scale : ℂ) * (t : ℂ) * (Circle.exp (-(Real.pi / 2)) : ℂ))))
    (hplus : ∀ t, spoke γ plus.val t = toSph (q * Complex.exp
      ((scale : ℂ) * (t : ℂ) * (Circle.exp (Real.pi / 2) : ℂ))))
    {y : ℂ} (hay : Φ (polarDiscPoint 1 (d a).val) = toSph y) (hy : ‖q‖ < ‖y‖) :
    CircleCyclic (d minus).val (d a).val (d plus).val := by
  subst p
  have hE0 : expChart q l polarCentre = toSph q := by
    rw [expChart_apply]
    simp only [polarCentre, planeOf.symm.map_zero, expMap_zero]
  obtain ⟨f, v, hf, hf0, hmap, hv, hvpos⟩ := exists_positive_source_rim_directions
    (expChart_injective hq hl hl1) (positive_expChart hq hl hl1) hp.inj hpos
    (hp.centre.trans hE0.symm) hsub
  have hminusRay (r : I) (hr : 0 < (r : ℝ)) (_ : (r : ℝ) ≤ 1) :
      expChart q l (polarDiscPoint r (Circle.exp (-(Real.pi / 2)))) ∈
        spoke γ minus.val '' Ioo (0 : I) 1 :=
    expChart_ray_mem_short_curve hl hls _ hminus r hr
  have hplusRay (r : I) (hr : 0 < (r : ℝ)) (_ : (r : ℝ) ≤ 1) :
      expChart q l (polarDiscPoint r (Circle.exp (Real.pi / 2))) ∈
        spoke γ plus.val '' Ioo (0 : I) 1 :=
    expChart_ray_mem_short_curve hl hls _ hplus r hr
  have hm := source_coordinate_ray_contact hγ hpV hp d hd f v hf hf0 hmap hv hvpos hf
    minus (Circle.exp (-(Real.pi / 2))) hminusRay
  have hp' := source_coordinate_ray_contact hγ hpV hp d hd f v hf hf0 hmap hv hvpos hf
    plus (Circle.exp (Real.pi / 2)) hplusRay
  have hre : 0 < (f (d a).val).re := re_pos_of_expChart_coordinate_outside_circle hq hl
    (hf _) ((hmap _).trans hay) hy
  have hre' : (f (d a).val).re = ‖f (d a).val‖ * (v (d a).val : ℂ).re := by
    have hh := congrArg Complex.re (hv (d a).val)
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hh
  rw [hre'] at hre
  have hunit := (mul_pos_iff_of_pos_left (norm_pos_iff.mpr (hf0 (d a).val))).mp hre
  have hinj : Function.Injective (fun b => (d b).val) := Subtype.val_injective.comp d.injective
  apply (circleCyclic_iff_positive_loop_outer_contacts v hvpos
    (fun w hw => (hm.2 w).mp (hw.trans hm.1))
    (fun w hw => (hp'.2 w).mp (hw.trans hp'.1))
    (hinj.ne hmp) (hinj.ne hma) (hinj.ne hpa)).mpr
  simpa only [hm.1, hp'.1] using circleCyclic_imaginary_of_re_pos hunit

/-- The forward half of the following cuff gap has the positive
signed angular parametrization from the source. -/
theorem initialCuffGapCurve_forward_half {k : ℕ} (i : Fin k) (t : I) :
    initialCuffGapCurve k i (halfPar false t) =
      cylinderPoint 1 (by norm_num)
        (2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k + (Real.pi / k) * (t : ℝ)) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (halfPar false t : ℝ)) * Real.pi / k) = _
    rw [halfPar_coe]
    simp only [Bool.false_eq_true, ite_false]
    congr 1
    ring

/-- The reverse half of the preceding cuff gap has the negative
signed angular parametrization, including the predecessor wrap. -/
theorem initialCuffGapCurve_backward_half {k : ℕ} (hk : 0 < k) (i : Fin k) (t : I) :
    initialCuffGapCurve k (finPredCycle i) (halfPar true t) =
      cylinderPoint 1 (by norm_num)
        (2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k - (Real.pi / k) * (t : ℝ)) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · have hpred : (finPredCycle i).val + 1 = if i.val = 0 then k else i.val := by
      unfold finPredCycle
      split <;> dsimp <;> omega
    change Circle.exp (2 * ((((finPredCycle i).val + 1 : ℕ) : ℝ) +
      (halfPar true t : ℝ)) * Real.pi / k) = Circle.exp
      (2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k - (Real.pi / k) * (t : ℝ))
    rw [halfPar_coe, hpred]
    simp only [ite_true]
    by_cases hi : i.val = 0
    · simp only [hi, ite_true]
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      have hangle : 2 * ((k : ℝ) + (1 - (t : ℝ) / 2)) * Real.pi / k =
          (2 * ((0 + 1 : ℕ) : ℝ) * Real.pi / k - (Real.pi / k) * (t : ℝ)) + 2 * Real.pi := by
        push_cast
        field_simp
        ring
      rw [hangle, Circle.exp_add_two_pi]
    · rw [if_neg hi]
      congr 1
      push_cast
      ring

private theorem coe_circle_exp_half_pi :
    (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  rw [Circle.coe_exp]
  apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

private theorem coe_circle_exp_neg_half_pi :
    (Circle.exp (-(Real.pi / 2)) : ℂ) = -Complex.I := by
  rw [Circle.coe_exp]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]; simp
  · rw [Complex.exp_ofReal_mul_I_im]; simp

/-- In sphere coordinates, the concrete positive cuff half-spoke
is the positive imaginary ray with scale π/k. -/
theorem cylinderToSphere_forward_cuff_half {k : ℕ} (i : Fin k) (t : I) :
    cylinderToSphere (initialCuffGapCurve k i (halfPar false t)) =
      toSph ((((1 / 2 : ℝ) : ℂ) * Complex.exp
        (((2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((Real.pi / k : ℝ) : ℂ) * (t : ℂ) * (Circle.exp (Real.pi / 2) : ℂ))) := by
  rw [initialCuffGapCurve_forward_half, cylinderToSphere_cylinderPoint,
    coe_circle_exp_half_pi]
  apply congrArg toSph
  simp only [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- In sphere coordinates, the concrete negative cuff half-spoke
is the negative imaginary ray with scale π/k, for every k > 0. -/
theorem cylinderToSphere_backward_cuff_half {k : ℕ} (hk : 0 < k) (i : Fin k) (t : I) :
    cylinderToSphere (initialCuffGapCurve k (finPredCycle i) (halfPar true t)) =
      toSph ((((1 / 2 : ℝ) : ℂ) * Complex.exp
        (((2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((Real.pi / k : ℝ) : ℂ) * (t : ℂ) * (Circle.exp (-(Real.pi / 2)) : ℂ))) := by
  rw [initialCuffGapCurve_backward_half hk, cylinderToSphere_cylinderPoint,
    coe_circle_exp_neg_half_pi]
  apply congrArg toSph
  simp only [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring


end GraphMinor.GM06
