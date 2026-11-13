module

public import GraphMinor.GM06.Alg57SourceChartOrientation
import GraphMinor.GM06.Alg57ChartOrientation
import GraphMinor.GM19.Winding
import GraphMinor.Surface.PlaneOrientation

/-!
# Winding when reading a loop in the full source chart

The local source comparison in Lemma 8 of the implementation of
VI (5.7), page 133, reads the rim of a smaller polar chart in the
explicit full source coordinates. A radial homotopy replaces that
coordinate loop by its directions. Lift these directions to real
angles. Their integral number of turns multiplies the winding of
the full chart's rim.

This calculation compares the two particular chart rims. It uses
continuous angle lifts and the explicit homotopy, without assigning
orientation signs to arbitrary surface maps.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 unitInterval

private theorem turn_int_periods
    {g : ℝ → ℂ} (hc : Continuous g) (h0 : ∀ t, g t ≠ 0)
    {P : ℝ} (hP : P ≠ 0) (hperiod : ∀ t, g (t + P) = g t) (s : ℝ) (n : ℤ) :
    turn g s (s + (n : ℝ) * P) = (n : ℝ) * turn g 0 P := by
  obtain ⟨L, hL⟩ := exists_isAngle hc h0
  let δ := turn g 0 P
  have hstep (t : ℝ) : L (t + P) = L t + δ := by
    have hh := turn_period hc h0 hperiod t 0
    rw [hL.turn_eq h0, hL.turn_eq h0, zero_add] at hh
    have hδ : δ = L P - L 0 := hL.turn_eq h0 0 P
    linarith
  have hres : Function.Periodic (fun t => L t - (δ / P) * t) P := by
    intro t
    change L (t + P) - (δ / P) * (t + P) = L t - (δ / P) * t
    rw [hstep, mul_add, div_mul_cancel₀ δ hP]
    ring
  have hn := hres.sub_zsmul_eq (x := s) (-n)
  simp only [zsmul_eq_mul, Int.cast_neg, neg_mul, sub_neg_eq_add] at hn
  rw [hL.turn_eq h0]
  change L (s + (n : ℝ) * P) - L s = (n : ℝ) * δ
  calc
    _ = (δ / P) * (s + (n : ℝ) * P) - (δ / P) * s := by linarith only [hn]
    _ = (n : ℝ) * δ := by field_simp; ring

private theorem normalize_loop_winding
    (χ : ℂ → ℂ) (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1))
    (f : C(Circle, ℂ)) (hf : ∀ w, ‖f w‖ ≤ 1) (h0 : ∀ w, f w ≠ 0)
    (v : C(Circle, Circle)) (hv : ∀ w, f w = (‖f w‖ : ℂ) * v w) :
    wind f 0 = wind (fun w => (v w : ℂ)) 0 ∧
      wind (fun w => χ (f w)) (χ 0) = wind (fun w => χ (v w : ℂ)) (χ 0) := by
  let u : ℝ → I := fun t => ⟨clampUnit t, clampUnit_mem t⟩
  have hu : Continuous u := continuous_clampUnit.subtype_mk _
  have hu0 : u 0 = 0 := Subtype.ext clampUnit_zero
  have hu1 : u 1 = 1 := Subtype.ext clampUnit_one
  let ρ : ℝ → Circle → ℝ := fun t w => (1 - (u t : ℝ)) * ‖f w‖ + (u t : ℝ)
  have hρc : Continuous (fun q : ℝ × Circle => ρ q.1 q.2) :=
    ((continuous_const.sub (continuous_subtype_val.comp (hu.comp continuous_fst))).mul
      (f.continuous.norm.comp continuous_snd)).add
        (continuous_subtype_val.comp (hu.comp continuous_fst))
  have hρ (t : ℝ) (w : Circle) : 0 < ρ t w ∧ ρ t w ≤ 1 := by
    have hu0' := (u t).property.1
    have hu1' := (u t).property.2
    have hn := norm_pos_iff.mpr (h0 w)
    have hb := hf w
    have hmul := mul_nonneg hu0' (sub_nonneg.mpr hb)
    have hmul' := mul_nonneg (sub_nonneg.mpr hu1') (sub_nonneg.mpr hb)
    dsimp only [ρ]
    constructor <;> nlinarith only [hn, hb, hmul, hmul']
  let G : ℝ → Circle → ℂ := fun t w => ((ρ t w : ℝ) : ℂ) * v w
  have hGc : Continuous (fun q : ℝ × Circle => G q.1 q.2) :=
    (Complex.continuous_ofReal.comp hρc).mul
      ((continuous_subtype_val.comp v.continuous).comp continuous_snd)
  have hGnorm (t : ℝ) (w : Circle) : ‖G t w‖ = ρ t w := by
    dsimp only [G]
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hρ t w).1.le]
  have hG0 : ∀ t w, G t w ≠ 0 := by
    intro t w heq
    have hh := congrArg norm heq
    rw [hGnorm, norm_zero] at hh
    exact (hρ t w).1.ne' hh
  have hGbound : ∀ t w, G t w ∈ closedBall (0 : ℂ) 1 := by
    intro t w
    rw [mem_closedBall_zero_iff, hGnorm]
    exact (hρ t w).2
  have hzero : ∀ w, G 0 w = f w := by
    intro w
    simp only [G, ρ, hu0, Icc.coe_zero, sub_zero, one_mul, add_zero]
    exact (hv w).symm
  have hone : ∀ w, G 1 w = (v w : ℂ) := by
    intro w
    simp only [G, ρ, hu1, Icc.coe_one, sub_self, zero_mul, zero_add,
      Complex.ofReal_one, one_mul]
  have hwind := wind_eq_of_family hGc continuous_const
    (fun t w heq => hG0 t w heq) 0 1
  have hχne : ∀ t w, χ (G t w) ≠ χ 0 := by
    intro t w heq
    exact hG0 t w (hi (hGbound t w) (by simp) heq)
  have hwindχ := wind_eq_of_family (hχ.comp hGc) continuous_const hχne 0 1
  have hzeroFn : G 0 = (f : Circle → ℂ) := funext hzero
  have honeFn : G 1 = fun w => (v w : ℂ) := funext hone
  rw [hzeroFn, honeFn] at hwind
  exact ⟨hwind, by simpa only [hzero, hone] using hwindχ⟩

/-- A coordinate loop makes an integral number of turns, and
reading it through an injective disc chart multiplies the chart-rim
winding by exactly that integer. Both assertions use the same
continuous angular lift of the coordinate loop. -/
theorem wind_chart_loop_multiple
    (χ : ℂ → ℂ) (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1))
    (f : C(Circle, ℂ)) (hf : ∀ w, ‖f w‖ ≤ 1) (h0 : ∀ w, f w ≠ 0) :
    ∃ n : ℤ, wind f 0 = (n : ℝ) * (2 * Real.pi) ∧
      wind (fun w => χ (f w)) (χ 0) =
        (n : ℝ) * wind (fun w : Circle => χ w) (χ 0) := by
  let v : C(Circle, Circle) := ⟨fun w => unitOf (f w) (h0 w),
    continuous_unitOf.comp (f.continuous.subtype_mk h0)⟩
  have hv : ∀ w, f w = (‖f w‖ : ℂ) * v w := fun w => (norm_mul_unitOf (f w) (h0 w)).symm
  obtain ⟨hnorm, hnormχ⟩ := normalize_loop_winding χ hχ hi f hf h0 v hv
  obtain ⟨L, hLc, hL⟩ := exists_circle_lift_map
    ⟨fun t => v (Circle.exp t), v.continuous.comp Circle.exp.continuous⟩
  change ∀ t, Circle.exp (L t) = v (Circle.exp t) at hL
  have hends : Circle.exp (L (2 * Real.pi)) = Circle.exp (L 0) := by
    rw [hL, hL, Circle.exp_two_pi, Circle.exp_zero]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hends
  have hAngle : IsAngle (fun t => (v (Circle.exp t) : ℂ)) L := by
    refine ⟨hLc, ?_⟩
    intro t
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul]
    exact (congrArg (fun w : Circle => (w : ℂ)) (hL t)).symm
  have hv0 : ∀ t, (v (Circle.exp t) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have hwindv : wind (fun w => (v w : ℂ)) 0 = (n : ℝ) * (2 * Real.pi) := by
    change turn (fun t => (v (Circle.exp t) : ℂ) - 0) 0 (2 * Real.pi) = _
    simp only [sub_zero]
    rw [hAngle.turn_eq hv0, hn]
    ring
  let g : ℝ → ℂ := fun t => χ (Circle.exp t) - χ 0
  have hgc : Continuous g := (hχ.comp (continuous_subtype_val.comp Circle.exp.continuous)).sub continuous_const
  have hg0 : ∀ t, g t ≠ 0 := by
    intro t heq
    have hh := hi (show (Circle.exp t : ℂ) ∈ closedBall (0 : ℂ) 1 by simp)
      (by simp) (sub_eq_zero.mp heq)
    exact Circle.coe_ne_zero _ hh
  have hperiod : ∀ t, g (t + 2 * Real.pi) = g t := by
    intro t
    simp only [g, Circle.exp_add_two_pi]
  have hcomp : (fun t => χ (v (Circle.exp t) : ℂ) - χ 0) = g ∘ L := by
    funext t
    dsimp only [g, Function.comp_apply]
    rw [hL]
  have hwindχv : wind (fun w => χ (v w : ℂ)) (χ 0) =
      (n : ℝ) * wind (fun w : Circle => χ w) (χ 0) := by
    change turn (fun t => χ (v (Circle.exp t) : ℂ) - χ 0) 0 (2 * Real.pi) = _
    rw [hcomp]
    change turn (fun t => g (L t)) 0 (2 * Real.pi) = (n : ℝ) * turn g 0 (2 * Real.pi)
    rw [turn_comp hgc hg0 hLc, hn]
    exact turn_int_periods hgc hg0 Real.two_pi_pos.ne' hperiod (L 0) n
  exact ⟨n, hnorm.trans hwindv, hnormχ.trans hwindχv⟩


/-- A loop read positively through the positive full source chart
has positive coordinate winding. The integer in the comparison is
positive because both image and chart-rim winding are positive. -/
theorem wind_coordinate_loop_pos
    (χ : ℂ → ℂ) (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1))
    (f : C(Circle, ℂ)) (hf : ∀ w, ‖f w‖ ≤ 1) (h0 : ∀ w, f w ≠ 0)
    (hchart : 0 < wind (fun w : Circle => χ w) (χ 0))
    (hloop : 0 < wind (fun w => χ (f w)) (χ 0)) :
    0 < wind f 0 := by
  obtain ⟨n, hn, hχn⟩ := wind_chart_loop_multiple χ hχ hi f hf h0
  have hnpos : (0 : ℝ) < n := by
    rw [hχn] at hloop
    exact (mul_pos_iff_of_pos_right hchart).mp hloop
  rw [hn]
  exact mul_pos hnpos Real.two_pi_pos


/-- The directions of a positively read coordinate loop form a
positive circle loop. The radial factor is retained pointwise for
identifying contacts with the surviving straight germs. -/
theorem exists_positive_coordinate_direction_loop
    (χ : ℂ → ℂ) (hχ : Continuous χ) (hi : InjOn χ (closedBall 0 1))
    (f : C(Circle, ℂ)) (hf : ∀ w, ‖f w‖ ≤ 1) (h0 : ∀ w, f w ≠ 0)
    (hchart : 0 < wind (fun w : Circle => χ w) (χ 0))
    (hloop : 0 < wind (fun w => χ (f w)) (χ 0)) :
    ∃ v : C(Circle, Circle), (∀ w, f w = (‖f w‖ : ℂ) * v w) ∧
      0 < wind (fun w => (v w : ℂ)) 0 := by
  let v : C(Circle, Circle) := ⟨fun w => unitOf (f w) (h0 w),
    continuous_unitOf.comp (f.continuous.subtype_mk h0)⟩
  have hv : ∀ w, f w = (‖f w‖ : ℂ) * v w :=
    fun w => (norm_mul_unitOf (f w) (h0 w)).symm
  have hn := (normalize_loop_winding χ hχ hi f hf h0 v hv).1
  refine ⟨v, hv, ?_⟩
  rw [← hn]
  exact wind_coordinate_loop_pos χ hχ hi f hf h0 hchart hloop

end GraphMinor.GM06
