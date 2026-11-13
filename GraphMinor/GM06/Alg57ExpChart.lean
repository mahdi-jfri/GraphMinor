module

public import GraphMinor.GM06.Alg57EdgeChain
public import GraphMinor.GM06.Alg57ChartOrientation

/-!
# An explicit positive chart along a circle

To know which region lies on the left of a cuff edge of the cylinder, we compute the corner in
one explicit chart. Near a point `q ≠ 0` of the plane, the map `w ↦ q · exp (l w)` sends the
imaginary axis to the circle `|z| = |q|`, the right half to the outside of the circle, and the
left half to the inside. For small `l > 0` it is a positive chart (`wind_expMap_pos`): it is close
to the affine map `w ↦ q (1 + l w)`, which turns once around `q`.

When the circle near `q` is a single edge of a drawing and nothing else of the drawing comes
near, this is a polar chart (`expChart_isPolar`). Its two edge directions are `±i`, and the corner
after `-i` is the region of a point outside the circle (`cornerRegion_expChart`). A curve that
moves clockwise along the circle runs out along `-i` (`runsOut_expChart`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The map `w ↦ q · exp (l w)`. -/
noncomputable def expMap (q : ℂ) (l : ℝ) (w : ℂ) : ℂ := q * Complex.exp ((l : ℂ) * w)

theorem continuous_expMap (q : ℂ) (l : ℝ) : Continuous (expMap q l) := by
  unfold expMap; fun_prop

theorem expMap_zero (q : ℂ) (l : ℝ) : expMap q l 0 = q := by
  simp [expMap]

/-- The chart `w ↦ q · exp (l w)` as a map of the closed unit disc into the plane. -/
noncomputable def expChartΨ (q : ℂ) (l : ℝ) : C(ClosedUnitDisc, EuclideanPlane) :=
  ⟨fun x => complexPlane (expMap q l (planeOf.symm x.1)),
    complexPlane.continuous.comp
      ((continuous_expMap q l).comp (planeOf.symm.continuous.comp continuous_subtype_val))⟩

/-- The chart `w ↦ q · exp (l w)` as a map of the closed unit disc into the sphere. -/
noncomputable def expChart (q : ℂ) (l : ℝ) : C(ClosedUnitDisc, OnePoint EuclideanPlane) :=
  ⟨fun x => ((expChartΨ q l x : EuclideanPlane) : OnePoint EuclideanPlane),
    OnePoint.continuous_coe.comp (expChartΨ q l).continuous⟩

theorem expChart_eq (q : ℂ) (l : ℝ) (x : ClosedUnitDisc) :
    expChart q l x = (expChartΨ q l x : OnePoint EuclideanPlane) := rfl

theorem expChart_apply (q : ℂ) (l : ℝ) (x : ClosedUnitDisc) :
    expChart q l x = toSph (expMap q l (planeOf.symm x.1)) := rfl

theorem chartC_expChartΨ (q : ℂ) (l : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    chartC (expChartΨ q l) w = expMap q l w := by
  simp only [chartC, expChartΨ, discPt, ContinuousMap.coe_mk, LinearIsometryEquiv.symm_apply_apply,
    ballClamp_of_norm_le hw]

/-- `exp (l w)` is injective on the closed unit disc when `l < π`. -/
theorem expMap_injOn {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    InjOn (expMap q l) (closedBall 0 1) := by
  intro w hw w' hw' h
  have h' : Complex.exp ((l : ℂ) * w) = Complex.exp ((l : ℂ) * w') :=
    mul_left_cancel₀ hq h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h'
  have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
  have hw1' : ‖w'‖ ≤ 1 := mem_closedBall_zero_iff.mp hw'
  have hdiff : ‖(l : ℂ) * w - (l : ℂ) * w'‖ < 2 * Real.pi := by
    calc ‖(l : ℂ) * w - (l : ℂ) * w'‖ ≤ ‖(l : ℂ) * w‖ + ‖(l : ℂ) * w'‖ := norm_sub_le _ _
      _ = l * ‖w‖ + l * ‖w'‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.le]
      _ ≤ l * 1 + l * 1 := by gcongr
      _ < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
    have heq : (l : ℂ) * w - (l : ℂ) * w' = n * (2 * Real.pi * Complex.I) := by
      rw [hn]; ring
    rw [heq] at hdiff
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real,
      Complex.norm_two, Real.norm_of_nonneg Real.pi_pos.le, mul_one] at hdiff
    nlinarith [Real.pi_pos]
  rw [hn0, Int.cast_zero, zero_mul, add_zero] at hn
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hl.ne') hn

/-- A circle `w ↦ c w` with `c ≠ 0` turns once, positively, around `0`. -/
theorem wind_mul_pos {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    0 < wind (fun w : Circle => z + c * w) z := by
  obtain ⟨α, hα⟩ := GM19.isAngle_const hc
  have hA := hα.mul isAngle_exp
  have h0 : ∀ t : ℝ, c * ((Circle.exp t : Circle) : ℂ) ≠ 0 := fun t =>
    mul_ne_zero hc (Circle.coe_ne_zero _)
  have hfun : (fun t : ℝ => (fun w : Circle => z + c * w) (Circle.exp t) - z) =
      fun t => c * ((Circle.exp t : Circle) : ℂ) := by
    funext t; ring
  rw [wind, hfun, hA.turn_eq h0]
  linarith [Real.two_pi_pos]

/-- **The exponential chart is positive.** -/
theorem wind_expMap_pos {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    0 < wind (fun w : Circle => expMap q l w) q := by
  let F : ℝ → Circle → ℂ := fun s w =>
    q * (1 + (l : ℂ) * w + ((1 - clampUnit s : ℝ) : ℂ) *
      (Complex.exp ((l : ℂ) * w) - 1 - (l : ℂ) * w))
  have hF : Continuous fun p : ℝ × Circle => F p.1 p.2 := by
    simp only [F]
    have := continuous_clampUnit
    fun_prop
  have hne : ∀ s (w : Circle), F s w ≠ q := by
    intro s w h
    have hw : ‖(w : ℂ)‖ = 1 := Circle.norm_coe w
    have hlw : ‖(l : ℂ) * w‖ = l := by
      rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_of_nonneg hl.le]
    have hR := Complex.norm_exp_sub_one_sub_id_le (x := (l : ℂ) * w) (by rw [hlw]; exact hl1.le)
    have hc := clampUnit_mem s
    have hc0 : 0 ≤ 1 - clampUnit s := by linarith [hc.2]
    have hc1 : 1 - clampUnit s ≤ 1 := by linarith [hc.1]
    have h0 : (l : ℂ) * w + ((1 - clampUnit s : ℝ) : ℂ) *
        (Complex.exp ((l : ℂ) * w) - 1 - (l : ℂ) * w) = 0 := by
      have : q * ((l : ℂ) * w + ((1 - clampUnit s : ℝ) : ℂ) *
          (Complex.exp ((l : ℂ) * w) - 1 - (l : ℂ) * w)) = 0 := by
        have h2 : F s w - q = 0 := sub_eq_zero.mpr h
        rw [← h2]; simp only [F]; ring
      exact (mul_eq_zero.mp this).resolve_left hq
    have hR' : ‖Complex.exp ((l : ℂ) * w) - 1 - (l : ℂ) * w‖ ≤ l ^ 2 := by
      rw [hlw] at hR; exact hR
    have hnorm : ‖(l : ℂ) * w‖ ≤ (1 - clampUnit s) * l ^ 2 :=
      calc ‖(l : ℂ) * w‖ = ‖((1 - clampUnit s : ℝ) : ℂ) *
            (Complex.exp ((l : ℂ) * w) - 1 - (l : ℂ) * w)‖ := by
            rw [congrArg norm (eq_neg_of_add_eq_zero_left h0), norm_neg]
        _ = (1 - clampUnit s) * ‖Complex.exp ((l : ℂ) * w) - 1 - (l : ℂ) * w‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
        _ ≤ (1 - clampUnit s) * l ^ 2 := by gcongr
    rw [hlw] at hnorm
    nlinarith
  have heq := wind_eq_of_family hF (z := fun _ => q) continuous_const (fun s w => hne s w) 0 1
  have hF0 : F 0 = fun w : Circle => expMap q l w := by
    funext w
    simp only [F, expMap]
    rw [show clampUnit 0 = 0 by simp [clampUnit]]
    push_cast; ring
  have hF1 : F 1 = fun w : Circle => q + (q * l) * w := by
    funext w
    simp only [F]
    rw [show clampUnit 1 = 1 by simp [clampUnit]]
    push_cast; ring
  rw [hF0, hF1] at heq
  rw [heq]
  exact wind_mul_pos (mul_ne_zero hq (Complex.ofReal_ne_zero.mpr hl.ne')) q

theorem wind_expChartΨ_pos {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    0 < wind (fun w : Circle => chartC (expChartΨ q l) w) (chartC (expChartΨ q l) 0) := by
  have h1 : (fun w : Circle => chartC (expChartΨ q l) w) = fun w : Circle => expMap q l w := by
    funext w
    exact chartC_expChartΨ q l (le_of_eq (Circle.norm_coe w))
  rw [h1, chartC_expChartΨ q l (by simp), expMap_zero]
  exact wind_expMap_pos hq hl hl1

section Polar

variable {Γ : Drawing (OnePoint EuclideanPlane)}

theorem expChart_injective {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    Function.Injective (expChart q l) := by
  intro x y h
  have hx : planeOf.symm x.1 ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.2
  have hy : planeOf.symm y.1 ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp y.2
  rw [expChart_apply, expChart_apply] at h
  have h1 := expMap_injOn hq hl hl1 hx hy (complexPlane.injective
    (OnePoint.coe_injective h))
  exact Subtype.ext (planeOf.symm.injective h1)

/-- The centre of the exponential chart is an interior point of its image. -/
theorem toSph_mem_interior_range_expChart {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) :
    toSph q ∈ interior (range (expChart q l)) := by
  have hcont : ContinuousAt (fun z : ℂ => Complex.log (z / q)) q := by
    have h1 : ContinuousAt Complex.log (q / q) := by
      rw [div_self hq]
      exact continuousAt_clog (by simp [Complex.slitPlane])
    exact h1.comp (f := fun z : ℂ => z / q) (continuousAt_id.div_const q)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont l hl
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr hq
  set ρ := min δ ‖q‖ with hρ
  have hρ0 : 0 < ρ := lt_min hδ hq0
  have hsub : toSph '' ball q ρ ⊆ range (expChart q l) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzδ : dist z q < δ := lt_of_lt_of_le hz (min_le_left _ _)
    have hzq : dist z q < ‖q‖ := lt_of_lt_of_le hz (min_le_right _ _)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [dist_zero_left] at hzq
      exact lt_irrefl _ hzq
    have hlog := hball hzδ
    simp only [div_self hq, Complex.log_one, dist_zero_right] at hlog
    set w : ℂ := Complex.log (z / q) / l with hw
    have hwn : ‖w‖ ≤ 1 := by
      rw [hw, norm_div, Complex.norm_real, Real.norm_of_nonneg hl.le, div_le_one hl]
      exact hlog.le
    refine ⟨⟨planeOf w, by
      rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]; exact hwn⟩, ?_⟩
    rw [expChart_apply]
    simp only [LinearIsometryEquiv.symm_apply_apply]
    congr 1
    rw [expMap, hw, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hl.ne'),
      Complex.exp_log (div_ne_zero hz0 hq), mul_div_cancel₀ _ hq]
  refine mem_interior.mpr ⟨_, hsub, isOpenEmbedding_toSph.isOpenMap _ isOpen_ball,
    mem_image_of_mem _ (mem_ball_self hρ0)⟩

/-- **The exponential chart is polar**, when the drawing meets its image exactly in the image of
the imaginary axis, and that lies in one edge. -/
theorem expChart_isPolar {q : ℂ} (hq : q ≠ 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1)
    {e : Set (OnePoint EuclideanPlane)} (he : e ∈ Γ.E)
    (hU : ∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap q l w) ∈ Γ.U → w.re = 0)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap q l w) ∈ e) :
    IsPolar Γ (toSph q) (expChart q l) := by
  refine ⟨expChart_injective hq hl hl1, ?_, toSph_mem_interior_range_expChart hq hl, ?_⟩
  · rw [expChart_apply]
    simp [polarCentre, expMap_zero]
  intro x hx c hc
  set w : ℂ := planeOf.symm x.1 with hw
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw, LinearIsometryEquiv.norm_map]; exact mem_closedBall_zero_iff.mp x.2
  have hw0 : w ≠ 0 := by
    intro h0
    apply hx
    apply Subtype.ext
    have : x.1 = planeOf w := by rw [hw, LinearIsometryEquiv.apply_symm_apply]
    rw [this, h0, map_zero]
    rfl
  have hc0 : (0 : ℝ) < c := hc
  have hc1 : (c : ℝ) ≤ 1 := c.2.2
  have hscale : expChart q l (discScale c x) = toSph (expMap q l ((c : ℝ) * w)) := by
    rw [expChart_apply]
    congr 2
    change planeOf.symm ((c.1 : ℝ) • x.1) = _
    rw [map_smul, Complex.real_smul]
  have hxw : expChart q l x = toSph (expMap q l w) := rfl
  rw [hscale, hxw]
  have hcw : ‖((c : ℝ) : ℂ) * w‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    nlinarith [norm_nonneg w]
  by_cases hre : w.re = 0
  · refine ⟨e, Or.inl (Or.inr he), hE w hwn hw0 hre, hE _ hcw ?_ ?_⟩
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc0.ne') hw0
    · simp [hre]
  · have hnot : toSph (expMap q l w) ∉ Γ.U := fun h => hre (hU w hwn h)
    refine ⟨connectedComponentIn (univ \ Γ.U) (toSph (expMap q l w)),
      Or.inr ((mem_R_iff Γ).mpr ⟨_, hnot, rfl⟩), mem_connectedComponentIn ⟨mem_univ _, hnot⟩, ?_⟩
    let g : ℝ → OnePoint EuclideanPlane := fun t => toSph (expMap q l ((t : ℂ) * w))
    have hg : Continuous g :=
      isOpenEmbedding_toSph.continuous.comp ((continuous_expMap q l).comp (by fun_prop))
    have hS : IsPreconnected (g '' Icc (c : ℝ) 1) := isPreconnected_Icc.image _ hg.continuousOn
    have hsub : g '' Icc (c : ℝ) 1 ⊆ univ \ Γ.U := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨mem_univ _, fun hU' => ?_⟩
      have ht0 : 0 < t := lt_of_lt_of_le hc0 ht.1
      have htw : ‖(t : ℂ) * w‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        nlinarith [norm_nonneg w, ht.2]
      have := hU _ htw hU'
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at this
      exact hre ((mul_eq_zero.mp this).resolve_left ht0.ne')
    have h1 : toSph (expMap q l w) = g 1 := by simp [g]
    rw [h1] at *
    exact hS.subset_connectedComponentIn ⟨1, ⟨hc1, le_rfl⟩, rfl⟩ hsub ⟨c, ⟨le_rfl, hc1⟩, rfl⟩

end Polar

/-- The two unit vectors on the imaginary axis are `exp (± π/2)`. -/
theorem circle_re_eq_zero_iff (w : Circle) :
    (w : ℂ).re = 0 ↔ w = Circle.exp (Real.pi / 2) ∨ w = Circle.exp (-(Real.pi / 2)) := by
  have hI : ((Circle.exp (Real.pi / 2) : Circle) : ℂ) = Complex.I := by
    rw [Circle.coe_exp]; apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  have hmI : ((Circle.exp (-(Real.pi / 2)) : Circle) : ℂ) = -Complex.I := by
    rw [Circle.coe_exp]; apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]; simp
    · rw [Complex.exp_ofReal_mul_I_im]; simp
  constructor
  · intro h
    have hn : (w : ℂ).re ^ 2 + (w : ℂ).im ^ 2 = 1 := by
      have := Complex.normSq_eq_norm_sq (w : ℂ)
      rw [Circle.norm_coe, Complex.normSq_apply] at this
      nlinarith [this]
    rw [h] at hn
    have him : (w : ℂ).im = 1 ∨ (w : ℂ).im = -1 := by
      have : ((w : ℂ).im - 1) * ((w : ℂ).im + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h1
      · left; linarith
      · right; linarith
    rcases him with him | him
    · left; apply Circle.ext; rw [hI]; exact Complex.ext h (by simpa using him)
    · right; apply Circle.ext; rw [hmI]; exact Complex.ext (by simpa using h) (by simpa using him)
  · rintro (rfl | rfl)
    · rw [hI]; simp
    · rw [hmI]; simp

theorem exp_neg_pi_div_two_ne : Circle.exp (-(Real.pi / 2)) ≠ Circle.exp (Real.pi / 2) := by
  intro h
  have := congrArg (fun c : Circle => (c : ℂ).im) h
  simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] at this
  simp at this
  linarith

theorem polarRimMap_expChart (q : ℂ) (l : ℝ) (w : Circle) :
    polarRimMap (expChart q l) w = toSph (expMap q l w) := by
  change expChart q l (polarDiscPoint 1 w) = _
  rw [expChart_apply]
  simp [polarDiscPoint]

section Rim

variable {Γ : Drawing (OnePoint EuclideanPlane)} {q : ℂ} {l : ℝ}
  {e : Set (OnePoint EuclideanPlane)}

/-- The two edge directions of the exponential chart are `± i`. -/
theorem rimDirs_expChart (he : e ∈ Γ.E)
    (hU : ∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap q l w) ∈ Γ.U → w.re = 0)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap q l w) ∈ e) :
    rimDirs Γ (expChart q l) = {Circle.exp (-(Real.pi / 2)), Circle.exp (Real.pi / 2)} := by
  ext w
  have hw1 : ‖(w : ℂ)‖ ≤ 1 := le_of_eq (Circle.norm_coe w)
  change polarRimMap (expChart q l) w ∈ Γ.U ↔ _
  rw [polarRimMap_expChart, mem_insert_iff, mem_singleton_iff, or_comm, ← circle_re_eq_zero_iff]
  constructor
  · exact hU _ hw1
  · intro h
    exact (he.2.1 (hE _ hw1 (Circle.coe_ne_zero w) h)).1

theorem gap_expChart_neg (he : e ∈ Γ.E)
    (hU : ∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap q l w) ∈ Γ.U → w.re = 0)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap q l w) ∈ e) :
    gap (rimDirs Γ (expChart q l)) (Circle.exp (-(Real.pi / 2))) = Real.pi := by
  rw [rimDirs_expChart he hU hE, gap_pair exp_neg_pi_div_two_ne]
  apply angleTo_eq ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
  rw [← Circle.exp_add]; congr 1; ring

theorem gap_expChart_pos (he : e ∈ Γ.E)
    (hU : ∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap q l w) ∈ Γ.U → w.re = 0)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap q l w) ∈ e) :
    gap (rimDirs Γ (expChart q l)) (Circle.exp (Real.pi / 2)) = Real.pi := by
  rw [rimDirs_expChart he hU hE, Set.pair_comm, gap_pair exp_neg_pi_div_two_ne.symm]
  apply angleTo_eq ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
  rw [← Circle.exp_add]
  have : -(Real.pi / 2) = Real.pi / 2 + Real.pi + -(2 * Real.pi) := by ring
  rw [this, Circle.exp_add, Circle.exp_neg, Circle.exp_two_pi, inv_one, mul_one]

/-- **The corner after `-i` is outside the circle**: it is the region of `q · exp l`. -/
theorem cornerRegion_expChart_neg (he : e ∈ Γ.E)
    (hU : ∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap q l w) ∈ Γ.U → w.re = 0)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap q l w) ∈ e) :
    cornerRegion Γ (expChart q l) (Circle.exp (-(Real.pi / 2))) =
      connectedComponentIn (univ \ Γ.U) (toSph (expMap q l 1)) := by
  rw [cornerRegion, gap_expChart_neg he hU hE, ← Circle.exp_add,
    show -(Real.pi / 2) + Real.pi / 2 = 0 by ring, Circle.exp_zero, polarRimMap_expChart]
  simp

/-- **The corner after `i` is inside the circle**: it is the region of `q · exp (-l)`. -/
theorem cornerRegion_expChart_pos (he : e ∈ Γ.E)
    (hU : ∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap q l w) ∈ Γ.U → w.re = 0)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap q l w) ∈ e) :
    cornerRegion Γ (expChart q l) (Circle.exp (Real.pi / 2)) =
      connectedComponentIn (univ \ Γ.U) (toSph (expMap q l (-1))) := by
  rw [cornerRegion, gap_expChart_pos he hU hE, ← Circle.exp_add,
    show Real.pi / 2 + Real.pi / 2 = Real.pi by ring, polarRimMap_expChart]
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

end Rim

/-- A curve that moves clockwise along the circle through `q`, at angular speed `μ`, runs out
along the direction `-i` of the exponential chart. -/
theorem runsOut_expChart_neg {q : ℂ} {l : ℝ} (hl : 0 < l) {G : ℝ → OnePoint EuclideanPlane}
    {a δ μ : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) (hμδ : μ * δ < l)
    (hG : ∀ t ∈ Icc a (a + δ),
      G t = toSph (q * Complex.exp (-(((μ * (t - a) : ℝ)) : ℂ) * Complex.I))) :
    RunsOut (expChartΨ q l) (Circle.exp (-(Real.pi / 2))) G a δ := by
  have hmI : ((Circle.exp (-(Real.pi / 2)) : Circle) : ℂ) = -Complex.I := by
    rw [Circle.coe_exp]; apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]; simp
    · rw [Complex.exp_ofReal_mul_I_im]; simp
  refine ⟨hδ, fun t => μ * (t - a) / l, by fun_prop, by simp, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · intro s _ t _ hst
    have : μ * (s - a) < μ * (t - a) := by nlinarith
    exact div_lt_div_of_pos_right this hl
  · rw [div_lt_one hl]; nlinarith [ht.2]
  · have hρ0 : 0 ≤ μ * (t - a) / l := div_nonneg (by nlinarith [ht.1]) hl.le
    have hρ1 : μ * (t - a) / l ≤ 1 := by rw [div_le_one hl]; nlinarith [ht.2]
    rw [hG t ht, chartC_expChartΨ q l (by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ0]
      exact hρ1), expMap, hmI]
    have hl' : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
    congr 3
    push_cast
    field_simp

end GraphMinor.GM06
