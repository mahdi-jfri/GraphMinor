module

public import GraphMinor.GM06.Alg57SectorTransfer

/-!
# Stars of rays in a chart

In a polar chart at a point of a drawing, the drawing is a finite star of rays: a finite set
`D` of directions. The open angle from one direction of `D` counterclockwise to the next one
is a corner. This file sets up the corners in `ℂ`, for Lemma 1 and Step 1 of Lemma 3 of our
proof of VI (5.7) (outlined in `Alg57Algorithm.lean`).

`angleTo x y` is the counterclockwise angle from `x` to `y`, in `(0, 2π]`. The corner after a
direction `w` of `D` is the open cone of the angles in `(0, gap D w)`, where `gap D w` is the
angle to the next direction of `D` (`2π` if there is none). No direction of `D` lies in a
corner (`not_mem_of_lt_gap`), and every other direction lies in some corner
(`exists_corner_of_notMem`). Thin sectors beside a ray lie in the corners next to it
(`osecP_subset_cone`, `osecM_subset_cone`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface

/-! ### The counterclockwise angle between two directions -/

/-- The counterclockwise angle from `x` to `y`, in `(0, 2π]`. -/
noncomputable def angleTo (x y : Circle) : ℝ :=
  toIocMod Real.two_pi_pos 0 (Complex.arg ((x⁻¹ * y : Circle) : ℂ))

theorem angleTo_mem (x y : Circle) : angleTo x y ∈ Ioc 0 (2 * Real.pi) := by
  have h := toIocMod_mem_Ioc Real.two_pi_pos 0 (Complex.arg ((x⁻¹ * y : Circle) : ℂ))
  rwa [zero_add] at h

theorem angleTo_pos (x y : Circle) : 0 < angleTo x y := (angleTo_mem x y).1

theorem angleTo_le (x y : Circle) : angleTo x y ≤ 2 * Real.pi := (angleTo_mem x y).2

theorem mul_exp_angleTo (x y : Circle) : x * Circle.exp (angleTo x y) = y := by
  have h : Circle.exp (angleTo x y) = x⁻¹ * y := by
    unfold angleTo
    rw [toIocMod, sub_eq_add_neg, ← neg_smul, zsmul_eq_mul,
      Circle.periodic_exp.int_mul _, Circle.exp_arg]
  rw [h, mul_inv_cancel_left]

/-- Two angles in `(0, 2π]` with the same exponential are equal. -/
theorem eq_of_exp_eq {s t : ℝ} (hs : s ∈ Ioc 0 (2 * Real.pi)) (ht : t ∈ Ioc 0 (2 * Real.pi))
    (h : Circle.exp s = Circle.exp t) : s = t := by
  by_contra hne
  exact circle_exp_ne hne (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]) h

/-- The counterclockwise angle is the only angle in `(0, 2π]` that turns `x` to `y`. -/
theorem angleTo_eq {x y : Circle} {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * Real.pi))
    (h : y = x * Circle.exp θ) : angleTo x y = θ := by
  apply eq_of_exp_eq (angleTo_mem x y) hθ
  apply mul_left_cancel (a := x)
  rw [mul_exp_angleTo, h]

theorem angleTo_self (x : Circle) : angleTo x x = 2 * Real.pi :=
  angleTo_eq ⟨Real.two_pi_pos, le_rfl⟩ (by rw [Circle.exp_two_pi, mul_one])

/-! ### Corners of a finite star -/

/-- The angle from `w` to the next direction of `D`, counterclockwise; `2π` if there is none. -/
noncomputable def gap (D : Set Circle) (w : Circle) : ℝ :=
  sInf (insert (2 * Real.pi) (angleTo w '' D))

section Gap

variable {D : Set Circle} (hD : D.Finite)
include hD

theorem gap_mem (w : Circle) : gap D w ∈ insert (2 * Real.pi) (angleTo w '' D) :=
  (insert_nonempty _ _).csInf_mem ((hD.image _).insert _)

theorem gap_le_angleTo (w : Circle) {w' : Circle} (hw' : w' ∈ D) : gap D w ≤ angleTo w w' :=
  csInf_le ((hD.image _).insert _).bddBelow (mem_insert_of_mem _ (mem_image_of_mem _ hw'))

theorem gap_le_two_pi (w : Circle) : gap D w ≤ 2 * Real.pi :=
  csInf_le ((hD.image _).insert _).bddBelow (mem_insert _ _)

theorem gap_pos (w : Circle) : 0 < gap D w := by
  rcases gap_mem hD w with h | ⟨w', -, h⟩
  · rw [h]; exact Real.two_pi_pos
  · rw [← h]; exact angleTo_pos _ _

/-- No direction of `D` lies strictly inside the corner after `w`. -/
theorem not_mem_of_lt_gap (w : Circle) {θ : ℝ} (h0 : 0 < θ) (hθ : θ < gap D w) :
    w * Circle.exp θ ∉ D := by
  intro hmem
  have h1 := gap_le_angleTo hD w hmem
  rw [angleTo_eq ⟨h0, hθ.le.trans (gap_le_two_pi hD w)⟩ rfl] at h1
  linarith

/-- The end of the corner after a direction of `D` is again a direction of `D`. -/
theorem mul_exp_gap_mem {w : Circle} (hw : w ∈ D) : w * Circle.exp (gap D w) ∈ D := by
  rcases gap_mem hD w with h | ⟨w', hw', h⟩
  · rw [h, Circle.exp_two_pi, mul_one]; exact hw
  · rw [← h, mul_exp_angleTo]; exact hw'

/-- Every direction outside a finite nonempty star lies in the corner after some direction of
the star. -/
theorem exists_corner_of_notMem (hne : D.Nonempty) {w : Circle} (hw : w ∉ D) :
    ∃ w₀ ∈ D, ∃ θ, 0 < θ ∧ θ < gap D w₀ ∧ w = w₀ * Circle.exp θ := by
  obtain ⟨w₀, hw₀, hmin⟩ := Set.exists_min_image D (fun x => angleTo x w) hD hne
  refine ⟨w₀, hw₀, angleTo w₀ w, angleTo_pos _ _, ?_, (mul_exp_angleTo w₀ w).symm⟩
  by_contra hge
  push Not at hge
  have hpi := Real.pi_pos
  rcases gap_mem hD w₀ with h | ⟨w₁, hw₁, h⟩
  · rw [h] at hge
    have h2 : angleTo w₀ w = 2 * Real.pi := le_antisymm (angleTo_le _ _) hge
    apply hw
    rw [← mul_exp_angleTo w₀ w, h2, Circle.exp_two_pi, mul_one]
    exact hw₀
  · rw [← h] at hge
    rcases hge.lt_or_eq with hlt | heq
    · have hw₁e : w₁ = w₀ * Circle.exp (angleTo w₀ w₁) := (mul_exp_angleTo _ _).symm
      have hwe : w = w₁ * Circle.exp (angleTo w₀ w - angleTo w₀ w₁) := by
        calc w = w₀ * Circle.exp (angleTo w₀ w) := (mul_exp_angleTo _ _).symm
          _ = (w₀ * Circle.exp (angleTo w₀ w₁)) *
              Circle.exp (angleTo w₀ w - angleTo w₀ w₁) := by
            rw [mul_assoc, ← Circle.exp_add, add_sub_cancel]
          _ = _ := by rw [mul_exp_angleTo]
      have := angleTo_eq ⟨by linarith, by linarith [angleTo_pos w₀ w₁, angleTo_le w₀ w]⟩ hwe
      have hm := hmin w₁ hw₁
      linarith [angleTo_pos w₀ w₁]
    · apply hw
      rw [← mul_exp_angleTo w₀ w, ← heq, mul_exp_angleTo]
      exact hw₁

end Gap

/-! ### Cones and thin sectors -/

/-- The open cone of radius `R` of the directions at angle in `(0, g)` after `w`. -/
def cone (w : Circle) (g R : ℝ) : Set ℂ :=
  {y | ∃ t : ℝ, 0 < t ∧ t ≤ R ∧ ∃ θ : ℝ, 0 < θ ∧ θ < g ∧ y = (t : ℂ) * (w * Circle.exp θ)}

theorem isPreconnected_cone (w : Circle) (g R : ℝ) : IsPreconnected (cone w g R) := by
  have : cone w g R =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * ((w * Circle.exp p.2 : Circle) : ℂ)) '' (Ioc 0 R ×ˢ Ioo 0 g) := by
    ext y
    constructor
    · rintro ⟨t, ht, htR, θ, hθ, hθg, rfl⟩
      exact ⟨(t, θ), ⟨⟨ht, htR⟩, ⟨hθ, hθg⟩⟩, rfl⟩
    · rintro ⟨⟨t, θ⟩, ⟨⟨ht, htR⟩, ⟨hθ, hθg⟩⟩, rfl⟩
      exact ⟨t, ht, htR, θ, hθ, hθg, rfl⟩
  rw [this]
  exact (isPreconnected_Ioc.prod isPreconnected_Ioo).image _ (by fun_prop)

/-- A point of a thin counterclockwise sector, in polar form about the ray. -/
theorem osecP_polar {W : Circle} {ε R : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi / 2) {y : ℂ}
    (hy : y ∈ osecP W ε R) :
    0 < ‖y‖ ∧ ‖y‖ < R ∧ ∃ θ, 0 < θ ∧ θ ≤ ε ∧ y = (‖y‖ : ℂ) * (W * Circle.exp θ) := by
  obtain ⟨hn, h1, h2⟩ := hy
  set u : ℂ := ((W⁻¹ : Circle) : ℂ) * y with hu
  have hyu : y = (W : ℂ) * u := by
    rw [hu, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]
  have hnu : ‖u‖ = ‖y‖ := by rw [hu, norm_mul, Circle.norm_coe, one_mul]
  have him : 0 < u.im := h1
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at h1; simp [across] at h1
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  refine ⟨hpos, hn, Complex.arg u, ?_, ?_, ?_⟩
  · have := Complex.arg_nonneg_iff.mpr him.le
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := Complex.arg_eq_zero_iff.mp h.symm
      have : u.im = 0 := by
        have := Complex.norm_mul_sin_arg u
        rw [← h, Real.sin_zero, mul_zero] at this
        exact this.symm
      linarith
  · rw [across_turnBy] at h2
    have hre : u.re = ‖u‖ * Real.cos (Complex.arg u) := (Complex.norm_mul_cos_arg u).symm
    have hima : u.im = ‖u‖ * Real.sin (Complex.arg u) := (Complex.norm_mul_sin_arg u).symm
    have h2' : Real.cos ε * u.im - Real.sin ε * u.re < 0 := h2
    rw [hre, hima] at h2'
    have hsin : Real.sin (Complex.arg u - ε) < 0 := by
      rw [Real.sin_sub]
      have hnu' : 0 < ‖u‖ := by rw [hnu]; exact hpos
      nlinarith
    by_contra hgt
    push Not at hgt
    have hlt : Complex.arg u - ε < Real.pi := by
      linarith [Complex.arg_le_pi u, Real.pi_pos]
    have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hlt.le
    linarith
  · have e1 := Complex.norm_mul_exp_arg_mul_I u
    rw [Circle.coe_exp, ← hnu]
    calc y = (W : ℂ) * u := hyu
      _ = (W : ℂ) * ((‖u‖ : ℂ) * Complex.exp (Complex.arg u * Complex.I)) := by
        conv_lhs => rw [← e1]
      _ = _ := by ring

/-- A point of a thin clockwise sector, in polar form about the ray. -/
theorem osecM_polar {W : Circle} {ε R : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi / 2) {y : ℂ}
    (hy : y ∈ osecM W ε R) :
    0 < ‖y‖ ∧ ‖y‖ < R ∧ ∃ θ, -ε ≤ θ ∧ θ < 0 ∧ y = (‖y‖ : ℂ) * (W * Circle.exp θ) := by
  obtain ⟨hn, h1, h2⟩ := hy
  set u : ℂ := ((W⁻¹ : Circle) : ℂ) * y with hu
  have hyu : y = (W : ℂ) * u := by
    rw [hu, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]
  have hnu : ‖u‖ = ‖y‖ := by rw [hu, norm_mul, Circle.norm_coe, one_mul]
  have him : u.im < 0 := h2
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at h2; simp [across] at h2
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  refine ⟨hpos, hn, Complex.arg u, ?_, Complex.arg_neg_iff.mpr him, ?_⟩
  · rw [across_turnBy, Real.cos_neg, Real.sin_neg] at h1
    have hre : u.re = ‖u‖ * Real.cos (Complex.arg u) := (Complex.norm_mul_cos_arg u).symm
    have hima : u.im = ‖u‖ * Real.sin (Complex.arg u) := (Complex.norm_mul_sin_arg u).symm
    have h1' : 0 < Real.cos ε * u.im - -Real.sin ε * u.re := h1
    rw [hre, hima] at h1'
    have hsin : 0 < Real.sin (Complex.arg u + ε) := by
      rw [Real.sin_add]
      have hnu' : 0 < ‖u‖ := by rw [hnu]; exact hpos
      nlinarith
    by_contra hlt
    push Not at hlt
    have hgt : -Real.pi < Complex.arg u + ε := by
      linarith [Complex.neg_pi_lt_arg u, Real.pi_pos]
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) hgt.le
    linarith
  · have e1 := Complex.norm_mul_exp_arg_mul_I u
    rw [Circle.coe_exp, ← hnu]
    calc y = (W : ℂ) * u := hyu
      _ = (W : ℂ) * ((‖u‖ : ℂ) * Complex.exp (Complex.arg u * Complex.I)) := by
        conv_lhs => rw [← e1]
      _ = _ := by ring

/-- A thin counterclockwise sector beside `w` lies in the corner after `w`. -/
theorem osecP_subset_cone {w : Circle} {ε g R : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi / 2) (hεg : ε < g) :
    osecP w ε R ⊆ cone w g R := by
  intro y hy
  obtain ⟨hpos, hR, θ, hθ, hθε, hyeq⟩ := osecP_polar hε hε' hy
  exact ⟨‖y‖, hpos, hR.le, θ, hθ, by linarith, hyeq⟩

/-- A thin clockwise sector beside the end `w * exp g` of a corner lies in that corner. -/
theorem osecM_subset_cone {w : Circle} {ε g R : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi / 2) (hεg : ε < g) :
    osecM (w * Circle.exp g) ε R ⊆ cone w g R := by
  intro y hy
  obtain ⟨hpos, hR, θ, hθ, hθ0, hyeq⟩ := osecM_polar hε hε' hy
  refine ⟨‖y‖, hpos, hR.le, g + θ, by linarith, by linarith, ?_⟩
  calc y = _ := hyeq
    _ = _ := by simp only [Circle.coe_mul, Circle.exp_add]; ring

/-- A nonzero point of a disc lies on the ray of its direction. -/
theorem eq_norm_mul_unitOf {y : ℂ} (hy : y ≠ 0) : y = (‖y‖ : ℂ) * unitOf y hy :=
  (norm_mul_unitOf y hy).symm

/-- A nonzero point whose direction lies in a corner lies in the cone of the corner. -/
theorem mem_cone_of_unitOf {w : Circle} {g R : ℝ} {y : ℂ} (hy : y ≠ 0) (hR : ‖y‖ ≤ R) {θ : ℝ}
    (hθ : 0 < θ) (hθg : θ < g) (hdir : unitOf y hy = w * Circle.exp θ) : y ∈ cone w g R :=
  ⟨‖y‖, norm_pos_iff.mpr hy, hR, θ, hθ, hθg, by
    have := eq_norm_mul_unitOf hy
    rw [hdir, Circle.coe_mul] at this
    exact this⟩

end GraphMinor.GM06
