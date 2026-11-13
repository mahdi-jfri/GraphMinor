module

public import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Reduction4
import GraphMinor.Surface.Crossing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Graph Minors VI, Section 5: Disjoint Paths along a Cylinder and Proof of (5.2)

This file develops the universal-cover strip crossing method on $[1, 2] \times \mathbb{R}$ and
proves `GM06.theorem_5_2 : Statement52` (and `GM06.theorem_5_4_red124`, the feasibility transfer
for Reductions 1, 2, and 4) of Robertson and Seymour, *Graph Minors. VI. Disjoint paths across a
disc*, J. Combin. Theory Ser. B **41** (1986), 115–138 (pages 127–135) with zero unproved
hypotheses.
-/

public section

namespace GraphMinor.GM06

open Set Function Complex Real Topology Metric Graph GraphMinor.Surface GraphMinor.GM11

/-! ## 1. Universal-Cover Strip Crossing via `disc_crossing` -/

private theorem circle_map_mem_closedUnitDisc (u : Circle) :
    complexPlane (u : ℂ) ∈ ClosedUnitDisc := by
  rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
  exact le_of_eq (mem_sphere_zero_iff_norm.mp u.2)

private theorem circle_map_mem_bd (u : Circle) :
    (⟨complexPlane (u : ℂ), circle_map_mem_closedUnitDisc u⟩ : ClosedUnitDisc) ∈
      bd ClosedUnitDisc := by
  rw [bd_closedUnitDisc]
  change complexPlane (u : ℂ) ∈ UnitCircle
  rw [UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact mem_sphere_zero_iff_norm.mp u.2

private theorem bd_inv_mem_circle (x : bd ClosedUnitDisc) :
    complexPlane.symm x.1.1 ∈ Submonoid.unitSphere ℂ := by
  have hx : x.1.1 ∈ UnitCircle := bd_closedUnitDisc.subset x.2
  change complexPlane.symm x.1.1 ∈ sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact mem_sphere_zero_iff_norm.mp hx

/-- The homeomorphism `Circle ≃ₜ bd ClosedUnitDisc` induced by `complexPlane`. -/
private noncomputable def circleHomeomorphBdClosedUnitDisc :
    Circle ≃ₜ bd ClosedUnitDisc where
  toFun u := ⟨⟨complexPlane (u : ℂ), circle_map_mem_closedUnitDisc u⟩, circle_map_mem_bd u⟩
  invFun x := ⟨complexPlane.symm x.1.1, bd_inv_mem_circle x⟩
  left_inv u := by
    ext1
    exact complexPlane.symm_apply_apply (u : ℂ)
  right_inv x := by
    ext1; ext1
    exact complexPlane.apply_symm_apply x.1.1
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact complexPlane.continuous.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact complexPlane.symm.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)

private theorem oArcMap_circleHomeomorphBdClosedUnitDisc (u : Circle) :
    (oArcMap circleHomeomorphBdClosedUnitDisc u).1 = complexPlane (u : ℂ) :=
  rfl

/-- Auxiliary angle map $\phi(M, y) = \frac{\pi}{4} + \frac{\pi}{8M} y$ mapping $[-M, M]$ into
$[\frac{\pi}{8}, \frac{3\pi}{8}] \subset (0, \frac{\pi}{2})$. -/
private noncomputable def stripAngle (M y : ℝ) : ℝ :=
  π / 4 + (π / (8 * M)) * y

private theorem stripAngle_mem_Icc {M y : ℝ} (hM : 0 < M) (hy1 : -M ≤ y) (hy2 : y ≤ M) :
    stripAngle M y ∈ Icc (π / 8) (3 * π / 8) := by
  unfold stripAngle
  have hpi : 0 < π := pi_pos
  have h1 : -(π / 8) ≤ (π / (8 * M)) * y := by
    have hdiv : 0 ≤ π / (8 * M) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hy1 hdiv
    have hsimp : (π / (8 * M)) * (-M) = -(π / 8) := by
      field_simp [ne_of_gt hM]
    linarith
  have h2 : (π / (8 * M)) * y ≤ π / 8 := by
    have hdiv : 0 ≤ π / (8 * M) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hy2 hdiv
    have hsimp : (π / (8 * M)) * M = π / 8 := by
      field_simp [ne_of_gt hM]
    linarith
  constructor <;> linarith

private theorem stripAngle_strictMono {M : ℝ} (hM : 0 < M) :
    StrictMono (stripAngle M) := by
  intro y₁ y₂ hy
  unfold stripAngle
  have hpos : 0 < π / (8 * M) := by positivity
  linarith [mul_lt_mul_of_pos_left hy hpos]

/-- The complex embedding of $[1, 2] \times [-M, M]$ into the closed unit disc in $\mathbb{C}$:
$(r, y) \mapsto (2r - 3) \cos \phi(M, y) + i \sin \phi(M, y)$. -/
private noncomputable def stripToComplex (M : ℝ) (p : ℝ × ℝ) : ℂ :=
  (((2 * p.1 - 3) * Real.cos (stripAngle M p.2) : ℝ) : ℂ) +
    ((Real.sin (stripAngle M p.2) : ℝ) : ℂ) * Complex.I

private theorem continuous_stripToComplex (M : ℝ) : Continuous (stripToComplex M) := by
  unfold stripToComplex stripAngle
  fun_prop

private theorem norm_stripToComplex_le_one {M : ℝ} {p : ℝ × ℝ} (hr : p.1 ∈ Icc (1 : ℝ) 2) :
    ‖stripToComplex M p‖ ≤ 1 := by
  let u : ℝ := 2 * p.1 - 3
  let θ : ℝ := stripAngle M p.2
  have hu_sq : u ^ 2 ≤ 1 := by
    have h1 : -1 ≤ u := by dsimp [u]; linarith [hr.1]
    have h2 : u ≤ 1 := by dsimp [u]; linarith [hr.2]
    nlinarith
  have hcos_nonneg : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hsum_le : (u * Real.cos θ) ^ 2 + Real.sin θ ^ 2 ≤ 1 := by
    calc (u * Real.cos θ) ^ 2 + Real.sin θ ^ 2
      _ = u ^ 2 * Real.cos θ ^ 2 + Real.sin θ ^ 2 := by ring
      _ ≤ 1 * Real.cos θ ^ 2 + Real.sin θ ^ 2 := by nlinarith
      _ = 1 := by rw [one_mul, Real.cos_sq_add_sin_sq]
  have hnorm_sq : ‖stripToComplex M p‖ ^ 2 = (u * Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
    have hre : (stripToComplex M p).re = u * Real.cos θ := by
      simp only [stripToComplex, u, θ, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
    have him : (stripToComplex M p).im = Real.sin θ := by
      simp only [stripToComplex, θ, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_one, mul_zero, add_zero, zero_add]
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  nlinarith [norm_nonneg (stripToComplex M p)]

private theorem injOn_stripToComplex {M : ℝ} (hM : 0 < M) :
    InjOn (stripToComplex M) (Icc (1 : ℝ) 2 ×ˢ Icc (-M) M) := by
  rintro ⟨r₁, y₁⟩ ⟨hr₁, hy₁⟩ ⟨r₂, y₂⟩ ⟨hr₂, hy₂⟩ heq
  have him : Real.sin (stripAngle M y₁) = Real.sin (stripAngle M y₂) := by
    have h := congrArg Complex.im heq
    simpa only [stripToComplex, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_one, mul_zero, zero_mul, add_zero, zero_add] using h
  have hθ₁ := stripAngle_mem_Icc hM hy₁.1 hy₁.2
  have hθ₂ := stripAngle_mem_Icc hM hy₂.1 hy₂.2
  have hpi : 0 < π := pi_pos
  have hθ₁_Icc : stripAngle M y₁ ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [hθ₁.1], by linarith [hθ₁.2]⟩
  have hθ₂_Icc : stripAngle M y₂ ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [hθ₂.1], by linarith [hθ₂.2]⟩
  have hθ_eq : stripAngle M y₁ = stripAngle M y₂ :=
    Real.injOn_sin hθ₁_Icc hθ₂_Icc him
  have hy_eq : y₁ = y₂ := (stripAngle_strictMono hM).injective hθ_eq
  subst hy_eq
  have hre : (2 * r₁ - 3) * Real.cos (stripAngle M y₁) =
      (2 * r₂ - 3) * Real.cos (stripAngle M y₁) := by
    have h := congrArg Complex.re heq
    simpa only [stripToComplex, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using h
  have hcos_pos : 0 < Real.cos (stripAngle M y₁) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ₁.1], by linarith [hθ₁.2]⟩
  have hr_eq : r₁ = r₂ := by
    have hmul := mul_right_cancel₀ (ne_of_gt hcos_pos) hre
    linarith
  exact Prod.ext hr_eq rfl

private theorem stripToComplex_left (M y : ℝ) :
    stripToComplex M (1, y) = (Circle.exp (π - stripAngle M y) : ℂ) := by
  unfold stripToComplex
  change (((2 * (1 : ℝ) - 3) * Real.cos (stripAngle M y) : ℝ) : ℂ) +
      ((Real.sin (stripAngle M y) : ℝ) : ℂ) * Complex.I =
    (Circle.exp (π - stripAngle M y) : ℂ)
  have h1 : (2 * (1 : ℝ) - 3) = -1 := by ring
  rw [h1, neg_one_mul, ← Real.cos_pi_sub, ← Real.sin_pi_sub,
    Circle.coe_exp, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

private theorem stripToComplex_right (M y : ℝ) :
    stripToComplex M (2, y) = (Circle.exp (stripAngle M y) : ℂ) := by
  unfold stripToComplex
  change (((2 * (2 : ℝ) - 3) * Real.cos (stripAngle M y) : ℝ) : ℂ) +
      ((Real.sin (stripAngle M y) : ℝ) : ℂ) * Complex.I =
    (Circle.exp (stripAngle M y) : ℂ)
  have h1 : (2 * (2 : ℝ) - 3) = 1 := by ring
  rw [h1, one_mul, Circle.coe_exp, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

private theorem arg_exp_of_mem_Ioo {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    Complex.arg (Circle.exp θ : ℂ) = θ := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨h1, h2⟩

/-- **Universal-Cover Strip Crossing Lemma**:
If $\gamma, \delta \colon [0, 1] \to [1, 2] \times \mathbb{R}$ are continuous curves with
$\gamma(0), \delta(0) \in \{1\} \times \mathbb{R}$ and
$\gamma(1), \delta(1) \in \{2\} \times \mathbb{R}$ whose vertical coordinates reverse order between
$r = 1$ and $r = 2$, then $\gamma$ and $\delta$ intersect. -/
theorem strip_crossing (γ δ : C(unitInterval, ℝ × ℝ))
    (hγ_r : ∀ t : unitInterval, (γ t).1 ∈ Icc (1 : ℝ) 2)
    (hδ_r : ∀ t : unitInterval, (δ t).1 ∈ Icc (1 : ℝ) 2)
    (hγ0 : (γ 0).1 = 1) (hγ1 : (γ 1).1 = 2)
    (hδ0 : (δ 0).1 = 1) (hδ1 : (δ 1).1 = 2)
    (hswap : ((γ 0).2 < (δ 0).2 ∧ (δ 1).2 < (γ 1).2) ∨
             ((δ 0).2 < (γ 0).2 ∧ (γ 1).2 < (δ 1).2)) :
    ∃ t₁ t₂ : unitInterval, γ t₁ = δ t₂ := by
  -- Bound the vertical coordinates of γ and δ on the compact interval `unitInterval`.
  let s_y : Set ℝ := range (fun t => (γ t).2) ∪ range (fun t => (δ t).2)
  have hs_comp : IsCompact s_y :=
    (isCompact_range (continuous_snd.comp γ.continuous)).union
      (isCompact_range (continuous_snd.comp δ.continuous))
  obtain ⟨R, hR⟩ := hs_comp.isBounded.subset_closedBall (0 : ℝ)
  let M : ℝ := max R 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hγ_y : ∀ t : unitInterval, (γ t).2 ∈ Icc (-M) M := by
    intro t
    have ht : (γ t).2 ∈ closedBall (0 : ℝ) R := hR (Or.inl ⟨t, rfl⟩)
    have hnorm : |(γ t).2| ≤ R := by simpa [mem_closedBall_zero_iff] using ht
    have hle : R ≤ M := le_max_left R 1
    exact ⟨by linarith [neg_abs_le (γ t).2], by linarith [le_abs_self (γ t).2]⟩
  have hδ_y : ∀ t : unitInterval, (δ t).2 ∈ Icc (-M) M := by
    intro t
    have ht : (δ t).2 ∈ closedBall (0 : ℝ) R := hR (Or.inr ⟨t, rfl⟩)
    have hnorm : |(δ t).2| ≤ R := by simpa [mem_closedBall_zero_iff] using ht
    have hle : R ≤ M := le_max_left R 1
    exact ⟨by linarith [neg_abs_le (δ t).2], by linarith [le_abs_self (δ t).2]⟩
  -- Map γ and δ into `ClosedUnitDisc`.
  let Ψ : ℝ × ℝ → EuclideanPlane := fun p => complexPlane (stripToComplex M p)
  have hΨ_cont : Continuous Ψ := complexPlane.continuous.comp (continuous_stripToComplex M)
  have hγD_mem : ∀ t : unitInterval, Ψ (γ t) ∈ ClosedUnitDisc := by
    intro t
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact norm_stripToComplex_le_one (hγ_r t)
  have hδD_mem : ∀ t : unitInterval, Ψ (δ t) ∈ ClosedUnitDisc := by
    intro t
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact norm_stripToComplex_le_one (hδ_r t)
  let γD : C(unitInterval, ClosedUnitDisc) :=
    ⟨fun t => ⟨Ψ (γ t), hγD_mem t⟩, (hΨ_cont.comp γ.continuous).subtype_mk hγD_mem⟩
  let δD : C(unitInterval, ClosedUnitDisc) :=
    ⟨fun t => ⟨Ψ (δ t), hδD_mem t⟩, (hΨ_cont.comp δ.continuous).subtype_mk hδD_mem⟩
  -- The four endpoints on `Circle`
  let u_a : Circle := Circle.exp (π - stripAngle M (γ 0).2)
  let u_c : Circle := Circle.exp (stripAngle M (γ 1).2)
  let u_b : Circle := Circle.exp (π - stripAngle M (δ 0).2)
  let u_d : Circle := Circle.exp (stripAngle M (δ 1).2)
  let φ := circleHomeomorphBdClosedUnitDisc
  have ha_eq : oArcMap φ u_a = γD 0 := by
    ext1
    change complexPlane (u_a : ℂ) = complexPlane (stripToComplex M (γ 0))
    have h0 : γ 0 = (1, (γ 0).2) := Prod.ext hγ0 rfl
    rw [h0, stripToComplex_left]
  have hc_eq : oArcMap φ u_c = γD 1 := by
    ext1
    change complexPlane (u_c : ℂ) = complexPlane (stripToComplex M (γ 1))
    have h1 : γ 1 = (2, (γ 1).2) := Prod.ext hγ1 rfl
    rw [h1, stripToComplex_right]
  have hb_eq : oArcMap φ u_b = δD 0 := by
    ext1
    change complexPlane (u_b : ℂ) = complexPlane (stripToComplex M (δ 0))
    have h0 : δ 0 = (1, (δ 0).2) := Prod.ext hδ0 rfl
    rw [h0, stripToComplex_left]
  have hd_eq : oArcMap φ u_d = δD 1 := by
    ext1
    change complexPlane (u_d : ℂ) = complexPlane (stripToComplex M (δ 1))
    have h1 : δ 1 = (2, (δ 1).2) := Prod.ext hδ1 rfl
    rw [h1, stripToComplex_right]
  have hpi : 0 < π := pi_pos
  have hθ_γ0 := stripAngle_mem_Icc hM_pos (hγ_y 0).1 (hγ_y 0).2
  have hθ_γ1 := stripAngle_mem_Icc hM_pos (hγ_y 1).1 (hγ_y 1).2
  have hθ_δ0 := stripAngle_mem_Icc hM_pos (hδ_y 0).1 (hδ_y 0).2
  have hθ_δ1 := stripAngle_mem_Icc hM_pos (hδ_y 1).1 (hδ_y 1).2
  have harg_a : circleStdCoord.angle u_a = π - stripAngle M (γ 0).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_γ0.2]) (by linarith [hθ_γ0.1])
  have harg_c : circleStdCoord.angle u_c = stripAngle M (γ 1).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_γ1.1]) (by linarith [hθ_γ1.2])
  have harg_b : circleStdCoord.angle u_b = π - stripAngle M (δ 0).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_δ0.2]) (by linarith [hθ_δ0.1])
  have harg_d : circleStdCoord.angle u_d = stripAngle M (δ 1).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_δ1.1]) (by linarith [hθ_δ1.2])
  have hcross_circle : circleCrosses circleStdCoord u_a u_c u_b u_d := by
    rcases hswap with ⟨h0_lt, h1_lt⟩ | ⟨h0_lt, h1_lt⟩
    · have hφ0 : stripAngle M (γ 0).2 < stripAngle M (δ 0).2 := stripAngle_strictMono hM_pos h0_lt
      have hφ1 : stripAngle M (δ 1).2 < stripAngle M (γ 1).2 := stripAngle_strictMono hM_pos h1_lt
      have h_ord1 : circleStdCoord.angle u_d < circleStdCoord.angle u_c := by linarith
      have h_ord2 : circleStdCoord.angle u_c < circleStdCoord.angle u_b := by linarith [hθ_γ1.2, hθ_δ0.2]
      have h_ord3 : circleStdCoord.angle u_b < circleStdCoord.angle u_a := by linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h => (ne_of_gt (h_ord2.trans h_ord3)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt (h_ord1.trans h_ord2)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord3) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt ((h_ord1.trans h_ord2).trans h_ord3)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_lt h_ord2) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord1) (congrArg circleStdCoord.angle h)
      · simp only [onOpenArc, min_eq_right (h_ord2.trans h_ord3).le,
          max_eq_left (h_ord2.trans h_ord3).le]
        exact iff_of_true ⟨h_ord2, h_ord3⟩ (fun hd => not_lt_of_ge hd.1.le h_ord1)
    · have hφ0 : stripAngle M (δ 0).2 < stripAngle M (γ 0).2 := stripAngle_strictMono hM_pos h0_lt
      have hφ1 : stripAngle M (γ 1).2 < stripAngle M (δ 1).2 := stripAngle_strictMono hM_pos h1_lt
      have h_ord1 : circleStdCoord.angle u_c < circleStdCoord.angle u_d := by linarith
      have h_ord2 : circleStdCoord.angle u_d < circleStdCoord.angle u_a := by linarith [hθ_δ1.2, hθ_γ0.2]
      have h_ord3 : circleStdCoord.angle u_a < circleStdCoord.angle u_b := by linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h => (ne_of_gt (h_ord1.trans h_ord2)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_lt (h_ord2.trans h_ord3)) (congrArg circleStdCoord.angle h.symm)
      · exact fun h => (ne_of_lt h_ord3) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord2) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_lt ((h_ord1.trans h_ord2).trans h_ord3)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_lt h_ord1) (congrArg circleStdCoord.angle h)
      · simp only [onOpenArc, min_eq_right (h_ord1.trans h_ord2).le,
          max_eq_left (h_ord1.trans h_ord2).le]
        exact iff_of_false (fun hb => not_lt_of_ge hb.2.le h_ord3)
          (not_not.mpr ⟨h_ord1, h_ord2⟩)
  have hcross_bd : CrossesOn (bd ClosedUnitDisc) (γD 0) (γD 1) (δD 0) (δD 1) := by
    rw [← ha_eq, ← hc_eq, ← hb_eq, ← hd_eq, crossesOn_oArcMap_iff φ,
      crossesOn_univ_iff_circleStdCoord]
    exact hcross_circle
  have hmeet := disc_crossing (univ : Set ClosedUnitDisc) (range γD) (range δD)
    (γD 0) (γD 1) (δD 0) (δD 1)
    ⟨Homeomorph.Set.univ ClosedUnitDisc |>.symm⟩
    (subset_univ _) (subset_univ _)
    (isCompact_range γD.continuous) (isCompact_range δD.continuous)
    (isConnected_range γD.continuous) (isConnected_range δD.continuous)
    ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩
    (by
      have hbd : discBd (univ : Set ClosedUnitDisc) = bd ClosedUnitDisc := by
        simpa [discBd, Homeomorph.Set.univ] using
          image_bd_homeomorph (Homeomorph.Set.univ ClosedUnitDisc)
      rw [hbd]; exact hcross_bd)
  rcases hmeet with ⟨w, ⟨t₁, rfl⟩, ⟨t₂, ht₂⟩⟩
  have hΨ_eq : stripToComplex M (δ t₂) = stripToComplex M (γ t₁) :=
    complexPlane.injective (congrArg Subtype.val ht₂)
  have h_eq := injOn_stripToComplex hM_pos ⟨hδ_r t₂, hδ_y t₂⟩ ⟨hγ_r t₁, hγ_y t₁⟩ hΨ_eq
  exact ⟨t₁, t₂, h_eq.symm⟩

/-- **Left-Boundary Strip Crossing Lemma**:
If $\gamma, \delta \colon [0, 1] \to [1, 2] \times \mathbb{R}$ are continuous curves with
$\gamma(0), \gamma(1), \delta(0) \in \{1\} \times \mathbb{R}$ and
$\delta(1) \in \{2\} \times \mathbb{R}$ such that $(\delta 0).2$ lies strictly between
$(\gamma 0).2$ and $(\gamma 1).2$, then $\gamma$ and $\delta$ intersect. -/
theorem strip_crossing_left (γ δ : C(unitInterval, ℝ × ℝ))
    (hγ_r : ∀ t : unitInterval, (γ t).1 ∈ Icc (1 : ℝ) 2)
    (hδ_r : ∀ t : unitInterval, (δ t).1 ∈ Icc (1 : ℝ) 2)
    (hγ0 : (γ 0).1 = 1) (hγ1 : (γ 1).1 = 1)
    (hδ0 : (δ 0).1 = 1) (hδ1 : (δ 1).1 = 2)
    (hbetween : ((γ 0).2 < (δ 0).2 ∧ (δ 0).2 < (γ 1).2) ∨
                ((γ 1).2 < (δ 0).2 ∧ (δ 0).2 < (γ 0).2)) :
    ∃ t₁ t₂ : unitInterval, γ t₁ = δ t₂ := by
  let s_y : Set ℝ := range (fun t => (γ t).2) ∪ range (fun t => (δ t).2)
  have hs_comp : IsCompact s_y :=
    (isCompact_range (continuous_snd.comp γ.continuous)).union
      (isCompact_range (continuous_snd.comp δ.continuous))
  obtain ⟨R, hR⟩ := hs_comp.isBounded.subset_closedBall (0 : ℝ)
  let M : ℝ := max R 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hγ_y : ∀ t : unitInterval, (γ t).2 ∈ Icc (-M) M := by
    intro t
    have ht : (γ t).2 ∈ closedBall (0 : ℝ) R := hR (Or.inl ⟨t, rfl⟩)
    have hnorm : |(γ t).2| ≤ R := by simpa [mem_closedBall_zero_iff] using ht
    have hle : R ≤ M := le_max_left R 1
    exact ⟨by linarith [neg_abs_le (γ t).2], by linarith [le_abs_self (γ t).2]⟩
  have hδ_y : ∀ t : unitInterval, (δ t).2 ∈ Icc (-M) M := by
    intro t
    have ht : (δ t).2 ∈ closedBall (0 : ℝ) R := hR (Or.inr ⟨t, rfl⟩)
    have hnorm : |(δ t).2| ≤ R := by simpa [mem_closedBall_zero_iff] using ht
    have hle : R ≤ M := le_max_left R 1
    exact ⟨by linarith [neg_abs_le (δ t).2], by linarith [le_abs_self (δ t).2]⟩
  let Ψ : ℝ × ℝ → EuclideanPlane := fun p => complexPlane (stripToComplex M p)
  have hΨ_cont : Continuous Ψ := complexPlane.continuous.comp (continuous_stripToComplex M)
  have hγD_mem : ∀ t : unitInterval, Ψ (γ t) ∈ ClosedUnitDisc := by
    intro t
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact norm_stripToComplex_le_one (hγ_r t)
  have hδD_mem : ∀ t : unitInterval, Ψ (δ t) ∈ ClosedUnitDisc := by
    intro t
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact norm_stripToComplex_le_one (hδ_r t)
  let γD : C(unitInterval, ClosedUnitDisc) :=
    ⟨fun t => ⟨Ψ (γ t), hγD_mem t⟩, (hΨ_cont.comp γ.continuous).subtype_mk hγD_mem⟩
  let δD : C(unitInterval, ClosedUnitDisc) :=
    ⟨fun t => ⟨Ψ (δ t), hδD_mem t⟩, (hΨ_cont.comp δ.continuous).subtype_mk hδD_mem⟩
  let u_a : Circle := Circle.exp (π - stripAngle M (γ 0).2)
  let u_c : Circle := Circle.exp (π - stripAngle M (γ 1).2)
  let u_b : Circle := Circle.exp (π - stripAngle M (δ 0).2)
  let u_d : Circle := Circle.exp (stripAngle M (δ 1).2)
  let φ := circleHomeomorphBdClosedUnitDisc
  have ha_eq : oArcMap φ u_a = γD 0 := by
    ext1
    change complexPlane (u_a : ℂ) = complexPlane (stripToComplex M (γ 0))
    have h0 : γ 0 = (1, (γ 0).2) := Prod.ext hγ0 rfl
    rw [h0, stripToComplex_left]
  have hc_eq : oArcMap φ u_c = γD 1 := by
    ext1
    change complexPlane (u_c : ℂ) = complexPlane (stripToComplex M (γ 1))
    have h1 : γ 1 = (1, (γ 1).2) := Prod.ext hγ1 rfl
    rw [h1, stripToComplex_left]
  have hb_eq : oArcMap φ u_b = δD 0 := by
    ext1
    change complexPlane (u_b : ℂ) = complexPlane (stripToComplex M (δ 0))
    have h0 : δ 0 = (1, (δ 0).2) := Prod.ext hδ0 rfl
    rw [h0, stripToComplex_left]
  have hd_eq : oArcMap φ u_d = δD 1 := by
    ext1
    change complexPlane (u_d : ℂ) = complexPlane (stripToComplex M (δ 1))
    have h1 : δ 1 = (2, (δ 1).2) := Prod.ext hδ1 rfl
    rw [h1, stripToComplex_right]
  have hpi : 0 < π := pi_pos
  have hθ_γ0 := stripAngle_mem_Icc hM_pos (hγ_y 0).1 (hγ_y 0).2
  have hθ_γ1 := stripAngle_mem_Icc hM_pos (hγ_y 1).1 (hγ_y 1).2
  have hθ_δ0 := stripAngle_mem_Icc hM_pos (hδ_y 0).1 (hδ_y 0).2
  have hθ_δ1 := stripAngle_mem_Icc hM_pos (hδ_y 1).1 (hδ_y 1).2
  have harg_a : circleStdCoord.angle u_a = π - stripAngle M (γ 0).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_γ0.2]) (by linarith [hθ_γ0.1])
  have harg_c : circleStdCoord.angle u_c = π - stripAngle M (γ 1).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_γ1.2]) (by linarith [hθ_γ1.1])
  have harg_b : circleStdCoord.angle u_b = π - stripAngle M (δ 0).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_δ0.2]) (by linarith [hθ_δ0.1])
  have harg_d : circleStdCoord.angle u_d = stripAngle M (δ 1).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_δ1.1]) (by linarith [hθ_δ1.2])
  have hcross_circle : circleCrosses circleStdCoord u_a u_c u_b u_d := by
    rcases hbetween with ⟨h0_lt, h1_lt⟩ | ⟨h1_lt, h0_lt⟩
    · have hφ0 : stripAngle M (γ 0).2 < stripAngle M (δ 0).2 := stripAngle_strictMono hM_pos h0_lt
      have hφ1 : stripAngle M (δ 0).2 < stripAngle M (γ 1).2 := stripAngle_strictMono hM_pos h1_lt
      have h_ord1 : circleStdCoord.angle u_d < circleStdCoord.angle u_c := by
        linarith [hθ_δ1.2, hθ_γ1.2]
      have h_ord2 : circleStdCoord.angle u_c < circleStdCoord.angle u_b := by linarith
      have h_ord3 : circleStdCoord.angle u_b < circleStdCoord.angle u_a := by linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h => (ne_of_gt (h_ord2.trans h_ord3)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt (h_ord1.trans h_ord2)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord3) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt ((h_ord1.trans h_ord2).trans h_ord3)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_lt h_ord2) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord1) (congrArg circleStdCoord.angle h)
      · simp only [onOpenArc, min_eq_right (h_ord2.trans h_ord3).le,
          max_eq_left (h_ord2.trans h_ord3).le]
        exact iff_of_true ⟨h_ord2, h_ord3⟩ (fun hd => not_lt_of_ge hd.1.le h_ord1)
    · have hφ0 : stripAngle M (δ 0).2 < stripAngle M (γ 0).2 := stripAngle_strictMono hM_pos h0_lt
      have hφ1 : stripAngle M (γ 1).2 < stripAngle M (δ 0).2 := stripAngle_strictMono hM_pos h1_lt
      have h_ord1 : circleStdCoord.angle u_d < circleStdCoord.angle u_a := by
        linarith [hθ_δ1.2, hθ_γ0.2]
      have h_ord2 : circleStdCoord.angle u_a < circleStdCoord.angle u_b := by linarith
      have h_ord3 : circleStdCoord.angle u_b < circleStdCoord.angle u_c := by linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h => (ne_of_lt (h_ord2.trans h_ord3)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt (h_ord1.trans h_ord2)) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_lt h_ord2) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord1) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt h_ord3) (congrArg circleStdCoord.angle h)
      · exact fun h => (ne_of_gt ((h_ord1.trans h_ord2).trans h_ord3)) (congrArg circleStdCoord.angle h)
      · simp only [onOpenArc, min_eq_left (h_ord2.trans h_ord3).le,
          max_eq_right (h_ord2.trans h_ord3).le]
        exact iff_of_true ⟨h_ord2, h_ord3⟩ (fun hd => not_lt_of_ge hd.1.le h_ord1)
  have hcross_bd : CrossesOn (bd ClosedUnitDisc) (γD 0) (γD 1) (δD 0) (δD 1) := by
    rw [← ha_eq, ← hc_eq, ← hb_eq, ← hd_eq, crossesOn_oArcMap_iff φ,
      crossesOn_univ_iff_circleStdCoord]
    exact hcross_circle
  have hmeet := disc_crossing (univ : Set ClosedUnitDisc) (range γD) (range δD)
    (γD 0) (γD 1) (δD 0) (δD 1)
    ⟨Homeomorph.Set.univ ClosedUnitDisc |>.symm⟩
    (subset_univ _) (subset_univ _)
    (isCompact_range γD.continuous) (isCompact_range δD.continuous)
    (isConnected_range γD.continuous) (isConnected_range δD.continuous)
    ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩
    (by
      have hbd : discBd (univ : Set ClosedUnitDisc) = bd ClosedUnitDisc := by
        simpa [discBd, Homeomorph.Set.univ] using
          image_bd_homeomorph (Homeomorph.Set.univ ClosedUnitDisc)
      rw [hbd]; exact hcross_bd)
  rcases hmeet with ⟨w, ⟨t₁, rfl⟩, ⟨t₂, ht₂⟩⟩
  have hΨ_eq : stripToComplex M (δ t₂) = stripToComplex M (γ t₁) :=
    complexPlane.injective (congrArg Subtype.val ht₂)
  have h_eq := injOn_stripToComplex hM_pos ⟨hδ_r t₂, hδ_y t₂⟩ ⟨hγ_r t₁, hγ_y t₁⟩ hΨ_eq
  exact ⟨t₁, t₂, h_eq.symm⟩

/-! ## 2. Integrality and Lifted Paths for Linkages and Helices -/

/-- For a helix $f$ in $G$, $\beta_0 = \operatorname{cylinderAngleLift} f\ 0$ has the form
$\frac{2m_0 + 1}{k}\pi$ for some $m_0 \in \mathbb{Z}$, and
$k \cdot \operatorname{windingNumber}(f)$ is an integer. -/
theorem helix_angle_and_winding_int {k : ℕ} {G : Drawing ClosedCylinder}
    {f : Curve ClosedCylinder} (hk : 0 < k) (hf : IsHelix k G f) :
    ∃ m₀ m₁ : ℤ,
      cylinderAngleLift f 0 = ((2 * m₀ + 1 : ℤ) : ℝ) * π / (k : ℝ) ∧
      cylinderAngleLift f 1 = ((2 * m₁ + 1 : ℤ) : ℝ) * π / (k : ℝ) ∧
      (k : ℝ) * windingNumber f = ((m₁ - m₀ : ℤ) : ℝ) := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
  rcases hf.2.1 with ⟨j₀, hj₀⟩
  rcases hf.2.2.1 with ⟨j₁, hj₁⟩
  have hexp0 : Circle.exp (cylinderAngleLift f 0) =
      Circle.exp ((2 * ((j₀.1 + 1 : ℕ) : ℝ) + 1) * π / k) := by
    rw [exp_cylinderAngleLift, ← hj₀]
    rfl
  have hexp1 : Circle.exp (cylinderAngleLift f 1) =
      Circle.exp ((2 * ((j₁.1 + 1 : ℕ) : ℝ) + 1) * π / k) := by
    rw [exp_cylinderAngleLift, ← hj₁]
    rfl
  obtain ⟨n₀, hn₀⟩ := Circle.exp_eq_exp.mp hexp0
  obtain ⟨n₁, hn₁⟩ := Circle.exp_eq_exp.mp hexp1
  let m₀ : ℤ := (j₀.1 + 1 : ℤ) + n₀ * (k : ℤ)
  let m₁ : ℤ := (j₁.1 + 1 : ℤ) + n₁ * (k : ℤ)
  have hm₀ : cylinderAngleLift f 0 = ((2 * m₀ + 1 : ℤ) : ℝ) * π / (k : ℝ) := by
    rw [hn₀]
    dsimp [m₀]
    push_cast
    field_simp [hk_ne]
    ring
  have hm₁ : cylinderAngleLift f 1 = ((2 * m₁ + 1 : ℤ) : ℝ) * π / (k : ℝ) := by
    rw [hn₁]
    dsimp [m₁]
    push_cast
    field_simp [hk_ne]
    ring
  refine ⟨m₀, m₁, hm₀, hm₁, ?_⟩
  unfold windingNumber
  rw [hm₀, hm₁]
  push_cast
  field_simp [hk_ne, h2pi_ne]
  ring

/-- If $\theta$ is feasible in $G$ (for $k > 0$), then $k \theta$ is an integer. -/
theorem linkage_winding_int {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (hk : 0 < k) (hFeas : IsThetaFeasible k G θ) :
    ∃ a : ℤ, (k : ℝ) * θ = (a : ℝ) := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
  rcases hFeas with ⟨L, hLθ⟩
  let i₀ : Fin k := ⟨0, hk⟩
  let g₀ := L.curve i₀
  have hg₀_0 : g₀ 0 = cylinderM1Point k i₀ := (L.curve_parametrizes i₀).2.2.1
  rcases L.curve_one_mem i₀ with ⟨j₁, hj₁⟩
  have hexp0 : Circle.exp (cylinderAngleLift g₀ 0) =
      Circle.exp (2 * ((i₀.1 + 1 : ℕ) : ℝ) * π / k) := by
    rw [exp_cylinderAngleLift, hg₀_0]
    rfl
  have hexp1 : Circle.exp (cylinderAngleLift g₀ 1) =
      Circle.exp (2 * ((j₁.1 + 1 : ℕ) : ℝ) * π / k) := by
    rw [exp_cylinderAngleLift, ← hj₁]
    rfl
  obtain ⟨n₀, hn₀⟩ := Circle.exp_eq_exp.mp hexp0
  obtain ⟨n₁, hn₁⟩ := Circle.exp_eq_exp.mp hexp1
  let a₀ : ℤ := (i₀.1 + 1 : ℤ) + n₀ * (k : ℤ)
  let a₁ : ℤ := (j₁.1 + 1 : ℤ) + n₁ * (k : ℤ)
  refine ⟨a₁ - a₀, ?_⟩
  rw [← hLθ i₀]
  unfold windingNumber
  rw [hn₀, hn₁]
  dsimp [a₀, a₁]
  push_cast
  field_simp [hk_ne, h2pi_ne]

/-- For $k > 0$ and any integer $m \in \mathbb{Z}$, the residue index
`modIdx k hk m : Fin k` such that $m \equiv \text{modIdx} + 1 \pmod{k}$. -/
def modIdx (k : ℕ) (hk : 0 < k) (m : ℤ) : Fin k :=
  ⟨((m - 1) % (k : ℤ)).toNat, by
    have hkZ : (0 : ℤ) < (k : ℤ) := Int.natCast_pos.mpr hk
    have h_nonneg : 0 ≤ (m - 1) % (k : ℤ) := Int.emod_nonneg (m - 1) (ne_of_gt hkZ)
    have h_lt : (m - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos (m - 1) hkZ
    omega⟩

/-- The integer residue used by the lifted linkage index. This lets
other modules use the residue without unfolding the index definition. -/
theorem modIdx_val (k : ℕ) (hk : 0 < k) (m : ℤ) :
    (modIdx k hk m).val = ((m - 1) % (k : ℤ)).toNat := by
  simp only [modIdx]

/-- Adding a full angular period preserves the path index. -/
theorem modIdx_add_mul {k : ℕ} (hk : 0 < k) (m q : ℤ) :
    modIdx k hk (m + (k : ℤ) * q) = modIdx k hk m := by
  ext
  dsimp [modIdx]
  rw [show m + (k : ℤ) * q - 1 = (m - 1) + (k : ℤ) * q by ring,
    Int.add_mul_emod_self_left]

theorem exp_two_mul_int_div_eq_cylinderM1Point {k : ℕ} (hk : 0 < k) (m : ℤ) :
    Circle.exp (2 * (m : ℝ) * π / (k : ℝ)) =
      (cylinderM1Point k (modIdx k hk m)).1.2 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hkZ : (0 : ℤ) < (k : ℤ) := Int.natCast_pos.mpr hk
  have h_nonneg : 0 ≤ (m - 1) % (k : ℤ) := Int.emod_nonneg (m - 1) (ne_of_gt hkZ)
  let j := modIdx k hk m
  have hj_eq : ((j.1 : ℕ) : ℤ) = (m - 1) % (k : ℤ) := Int.toNat_of_nonneg h_nonneg
  let q : ℤ := (m - 1) / (k : ℤ)
  have hdiv : m - 1 = (k : ℤ) * q + ((j.1 : ℕ) : ℤ) := by
    dsimp [q]
    rw [hj_eq, add_comm]
    exact (Int.emod_add_mul_ediv (m - 1) (k : ℤ)).symm
  have hm_eq : (m : ℝ) = (k : ℝ) * (q : ℝ) + ((j.1 + 1 : ℕ) : ℝ) := by
    have h1 : m = (k : ℤ) * q + ((j.1 : ℕ) : ℤ) + 1 := by omega
    conv_lhs => rw [h1]
    push_cast
    ring
  change Circle.exp (2 * (m : ℝ) * π / (k : ℝ)) =
    Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / (k : ℝ))
  refine Circle.exp_eq_exp.mpr ⟨q, ?_⟩
  rw [hm_eq]
  field_simp [hk_ne]
  ring

/-- For a linkage $L$ with `L.HasTheta θ` and an integer $m \in \mathbb{Z}$, the lifted path
$\Gamma_m \colon [0, 1] \to \mathbb{R} \times \mathbb{R}$ in the universal cover strip starting at
$(1, 2m\pi/k)$ and ending at $(2, 2m\pi/k + 2\pi\theta)$. -/
noncomputable def liftedLinkageCurve {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) : C(unitInterval, ℝ × ℝ) :=
  let i := modIdx k hk m
  let g := L.curve i
  ⟨fun t =>
    ((g t).1.1,
      cylinderAngleLift g t + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0)),
    Continuous.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp g.continuous))
      ((cylinderAngleLift g).continuous.add continuous_const)⟩

/-- The first coordinate of a lifted linkage curve is the radial
coordinate of the original curve. -/
theorem liftedLinkageCurve_fst {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) (t : unitInterval) :
    (liftedLinkageCurve hk L m t).1 = (L.curve (modIdx k hk m) t).1.1 := by
  rw [liftedLinkageCurve]
  rfl

/-- Increasing the index by one full period translates the lifted
curve by that many angular periods. -/
theorem liftedLinkageCurve_add_mul {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (m q : ℤ) (t : unitInterval) :
    liftedLinkageCurve hk L (m + (k : ℤ) * q) t =
      ((liftedLinkageCurve hk L m t).1,
        (liftedLinkageCurve hk L m t).2 + (q : ℝ) * (2 * π)) := by
  simp only [liftedLinkageCurve, modIdx_add_mul]
  apply Prod.ext
  · rfl
  change cylinderAngleLift (L.curve (modIdx k hk m)) t +
      (2 * ((m + (k : ℤ) * q : ℤ) : ℝ) * π / (k : ℝ) -
        cylinderAngleLift (L.curve (modIdx k hk m)) 0) =
    cylinderAngleLift (L.curve (modIdx k hk m)) t +
      (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve (modIdx k hk m)) 0) +
        (q : ℝ) * (2 * π)
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hk)]
  ring

theorem liftedLinkageCurve_props {k : ℕ} {G : Drawing ClosedCylinder}
    {θ : ℝ} (hk : 0 < k) (L : CylinderLinkage k G) (hLθ : L.HasTheta θ) (m : ℤ) :
    let i := modIdx k hk m
    let g := L.curve i
    let Γ := liftedLinkageCurve hk L m
    (∀ t : unitInterval, (Γ t).1 ∈ Icc (1 : ℝ) 2) ∧
    (Γ 0).1 = 1 ∧ (Γ 1).1 = 2 ∧
    (Γ 0).2 = 2 * (m : ℝ) * π / (k : ℝ) ∧
    (Γ 1).2 = 2 * (m : ℝ) * π / (k : ℝ) + 2 * π * θ ∧
    (∀ t : unitInterval, Circle.exp (Γ t).2 = (g t).1.2) := by
  intro i g Γ
  refine ⟨fun t => (g t).2.1, ?_, ?_, ?_, ?_, ?_⟩
  · have hg0 : g 0 = cylinderM1Point k i := (L.curve_parametrizes i).2.2.1
    change (g 0).1.1 = 1
    rw [hg0]; rfl
  · rcases L.curve_one_mem i with ⟨j, hj⟩
    change (g 1).1.1 = 2
    rw [← hj]; rfl
  · change cylinderAngleLift g 0 + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0) = _
    ring
  · change cylinderAngleLift g 1 + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0) = _
    have hw : windingNumber g = θ := hLθ i
    unfold windingNumber at hw
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
    have hdiff : cylinderAngleLift g 1 - cylinderAngleLift g 0 = 2 * π * θ := by
      calc cylinderAngleLift g 1 - cylinderAngleLift g 0
        _ = ((cylinderAngleLift g 1 - cylinderAngleLift g 0) / (2 * π)) * (2 * π) :=
            (div_mul_cancel₀ _ h2pi_ne).symm
        _ = 2 * π * θ := by rw [hw]; ring
    linarith
  · intro t
    change Circle.exp (cylinderAngleLift g t + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0)) = (g t).1.2
    rw [Circle.exp_add, Circle.exp_sub, exp_cylinderAngleLift, exp_cylinderAngleLift,
      exp_two_mul_int_div_eq_cylinderM1Point hk m]
    have hg0 : g 0 = cylinderM1Point k i := (L.curve_parametrizes i).2.2.1
    rw [hg0]
    change (g t).1.2 * ((cylinderM1Point k i).1.2 / (cylinderM1Point k i).1.2) = (g t).1.2
    rw [div_self', mul_one]

/-- Key intersection and injectivity lemma for `(5.2)`:
Each integer $m \in \mathbb{Z}$ whose lifted linkage curve $\Gamma_m$ swaps vertical order with the
lifted helix $\tilde{f}$ produces a vertex hit $t_f(m) \in \operatorname{curveVertexHits} G f$, and
distinct integers $m_1 \ne m_2$ produce distinct parameter values $t_f(m_1) \ne t_f(m_2)$. -/
theorem exists_hit_of_lifted_swap {k : ℕ} {G : Drawing ClosedCylinder}
    {θ : ℝ} {f : Curve ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (hLθ : L.HasTheta θ) (hf : IsHelix k G f)
    (m : ℤ)
    (hswap :
      (2 * (m : ℝ) * π / (k : ℝ) < cylinderAngleLift f 0 ∧
        cylinderAngleLift f 1 < 2 * (m : ℝ) * π / (k : ℝ) + 2 * π * θ) ∨
      (cylinderAngleLift f 0 < 2 * (m : ℝ) * π / (k : ℝ) ∧
        2 * (m : ℝ) * π / (k : ℝ) + 2 * π * θ < cylinderAngleLift f 1)) :
    ∃ t_f ∈ curveVertexHits G f, ∃ t_g : unitInterval,
      liftedLinkageCurve hk L m t_g = ((f t_f).1.1, cylinderAngleLift f t_f) := by
  let F_lift : C(unitInterval, ℝ × ℝ) :=
    ⟨fun t => ((f t).1.1, cylinderAngleLift f t),
      Continuous.prodMk
        (continuous_fst.comp (continuous_subtype_val.comp f.continuous))
        (cylinderAngleLift f).continuous⟩
  have hF0 : (F_lift 0).1 = 1 := by
    rcases hf.2.1 with ⟨j₀, hj₀⟩
    change (f 0).1.1 = 1
    rw [← hj₀]; rfl
  have hF1 : (F_lift 1).1 = 2 := by
    rcases hf.2.2.1 with ⟨j₁, hj₁⟩
    change (f 1).1.1 = 2
    rw [← hj₁]; rfl
  obtain ⟨hΓ_r, hΓ0_r, hΓ1_r, hΓ0_y, hΓ1_y, hΓ_exp⟩ :=
    liftedLinkageCurve_props hk L hLθ m
  have hswap' :
      ((liftedLinkageCurve hk L m 0).2 < (F_lift 0).2 ∧
        (F_lift 1).2 < (liftedLinkageCurve hk L m 1).2) ∨
      ((F_lift 0).2 < (liftedLinkageCurve hk L m 0).2 ∧
        (liftedLinkageCurve hk L m 1).2 < (F_lift 1).2) := by
    change ((liftedLinkageCurve hk L m 0).2 < cylinderAngleLift f 0 ∧
        cylinderAngleLift f 1 < (liftedLinkageCurve hk L m 1).2) ∨
      (cylinderAngleLift f 0 < (liftedLinkageCurve hk L m 0).2 ∧
        (liftedLinkageCurve hk L m 1).2 < cylinderAngleLift f 1)
    rw [hΓ0_y, hΓ1_y]
    exact hswap
  let Γ := liftedLinkageCurve hk L m
  have hF_r : ∀ t : unitInterval, (F_lift t).1 ∈ Icc (1 : ℝ) 2 := fun t => (f t).2.1
  obtain ⟨t_g, t_f, h_eq⟩ :=
    strip_crossing Γ F_lift hΓ_r hF_r hΓ0_r hΓ1_r hF0 hF1 hswap'
  refine ⟨t_f, ?_, t_g, h_eq⟩
  let i := modIdx k hk m
  let g := L.curve i
  have h_r_eq : (g t_g).1.1 = (f t_f).1.1 := congrArg (Prod.fst : ℝ × ℝ → ℝ) h_eq
  have h_y_eq : (Γ t_g).2 = cylinderAngleLift f t_f := congrArg (Prod.snd : ℝ × ℝ → ℝ) h_eq
  have h_u_eq : (g t_g).1.2 = (f t_f).1.2 := by
    calc (g t_g).1.2
      _ = Circle.exp (Γ t_g).2 := (hΓ_exp t_g).symm
      _ = Circle.exp (cylinderAngleLift f t_f) := by rw [h_y_eq]
      _ = (f t_f).1.2 := exp_cylinderAngleLift f t_f
  have hg_eq_f : g t_g = f t_f := by
    apply Subtype.ext
    exact Prod.ext h_r_eq h_u_eq
  have hg_mem_U : g t_g ∈ G.U := by
    apply (L.isSubdrawing i).2
    rw [← (L.curve_parametrizes i).2.1]
    exact ⟨t_g, rfl⟩
  have hf_mem_U : f t_f ∈ range f ∩ G.U := ⟨⟨t_f, rfl⟩, hg_eq_f ▸ hg_mem_U⟩
  exact hf.1 hf_mem_U

/-- Distinct integers $m_1, m_2 \in \mathbb{Z}$ cannot share the same helix parameter $t_f$ in
`exists_hit_of_lifted_swap`. -/
theorem eq_of_liftedLinkageCurve_eq_helix {k : ℕ} {G : Drawing ClosedCylinder}
    {θ : ℝ} {f : Curve ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (hLθ : L.HasTheta θ)
    {m₁ m₂ : ℤ} {t₁ t₂ t_f : unitInterval}
    (h₁ : liftedLinkageCurve hk L m₁ t₁ = ((f t_f).1.1, cylinderAngleLift f t_f))
    (h₂ : liftedLinkageCurve hk L m₂ t₂ = ((f t_f).1.1, cylinderAngleLift f t_f)) :
    m₁ = m₂ := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
  obtain ⟨_, _, _, _, _, hΓ₁_exp⟩ := liftedLinkageCurve_props hk L hLθ m₁
  obtain ⟨_, _, _, _, _, hΓ₂_exp⟩ := liftedLinkageCurve_props hk L hLθ m₂
  let i₁ := modIdx k hk m₁
  let i₂ := modIdx k hk m₂
  have h₁_fst : (L.curve i₁ t₁).1.1 = (f t_f).1.1 := congrArg (Prod.fst : ℝ × ℝ → ℝ) h₁
  have h₂_fst : (L.curve i₂ t₂).1.1 = (f t_f).1.1 := congrArg (Prod.fst : ℝ × ℝ → ℝ) h₂
  have hg₁_eq : L.curve i₁ t₁ = f t_f := by
    apply Subtype.ext
    refine Prod.ext h₁_fst ?_
    calc (L.curve i₁ t₁).1.2
      _ = Circle.exp (liftedLinkageCurve hk L m₁ t₁).2 := (hΓ₁_exp t₁).symm
      _ = Circle.exp (cylinderAngleLift f t_f) := by rw [congrArg Prod.snd h₁]
      _ = (f t_f).1.2 := exp_cylinderAngleLift f t_f
  have hg₂_eq : L.curve i₂ t₂ = f t_f := by
    apply Subtype.ext
    refine Prod.ext h₂_fst ?_
    calc (L.curve i₂ t₂).1.2
      _ = Circle.exp (liftedLinkageCurve hk L m₂ t₂).2 := (hΓ₂_exp t₂).symm
      _ = Circle.exp (cylinderAngleLift f t_f) := by rw [congrArg Prod.snd h₂]
      _ = (f t_f).1.2 := exp_cylinderAngleLift f t_f
  have hi_eq : i₁ = i₂ := by
    by_contra hne
    have hdisj := L.pairwise_disjoint hne
    have hmem₁ : f t_f ∈ (L.pathDrawing i₁).U := by
      rw [← (L.curve_parametrizes i₁).2.1]
      exact ⟨t₁, hg₁_eq⟩
    have hmem₂ : f t_f ∈ (L.pathDrawing i₂).U := by
      rw [← (L.curve_parametrizes i₂).2.1]
      exact ⟨t₂, hg₂_eq⟩
    exact Set.disjoint_left.mp hdisj hmem₁ hmem₂
  have ht_eq : t₁ = t₂ := by
    apply (L.curve_parametrizes i₁).1
    calc L.curve i₁ t₁
      _ = f t_f := hg₁_eq
      _ = L.curve i₂ t₂ := hg₂_eq.symm
      _ = L.curve i₁ t₂ := by rw [hi_eq]
  have hy_eq : (liftedLinkageCurve hk L m₁ t₁).2 = (liftedLinkageCurve hk L m₂ t₂).2 :=
    (congrArg Prod.snd h₁).trans (congrArg Prod.snd h₂).symm
  change cylinderAngleLift (L.curve i₁) t₁ +
      (2 * (m₁ : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve i₁) 0) =
    cylinderAngleLift (L.curve i₂) t₂ +
      (2 * (m₂ : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve i₂) 0) at hy_eq
  rw [← hi_eq, ← ht_eq] at hy_eq
  have hm_div : 2 * (m₁ : ℝ) * π / (k : ℝ) = 2 * (m₂ : ℝ) * π / (k : ℝ) := by linarith
  have hm_real : (m₁ : ℝ) = (m₂ : ℝ) := by
    have hmul : (2 * (m₁ : ℝ) * π / (k : ℝ)) * (k : ℝ) =
        (2 * (m₂ : ℝ) * π / (k : ℝ)) * (k : ℝ) := by rw [hm_div]
    rw [div_mul_cancel₀ _ hk_ne, div_mul_cancel₀ _ hk_ne] at hmul
    nlinarith [Real.pi_pos]
  exact Int.cast_injective hm_real

/-! ## 3. Proof of Graph Minors VI, (5.2) -/

/-- **Graph Minors VI, (5.2)** (page 130):
"Let $\theta$ be feasible in $G$, and let $f$ be a helix. Then $L(f) \ge k|\theta(f) -
\theta|$, that is,* $$\theta(f) - k^{-1}L(f) \le \theta \le \theta(f) + k^{-1}L(f).$$"

Proved by lifting $f$ and the linkage paths to the universal cover $[1, 2] \times \mathbb{R}$,
applying `strip_crossing` (`disc_crossing`) to obtain a distinct vertex hit for each integer $m$
between $m_0$ and $m_0 + k(\theta(f) - \theta)$, and injecting into `curveVertexHits G f`. -/
theorem theorem_5_2_proof : Statement52 := by
  intro k G θ f hG hFeas hf
  have hk : 0 < k := hG.1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  obtain ⟨m₀, m₁, hm₀, hm₁, hwf⟩ := helix_angle_and_winding_int hk hf
  obtain ⟨a, ha⟩ := linkage_winding_int hk hFeas
  rcases hFeas with ⟨L, hLθ⟩
  let D : ℤ := (m₁ - m₀) - a
  have hD_real : (k : ℝ) * (windingNumber f - θ) = (D : ℝ) := by
    calc (k : ℝ) * (windingNumber f - θ)
      _ = (k : ℝ) * windingNumber f - (k : ℝ) * θ := mul_sub _ _ _
      _ = ((m₁ - m₀ : ℤ) : ℝ) - (a : ℝ) := by rw [hwf, ha]
      _ = (D : ℝ) := by dsimp [D]; push_cast; ring
  let lo : ℤ := min m₀ (m₀ + D) + 1
  let hi : ℤ := max m₀ (m₀ + D)
  let S : Finset ℤ := Finset.Icc lo hi
  have hS_swap : ∀ m ∈ S,
      (2 * (m : ℝ) * π / (k : ℝ) < cylinderAngleLift f 0 ∧
        cylinderAngleLift f 1 < 2 * (m : ℝ) * π / (k : ℝ) + 2 * π * θ) ∨
      (cylinderAngleLift f 0 < 2 * (m : ℝ) * π / (k : ℝ) ∧
        2 * (m : ℝ) * π / (k : ℝ) + 2 * π * θ < cylinderAngleLift f 1) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hθ_eq : θ = (a : ℝ) / (k : ℝ) := by
      rw [← ha, mul_div_cancel_left₀ _ hk_ne]
    have h_start : 2 * (m : ℝ) * π / (k : ℝ) = ((2 * m : ℤ) : ℝ) * π / (k : ℝ) := by
      push_cast; rfl
    have h_end : 2 * (m : ℝ) * π / (k : ℝ) + 2 * π * θ =
        ((2 * (m + a) : ℤ) : ℝ) * π / (k : ℝ) := by
      rw [hθ_eq]
      push_cast
      field_simp [hk_ne]
    rw [hm₀, hm₁, h_end, h_start]
    have hpi_div_pos : (0 : ℝ) < π / (k : ℝ) := div_pos Real.pi_pos hk_pos
    have h_lt_iff : ∀ x y : ℤ,
        (x : ℝ) * π / (k : ℝ) < (y : ℝ) * π / (k : ℝ) ↔ x < y := by
      intro x y
      rw [mul_div_assoc, mul_div_assoc, mul_lt_mul_iff_left₀ hpi_div_pos, Int.cast_lt]
    by_cases hD_nonneg : 0 ≤ D
    · right
      have hlo : lo = m₀ + 1 := by
        dsimp [lo]; rw [min_eq_left (by omega)]
      have hhi : hi = m₀ + D := by
        dsimp [hi]; rw [max_eq_right (by omega)]
      have hm1 : m₀ + 1 ≤ m := hlo ▸ hm.1
      have hm2 : m ≤ m₀ + D := hhi ▸ hm.2
      refine ⟨?_, ?_⟩
      · exact (h_lt_iff (2 * m₀ + 1) (2 * m)).mpr (by omega)
      · exact (h_lt_iff (2 * (m + a)) (2 * m₁ + 1)).mpr (by omega)
    · left
      have hlo : lo = m₀ + D + 1 := by
        dsimp [lo]; rw [min_eq_right (by omega)]
      have hhi : hi = m₀ := by
        dsimp [hi]; rw [max_eq_left (by omega)]
      have hm1 : m₀ + D + 1 ≤ m := hlo ▸ hm.1
      have hm2 : m ≤ m₀ := hhi ▸ hm.2
      refine ⟨?_, ?_⟩
      · exact (h_lt_iff (2 * m) (2 * m₀ + 1)).mpr (by omega)
      · exact (h_lt_iff (2 * m₁ + 1) (2 * (m + a))).mpr (by omega)
  let hitMap : S → unitInterval := fun m =>
    Classical.choose (exists_hit_of_lifted_swap hk L hLθ hf m.1 (hS_swap m.1 m.2))
  have hhit_mem : ∀ m : S, hitMap m ∈ hf.2.2.2.toFinset := by
    intro m
    rw [Set.Finite.mem_toFinset]
    exact (Classical.choose_spec (exists_hit_of_lifted_swap hk L hLθ hf m.1 (hS_swap m.1 m.2))).1
  have hhit_inj : Function.Injective hitMap := by
    intro m₁ m₂ heq
    apply Subtype.ext
    obtain ⟨t₁, ht₁⟩ :=
      (Classical.choose_spec (exists_hit_of_lifted_swap hk L hLθ hf m₁.1 (hS_swap m₁.1 m₁.2))).2
    obtain ⟨t₂, ht₂⟩ :=
      (Classical.choose_spec (exists_hit_of_lifted_swap hk L hLθ hf m₂.1 (hS_swap m₂.1 m₂.2))).2
    change liftedLinkageCurve hk L m₁.1 t₁ =
      ((f (hitMap m₁)).1.1, cylinderAngleLift f (hitMap m₁)) at ht₁
    change liftedLinkageCurve hk L m₂.1 t₂ =
      ((f (hitMap m₂)).1.1, cylinderAngleLift f (hitMap m₂)) at ht₂
    rw [heq] at ht₁
    exact eq_of_liftedLinkageCurve_eq_helix hk L hLθ ht₁ ht₂
  let hitEmb : S → hf.2.2.2.toFinset := fun m => ⟨hitMap m, hhit_mem m⟩
  have hhitEmb_inj : Function.Injective hitEmb := by
    intro m₁ m₂ heq
    exact hhit_inj (congrArg Subtype.val heq)
  have hcard_le : S.card ≤ hf.2.2.2.toFinset.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective hitEmb hhitEmb_inj
  have hS_card : S.card = D.natAbs := by
    dsimp [S, lo, hi]
    rw [Int.card_Icc]
    omega
  have htoFinset_card : hf.2.2.2.toFinset.card = curveL G f := by
    unfold curveL
    exact (Set.ncard_eq_toFinset_card (curveVertexHits G f) hf.2.2.2).symm
  have hnat_le : D.natAbs ≤ curveL G f := by
    omega
  have hreal_le : |(D : ℝ)| ≤ (curveL G f : ℝ) := by
    have h1 : (D.natAbs : ℝ) ≤ (curveL G f : ℝ) := Nat.cast_le.mpr hnat_le
    have h2 : |(D : ℝ)| = (D.natAbs : ℝ) := by
      rw [← Int.cast_abs, Nat.cast_natAbs]
    linarith
  rw [← hD_real, abs_mul, abs_of_pos hk_pos] at hreal_le
  have h_abs_diff : |windingNumber f - θ| ≤ (k : ℝ)⁻¹ * (curveL G f : ℝ) := by
    calc |windingNumber f - θ|
      _ = (k : ℝ)⁻¹ * ((k : ℝ) * |windingNumber f - θ|) := by
          rw [← mul_assoc, inv_mul_cancel₀ hk_ne, one_mul]
      _ ≤ (k : ℝ)⁻¹ * (curveL G f : ℝ) :=
          mul_le_mul_of_nonneg_left hreal_le (inv_nonneg.mpr hk_pos.le)
  rw [abs_le] at h_abs_diff
  exact ⟨by linarith [h_abs_diff.2], by linarith [h_abs_diff.1]⟩

/-- **Graph Minors VI, (5.4)** for Reductions 1, 2, and 4 (pages 130–131):
If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by Reduction 1, 2, or 4, and
$\theta(\mathcal{L}') + 1/k$ is feasible in $G'$, then $\theta(\mathcal{L}) + 1/k$ is feasible in
$G$. -/
theorem theorem_5_4_red124 (k : ℕ) (G G' : Drawing ClosedCylinder)
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G') (θ θ' : ℝ)
    (hG : IsCylinderSection5Drawing k G)
    (hL : L.HasTheta θ) (hL' : L'.HasTheta θ')
    (hRed : Section5Reduction1Step k G L G' L' ∨
      Section5Reduction2Step k G L G' L' ∨
      Section5Reduction4Step k G L G' L')
    (hFeas' : IsThetaFeasible k G' (θ' + 1 / (k : ℝ))) :
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
  have hk : 0 < k := hG.1
  let i₀ : Fin k := ⟨0, hk⟩
  have hθ_eq : θ' = θ := by
    rcases hRed with h1 | h2 | h4
    · rcases h1 with ⟨_, _, _, _, _, _, _, _, hcurve⟩
      rw [← hL' i₀, ← hL i₀, hcurve]
    · rcases h2 with ⟨_, _, _, _, _, _, _, _, hcurve⟩
      rw [← hL' i₀, ← hL i₀, hcurve]
    · exact theta_eq_of_reduction4 L L' hL hL' h4
  have hSub : G'.IsSubdrawing G ∧ G'.U ⊆ G.U := by
    rcases hRed with h1 | h2 | h4
    · rcases h1 with ⟨_, e, _, _, hV, hE, hU, _, _⟩
      refine ⟨⟨by rw [hV], by rw [hE]; exact Set.sdiff_subset⟩, by rw [hU]; exact Set.sdiff_subset⟩
    · rcases h2 with ⟨_, G₂, hSep, hU, _, _, _, _, _⟩
      have hV_sub : G'.V ⊆ G.V := Set.subset_union_left.trans hSep.2.2.1.subset
      have hE_sub : G'.E ⊆ G.E := Set.subset_union_left.trans hSep.2.2.2.1.subset
      exact ⟨⟨hV_sub, hE_sub⟩, hU⟩
    · rcases h4 with ⟨rfl, _⟩
      exact ⟨⟨Subset.rfl, Subset.rfl⟩, Subset.rfl⟩
  rw [hθ_eq] at hFeas'
  rcases hFeas' with ⟨M, hM⟩
  refine ⟨{
    pathDrawing := M.pathDrawing
    curve := M.curve
    isSubdrawing := fun i => ⟨
      ⟨(M.isSubdrawing i).1.1.trans hSub.1.1, (M.isSubdrawing i).1.2.trans hSub.1.2⟩,
      (M.isSubdrawing i).2.trans hSub.2⟩
    isPath := M.isPath
    curve_parametrizes := M.curve_parametrizes
    curve_one_mem := M.curve_one_mem
    pairwise_disjoint := M.pairwise_disjoint
  }, hM⟩

/-- **Graph Minors VI, (5.8) ((i) $\Rightarrow$ (iii) and (i) $\Rightarrow$ (ii))** (page 133):
If there is a helix $f$ in $G$ with $\phi_G(f) = \theta$, then no $\theta' > \theta$ is feasible in
$G$ (and in particular $\theta + 1/k$ is not feasible in $G$). -/
theorem theorem_5_8_of_helix (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ)
    (hG : IsCylinderSection5Drawing k G)
    (hHelix : ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ) :
    (∀ θ' : ℝ, θ < θ' → ¬ IsThetaFeasible k G θ') ∧
      ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
  rcases hHelix with ⟨f, hf, hphi⟩
  have hno : ∀ θ' : ℝ, θ < θ' → ¬ IsThetaFeasible k G θ' := by
    intro θ' hlt hFeas'
    have hle := (theorem_5_2_proof k G θ' f hG hFeas' hf).2
    unfold curvePhi at hphi
    linarith
  refine ⟨hno, ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hG.1
  have h1k_pos : 0 < 1 / (k : ℝ) := div_pos one_pos hk_pos
  exact hno (θ + 1 / (k : ℝ)) (by linarith)

/-- **Graph Minors VI, (5.10) (necessity direction)** (page 134):
If $\theta$ is feasible in $G$, then (i) $k\theta$ is an integer, (ii) there is some linkage in $G$,
and (iii) for every helix $f$, $\theta(f) - k^{-1} L(f) \le \theta \le \theta(f) + k^{-1} L(f)$. -/
theorem theorem_5_10_mp (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ)
    (hG : IsCylinderSection5Drawing k G) (hFeas : IsThetaFeasible k G θ) :
    (∃ m : ℤ, (k : ℝ) * θ = m) ∧
    Nonempty (CylinderLinkage k G) ∧
    ∀ f : Curve ClosedCylinder, IsHelix k G f →
      windingNumber f - (k : ℝ)⁻¹ * (curveL G f : ℝ) ≤ θ ∧
        θ ≤ windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ) := by
  refine ⟨linkage_winding_int hG.1 hFeas, ?_, fun f hf => theorem_5_2_proof k G θ f hG hFeas hf⟩
  rcases hFeas with ⟨L, _⟩
  exact ⟨L⟩

/-! ## 4. Proof of Graph Minors VI, (5.12) -/

theorem modIdx_natCast_succ {k : ℕ} (hk : 0 < k) (j : Fin k) :
    modIdx k hk ((j.1 : ℤ) + 1) = j := by
  ext
  dsimp [modIdx]
  have h1 : ((j.1 : ℤ) + 1 - 1) = (j.1 : ℤ) := by omega
  rw [h1, Int.emod_eq_of_lt (Int.natCast_nonneg j.1) (Int.ofNat_lt.mpr j.2), Int.toNat_natCast]

theorem eq_of_liftedLinkageCurve_eq {k : ℕ} {G : Drawing ClosedCylinder}
    {θ : ℝ} (hk : 0 < k) (L : CylinderLinkage k G) (hLθ : L.HasTheta θ)
    {m₁ m₂ : ℤ} {t₁ t₂ : unitInterval}
    (h : liftedLinkageCurve hk L m₁ t₁ = liftedLinkageCurve hk L m₂ t₂) :
    m₁ = m₂ := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  obtain ⟨_, _, _, _, _, hΓ₁_exp⟩ := liftedLinkageCurve_props hk L hLθ m₁
  obtain ⟨_, _, _, _, _, hΓ₂_exp⟩ := liftedLinkageCurve_props hk L hLθ m₂
  let i₁ := modIdx k hk m₁
  let i₂ := modIdx k hk m₂
  have h_fst : (L.curve i₁ t₁).1.1 = (L.curve i₂ t₂).1.1 :=
    congrArg (Prod.fst : ℝ × ℝ → ℝ) h
  have h_snd : (liftedLinkageCurve hk L m₁ t₁).2 = (liftedLinkageCurve hk L m₂ t₂).2 :=
    congrArg (Prod.snd : ℝ × ℝ → ℝ) h
  have hg_eq : L.curve i₁ t₁ = L.curve i₂ t₂ := by
    apply Subtype.ext
    refine Prod.ext h_fst ?_
    calc (L.curve i₁ t₁).1.2
      _ = Circle.exp (liftedLinkageCurve hk L m₁ t₁).2 := (hΓ₁_exp t₁).symm
      _ = Circle.exp (liftedLinkageCurve hk L m₂ t₂).2 := by rw [h_snd]
      _ = (L.curve i₂ t₂).1.2 := hΓ₂_exp t₂
  have hi_eq : i₁ = i₂ := by
    by_contra hne
    have hdisj := L.pairwise_disjoint hne
    have hmem₁ : L.curve i₁ t₁ ∈ (L.pathDrawing i₁).U := by
      rw [← (L.curve_parametrizes i₁).2.1]
      exact ⟨t₁, rfl⟩
    have hmem₂ : L.curve i₁ t₁ ∈ (L.pathDrawing i₂).U := by
      rw [← (L.curve_parametrizes i₂).2.1]
      exact ⟨t₂, hg_eq.symm⟩
    exact Set.disjoint_left.mp hdisj hmem₁ hmem₂
  have ht_eq : t₁ = t₂ := by
    apply (L.curve_parametrizes i₁).1
    rw [hg_eq, hi_eq]
  change cylinderAngleLift (L.curve i₁) t₁ +
      (2 * (m₁ : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve i₁) 0) =
    cylinderAngleLift (L.curve i₂) t₂ +
      (2 * (m₂ : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve i₂) 0) at h_snd
  rw [← hi_eq, ← ht_eq] at h_snd
  have hm_div : 2 * (m₁ : ℝ) * π / (k : ℝ) = 2 * (m₂ : ℝ) * π / (k : ℝ) := by linarith
  have hm_real : (m₁ : ℝ) = (m₂ : ℝ) := by
    have hmul : (2 * (m₁ : ℝ) * π / (k : ℝ)) * (k : ℝ) =
        (2 * (m₂ : ℝ) * π / (k : ℝ)) * (k : ℝ) := by rw [hm_div]
    rw [div_mul_cancel₀ _ hk_ne, div_mul_cancel₀ _ hk_ne] at hmul
    nlinarith [Real.pi_pos]
  exact Int.cast_injective hm_real

/-- If $t_m$ is the least parameter in $[0, 1]$ at which the lifted path $\Gamma_2$ of $P_j \in \mathcal{L}_2$
meets the lifted path $\Gamma_1(m)$ of $\mathcal{L}_1$, then $L_2.\text{curve } j\ t_m$ is a vertex
of $P_j$. -/
theorem mem_pathDrawing_V_of_isLeast_lifted_hit {k : ℕ} {G : Drawing ClosedCylinder}
    {θ₁ θ₂ : ℝ} (hk : 0 < k) (L₁ L₂ : CylinderLinkage k G)
    (hL₁ : L₁.HasTheta θ₁) (hL₂ : L₂.HasTheta θ₂) (j : Fin k) (m : ℤ)
    {t_m : unitInterval}
    (ht_m : IsLeast {t : unitInterval |
      liftedLinkageCurve hk L₂ ((j.1 : ℤ) + 1) t ∈ range (liftedLinkageCurve hk L₁ m)} t_m) :
    L₂.curve j t_m ∈ (L₂.pathDrawing j).V := by
  let m₀ : ℤ := (j.1 : ℤ) + 1
  have hm₀_idx : modIdx k hk m₀ = j := modIdx_natCast_succ hk j
  let Γ₂ := liftedLinkageCurve hk L₂ m₀
  let Γ₁ := liftedLinkageCurve hk L₁ m
  let P₂ := L₂.pathDrawing j
  let g₂ := L₂.curve j
  let i := modIdx k hk m
  let P₁ := L₁.pathDrawing i
  let g₁ := L₁.curve i
  rcases eq_or_lt_of_le (unitInterval.nonneg t_m) with h0 | ht_m_pos
  · have ht_m0 : t_m = 0 := Subtype.ext h0.symm
    rw [ht_m0]
    have hg0 : g₂ 0 = cylinderM1Point k j := (L₂.curve_parametrizes j).2.2.1
    rw [hg0]
    rcases (L₂.isPath j).1 with ⟨W, _, hPV, _⟩
    rw [hPV]
    exact W.start_mem_support
  · by_contra hnotV
    have hg₂_mem_U : ∀ t : unitInterval, g₂ t ∈ P₂.U := by
      intro t
      rw [← (L₂.curve_parametrizes j).2.1]
      exact ⟨t, rfl⟩
    obtain ⟨e, he, hxe⟩ := P₂.exists_edge_of_mem (hg₂_mem_U t_m) hnotV
    have he_G : e ∈ G.E := (L₂.isSubdrawing j).1.2 he
    have hx_not_GV : g₂ t_m ∉ G.V := (he_G.2.1 hxe).2
    rcases ht_m.1 with ⟨s_m, hs_m⟩
    obtain ⟨_, _, _, _, _, hΓ₁_exp⟩ := liftedLinkageCurve_props hk L₁ hL₁ m
    obtain ⟨_, _, _, _, _, hΓ₂_exp⟩ := liftedLinkageCurve_props hk L₂ hL₂ m₀
    have hΓ₂_exp' : ∀ t : unitInterval, Circle.exp (Γ₂ t).2 = (g₂ t).1.2 := by
      intro t
      simpa [g₂, hm₀_idx] using hΓ₂_exp t
    have hΓ₂_fst' : ∀ t : unitInterval, (Γ₂ t).1 = (g₂ t).1.1 := by
      intro t
      change (L₂.curve (modIdx k hk m₀) t).1.1 = (g₂ t).1.1
      rw [hm₀_idx]
    have hg₁_eq_g₂ : g₁ s_m = g₂ t_m := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · calc (g₁ s_m).1.1
          _ = (Γ₁ s_m).1 := rfl
          _ = (Γ₂ t_m).1 := congrArg Prod.fst hs_m
          _ = (g₂ t_m).1.1 := hΓ₂_fst' t_m
      · calc (g₁ s_m).1.2
          _ = Circle.exp (Γ₁ s_m).2 := (hΓ₁_exp s_m).symm
          _ = Circle.exp (Γ₂ t_m).2 := by rw [congrArg Prod.snd hs_m]
          _ = (g₂ t_m).1.2 := hΓ₂_exp' t_m
    have hg₁_mem_U : g₁ s_m ∈ P₁.U := by
      rw [← (L₁.curve_parametrizes i).2.1]
      exact ⟨s_m, rfl⟩
    have hg₁_not_V : g₁ s_m ∉ P₁.V := fun hV =>
      hx_not_GV (hg₁_eq_g₂ ▸ (L₁.isSubdrawing i).1.1 hV)
    obtain ⟨e₁, he₁, hxe₁⟩ := P₁.exists_edge_of_mem hg₁_mem_U hg₁_not_V
    have he₁_G : e₁ ∈ G.E := (L₁.isSubdrawing i).1.2 he₁
    have he₁_eq_e : e₁ = e := G.edge_eq_of_mem he₁_G he_G hxe₁ (hg₁_eq_g₂.symm ▸ hxe)
    have he_sub_P₁U : e ⊆ P₁.U := he₁_eq_e ▸ (he₁.2.1.trans sdiff_subset)
    have hcl_sdiff : IsClosed (P₂.U \ e) := isClosed_U_sdiff_edge P₂ he
    let U_e : Set unitInterval := {t : unitInterval | g₂ t ∉ P₂.U \ e}
    have hUe_open : IsOpen U_e := hcl_sdiff.isOpen_compl.preimage g₂.continuous
    have ht_m_Ue : t_m ∈ U_e := fun h => h.2 hxe
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hUe_open t_m ht_m_Ue
    have ht_m_pos_real : (0 : ℝ) < (t_m : ℝ) := ht_m_pos
    let δ : ℝ := min (t_m : ℝ) (ε / 2)
    have hδ_pos : 0 < δ := lt_min ht_m_pos_real (half_pos hε_pos)
    let t' : unitInterval :=
      ⟨(t_m : ℝ) - δ,
        sub_nonneg.mpr (min_le_left _ _),
        le_trans (sub_le_self _ (le_of_lt hδ_pos)) t_m.2.2⟩
    have ht'_lt : t' < t_m := Subtype.mk_lt_mk.mpr (by linarith)
    let clamp : unitInterval → unitInterval := fun t => max t' (min t_m t)
    have hclamp_cont : Continuous clamp :=
      continuous_const.max (continuous_const.min continuous_id)
    have hclamp_mem : ∀ t : unitInterval, clamp t ∈ Icc t' t_m := by
      intro t
      dsimp [clamp]
      exact ⟨le_max_left t' (min t_m t), max_le (le_of_lt ht'_lt) (min_le_left t_m t)⟩
    have hclamp_one : clamp 1 = t_m := by
      dsimp [clamp]
      rw [min_eq_left (unitInterval.le_one' : t_m ≤ 1), max_eq_right (le_of_lt ht'_lt)]
    have hclamp_zero : clamp 0 = t' := by
      dsimp [clamp]
      rw [min_eq_right (unitInterval.nonneg' : 0 ≤ t_m), max_eq_left (unitInterval.nonneg' : 0 ≤ t')]
    have hg₂_clamp_mem_e : ∀ t : unitInterval, g₂ (clamp t) ∈ e := by
      intro t
      have h_icc := hclamp_mem t
      have h_dist : dist (clamp t) t_m < ε := by
        rw [Subtype.dist_eq, Real.dist_eq]
        have h1 : (t' : ℝ) ≤ (clamp t : ℝ) := h_icc.1
        have h2 : (clamp t : ℝ) ≤ (t_m : ℝ) := h_icc.2
        have h3 : (t' : ℝ) = (t_m : ℝ) - δ := rfl
        have h4 : δ ≤ ε / 2 := min_le_right _ _
        rw [abs_of_nonpos (by linarith)]
        linarith
      have h_not_sdiff : g₂ (clamp t) ∉ P₂.U \ e := hball h_dist
      by_contra hnot_e
      exact h_not_sdiff ⟨hg₂_mem_U (clamp t), hnot_e⟩
    have hg₂_clamp_mem_range : ∀ t : unitInterval, g₂ (clamp t) ∈ range g₁ := by
      intro t
      rw [(L₁.curve_parametrizes i).2.1]
      exact he_sub_P₁U (hg₂_clamp_mem_e t)
    let φ₁ : unitInterval ≃ₜ range g₁ :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofInjective g₁ (L₁.curve_parametrizes i).1)
        g₁.continuous.rangeFactorization
    let σ : unitInterval → unitInterval := fun t =>
      φ₁.symm ⟨g₂ (clamp t), hg₂_clamp_mem_range t⟩
    have hσ_cont : Continuous σ :=
      φ₁.symm.continuous.comp ((g₂.continuous.comp hclamp_cont).subtype_mk hg₂_clamp_mem_range)
    have hg₁_σ : ∀ t : unitInterval, g₁ (σ t) = g₂ (clamp t) := by
      intro t
      exact congrArg Subtype.val (φ₁.apply_symm_apply ⟨g₂ (clamp t), hg₂_clamp_mem_range t⟩)
    have hσ_one : σ 1 = s_m := by
      apply (L₁.curve_parametrizes i).1
      rw [hg₁_σ 1, hclamp_one, hg₁_eq_g₂]
    let α : unitInterval → ℝ := fun t => (Γ₂ (clamp t)).2
    let β : unitInterval → ℝ := fun t => (Γ₁ (σ t)).2
    have hα_cont : Continuous α := (continuous_snd.comp Γ₂.continuous).comp hclamp_cont
    have hβ_cont : Continuous β := (continuous_snd.comp Γ₁.continuous).comp hσ_cont
    have hexp_eq : Circle.exp ∘ α = Circle.exp ∘ β := by
      funext t
      change Circle.exp (Γ₂ (clamp t)).2 = Circle.exp (Γ₁ (σ t)).2
      rw [hΓ₂_exp' (clamp t), hΓ₁_exp (σ t), hg₁_σ t]
    have hαβ_one : α 1 = β 1 := by
      change (Γ₂ (clamp 1)).2 = (Γ₁ (σ 1)).2
      rw [hclamp_one, hσ_one, hs_m]
    have hαβ_eq : α = β :=
      Circle.isCoveringMap_exp.eq_of_comp_eq hα_cont hβ_cont hexp_eq 1 hαβ_one
    have h_at_zero : Γ₂ t' = Γ₁ (σ 0) := by
      apply Prod.ext
      · calc (Γ₂ t').1
          _ = (g₂ t').1.1 := hΓ₂_fst' t'
          _ = (g₂ (clamp 0)).1.1 := by rw [hclamp_zero]
          _ = (g₁ (σ 0)).1.1 := by rw [hg₁_σ 0]
          _ = (Γ₁ (σ 0)).1 := rfl
      · calc (Γ₂ t').2
          _ = α 0 := by dsimp [α]; rw [hclamp_zero]
          _ = β 0 := congr_fun hαβ_eq 0
          _ = (Γ₁ (σ 0)).2 := rfl
    have ht'_mem : t' ∈ {t : unitInterval | Γ₂ t ∈ range Γ₁} := ⟨σ 0, h_at_zero.symm⟩
    exact not_le_of_gt ht'_lt (ht_m.2 ht'_mem)

/-- **Graph Minors VI, (5.12)** (page 135):
"If $\theta_1, \theta_2$ are both feasible in $G$ then* $$|\theta_1 - \theta_2| \le
\frac{1}{k^2} |V(G)|.$$" -/
theorem theorem_5_12_proof : Statement512 := by
  classical
  intro k G θ₁ θ₂ hG hFeas₁ hFeas₂
  have hk : 0 < k := hG.1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  obtain ⟨a₁, ha₁⟩ := linkage_winding_int hk hFeas₁
  obtain ⟨a₂, ha₂⟩ := linkage_winding_int hk hFeas₂
  rcases hFeas₁ with ⟨L₁, hL₁⟩
  rcases hFeas₂ with ⟨L₂, hL₂⟩
  let D : ℤ := a₂ - a₁
  have hD_real : (k : ℝ) * (θ₂ - θ₁) = (D : ℝ) := by
    calc (k : ℝ) * (θ₂ - θ₁)
      _ = (k : ℝ) * θ₂ - (k : ℝ) * θ₁ := mul_sub _ _ _
      _ = (a₂ : ℝ) - (a₁ : ℝ) := by rw [ha₂, ha₁]
      _ = (D : ℝ) := by dsimp [D]; push_cast; ring
  have hpath_card : ∀ j : Fin k, D.natAbs ≤ (L₂.pathDrawing j).V.ncard := by
    intro j
    by_cases hD0 : D = 0
    · simp [hD0]
    · let m₀ : ℤ := (j.1 : ℤ) + 1
      have hm₀_idx : modIdx k hk m₀ = j := modIdx_natCast_succ hk j
      let Γ₂ := liftedLinkageCurve hk L₂ m₀
      let T : ℤ → Set unitInterval := fun m =>
        {t : unitInterval | Γ₂ t ∈ range (liftedLinkageCurve hk L₁ m)}
      have hT_closed : ∀ m : ℤ, IsClosed (T m) := fun m =>
        (isCompact_range (liftedLinkageCurve hk L₁ m).continuous).isClosed.preimage Γ₂.continuous
      let S : Finset ℤ :=
        if 0 < D then Finset.Icc m₀ (m₀ + D - 1) else Finset.Icc (m₀ + D + 1) m₀
      have hS_card : S.card = D.natAbs := by
        dsimp [S]
        split_ifs with hD_pos
        · rw [Int.card_Icc]; omega
        · rw [Int.card_Icc]; omega
      have hT_nonempty : ∀ m ∈ S, (T m).Nonempty := by
        intro m hm
        rcases eq_or_ne m m₀ with rfl | hm_ne
        · refine ⟨0, 0, ?_⟩
          obtain ⟨_, hΓ₁0_r, _, hΓ₁0_y, _, _⟩ := liftedLinkageCurve_props hk L₁ hL₁ m₀
          obtain ⟨_, hΓ₂0_r, _, hΓ₂0_y, _, _⟩ := liftedLinkageCurve_props hk L₂ hL₂ m₀
          exact Prod.ext (hΓ₁0_r.trans hΓ₂0_r.symm) (hΓ₁0_y.trans hΓ₂0_y.symm)
        · obtain ⟨hΓ₁_r, hΓ₁0_r, hΓ₁1_r, hΓ₁0_y, hΓ₁1_y, _⟩ :=
            liftedLinkageCurve_props hk L₁ hL₁ m
          obtain ⟨hΓ₂_r, hΓ₂0_r, hΓ₂1_r, hΓ₂0_y, hΓ₂1_y, _⟩ :=
            liftedLinkageCurve_props hk L₂ hL₂ m₀
          have hθ₁_eq : θ₁ = (a₁ : ℝ) / (k : ℝ) := by
            rw [← ha₁, mul_div_cancel_left₀ _ hk_ne]
          have hθ₂_eq : θ₂ = (a₂ : ℝ) / (k : ℝ) := by
            rw [← ha₂, mul_div_cancel_left₀ _ hk_ne]
          have hpi_div_pos : (0 : ℝ) < 2 * π / (k : ℝ) := by positivity
          have h_lt_iff : ∀ x y : ℤ,
              2 * (x : ℝ) * π / (k : ℝ) < 2 * (y : ℝ) * π / (k : ℝ) ↔ x < y := by
            intro x y
            have hx_eq : 2 * (x : ℝ) * π / (k : ℝ) = (x : ℝ) * (2 * π / (k : ℝ)) := by ring
            have hy_eq : 2 * (y : ℝ) * π / (k : ℝ) = (y : ℝ) * (2 * π / (k : ℝ)) := by ring
            rw [hx_eq, hy_eq, mul_lt_mul_iff_left₀ hpi_div_pos, Int.cast_lt]
          have hΓ₁1_y' : (liftedLinkageCurve hk L₁ m 1).2 =
              2 * ((m + a₁ : ℤ) : ℝ) * π / (k : ℝ) := by
            rw [hΓ₁1_y, hθ₁_eq]; push_cast; field_simp [hk_ne]
          have hΓ₂1_y' : (Γ₂ 1).2 = 2 * ((m₀ + a₂ : ℤ) : ℝ) * π / (k : ℝ) := by
            rw [hΓ₂1_y, hθ₂_eq]; push_cast; field_simp [hk_ne]
          have hswap :
              ((liftedLinkageCurve hk L₁ m 0).2 < (Γ₂ 0).2 ∧
                (Γ₂ 1).2 < (liftedLinkageCurve hk L₁ m 1).2) ∨
              ((Γ₂ 0).2 < (liftedLinkageCurve hk L₁ m 0).2 ∧
                (liftedLinkageCurve hk L₁ m 1).2 < (Γ₂ 1).2) := by
            rw [hΓ₁0_y, hΓ₂0_y, hΓ₁1_y', hΓ₂1_y']
            dsimp [S] at hm
            split_ifs at hm with hD_pos
            · rw [Finset.mem_Icc] at hm
              right
              exact ⟨(h_lt_iff m₀ m).mpr (by omega), (h_lt_iff (m + a₁) (m₀ + a₂)).mpr (by omega)⟩
            · rw [Finset.mem_Icc] at hm
              left
              exact ⟨(h_lt_iff m m₀).mpr (by omega), (h_lt_iff (m₀ + a₂) (m + a₁)).mpr (by omega)⟩
          obtain ⟨t₁, t₂, heq⟩ :=
            strip_crossing (liftedLinkageCurve hk L₁ m) Γ₂
              hΓ₁_r hΓ₂_r hΓ₁0_r hΓ₁1_r hΓ₂0_r hΓ₂1_r hswap
          exact ⟨t₂, t₁, heq⟩
      have h_least : ∀ m : S, ∃ t_m : unitInterval, IsLeast (T m.1) t_m := fun m =>
        (hT_closed m.1).isCompact.exists_isLeast (hT_nonempty m.1 m.2)
      let tMap : S → unitInterval := fun m => Classical.choose (h_least m)
      have htMap_spec : ∀ m : S, IsLeast (T m.1) (tMap m) := fun m =>
        Classical.choose_spec (h_least m)
      let vMap : S → (L₂.pathDrawing j).finite_V.toFinset := fun m =>
        ⟨L₂.curve j (tMap m), (Set.Finite.mem_toFinset _).mpr
          (mem_pathDrawing_V_of_isLeast_lifted_hit hk L₁ L₂ hL₁ hL₂ j m.1 (htMap_spec m))⟩
      have hvMap_inj : Function.Injective vMap := by
        intro m₁ m₂ heq
        apply Subtype.ext
        have ht_eq : tMap m₁ = tMap m₂ :=
          (L₂.curve_parametrizes j).1 (congrArg Subtype.val heq)
        rcases (htMap_spec m₁).1 with ⟨s₁, hs₁⟩
        rcases (htMap_spec m₂).1 with ⟨s₂, hs₂⟩
        have hΓ_eq : liftedLinkageCurve hk L₁ m₁.1 s₁ = liftedLinkageCurve hk L₁ m₂.1 s₂ := by
          rw [hs₁, ht_eq, hs₂]
        exact eq_of_liftedLinkageCurve_eq hk L₁ hL₁ hΓ_eq
      have hcard_le : S.card ≤ (L₂.pathDrawing j).finite_V.toFinset.card := by
        simpa [Fintype.card_coe] using Fintype.card_le_of_injective vMap hvMap_inj
      have htoFinset_eq : (L₂.pathDrawing j).finite_V.toFinset.card =
          (L₂.pathDrawing j).V.ncard :=
        (Set.ncard_eq_toFinset_card (L₂.pathDrawing j).V (L₂.pathDrawing j).finite_V).symm
      omega
  -- Sum over `j : Fin k` using pairwise disjointness of `(L₂.pathDrawing j).V`.
  let V_j : Fin k → Finset ClosedCylinder := fun j => (L₂.pathDrawing j).finite_V.toFinset
  have hVj_disj : Pairwise fun i j : Fin k => Disjoint (V_j i) (V_j j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [Set.Finite.mem_toFinset] at hxi hxj
    exact Set.disjoint_left.mp (L₂.pairwise_disjoint hij)
      ((L₂.pathDrawing i).V_subset_U hxi) ((L₂.pathDrawing j).V_subset_U hxj)
  have h_bUnion_sub : Finset.biUnion Finset.univ V_j ⊆ G.finite_V.toFinset := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨j, _, hxj⟩
    rw [Set.Finite.mem_toFinset] at hxj ⊢
    exact (L₂.isSubdrawing j).1.1 hxj
  have h_sum_le : ∑ j : Fin k, (V_j j).card ≤ G.V.ncard := by
    calc ∑ j : Fin k, (V_j j).card
      _ = (Finset.biUnion Finset.univ V_j).card := by
          rw [Finset.card_biUnion]
          intro i _ j _ hij
          exact hVj_disj hij
      _ ≤ G.finite_V.toFinset.card := Finset.card_le_card h_bUnion_sub
      _ = G.V.ncard := (Set.ncard_eq_toFinset_card G.V G.finite_V).symm
  have h_k_mul_le : k * D.natAbs ≤ G.V.ncard := by
    calc k * D.natAbs
      _ = ∑ _j : Fin k, D.natAbs := by simp
      _ ≤ ∑ j : Fin k, (V_j j).card := by
          apply Finset.sum_le_sum
          intro j _
          rw [← Set.ncard_eq_toFinset_card (L₂.pathDrawing j).V (L₂.pathDrawing j).finite_V]
          exact hpath_card j
      _ ≤ G.V.ncard := h_sum_le
  have h_real_le : (k : ℝ) * |(D : ℝ)| ≤ (G.V.ncard : ℝ) := by
    have h1 : ((k * D.natAbs : ℕ) : ℝ) ≤ (G.V.ncard : ℝ) := Nat.cast_le.mpr h_k_mul_le
    have h2 : |(D : ℝ)| = (D.natAbs : ℝ) := by rw [← Int.cast_abs, Nat.cast_natAbs]
    push_cast at h1
    rw [h2]
    exact h1
  rw [← hD_real, abs_mul, abs_of_pos hk_pos, abs_sub_comm] at h_real_le
  have hk2_pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hk_pos
  have hk2_ne : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hk2_pos
  calc |θ₁ - θ₂|
    _ = (1 / (k : ℝ) ^ 2) * ((k : ℝ) * ((k : ℝ) * |θ₁ - θ₂|)) := by
        field_simp [hk_ne]
    _ ≤ (1 / (k : ℝ) ^ 2) * (G.V.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left h_real_le (by positivity)

/-! ## 5. Constancy of Winding Number Across Any Cylinder Linkage -/

theorem liftedLinkageCurve_props_raw {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (m : ℤ) :
    let i := modIdx k hk m
    let g := L.curve i
    let Γ := liftedLinkageCurve hk L m
    (∀ t : unitInterval, (Γ t).1 ∈ Icc (1 : ℝ) 2) ∧
    (Γ 0).1 = 1 ∧ (Γ 1).1 = 2 ∧
    (Γ 0).2 = 2 * (m : ℝ) * π / (k : ℝ) ∧
    (Γ 1).2 = 2 * (m : ℝ) * π / (k : ℝ) + 2 * π * windingNumber g ∧
    (∀ t : unitInterval, Circle.exp (Γ t).2 = (g t).1.2) := by
  intro i g Γ
  refine ⟨fun t => (g t).2.1, ?_, ?_, ?_, ?_, ?_⟩
  · have hg0 : g 0 = cylinderM1Point k i := (L.curve_parametrizes i).2.2.1
    change (g 0).1.1 = 1
    rw [hg0]; rfl
  · rcases L.curve_one_mem i with ⟨j, hj⟩
    change (g 1).1.1 = 2
    rw [← hj]; rfl
  · change cylinderAngleLift g 0 + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0) = _
    ring
  · change cylinderAngleLift g 1 + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0) = _
    unfold windingNumber
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
    have hdiff : cylinderAngleLift g 1 - cylinderAngleLift g 0 =
        2 * π * ((cylinderAngleLift g 1 - cylinderAngleLift g 0) / (2 * π)) := by
      field_simp [h2pi_ne]
    linarith
  · intro t
    change Circle.exp (cylinderAngleLift g t + (2 * (m : ℝ) * π / (k : ℝ) - cylinderAngleLift g 0)) = (g t).1.2
    rw [Circle.exp_add, Circle.exp_sub, exp_cylinderAngleLift, exp_cylinderAngleLift,
      exp_two_mul_int_div_eq_cylinderM1Point hk m]
    have hg0 : g 0 = cylinderM1Point k i := (L.curve_parametrizes i).2.2.1
    rw [hg0]
    change (g t).1.2 * ((cylinderM1Point k i).1.2 / (cylinderM1Point k i).1.2) = (g t).1.2
    rw [div_self', mul_one]

theorem eq_of_liftedLinkageCurve_eq_raw {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G)
    {m₁ m₂ : ℤ} {t₁ t₂ : unitInterval}
    (h : liftedLinkageCurve hk L m₁ t₁ = liftedLinkageCurve hk L m₂ t₂) :
    m₁ = m₂ := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  obtain ⟨_, _, _, _, _, hΓ₁_exp⟩ := liftedLinkageCurve_props_raw hk L m₁
  obtain ⟨_, _, _, _, _, hΓ₂_exp⟩ := liftedLinkageCurve_props_raw hk L m₂
  let i₁ := modIdx k hk m₁
  let i₂ := modIdx k hk m₂
  have h_fst : (L.curve i₁ t₁).1.1 = (L.curve i₂ t₂).1.1 :=
    congrArg (Prod.fst : ℝ × ℝ → ℝ) h
  have h_snd : (liftedLinkageCurve hk L m₁ t₁).2 = (liftedLinkageCurve hk L m₂ t₂).2 :=
    congrArg (Prod.snd : ℝ × ℝ → ℝ) h
  have hg_eq : L.curve i₁ t₁ = L.curve i₂ t₂ := by
    apply Subtype.ext
    refine Prod.ext h_fst ?_
    calc (L.curve i₁ t₁).1.2
      _ = Circle.exp (liftedLinkageCurve hk L m₁ t₁).2 := (hΓ₁_exp t₁).symm
      _ = Circle.exp (liftedLinkageCurve hk L m₂ t₂).2 := by rw [h_snd]
      _ = (L.curve i₂ t₂).1.2 := hΓ₂_exp t₂
  have hi_eq : i₁ = i₂ := by
    by_contra hne
    have hdisj := L.pairwise_disjoint hne
    have hmem₁ : L.curve i₁ t₁ ∈ (L.pathDrawing i₁).U := by
      rw [← (L.curve_parametrizes i₁).2.1]
      exact ⟨t₁, rfl⟩
    have hmem₂ : L.curve i₁ t₁ ∈ (L.pathDrawing i₂).U := by
      rw [← (L.curve_parametrizes i₂).2.1]
      exact ⟨t₂, hg_eq.symm⟩
    exact Set.disjoint_left.mp hdisj hmem₁ hmem₂
  have ht_eq : t₁ = t₂ := by
    apply (L.curve_parametrizes i₁).1
    rw [hg_eq, hi_eq]
  change cylinderAngleLift (L.curve i₁) t₁ +
      (2 * (m₁ : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve i₁) 0) =
    cylinderAngleLift (L.curve i₂) t₂ +
      (2 * (m₂ : ℝ) * π / (k : ℝ) - cylinderAngleLift (L.curve i₂) 0) at h_snd
  rw [← hi_eq, ← ht_eq] at h_snd
  have hm_div : 2 * (m₁ : ℝ) * π / (k : ℝ) = 2 * (m₂ : ℝ) * π / (k : ℝ) := by linarith
  have hm_real : (m₁ : ℝ) = (m₂ : ℝ) := by
    have hmul : (2 * (m₁ : ℝ) * π / (k : ℝ)) * (k : ℝ) =
        (2 * (m₂ : ℝ) * π / (k : ℝ)) * (k : ℝ) := by rw [hm_div]
    rw [div_mul_cancel₀ _ hk_ne, div_mul_cancel₀ _ hk_ne] at hmul
    nlinarith [Real.pi_pos]
  exact Int.cast_injective hm_real

/-- Graph Minors VI, Section 5 (page 128):
"If $\mathcal{L}$ is a linkage then clearly $\theta(P)$ is constant for $P \in \mathcal{L}$, and we
denote this common value by $\theta(\mathcal{L})$." -/
theorem CylinderLinkage.exists_hasTheta {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) :
    ∃ θ : ℝ, L.HasTheta θ := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
  have hex_a : ∀ i : Fin k, ∃ a : ℤ, (k : ℝ) * windingNumber (L.curve i) = (a : ℝ) := by
    intro i
    let g := L.curve i
    have hg0 : g 0 = cylinderM1Point k i := (L.curve_parametrizes i).2.2.1
    rcases L.curve_one_mem i with ⟨j₁, hj₁⟩
    have hexp0 : Circle.exp (cylinderAngleLift g 0) =
        Circle.exp (2 * ((i.1 + 1 : ℕ) : ℝ) * π / k) := by
      rw [exp_cylinderAngleLift, hg0]; rfl
    have hexp1 : Circle.exp (cylinderAngleLift g 1) =
        Circle.exp (2 * ((j₁.1 + 1 : ℕ) : ℝ) * π / k) := by
      rw [exp_cylinderAngleLift, ← hj₁]; rfl
    obtain ⟨n₀, hn₀⟩ := Circle.exp_eq_exp.mp hexp0
    obtain ⟨n₁, hn₁⟩ := Circle.exp_eq_exp.mp hexp1
    let a₀ : ℤ := (i.1 + 1 : ℤ) + n₀ * (k : ℤ)
    let a₁ : ℤ := (j₁.1 + 1 : ℤ) + n₁ * (k : ℤ)
    refine ⟨a₁ - a₀, ?_⟩
    unfold windingNumber
    rw [hn₀, hn₁]
    dsimp [a₀, a₁]
    push_cast
    field_simp [hk_ne, h2pi_ne]
  choose a ha using hex_a
  let b : ℤ → ℤ := fun m => m + a (modIdx k hk m)
  have hΓ1_y : ∀ m : ℤ,
      (liftedLinkageCurve hk L m 1).2 = 2 * (b m : ℝ) * π / (k : ℝ) := by
    intro m
    obtain ⟨_, _, _, _, h1_y, _⟩ := liftedLinkageCurve_props_raw hk L m
    rw [h1_y]
    have hw : windingNumber (L.curve (modIdx k hk m)) = (a (modIdx k hk m) : ℝ) / (k : ℝ) := by
      rw [← ha (modIdx k hk m), mul_div_cancel_left₀ _ hk_ne]
    rw [hw]
    dsimp [b]
    push_cast
    field_simp [hk_ne]
  have hpi_div_pos : (0 : ℝ) < 2 * π / (k : ℝ) := by positivity
  have h_lt_iff : ∀ x y : ℤ,
      2 * (x : ℝ) * π / (k : ℝ) < 2 * (y : ℝ) * π / (k : ℝ) ↔ x < y := by
    intro x y
    have hx_eq : 2 * (x : ℝ) * π / (k : ℝ) = (x : ℝ) * (2 * π / (k : ℝ)) := by ring
    have hy_eq : 2 * (y : ℝ) * π / (k : ℝ) = (y : ℝ) * (2 * π / (k : ℝ)) := by ring
    rw [hx_eq, hy_eq, mul_lt_mul_iff_left₀ hpi_div_pos, Int.cast_lt]
  have hb_step : ∀ m : ℤ, b m + 1 ≤ b (m + 1) := by
    intro m
    by_contra hnot
    obtain ⟨hΓ₁_r, hΓ₁0_r, hΓ₁1_r, hΓ₁0_y, _, _⟩ := liftedLinkageCurve_props_raw hk L m
    obtain ⟨hΓ₂_r, hΓ₂0_r, hΓ₂1_r, hΓ₂0_y, _, _⟩ := liftedLinkageCurve_props_raw hk L (m + 1)
    rcases eq_or_lt_of_le (Int.le_of_lt_add_one (not_le.mp hnot)) with heq | hlt
    · have h1_eq : liftedLinkageCurve hk L m 1 = liftedLinkageCurve hk L (m + 1) 1 := by
        refine Prod.ext (hΓ₁1_r.trans hΓ₂1_r.symm) ?_
        rw [hΓ1_y m, hΓ1_y (m + 1), heq]
      have hm_eq := eq_of_liftedLinkageCurve_eq_raw hk L h1_eq
      omega
    · have hswap :
          ((liftedLinkageCurve hk L m 0).2 < (liftedLinkageCurve hk L (m + 1) 0).2 ∧
            (liftedLinkageCurve hk L (m + 1) 1).2 < (liftedLinkageCurve hk L m 1).2) ∨
          ((liftedLinkageCurve hk L (m + 1) 0).2 < (liftedLinkageCurve hk L m 0).2 ∧
            (liftedLinkageCurve hk L m 1).2 < (liftedLinkageCurve hk L (m + 1) 1).2) := by
        left
        rw [hΓ₁0_y, hΓ₂0_y, hΓ1_y m, hΓ1_y (m + 1)]
        exact ⟨(h_lt_iff m (m + 1)).mpr (by omega), (h_lt_iff (b (m + 1)) (b m)).mpr hlt⟩
      obtain ⟨t₁, t₂, heq⟩ :=
        strip_crossing (liftedLinkageCurve hk L m) (liftedLinkageCurve hk L (m + 1))
          hΓ₁_r hΓ₂_r hΓ₁0_r hΓ₁1_r hΓ₂0_r hΓ₂1_r hswap
      have hm_eq := eq_of_liftedLinkageCurve_eq_raw hk L heq
      omega
  have hb_mono : ∀ (n : ℕ) (m : ℤ), b m + (n : ℤ) ≤ b (m + (n : ℤ)) := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      have h1 := ih m
      have h2 := hb_step (m + (n : ℤ))
      have h3 : m + ((n + 1 : ℕ) : ℤ) = m + (n : ℤ) + 1 := by push_cast; ring
      rw [h3]
      omega
  have hmod_add_k : ∀ m : ℤ, modIdx k hk (m + (k : ℤ)) = modIdx k hk m := by
    intro m
    ext
    dsimp [modIdx]
    have h1 : m + (k : ℤ) - 1 = (m - 1) + (k : ℤ) * 1 := by ring
    rw [h1, Int.add_mul_emod_self_left]
  have hb_add_k : ∀ m : ℤ, b (m + (k : ℤ)) = b m + (k : ℤ) := by
    intro m
    dsimp [b]
    rw [hmod_add_k m]
    ring
  have hb_eq_succ : ∀ m : ℤ, b (m + 1) = b m + 1 := by
    intro m
    have hle := hb_step m
    by_contra hne
    have hlt : b m + 2 ≤ b (m + 1) := by omega
    have hrem := hb_mono (k - 1) (m + 1)
    have hm_k : (m + 1) + ((k - 1 : ℕ) : ℤ) = m + (k : ℤ) := by omega
    rw [hm_k, hb_add_k m] at hrem
    omega
  have hb_nat : ∀ n : ℕ, b ((n : ℤ) + 1) = b 1 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (((n + 1 : ℕ) : ℤ) + 1) = ((n : ℤ) + 1) + 1 := by push_cast; ring
      rw [h1, hb_eq_succ, ih]
      push_cast
      ring
  let i₀ : Fin k := ⟨0, hk⟩
  refine ⟨windingNumber (L.curve i₀), fun j => ?_⟩
  have hj1 := hb_nat j.1
  dsimp [b] at hj1
  rw [modIdx_natCast_succ hk j] at hj1
  have h1_idx : modIdx k hk 1 = i₀ := modIdx_natCast_succ hk i₀
  rw [h1_idx] at hj1
  have haj : a j = a i₀ := by omega
  have h_mul : (k : ℝ) * windingNumber (L.curve j) = (k : ℝ) * windingNumber (L.curve i₀) := by
    rw [ha j, ha i₀, haj]
  exact mul_left_cancel₀ hk_ne h_mul

end GraphMinor.GM06
