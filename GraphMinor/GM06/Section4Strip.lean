module

public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4
import GraphMinor.Surface.Crossing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Alternating endpoints on one side of a strip

For the lifted-path argument in Graph Minors VI (4.2), claim (1), two curves
with alternating ends on the same side of a strip must meet. We embed a
bounded part of the strip into a disc and apply the disc crossing theorem.
-/

public section

namespace GraphMinor.GM06

open Set Function Complex Real Topology Metric Graph GraphMinor.Surface GraphMinor.GM11

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

/-- Curves in a strip whose four ends alternate on its left boundary meet.
This is the planar crossing fact used for Graph Minors VI (4.2), claim (1). -/
theorem strip_crossing_same_side (γ δ : C(unitInterval, ℝ × ℝ))
    (hγ_r : ∀ t : unitInterval, (γ t).1 ∈ Icc (1 : ℝ) 2)
    (hδ_r : ∀ t : unitInterval, (δ t).1 ∈ Icc (1 : ℝ) 2)
    (hγ0 : (γ 0).1 = 1) (hγ1 : (γ 1).1 = 1)
    (hδ0 : (δ 0).1 = 1) (hδ1 : (δ 1).1 = 1)
    (horder : (γ 0).2 < (δ 0).2 ∧ (δ 0).2 < (γ 1).2 ∧ (γ 1).2 < (δ 1).2) :
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
  let u_d : Circle := Circle.exp (π - stripAngle M (δ 1).2)
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
    have h1 : δ 1 = (1, (δ 1).2) := Prod.ext hδ1 rfl
    rw [h1, stripToComplex_left]
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
  have harg_d : circleStdCoord.angle u_d = π - stripAngle M (δ 1).2 :=
    arg_exp_of_mem_Ioo (by linarith [hθ_δ1.2]) (by linarith [hθ_δ1.1])
  have hφ0 := stripAngle_strictMono hM_pos horder.1
  have hφ1 := stripAngle_strictMono hM_pos horder.2.1
  have hφ2 := stripAngle_strictMono hM_pos horder.2.2
  have h_ord1 : circleStdCoord.angle u_d < circleStdCoord.angle u_c := by
    rw [harg_d, harg_c]; linarith only [hφ2]
  have h_ord2 : circleStdCoord.angle u_c < circleStdCoord.angle u_b := by
    rw [harg_c, harg_b]; linarith only [hφ1]
  have h_ord3 : circleStdCoord.angle u_b < circleStdCoord.angle u_a := by
    rw [harg_b, harg_a]; linarith only [hφ0]
  have hcross_circle : circleCrosses circleStdCoord u_a u_c u_b u_d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => (ne_of_gt (h_ord2.trans h_ord3)) (congrArg circleStdCoord.angle h)
    · exact fun h => (ne_of_gt (h_ord1.trans h_ord2)) (congrArg circleStdCoord.angle h)
    · exact fun h => (ne_of_gt h_ord3) (congrArg circleStdCoord.angle h)
    · exact fun h => (ne_of_gt ((h_ord1.trans h_ord2).trans h_ord3))
        (congrArg circleStdCoord.angle h)
    · exact fun h => (ne_of_lt h_ord2) (congrArg circleStdCoord.angle h)
    · exact fun h => (ne_of_gt h_ord1) (congrArg circleStdCoord.angle h)
    · simp only [onOpenArc, min_eq_right (h_ord2.trans h_ord3).le,
        max_eq_left (h_ord2.trans h_ord3).le]
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

/-- The same crossing conclusion allows coincidences between successive
ends, since a coincidence itself is a meeting. -/
theorem strip_crossing_same_side_le (γ δ : C(unitInterval, ℝ × ℝ))
    (hγ_r : ∀ t : unitInterval, (γ t).1 ∈ Icc (1 : ℝ) 2)
    (hδ_r : ∀ t : unitInterval, (δ t).1 ∈ Icc (1 : ℝ) 2)
    (hγ0 : (γ 0).1 = 1) (hγ1 : (γ 1).1 = 1)
    (hδ0 : (δ 0).1 = 1) (hδ1 : (δ 1).1 = 1)
    (horder : (γ 0).2 ≤ (δ 0).2 ∧ (δ 0).2 ≤ (γ 1).2 ∧ (γ 1).2 ≤ (δ 1).2) :
    ∃ t₁ t₂ : unitInterval, γ t₁ = δ t₂ := by
  by_cases h₀ : (γ 0).2 = (δ 0).2
  · exact ⟨0, 0, Prod.ext (hγ0.trans hδ0.symm) h₀⟩
  by_cases h₁ : (δ 0).2 = (γ 1).2
  · exact ⟨1, 0, Prod.ext (hγ1.trans hδ0.symm) h₁.symm⟩
  by_cases h₂ : (γ 1).2 = (δ 1).2
  · exact ⟨1, 1, Prod.ext (hγ1.trans hδ1.symm) h₂⟩
  exact strip_crossing_same_side γ δ hγ_r hδ_r hγ0 hγ1 hδ0 hδ1
    ⟨lt_of_le_of_ne horder.1 h₀, lt_of_le_of_ne horder.2.1 h₁,
      lt_of_le_of_ne horder.2.2 h₂⟩

end GraphMinor.GM06
