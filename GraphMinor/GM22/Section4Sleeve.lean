module

public import GraphMinor.GM22.Section4
public import GraphMinor.Surface.DiscMatch
public import GraphMinor.GM19.CircleOrder
public import GraphMinor.GM19.Winding
public import GraphMinor.GM19.RadialExists
public import GraphMinor.GM19.CutFragment
public import GraphMinor.GM12.Section4DiscEnlargement
public import GraphMinor.GM12.Section4RadialResize
public import GraphMinor.GM11.RadialBasics
public import GraphMinor.GM11.Section6

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 4 (Part 3): Sleeves and Theorem 4.2

This file formalizes **4.2** (`theorem_4_2`) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 538–539).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric unitInterval Classical Graph
  GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM16 GraphMinor.GM19
open scoped Pointwise

local notation "𝕀" => unitInterval

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## 1. Disjoint Paths Across an Annulus Preserve Cyclic Order -/

private noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

private theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01
  fun_prop

private theorem clamp01_mem_Icc (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

private theorem clamp01_of_le_zero {t : ℝ} (ht : t ≤ 0) : clamp01 t = 0 := by
  simp [clamp01, min_eq_left (ht.trans zero_le_one), max_eq_left ht]

private theorem clamp01_of_one_le {t : ℝ} (ht : 1 ≤ t) : clamp01 t = 1 := by
  simp [clamp01, min_eq_right ht]

private theorem clamp01_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  simp [clamp01, min_eq_left ht.2, max_eq_right ht.1]

/-- A path in the annulus `closedBall 0 2 \ ball 0 1` from `u ∈ Circle` at `t ≤ 0` to
`2 * v` (`v ∈ Circle`) at `1 ≤ t`, meeting `sphere 0 1` only for `t ≤ 0` and `sphere 0 2` only for
`1 ≤ t`. -/
structure IsAnnulusPath (γ : ℝ → ℂ) (u v : Circle) : Prop where
  continuous : Continuous γ
  norm_bounds : ∀ t, 1 ≤ ‖γ t‖ ∧ ‖γ t‖ ≤ 2
  eq_start : ∀ t ≤ 0, γ t = (u : ℂ)
  eq_end : ∀ t, 1 ≤ t → γ t = 2 * (v : ℂ)
  norm_eq_one_iff : ∀ t, ‖γ t‖ = 1 ↔ t ≤ 0
  norm_eq_two_iff : ∀ t, ‖γ t‖ = 2 ↔ 1 ≤ t

theorem IsAnnulusPath.ne_zero {γ : ℝ → ℂ} {u v : Circle} (h : IsAnnulusPath γ u v) (t : ℝ) :
    γ t ≠ 0 := by
  intro h0
  have := (h.norm_bounds t).1
  rw [h0, norm_zero] at this
  linarith

theorem IsAnnulusPath.norm_gt_one {γ : ℝ → ℂ} {u v : Circle} (h : IsAnnulusPath γ u v)
    {t : ℝ} (ht : 0 < t) : 1 < ‖γ t‖ :=
  lt_of_le_of_ne (h.norm_bounds t).1 fun he => not_le.mpr ht ((h.norm_eq_one_iff t).mp he.symm)

theorem IsAnnulusPath.norm_lt_two {γ : ℝ → ℂ} {u v : Circle} (h : IsAnnulusPath γ u v)
    {t : ℝ} (ht : t < 1) : ‖γ t‖ < 2 :=
  lt_of_le_of_ne (h.norm_bounds t).2 fun he => not_le.mpr ht ((h.norm_eq_two_iff t).mp he)

/-- Linearly parametrized circular arc of radius `r > 0` from `w * exp(a i)` to `w * exp(a' i)`. -/
private noncomputable def circleArc (r : ℝ) (w : Circle) (a a' : ℝ) (t : ℝ) : ℂ :=
  (r : ℂ) * (w : ℂ) * Complex.exp ((((1 - t) * a + t * a' : ℝ) : ℂ) * Complex.I)

private theorem continuous_circleArc (r : ℝ) (w : Circle) (a a' : ℝ) :
    Continuous (circleArc r w a a') := by
  unfold circleArc
  fun_prop

private theorem circleArc_zero (r : ℝ) (w : Circle) (a a' : ℝ) :
    circleArc r w a a' 0 = (r : ℂ) * ((w * Circle.exp a : Circle) : ℂ) := by
  simp [circleArc, Circle.coe_mul, Circle.coe_exp, mul_assoc]

private theorem circleArc_one (r : ℝ) (w : Circle) (a a' : ℝ) :
    circleArc r w a a' 1 = (r : ℂ) * ((w * Circle.exp a' : Circle) : ℂ) := by
  simp [circleArc, Circle.coe_mul, Circle.coe_exp, mul_assoc]

private theorem norm_circleArc {r : ℝ} (hr : 0 ≤ r) (w : Circle) (a a' t : ℝ) :
    ‖circleArc r w a a' t‖ = r := by
  unfold circleArc
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, Circle.norm_coe,
    Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]

private theorem turn_circleArc {r : ℝ} (hr : 0 < r) (w : Circle) (a a' : ℝ) :
    turn (circleArc r w a a') 0 1 = a' - a := by
  obtain ⟨θ, rfl⟩ := GM19.exists_angle_of_circle w
  let L : ℝ → ℝ := fun t => θ + ((1 - t) * a + t * a')
  have hL : IsAngle (circleArc r (Circle.exp θ) a a') L := by
    refine ⟨by fun_prop, fun t => ?_⟩
    rw [norm_circleArc hr.le]
    unfold circleArc L
    rw [Circle.coe_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h0 : ∀ t, circleArc r (Circle.exp θ) a a' t ≠ 0 := fun t ht => by
    have := norm_circleArc hr.le (Circle.exp θ) a a' t
    rw [ht, norm_zero] at this
    linarith
  rw [hL.turn_eq h0 0 1]
  simp [L]

private theorem circleArc_ne_base {r : ℝ} (hr : 0 < r) (w : Circle) {a a' : ℝ}
    (ha0 : 0 < a) (ha2 : a < 2 * Real.pi) (ha'0 : 0 < a') (ha'2 : a' < 2 * Real.pi)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    circleArc r w a a' t ≠ (r : ℂ) * (w : ℂ) := by
  intro heq
  unfold circleArc at heq
  have hrw : (r : ℂ) * (w : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Circle.coe_ne_zero w)
  have hexp : Complex.exp ((((1 - t) * a + t * a' : ℝ) : ℂ) * Complex.I) = 1 :=
    mul_left_cancel₀ hrw (heq.trans (mul_one _).symm)
  have hcexp : Circle.exp ((1 - t) * a + t * a') = 1 := by
    apply Circle.ext
    rw [Circle.coe_exp, Circle.coe_one]
    exact hexp
  have hpos : 0 < (1 - t) * a + t * a' := by
    rcases ht.1.eq_or_lt with rfl | ht0
    · simp [ha0]
    · have : 0 ≤ (1 - t) * a := mul_nonneg (sub_nonneg.mpr ht.2) ha0.le
      have : 0 < t * a' := mul_pos ht0 ha'0
      linarith
  have hlt : (1 - t) * a + t * a' < 2 * Real.pi := by
    have : (1 - t) * a + t * a' ≤ (1 - t) * max a a' + t * max a a' :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left a a') (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (le_max_right a a') ht.1)
    have hmax : max a a' < 2 * Real.pi := max_lt ha2 ha'2
    linarith
  have hne := circle_exp_ne (x := (1 - t) * a + t * a') (y := 0) hpos.ne'
    (by rw [sub_zero, abs_of_pos hpos]; exact hlt)
  rw [Circle.exp_zero] at hne
  exact hne hcexp

/-- Two annulus paths `γ_a, γ_c` disjoint from a third annulus path `γ_b` satisfy the turn identity
`(α_c - α_a) - (β_c - β_a) = turn γ_a 0 1 - turn γ_c 0 1`. -/
theorem turn_diff_eq_of_avoid_annulus_path
    {γ_a γ_b γ_c : ℝ → ℂ} {u_a u_b u_c v_a v_b v_c : Circle}
    (ha : IsAnnulusPath γ_a u_a v_a) (hb : IsAnnulusPath γ_b u_b v_b)
    (hc : IsAnnulusPath γ_c u_c v_c)
    (hab_disj : ∀ s t, γ_a s ≠ γ_b t) (hcb_disj : ∀ s t, γ_c s ≠ γ_b t)
    {α_a α_c β_a β_c : ℝ}
    (hα_a0 : 0 < α_a) (hα_a2 : α_a < 2 * Real.pi)
    (hα_c0 : 0 < α_c) (hα_c2 : α_c < 2 * Real.pi)
    (hβ_a0 : 0 < β_a) (hβ_a2 : β_a < 2 * Real.pi)
    (hβ_c0 : 0 < β_c) (hβ_c2 : β_c < 2 * Real.pi)
    (hua : u_a = u_b * Circle.exp α_a) (huc : u_c = u_b * Circle.exp α_c)
    (hva : v_a = v_b * Circle.exp β_a) (hvc : v_c = v_b * Circle.exp β_c) :
    (α_c - α_a) - (β_c - β_a) = turn γ_a 0 1 - turn γ_c 0 1 := by
  let g : ℝ → ℂ := circleArc 1 u_b α_a α_c
  have hg : Continuous g := continuous_circleArc 1 u_b α_a α_c
  have hg0 : g 0 = (u_a : ℂ) := by
    rw [hua]
    simpa using circleArc_zero 1 u_b α_a α_c
  have hg1 : g 1 = (u_c : ℂ) := by
    rw [huc]
    simpa using circleArc_one 1 u_b α_a α_c
  let k₁ : ℝ → ℂ := fun t => if t ≤ 1 then γ_a t else circleArc 2 v_b β_a β_c (t - 1)
  have hk₁ : Continuous k₁ := Continuous.if_le ha.continuous
    ((continuous_circleArc 2 v_b β_a β_c).comp (by fun_prop)) continuous_id continuous_const
    fun t ht => by
      subst ht
      rw [ha.eq_end 1 le_rfl, sub_self, circleArc_zero, hva]
      rfl
  let k : ℝ → ℂ := fun t => if t ≤ 2 then k₁ t else γ_c (3 - t)
  have hk : Continuous k := Continuous.if_le hk₁ (hc.continuous.comp (by fun_prop))
    continuous_id continuous_const fun t ht => by
      subst ht
      dsimp only [k₁]
      have h21 : ¬ ((2 : ℝ) ≤ 1) := by norm_num
      have h2_sub : (2 : ℝ) - 1 = 1 := by norm_num
      have h3_sub : (3 : ℝ) - 2 = 1 := by norm_num
      rw [ite_eq_right h21, h2_sub, h3_sub, circleArc_one, hc.eq_end 1 le_rfl, hvc]
      rfl
  have hk0 : k 0 = (u_a : ℂ) := by
    dsimp only [k, k₁]
    rw [ite_eq_left (by norm_num : (0 : ℝ) ≤ 2), ite_eq_left zero_le_one, ha.eq_start 0 le_rfl]
  have hk3 : k 3 = (u_c : ℂ) := by
    dsimp only [k]
    rw [ite_eq_right (by norm_num : ¬ ((3 : ℝ) ≤ 2)), sub_self, hc.eq_start 0 le_rfl]
  let p₁ : ℝ → ℂ := fun u => ((clamp01 (3 * u) : ℝ) : ℂ) * (u_b : ℂ)
  have hp₁ : Continuous p₁ :=
    (Complex.continuous_ofReal.comp (continuous_clamp01.comp (by fun_prop))).mul continuous_const
  let p₂ : ℝ → ℂ := fun u =>
    if u ≤ 1 / 3 then p₁ u else γ_b (3 * u - 1)
  have hp₂ : Continuous p₂ := Continuous.if_le hp₁ (hb.continuous.comp (by fun_prop))
    continuous_id continuous_const fun u hu => by
      subst hu
      dsimp only [p₁]
      have h1 : (3 : ℝ) * (1 / 3) = 1 := by norm_num
      rw [h1, sub_self, clamp01_of_one_le le_rfl, hb.eq_start 0 le_rfl, Complex.ofReal_one, one_mul]
  let p : ℝ → ℂ := fun u =>
    if u ≤ 2 / 3 then p₂ u else ((2 + clamp01 (3 * u - 2) : ℝ) : ℂ) * (v_b : ℂ)
  have hp : Continuous p := Continuous.if_le hp₂
    ((Complex.continuous_ofReal.comp
      (continuous_const.add (continuous_clamp01.comp (by fun_prop)))).mul continuous_const)
    continuous_id continuous_const fun u hu => by
      subst hu
      dsimp only [p₂]
      have hnot : ¬ ((2 / 3 : ℝ) ≤ 1 / 3) := by norm_num
      have h1 : (3 : ℝ) * (2 / 3) - 1 = 1 := by norm_num
      have h0 : (3 : ℝ) * (2 / 3) - 2 = 0 := by norm_num
      rw [ite_eq_right hnot, h1, h0, clamp01_of_le_zero le_rfl, hb.eq_end 1 le_rfl]
      norm_num
  have hp0 : p 0 = 0 := by
    dsimp only [p, p₂, p₁]
    rw [ite_eq_left (by norm_num : (0 : ℝ) ≤ 2 / 3),
      ite_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 3),
      mul_zero, clamp01_of_le_zero le_rfl, Complex.ofReal_zero, zero_mul]
  have hp1_norm : ‖p 1‖ = 3 := by
    dsimp only [p]
    have hnot : ¬ ((1 : ℝ) ≤ 2 / 3) := by norm_num
    have h1 : (3 : ℝ) * 1 - 2 = 1 := by norm_num
    rw [ite_eq_right hnot, h1, clamp01_of_one_le le_rfl,
      norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]
    norm_num
  have hp_cases : ∀ u,
      (‖p u‖ < 1) ∨ (p u = (u_b : ℂ)) ∨ (∃ s, p u = γ_b s) ∨ (p u = 2 * (v_b : ℂ)) ∨ (2 < ‖p u‖) := by
    intro u
    by_cases hu2 : u ≤ 2 / 3
    · rw [show p u = p₂ u from ite_eq_left hu2]
      by_cases hu1 : u ≤ 1 / 3
      · rw [show p₂ u = p₁ u from ite_eq_left hu1]
        have hcl := clamp01_mem_Icc (3 * u)
        rcases hcl.2.lt_or_eq with hlt | heq
        · left
          dsimp [p₁]
          rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hcl.1]
          exact hlt
        · right; left
          dsimp [p₁]
          rw [heq, Complex.ofReal_one, one_mul]
      · rw [show p₂ u = γ_b (3 * u - 1) from ite_eq_right hu1]
        exact Or.inr (Or.inr (Or.inl ⟨3 * u - 1, rfl⟩))
    · rw [show p u = ((2 + clamp01 (3 * u - 2) : ℝ) : ℂ) * (v_b : ℂ) from ite_eq_right hu2]
      have hcl := clamp01_mem_Icc (3 * u - 2)
      rcases hcl.1.eq_or_lt with heq | hgt
      · right; right; right; left
        rw [← heq, add_zero, Complex.ofReal_ofNat]
      · right; right; right; right
        rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
          Real.norm_of_nonneg (by linarith)]
        linarith
  have hg_norm : ∀ t, ‖g t‖ = 1 := norm_circleArc zero_le_one u_b α_a α_c
  have hg_ne0 : ∀ t, g t ≠ 0 := fun t ht => by
    have := hg_norm t; rw [ht, norm_zero] at this; linarith
  have hk_norm_bounds : ∀ t, 1 ≤ ‖k t‖ ∧ ‖k t‖ ≤ 2 := by
    intro t
    by_cases ht2 : t ≤ 2
    · rw [show k t = k₁ t from ite_eq_left ht2]
      by_cases ht1 : t ≤ 1
      · rw [show k₁ t = γ_a t from ite_eq_left ht1]
        exact ha.norm_bounds t
      · rw [show k₁ t = circleArc 2 v_b β_a β_c (t - 1) from ite_eq_right ht1]
        rw [norm_circleArc (by norm_num) v_b β_a β_c (t - 1)]
        exact ⟨by norm_num, le_rfl⟩
    · rw [show k t = γ_c (3 - t) from ite_eq_right ht2]
      exact hc.norm_bounds (3 - t)
  have hk_ne0 : ∀ t, k t ≠ 0 := fun t ht => by
    have := (hk_norm_bounds t).1; rw [ht, norm_zero] at this; linarith
  have hgp : ∀ u, ∀ t ∈ Icc (0 : ℝ) 1, g t ≠ p u := by
    intro u t ht h_eq
    have hgn := hg_norm t
    rcases hp_cases u with h1 | h2 | ⟨s, h3⟩ | h4 | h5
    · linarith [h_eq ▸ h1]
    · apply circleArc_ne_base zero_lt_one u_b hα_a0 hα_a2 hα_c0 hα_c2 ht
      simpa using h_eq.trans h2
    · rw [h3] at h_eq
      have hbn : ‖γ_b s‖ = 1 := h_eq ▸ hgn
      have hs0 : s ≤ 0 := (hb.norm_eq_one_iff s).mp hbn
      have hbu : γ_b s = (u_b : ℂ) := hb.eq_start s hs0
      apply circleArc_ne_base zero_lt_one u_b hα_a0 hα_a2 hα_c0 hα_c2 ht
      simpa using h_eq.trans hbu
    · have : ‖(2 : ℂ) * (v_b : ℂ)‖ = 2 := by simp
      linarith [h_eq ▸ h4 ▸ this]
    · linarith [h_eq ▸ h5]
  have hkp : ∀ u, ∀ t ∈ Icc (0 : ℝ) 3, k t ≠ p u := by
    intro u t ht h_eq
    have hkn := hk_norm_bounds t
    rcases hp_cases u with h1 | h2 | ⟨s, h3⟩ | h4 | h5
    · linarith [h_eq ▸ h1, hkn.1]
    · have hpu : p u = γ_b 0 := h2.trans (hb.eq_start 0 le_rfl).symm
      rw [hpu] at h_eq
      by_cases ht2 : t ≤ 2
      · rw [show k t = k₁ t from ite_eq_left ht2] at h_eq
        by_cases ht1 : t ≤ 1
        · rw [show k₁ t = γ_a t from ite_eq_left ht1] at h_eq
          exact hab_disj t 0 h_eq
        · rw [show k₁ t = circleArc 2 v_b β_a β_c (t - 1) from ite_eq_right ht1] at h_eq
          have h1 : ‖circleArc 2 v_b β_a β_c (t - 1)‖ = 2 :=
            norm_circleArc (by norm_num) v_b β_a β_c (t - 1)
          have h2' : ‖γ_b 0‖ = 1 := (hb.norm_eq_one_iff 0).mpr le_rfl
          linarith [h_eq ▸ h1]
      · rw [show k t = γ_c (3 - t) from ite_eq_right ht2] at h_eq
        exact hcb_disj (3 - t) 0 h_eq
    · rw [h3] at h_eq
      by_cases ht2 : t ≤ 2
      · rw [show k t = k₁ t from ite_eq_left ht2] at h_eq
        by_cases ht1 : t ≤ 1
        · rw [show k₁ t = γ_a t from ite_eq_left ht1] at h_eq
          exact hab_disj t s h_eq
        · rw [show k₁ t = circleArc 2 v_b β_a β_c (t - 1) from ite_eq_right ht1] at h_eq
          have h1 : ‖circleArc 2 v_b β_a β_c (t - 1)‖ = 2 :=
            norm_circleArc (by norm_num) v_b β_a β_c (t - 1)
          have hs1 : 1 ≤ s := (hb.norm_eq_two_iff s).mp (h_eq ▸ h1)
          have hbs : γ_b s = 2 * (v_b : ℂ) := hb.eq_end s hs1
          apply circleArc_ne_base (by norm_num : (0 : ℝ) < 2) v_b hβ_a0 hβ_a2 hβ_c0 hβ_c2
            (t := t - 1) ⟨by linarith, by linarith⟩
          simpa using h_eq.trans hbs
      · rw [show k t = γ_c (3 - t) from ite_eq_right ht2] at h_eq
        exact hcb_disj (3 - t) s h_eq
    · have hpv : p u = γ_b 1 := h4.trans (hb.eq_end 1 le_rfl).symm
      rw [hpv] at h_eq
      by_cases ht2 : t ≤ 2
      · rw [show k t = k₁ t from ite_eq_left ht2] at h_eq
        by_cases ht1 : t ≤ 1
        · rw [show k₁ t = γ_a t from ite_eq_left ht1] at h_eq
          exact hab_disj t 1 h_eq
        · rw [show k₁ t = circleArc 2 v_b β_a β_c (t - 1) from ite_eq_right ht1] at h_eq
          apply circleArc_ne_base (by norm_num : (0 : ℝ) < 2) v_b hβ_a0 hβ_a2 hβ_c0 hβ_c2
            (t := t - 1) ⟨by linarith, by linarith⟩
          simpa [hb.eq_end 1 le_rfl] using h_eq
      · rw [show k t = γ_c (3 - t) from ite_eq_right ht2] at h_eq
        exact hcb_disj (3 - t) 1 h_eq
    · linarith [h_eq ▸ h5, hkn.2]
  have hturn_eq := turn_eq_of_path hg hk zero_le_one (by norm_num : (0 : ℝ) ≤ 3)
    (hg0.trans hk0.symm) (hg1.trans hk3.symm) hp
    (fun t => by rw [hp0]; exact hg_ne0 t)
    (fun t => by rw [hp0]; exact hk_ne0 t)
    hgp hkp
    (fun t _ => by rw [hp1_norm, hg_norm t]; norm_num)
    (fun t _ => by rw [hp1_norm]; linarith [(hk_norm_bounds t).2])
  simp only [hp0, sub_zero] at hturn_eq
  have hturn_g : turn g 0 1 = α_c - α_a := turn_circleArc zero_lt_one u_b α_a α_c
  have hk_01 : turn k 0 1 = turn γ_a 0 1 := by
    let f : ℝ → ℝ := fun t => min t 1
    have hf : Continuous f := by fun_prop
    have hkf : (fun t => k (f t)) = fun t => γ_a (f t) := by
      ext t
      have h1 : f t ≤ 1 := min_le_right t 1
      have h2 : f t ≤ 2 := h1.trans (by norm_num)
      dsimp only [k, k₁]
      rw [ite_eq_left h2, ite_eq_left h1]
    have h_lhs := turn_comp hk hk_ne0 hf 0 1
    have h_rhs := turn_comp ha.continuous ha.ne_zero hf 0 1
    have hf0 : f 0 = 0 := min_eq_left zero_le_one
    have hf1 : f 1 = 1 := min_eq_right le_rfl
    rw [hf0, hf1] at h_lhs h_rhs
    rw [← h_lhs, hkf, h_rhs]
  have hk_12 : turn k 1 2 = β_c - β_a := by
    let f : ℝ → ℝ := fun t => 1 + clamp01 t
    have hf : Continuous f := continuous_const.add continuous_clamp01
    have hkf : (fun t => k (f t)) = fun t => circleArc 2 v_b β_a β_c (clamp01 t) := by
      ext t
      have hcl := clamp01_mem_Icc t
      have h2 : f t ≤ 2 := by dsimp [f]; linarith [hcl.2]
      rw [show k (f t) = k₁ (f t) from ite_eq_left h2]
      dsimp only [k₁]
      by_cases h1 : f t ≤ 1
      · have hcl0 : clamp01 t = 0 := le_antisymm (by dsimp [f] at h1; linarith) hcl.1
        have hft1 : f t = 1 := by dsimp [f]; rw [hcl0, add_zero]
        rw [ite_eq_left h1, hft1, hcl0, ha.eq_end 1 le_rfl, circleArc_zero, hva]
        rfl
      · rw [ite_eq_right h1]
        dsimp [f]
        ring_nf
    have hca_ne0 : ∀ t, circleArc 2 v_b β_a β_c t ≠ 0 := fun t ht => by
      have := norm_circleArc (by norm_num : (0 : ℝ) ≤ 2) v_b β_a β_c t
      rw [ht, norm_zero] at this; linarith
    have h_lhs := turn_comp hk hk_ne0 hf 0 1
    have h_rhs := turn_comp (continuous_circleArc 2 v_b β_a β_c) hca_ne0 continuous_clamp01 0 1
    have hf0 : f 0 = 1 := by simp [f, clamp01_of_le_zero le_rfl]
    have hf1 : f 1 = 2 := by simp [f, clamp01_of_one_le le_rfl]; norm_num
    rw [hf0, hf1] at h_lhs
    rw [clamp01_of_le_zero le_rfl, clamp01_of_one_le le_rfl] at h_rhs
    rw [← h_lhs, hkf, h_rhs, turn_circleArc (by norm_num : (0 : ℝ) < 2) v_b β_a β_c]
  have hk_23 : turn k 2 3 = - turn γ_c 0 1 := by
    let f : ℝ → ℝ := fun t => max 2 (3 - t)
    have hf : Continuous f := by fun_prop
    have hkf : (fun t => k (f t)) = fun t => γ_c (3 - f t) := by
      ext t
      have h2 : 2 ≤ f t := le_max_left 2 (3 - t)
      rcases h2.eq_or_lt with heq | hlt
      · rw [← heq]
        dsimp only [k, k₁]
        have h22 : (2 : ℝ) ≤ 2 := le_rfl
        have h21 : ¬ ((2 : ℝ) ≤ 1) := by norm_num
        have h2_sub : (2 : ℝ) - 1 = 1 := by norm_num
        have h3_sub : (3 : ℝ) - 2 = 1 := by norm_num
        rw [ite_eq_left h22, ite_eq_right h21, h2_sub, h3_sub, circleArc_one,
          hc.eq_end 1 le_rfl, hvc]
        rfl
      · exact ite_eq_right (not_le.mpr hlt)
    have h_lhs := turn_comp hk hk_ne0 hf 1 0
    have h_rhs := turn_comp (f := fun t => 3 - f t) hc.continuous hc.ne_zero
      (continuous_const.sub hf) 1 0
    have hf1 : f 1 = 2 := by dsimp [f]; norm_num
    have hf0 : f 0 = 3 := by dsimp [f]; norm_num
    rw [hf1, hf0] at h_lhs
    have h3f1 : 3 - f 1 = 1 := by rw [hf1]; norm_num
    have h3f0 : 3 - f 0 = 0 := by rw [hf0]; norm_num
    rw [h3f1, h3f0] at h_rhs
    have hadd := turn_add hc.continuous hc.ne_zero 0 1 0
    rw [turn_self hc.continuous hc.ne_zero 0] at hadd
    rw [← h_lhs, hkf, h_rhs]
    linarith
  have hk_add1 := turn_add hk hk_ne0 0 1 2
  have hk_add2 := turn_add hk hk_ne0 0 2 3
  linarith

/-- Three pairwise disjoint paths across the annulus `closedBall 0 2 \ ball 0 1` preserve the
cyclic order of their endpoints on `Circle`. -/
theorem annulus_paths_preserve_circleCyclic
    {γ₁ γ₂ γ₃ : ℝ → ℂ} {u₁ u₂ u₃ v₁ v₂ v₃ : Circle}
    (h₁ : IsAnnulusPath γ₁ u₁ v₁) (h₂ : IsAnnulusPath γ₂ u₂ v₂) (h₃ : IsAnnulusPath γ₃ u₃ v₃)
    (h12 : ∀ s t, γ₁ s ≠ γ₂ t) (h23 : ∀ s t, γ₂ s ≠ γ₃ t) (h31 : ∀ s t, γ₃ s ≠ γ₁ t) :
    GM19.CircleCyclic u₁ u₂ u₃ ↔ GM19.CircleCyclic v₁ v₂ v₃ := by
  have h21 : ∀ s t, γ₂ s ≠ γ₁ t := fun s t h => h12 t s h.symm
  have h32 : ∀ s t, γ₃ s ≠ γ₂ t := fun s t h => h23 t s h.symm
  have h13 : ∀ s t, γ₁ s ≠ γ₃ t := fun s t h => h31 t s h.symm
  have hv12 : v₁ ≠ v₂ := fun h => h12 1 1 (by rw [h₁.eq_end 1 le_rfl, h₂.eq_end 1 le_rfl, h])
  have hv23 : v₂ ≠ v₃ := fun h => h23 1 1 (by rw [h₂.eq_end 1 le_rfl, h₃.eq_end 1 le_rfl, h])
  have hv13 : v₁ ≠ v₃ := fun h => h13 1 1 (by rw [h₁.eq_end 1 le_rfl, h₃.eq_end 1 le_rfl, h])
  have hu12 : u₁ ≠ u₂ := fun h => h12 0 0 (by rw [h₁.eq_start 0 le_rfl, h₂.eq_start 0 le_rfl, h])
  have hu23 : u₂ ≠ u₃ := fun h => h23 0 0 (by rw [h₂.eq_start 0 le_rfl, h₃.eq_start 0 le_rfl, h])
  have hu13 : u₁ ≠ u₃ := fun h => h13 0 0 (by rw [h₁.eq_start 0 le_rfl, h₃.eq_start 0 le_rfl, h])
  have hexp_2pi : Circle.exp (2 * Real.pi) = 1 := Circle.exp_two_pi
  have h_imp : ∀ {γa γb γc : ℝ → ℂ} {ua ub uc va vb vc : Circle},
      IsAnnulusPath γa ua va → IsAnnulusPath γb ub vb → IsAnnulusPath γc uc vc →
      (∀ s t, γa s ≠ γb t) → (∀ s t, γb s ≠ γc t) → (∀ s t, γc s ≠ γa t) →
      va ≠ vb → vb ≠ vc → va ≠ vc →
      GM19.CircleCyclic ua ub uc → GM19.CircleCyclic va vb vc := by
    intro γa γb γc ua ub uc va vb vc ha hb hc hab hbc hca hvab hvbc hvac ⟨s, t, hs0, hst, ht2, hub, huc⟩
    have hba : ∀ x y, γb x ≠ γa y := fun x y h => hab y x h.symm
    have hcb : ∀ x y, γc x ≠ γb y := fun x y h => hbc y x h.symm
    have hac : ∀ x y, γa x ≠ γc y := fun x y h => hca y x h.symm
    obtain ⟨t', ht'0, ht'2, hvb'⟩ := GM19.exists_angle (z := va⁻¹ * vb)
      (fun h => hvab (inv_mul_eq_one.mp h))
    have hvb : vb = va * Circle.exp t' := by rw [← hvb', mul_inv_cancel_left]
    obtain ⟨s', hs'0, hs'2, hvc'⟩ := GM19.exists_angle (z := va⁻¹ * vc)
      (fun h => hvac (inv_mul_eq_one.mp h))
    have hvc : vc = va * Circle.exp s' := by rw [← hvc', mul_inv_cancel_left]
    rcases lt_trichotomy t' s' with hlt | rfl | hgt
    · exact ⟨t', s', ht'0, hlt, hs'2, hvb, hvc⟩
    · exact (hvbc (hvb.trans hvc.symm)).elim
    · exfalso
      have eq1 := turn_diff_eq_of_avoid_annulus_path ha hc hb hac hbc
        (α_a := 2 * Real.pi - t) (α_c := 2 * Real.pi - t + s)
        (β_a := 2 * Real.pi - s') (β_c := t' - s')
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by rw [huc, mul_assoc, ← Circle.exp_add, show t + (2 * Real.pi - t) = 2 * Real.pi by ring,
          hexp_2pi, mul_one])
        (by rw [huc, hub, mul_assoc, ← Circle.exp_add,
          show t + (2 * Real.pi - t + s) = s + 2 * Real.pi by ring, exp_add_two_pi])
        (by rw [hvc, mul_assoc, ← Circle.exp_add,
          show s' + (2 * Real.pi - s') = 2 * Real.pi by ring, hexp_2pi, mul_one])
        (by rw [hvc, hvb, mul_assoc, ← Circle.exp_add, show s' + (t' - s') = t' by ring])
      have eq2 := turn_diff_eq_of_avoid_annulus_path hb ha hc hba hca
        (α_a := s) (α_c := t) (β_a := t') (β_c := s')
        hs0 (hst.trans ht2) (hs0.trans hst) ht2
        ht'0 ht'2 hs'0 hs'2 hub huc hvb hvc
      have eq3 := turn_diff_eq_of_avoid_annulus_path hc hb ha hcb hab
        (α_a := t - s) (α_c := 2 * Real.pi - s)
        (β_a := 2 * Real.pi - t' + s') (β_c := 2 * Real.pi - t')
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by rw [hub, huc, mul_assoc, ← Circle.exp_add, show s + (t - s) = t by ring])
        (by rw [hub, mul_assoc, ← Circle.exp_add,
          show s + (2 * Real.pi - s) = 2 * Real.pi by ring, hexp_2pi, mul_one])
        (by rw [hvb, hvc, mul_assoc, ← Circle.exp_add,
          show t' + (2 * Real.pi - t' + s') = s' + 2 * Real.pi by ring, exp_add_two_pi])
        (by rw [hvb, mul_assoc, ← Circle.exp_add,
          show t' + (2 * Real.pi - t') = 2 * Real.pi by ring, hexp_2pi, mul_one])
      linarith [Real.pi_pos, eq1, eq2, eq3]
  refine ⟨h_imp h₁ h₂ h₃ h12 h23 h31 hv12 hv23 hv13, fun hcyc_v => ?_⟩
  by_contra hnot_u
  obtain ⟨s, hs0, hs2, hub'⟩ := GM19.exists_angle (z := u₁⁻¹ * u₂)
    (fun h => hu12 (inv_mul_eq_one.mp h))
  have hub : u₂ = u₁ * Circle.exp s := by rw [← hub', mul_inv_cancel_left]
  obtain ⟨t, ht0, ht2, huc'⟩ := GM19.exists_angle (z := u₁⁻¹ * u₃)
    (fun h => hu13 (inv_mul_eq_one.mp h))
  have huc : u₃ = u₁ * Circle.exp t := by rw [← huc', mul_inv_cancel_left]
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact hnot_u ⟨s, t, hs0, hst, ht2, hub, huc⟩
  · exact hu23 (hub.trans huc.symm)
  · have hcyc_u132 : GM19.CircleCyclic u₁ u₃ u₂ := ⟨t, s, ht0, hts, hs2, huc, hub⟩
    have hcyc_v132 : GM19.CircleCyclic v₁ v₃ v₂ :=
      h_imp h₁ h₃ h₂ h13 h32 h21 hv13 hv23.symm hv12 hcyc_u132
    rcases hcyc_v with ⟨sv, tv, hsv0, hstv, htv2, hvb, hvc⟩
    rcases hcyc_v132 with ⟨sv', tv', hsv'0, hstv', htv'2, hvc', hvb'⟩
    have heq_b : Circle.exp sv = Circle.exp tv' :=
      mul_left_cancel (hvb.symm.trans hvb')
    have heq_c : Circle.exp tv = Circle.exp sv' :=
      mul_left_cancel (hvc.symm.trans hvc')
    have h_sv_eq : sv = tv' := by
      by_contra hne
      exact circle_exp_ne hne (by rw [abs_lt]; constructor <;> linarith) heq_b
    have h_tv_eq : tv = sv' := by
      by_contra hne
      exact circle_exp_ne hne (by rw [abs_lt]; constructor <;> linarith) heq_c
    linarith

/-- Given a finite family of pairwise disjoint paths across the annulus `closedBall 0 2 \ ball 0 1`,
there is an orientation-preserving circle homeomorphism sending their inner endpoints to their
outer endpoints. -/
theorem exists_circle_interp_of_annulus_paths
    {Y : Type} [Finite Y] {γ : Y → ℝ → ℂ} {u v : Y → Circle}
    (hγ : ∀ i, IsAnnulusPath (γ i) (u i) (v i))
    (hdisj : ∀ i j, i ≠ j → ∀ s t, γ i s ≠ γ j t) :
    ∃ τ : Circle ≃ₜ Circle, PreservesCircleOrientation τ ∧ ∀ i, τ (u i) = v i := by
  have hu_inj : Function.Injective u := by
    intro i j hij
    by_contra hne
    exact hdisj i j hne 0 0 (by rw [(hγ i).eq_start 0 le_rfl, (hγ j).eq_start 0 le_rfl, hij])
  have hv_inj : Function.Injective v := by
    intro i j hij
    by_contra hne
    exact hdisj i j hne 1 1 (by rw [(hγ i).eq_end 1 le_rfl, (hγ j).eq_end 1 le_rfl, hij])
  have hex : ∀ i : Y, ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ ee a = u i := fun i => by
    obtain ⟨x, hx⟩ := ee_surjective (u i)
    refine ⟨Int.fract x, Int.fract_nonneg x, Int.fract_lt_one x, ?_⟩
    rw [← hx]
    exact (ee_eq_iff.mpr ⟨⌊x⌋, (Int.fract_add_floor x).symm⟩).symm
  choose a ha0 ha1 ha_eq using hex
  have ha_inj : Function.Injective a := fun i j hij => hu_inj (by rw [← ha_eq i, ← ha_eq j, hij])
  have hw : ∀ i j, a i < a j + 1 := fun i j => by linarith [ha1 i, ha0 j]
  have hc : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (GM19.CircleCyclic (v x) (v y) (v z) ↔ CycOrder (a x) (a y) (a z)) := by
    intro x y z hxy hyz hxz
    have hcyc := annulus_paths_preserve_circleCyclic (hγ x) (hγ y) (hγ z)
      (hdisj x y hxy) (hdisj y z hyz) (hdisj z x hxz.symm)
    rw [← hcyc, ← ha_eq x, ← ha_eq y, ← ha_eq z]
    exact circleCyclic_ee_iff (hw x y) (hw y x) (hw y z) (hw z y) (hw x z) (hw z x)
      (ha_inj.ne hxy) (ha_inj.ne hyz) (ha_inj.ne hxz)
  obtain ⟨τ, hτ, hτ_eq⟩ := exists_circle_interp a ha_inj hw v hv_inj hc
  refine ⟨τ, hτ, fun i => ?_⟩
  rw [← ha_eq i, hτ_eq i]

/-! ## 2. Radial Resize With Explicit Inner Scaling and Cuff Sleeve Homeomorphism -/

private theorem tentMap_pos' {l w t r : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (_hwt : w < t) (hr : 0 < r) : 0 < tentMap 0 l w t r := by
  by_cases hrl : r ≤ l
  · rw [tentMap, tent_left hl hlt hr.le hrl]
    simp only [sub_zero]
    have heq : r + (w - l) * (r / l) = w * r / l := by field_simp; ring
    rw [heq]
    exact div_pos (mul_pos hw hr) hl
  · by_cases hrt : r ≤ t
    · rw [tentMap, tent_right hl hlt (le_of_not_ge hrl) hrt]
      have heq : r + (w - l) * ((t - r) / (t - l)) =
          w * ((t - r) / (t - l)) + t * ((r - l) / (t - l)) := by
        field_simp [sub_ne_zero.mpr hlt.ne']; ring
      rw [heq]
      have h1 := mul_nonneg hw.le (div_nonneg (sub_nonneg.mpr hrt) (sub_pos.mpr hlt).le)
      have h2 := mul_pos (hl.trans hlt) (div_pos (sub_pos.mpr (lt_of_not_ge hrl)) (sub_pos.mpr hlt))
      exact add_pos_of_nonneg_of_pos h1 h2
    · rw [tentMap, tent_high hl hlt (le_of_not_ge hrt), mul_zero, add_zero]
      exact hr

private noncomputable def radialFactor' (l w t r : ℝ) : ℝ :=
  tentMap 0 l w t (max l r) / max l r

private theorem radialFactor'_pos {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (r : ℝ) : 0 < radialFactor' l w t r :=
  div_pos (tentMap_pos' hl hlt hw hwt (hl.trans_le (le_max_left _ _)))
    (hl.trans_le (le_max_left _ _))

private theorem radialFactor'_mul {l w t r : ℝ} (hl : 0 < l) (hlt : l < t)
    (hr : 0 ≤ r) : radialFactor' l w t r * r = tentMap 0 l w t r := by
  by_cases hrl : r ≤ l
  · simp only [radialFactor', max_eq_left hrl]
    rw [tentMap, tent_left hl hlt hl.le le_rfl]
    simp only [sub_zero, div_self hl.ne', mul_one]
    rw [tentMap, tent_left hl hlt hr hrl]
    simp only [sub_zero]
    field_simp
  · simp only [radialFactor', max_eq_right (le_of_not_ge hrl)]
    exact div_mul_cancel₀ _ (hl.trans (lt_of_not_ge hrl)).ne'

private theorem radialFactor'_continuous {l w t : ℝ} (hl : 0 < l) (_hlt : l < t) :
    Continuous (radialFactor' l w t) := by
  unfold radialFactor' tentMap tent
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro r
    exact (hl.trans_le (le_max_left _ _)).ne'

private noncomputable def radialMap' (l w t : ℝ) (z : ℂ) : ℂ :=
  radialFactor' l w t ‖z‖ • z

private theorem radialMap'_norm {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (z : ℂ) :
    ‖radialMap' l w t z‖ = tentMap 0 l w t ‖z‖ := by
  rw [radialMap', norm_smul, Real.norm_eq_abs,
    abs_of_pos (radialFactor'_pos hl hlt hw hwt _)]
  exact radialFactor'_mul hl hlt (norm_nonneg z)

private theorem radialMap'_inverse {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (z : ℂ) :
    radialMap' w l t (radialMap' l w t z) = z := by
  by_cases hz : z = 0
  · simp [hz, radialMap']
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have heq : radialFactor' w l t (tentMap 0 l w t ‖z‖) * radialFactor' l w t ‖z‖ = 1 := by
    apply mul_right_cancel₀ hn.ne'
    rw [one_mul, mul_assoc, radialFactor'_mul hl hlt hn.le,
      radialFactor'_mul hw hwt (tentMap_pos' hl hlt hw hwt hn).le,
      tentMap_inv hl hlt hw hwt]
  change radialFactor' w l t ‖radialMap' l w t z‖ • (radialFactor' l w t ‖z‖ • z) = z
  rw [radialMap'_norm hl hlt hw hwt, smul_smul, heq, one_smul]

/-- Radial disc resize that also records the exact linear scaling `(w / l) • z` on `closedBall 0 l`. -/
theorem exists_radial_disc_resize_scale {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) :
    ∃ Θ : ℂ ≃ₜ ℂ,
      (∀ z, t ≤ ‖z‖ → Θ z = z) ∧
      (∀ z, ‖z‖ ≤ l → Θ z = (w / l) • z) ∧
      Θ '' closedBall 0 l = closedBall 0 w := by
  let Θ : ℂ ≃ₜ ℂ := {
    toFun := radialMap' l w t
    invFun := radialMap' w l t
    left_inv := radialMap'_inverse hl hlt hw hwt
    right_inv := radialMap'_inverse hw hwt hl hlt
    continuous_toFun := (radialFactor'_continuous hl hlt).comp continuous_norm |>.smul continuous_id
    continuous_invFun := (radialFactor'_continuous hw hwt).comp continuous_norm |>.smul continuous_id }
  have hscale : ∀ z : ℂ, ‖z‖ ≤ l → Θ z = (w / l) • z := by
    intro z hz
    change radialFactor' l w t ‖z‖ • z = _
    congr 1
    simp only [radialFactor', max_eq_left hz, tentMap, tent_left hl hlt hl.le le_rfl,
      sub_zero, div_self hl.ne', mul_one]
    congr 1
    ring
  refine ⟨Θ, ?_, hscale, ?_⟩
  · intro z hz
    change radialFactor' l w t ‖z‖ • z = z
    have hn : l ≤ ‖z‖ := hlt.le.trans hz
    have hnpos : 0 < ‖z‖ := hl.trans_le hn
    simp only [radialFactor', max_eq_right hn, tentMap, tent_high hl hlt hz,
      mul_zero, add_zero, div_self hnpos.ne', one_smul]
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_closedBall_zero_iff] at hz ⊢
      rw [hscale z hz, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hw hl)]
      exact (mul_le_mul_of_nonneg_left hz (div_pos hw hl).le).trans_eq (div_mul_cancel₀ w hl.ne')
    · intro z hz
      rw [mem_closedBall_zero_iff] at hz
      let v : ℂ := (l / w) • z
      have hv : ‖v‖ ≤ l := by
        dsimp only [v]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hw)]
        exact (mul_le_mul_of_nonneg_left hz (div_pos hl hw).le).trans_eq (div_mul_cancel₀ l hw.ne')
      refine ⟨v, mem_closedBall_zero_iff.mpr hv, ?_⟩
      rw [hscale v hv]
      dsimp only [v]
      rw [smul_smul]
      have heq : w / l * (l / w) = 1 := by field_simp
      rw [heq, one_smul]

private theorem exists_inverse_on_compact {K : Set ℂ} (hK : IsCompact K) {c : ℂ → S}
    (hc : ContinuousOn c K) (hi : InjOn c K) :
    ∃ c' : S → ℂ, ContinuousOn c' (c '' K) ∧ MapsTo c' (c '' K) K ∧
      LeftInvOn c' c K ∧ RightInvOn c' c (c '' K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → S := K.domRestrict c
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  have hfi : Function.Injective f := fun a b he => Subtype.ext (hi a.2 b.2 he)
  have hem := hf.isClosedEmbedding hfi
  let e : K ≃ₜ range f := hem.isEmbedding.toHomeomorph
  have hrange : range f = c '' K := by
    ext x; constructor
    · rintro ⟨z, rfl⟩; exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
  let c' : S → ℂ := fun x => if hx : x ∈ range f then (e.symm ⟨x, hx⟩).1 else 0
  have hval : ∀ z (hz : z ∈ K), c' (c z) = z := fun z hz => by
    have hx : c z ∈ range f := ⟨⟨z, hz⟩, rfl⟩
    show (if hx : c z ∈ range f then (e.symm ⟨c z, hx⟩).1 else 0) = z
    rw [dite_eq_left hx]
    have : (⟨c z, hx⟩ : range f) = e ⟨z, hz⟩ := rfl
    rw [this, e.symm_apply_apply]
  refine ⟨c', ?_, ?_, fun z hz => hval z hz, ?_⟩
  · rw [← hrange, continuousOn_iff_continuous_domRestrict]
    have : (range f).domRestrict c' = fun x : range f => (e.symm x).1 := by
      funext x
      show (if hx : x.1 ∈ range f then (e.symm ⟨x.1, hx⟩).1 else 0) = _
      rw [dite_eq_left x.2]
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous
  · rintro _ ⟨z, hz, rfl⟩; rw [hval z hz]; exact hz
  · rintro _ ⟨z, hz, rfl⟩; show c (c' (c z)) = c z; rw [hval z hz]

omit [T2Space S] in
private theorem exists_joined_collar_coordinates_eq
    {A B E : Set S} (c₁ c₂ : ℂ → S)
    (hc₁ : ContinuousOn c₁ (closedBall 0 2)) (hi₁ : InjOn c₁ (closedBall 0 2))
    (hc₂ : ContinuousOn c₂ (closedBall 0 2)) (hi₂ : InjOn c₂ (closedBall 0 2))
    (hA : c₁ '' closedBall 0 1 = A) (hB₁ : c₁ '' closedBall 0 2 = B)
    (hB₂ : c₂ '' closedBall 0 1 = B) (hE : c₂ '' closedBall 0 2 = E)
    (hbd : c₂ '' sphere 0 2 = discBd E)
    (hcompat : ∀ z : ℂ, ‖z‖ = 2 → c₁ z = c₂ (collarOuterStep z)) :
    ∃ c : ℂ → S, ContinuousOn c (closedBall 0 3) ∧ InjOn c (closedBall 0 3) ∧
      c '' closedBall 0 1 = A ∧ c '' closedBall 0 2 = B ∧
      c '' closedBall 0 3 = E ∧ c '' sphere 0 3 = discBd E ∧
      (∀ z : ℂ, ‖z‖ ≤ 2 → c z = c₁ z) := by
  let c : ℂ → S := fun z => if ‖z‖ ≤ 2 then c₁ z else c₂ (collarOuterStep z)
  have hcinner : ∀ z, ‖z‖ ≤ 2 → c z = c₁ z := fun z hz => ite_eq_left hz
  have hcouter : ∀ z, 2 ≤ ‖z‖ → c z = c₂ (collarOuterStep z) := by
    intro z hz
    rcases eq_or_lt_of_le hz with heq | hlt
    · rw [hcinner z heq.ge]; exact hcompat z heq.symm
    · exact ite_eq_right (not_le.mpr hlt)
  have hJ : ∀ z, 2 ≤ ‖z‖ → ‖z‖ ≤ 3 → collarOuterStep z ∈ closedBall 0 2 := by
    intro z hlo hhi
    rw [mem_closedBall_zero_iff, collarOuterStep_norm hlo]; linarith
  have hBc₂ : ∀ w ∈ closedBall (0 : ℂ) 2, c₂ w ∈ B → ‖w‖ ≤ 1 := by
    intro w hw hBw
    obtain ⟨v, hv, heq⟩ := hB₂.symm ▸ hBw
    have hvw := hi₂ (closedBall_subset_closedBall (by norm_num) hv) hw heq
    exact hvw ▸ mem_closedBall_zero_iff.mp hv
  have hccont : ContinuousOn c (closedBall 0 3) := by
    let R : Set ℂ := closedBall 0 3 ∩ {z | 2 ≤ ‖z‖}
    have hR : IsClosed R := isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)
    have hcontinner : ContinuousOn c (closedBall 0 2) :=
      hc₁.congr (fun z hz => hcinner z (mem_closedBall_zero_iff.mp hz))
    have hcontouter : ContinuousOn c R := by
      apply (hc₂.comp continuous_collarOuterStep.continuousOn ?_).congr
        (fun z hz => hcouter z hz.2)
      intro z hz
      exact hJ z hz.2 (mem_closedBall_zero_iff.mp hz.1)
    have hcover : closedBall (0 : ℂ) 2 ∪ R = closedBall 0 3 := by
      ext z; constructor
      · rintro (hz | hz)
        · exact closedBall_subset_closedBall (by norm_num) hz
        · exact hz.1
      · intro hz
        by_cases hz2 : ‖z‖ ≤ 2
        · exact Or.inl (mem_closedBall_zero_iff.mpr hz2)
        · exact Or.inr ⟨hz, le_of_not_ge hz2⟩
    exact hcover ▸ hcontinner.union_of_isClosed hcontouter isClosed_closedBall hR
  have hcB : c '' closedBall 0 2 = B := by
    rw [← hB₁]
    exact image_congr (fun z hz => hcinner z (mem_closedBall_zero_iff.mp hz))
  have hcA : c '' closedBall 0 1 = A := by
    rw [← hA]
    exact image_congr (fun z hz => hcinner z ((mem_closedBall_zero_iff.mp hz).trans (by norm_num)))
  have hcEsub : c '' closedBall 0 3 ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hz2 : ‖z‖ ≤ 2
    · rw [hcinner z hz2]
      have hzB : c₁ z ∈ B := hB₁ ▸ mem_image_of_mem c₁ (mem_closedBall_zero_iff.mpr hz2)
      obtain ⟨w, hw, heq⟩ := hB₂.symm ▸ hzB
      rw [← heq]
      exact hE ▸ mem_image_of_mem c₂ (closedBall_subset_closedBall (by norm_num) hw)
    · rw [hcouter z (le_of_not_ge hz2)]
      exact hE ▸ mem_image_of_mem c₂ (hJ z (le_of_not_ge hz2) (mem_closedBall_zero_iff.mp hz))
  have hcEsurj : E ⊆ c '' closedBall 0 3 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hE.symm ▸ hx
    by_cases hw1 : ‖w‖ ≤ 1
    · have hwB : c₂ w ∈ B := hB₂ ▸ mem_image_of_mem c₂ (mem_closedBall_zero_iff.mpr hw1)
      obtain ⟨z, hz, heq⟩ := hcB.symm ▸ hwB
      exact ⟨z, closedBall_subset_closedBall (by norm_num) hz, heq⟩
    · obtain ⟨z, hzn, hzJ⟩ := exists_collarOuterStep_preimage (le_of_not_ge hw1)
      have hz2 : 2 ≤ ‖z‖ := by rw [hzn]; linarith [le_of_not_ge hw1]
      refine ⟨z, mem_closedBall_zero_iff.mpr ?_, ?_⟩
      · rw [hzn]; linarith [mem_closedBall_zero_iff.mp hw]
      · rw [hcouter z hz2, hzJ]
  have hci : InjOn c (closedBall 0 3) := by
    intro z hz w hw heq
    by_cases hz2 : ‖z‖ ≤ 2
    · by_cases hw2 : ‖w‖ ≤ 2
      · rw [hcinner z hz2, hcinner w hw2] at heq
        exact hi₁ (mem_closedBall_zero_iff.mpr hz2) (mem_closedBall_zero_iff.mpr hw2) heq
      · have hwlo : 2 ≤ ‖w‖ := le_of_not_ge hw2
        have hzB : c z ∈ B := hcB ▸ mem_image_of_mem c (mem_closedBall_zero_iff.mpr hz2)
        rw [heq, hcouter w hwlo] at hzB
        have hn := hBc₂ _ (hJ w hwlo (mem_closedBall_zero_iff.mp hw)) hzB
        rw [collarOuterStep_norm hwlo] at hn
        exact False.elim (hw2 (by linarith))
    · have hzlo : 2 ≤ ‖z‖ := le_of_not_ge hz2
      by_cases hw2 : ‖w‖ ≤ 2
      · have hwB : c w ∈ B := hcB ▸ mem_image_of_mem c (mem_closedBall_zero_iff.mpr hw2)
        rw [← heq, hcouter z hzlo] at hwB
        have hn := hBc₂ _ (hJ z hzlo (mem_closedBall_zero_iff.mp hz)) hwB
        rw [collarOuterStep_norm hzlo] at hn
        exact False.elim (hz2 (by linarith))
      · have hwlo : 2 ≤ ‖w‖ := le_of_not_ge hw2
        rw [hcouter z hzlo, hcouter w hwlo] at heq
        exact collarOuterStep_injOn hzlo hwlo
          (hi₂ (hJ z hzlo (mem_closedBall_zero_iff.mp hz))
            (hJ w hwlo (mem_closedBall_zero_iff.mp hw)) heq)
  refine ⟨c, hccont, hci, hcA, hcB, hcEsub.antisymm hcEsurj, ?_, hcinner⟩
  rw [← hbd]
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hzn : ‖z‖ = 3 := mem_sphere_zero_iff_norm.mp hz
    have hz2 : 2 ≤ ‖z‖ := by rw [hzn]; norm_num
    refine ⟨collarOuterStep z, ?_, (hcouter z hz2).symm⟩
    rw [mem_sphere_zero_iff_norm, collarOuterStep_norm hz2, hzn]; norm_num
  · rintro _ ⟨w, hw, rfl⟩
    have hwn : ‖w‖ = 2 := mem_sphere_zero_iff_norm.mp hw
    obtain ⟨z, hzn, hzJ⟩ := exists_collarOuterStep_preimage (by rw [hwn]; norm_num)
    have hz3 : ‖z‖ = 3 := by rw [hzn, hwn]; norm_num
    refine ⟨z, mem_sphere_zero_iff_norm.mpr hz3, ?_⟩
    rw [hcouter z (by rw [hz3]; norm_num), hzJ]

/-- Given nested closed discs `A ⊆ B \ discBd B` and `B ⊆ E \ discBd E` in a manifold `S`, and a
finite family of pairwise disjoint paths `φ i` across the annulus `B \ discInt A` from `discBd A`
at `t = 0` to `discBd B` at `t = 1`, there is a homeomorphism `e : S ≃ₜ S` supported in `E` that
maps `A` onto `B` and sends `φ i 0` to `φ i 1` for every `i`. -/
theorem exists_cuff_sleeve_homeo
    (hman : ∀ x : S, IsManifoldPoint x)
    {A B E : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hE : IsClosedDisc E)
    (hAB : A ⊆ B \ discBd B) (hBE : B ⊆ E \ discBd E)
    {Y : Type} [Finite Y] (φ : Y → 𝕀 → S)
    (hφ_cont : ∀ i, Continuous (φ i))
    (hφ_mem : ∀ i t, φ i t ∈ B \ discInt A)
    (hφ_bdA : ∀ i t, φ i t ∈ discBd A ↔ t = 0)
    (hφ_bdB : ∀ i t, φ i t ∈ discBd B ↔ t = 1)
    (hφ_disj : ∀ i j, i ≠ j → ∀ s t, φ i s ≠ φ j t) :
    ∃ e : S ≃ₜ S, e '' A = B ∧ (∀ x, x ∉ E → e x = x) ∧ ∀ i, e (φ i 0) = φ i 1 := by
  obtain ⟨pA⟩ := hA.isOArc_discBd
  obtain ⟨c₁, c₁', hcc₁, hcc₁', hm₁, hm₁', hl₁, hr₁, hin₁, hs₁, hp₁⟩ :=
    exists_disc_collar hA hB hAB pA
  have hi₁ : InjOn c₁ (closedBall 0 2) := hl₁.injOn
  have hB₁ : c₁ '' closedBall 0 2 = B :=
    (hm₁.image_subset).antisymm fun x hx => ⟨_, hm₁' hx, hr₁ hx⟩
  have hsA₁ : c₁ '' sphere 0 1 = discBd A := by
    ext x; constructor
    · rintro ⟨z, hz, rfl⟩
      have hzn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
      have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
      have hunit : z = (unitOf z hz0 : ℂ) := by
        simpa [hzn] using (norm_mul_unitOf z hz0).symm
      rw [hunit, hp₁]
      exact (pA (unitOf z hz0)).2
    · intro hx
      let w := pA.symm ⟨x, hx⟩
      refine ⟨(w : ℂ), mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w), ?_⟩
      rw [hp₁]
      exact congrArg Subtype.val (pA.apply_symm_apply ⟨x, hx⟩)
  have hc₁'_mem_A_iff : ∀ x ∈ B, x ∈ A ↔ ‖c₁' x‖ ≤ 1 := fun x hx => by
    constructor
    · rw [← hin₁]
      rintro ⟨z, hz, rfl⟩
      rw [hl₁ (closedBall_subset_closedBall (by norm_num) hz)]
      exact mem_closedBall_zero_iff.mp hz
    · intro hn
      rw [← hr₁ hx, ← hin₁]
      exact mem_image_of_mem c₁ (mem_closedBall_zero_iff.mpr hn)
  have hc₁'_mem_bdA_iff : ∀ x ∈ B, x ∈ discBd A ↔ ‖c₁' x‖ = 1 := fun x hx => by
    constructor
    · rw [← hsA₁]
      rintro ⟨z, hz, rfl⟩
      have hz2 : z ∈ closedBall (0 : ℂ) 2 :=
        closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall hz)
      rw [hl₁ hz2]
      exact mem_sphere_zero_iff_norm.mp hz
    · intro hn
      rw [← hr₁ hx, ← hsA₁]
      exact mem_image_of_mem c₁ (mem_sphere_zero_iff_norm.mpr hn)
  have hc₁'_mem_intA_iff : ∀ x ∈ B, x ∈ discInt A ↔ ‖c₁' x‖ < 1 := fun x hx => by
    rw [discInt, mem_sdiff, hc₁'_mem_A_iff x hx, hc₁'_mem_bdA_iff x hx, lt_iff_le_and_ne]
  have hc₁'_mem_bdB_iff : ∀ x ∈ B, x ∈ discBd B ↔ ‖c₁' x‖ = 2 := fun x hx => by
    constructor
    · rw [← hs₁]
      rintro ⟨z, hz, rfl⟩
      rw [hl₁ (sphere_subset_closedBall hz)]
      exact mem_sphere_zero_iff_norm.mp hz
    · intro hn
      rw [← hr₁ hx, ← hs₁]
      exact mem_image_of_mem c₁ (mem_sphere_zero_iff_norm.mpr hn)
  let clampI : ℝ → 𝕀 := fun t => ⟨clamp01 t, clamp01_mem_Icc t⟩
  have hclampI_cont : Continuous clampI := continuous_clamp01.subtype_mk _
  let γ : Y → ℝ → ℂ := fun i t => c₁' (φ i (clampI t))
  have hγ_bounds : ∀ i t, 1 ≤ ‖γ i t‖ ∧ ‖γ i t‖ ≤ 2 := fun i t => by
    have hmem := hφ_mem i (clampI t)
    refine ⟨?_, mem_closedBall_zero_iff.mp (hm₁' hmem.1)⟩
    exact not_lt.mp ((hc₁'_mem_intA_iff _ hmem.1).not.mp hmem.2)
  have hγ_ne0 : ∀ i t, γ i t ≠ 0 := fun i t h0 => by
    have := (hγ_bounds i t).1; rw [h0, norm_zero] at this; linarith
  let u : Y → Circle := fun i => unitOf (γ i 0) (hγ_ne0 i 0)
  let v : Y → Circle := fun i => unitOf (γ i 1) (hγ_ne0 i 1)
  have hclampI_0 : clampI 0 = 0 := Subtype.ext (clamp01_of_le_zero le_rfl)
  have hclampI_1 : clampI 1 = 1 := Subtype.ext (clamp01_of_one_le le_rfl)
  have hγ0_norm : ∀ i, ‖γ i 0‖ = 1 := fun i => by
    dsimp [γ]
    rw [hclampI_0]
    exact (hc₁'_mem_bdA_iff _ (hφ_mem i 0).1).mp ((hφ_bdA i 0).mpr rfl)
  have hγ1_norm : ∀ i, ‖γ i 1‖ = 2 := fun i => by
    dsimp [γ]
    rw [hclampI_1]
    exact (hc₁'_mem_bdB_iff _ (hφ_mem i 1).1).mp ((hφ_bdB i 1).mpr rfl)
  have hu_coe : ∀ i, (u i : ℂ) = γ i 0 := fun i => by
    have := norm_mul_unitOf (γ i 0) (hγ_ne0 i 0)
    rw [hγ0_norm i, Complex.ofReal_one, one_mul] at this
    exact this
  have hv_coe : ∀ i, 2 * (v i : ℂ) = γ i 1 := fun i => by
    have := norm_mul_unitOf (γ i 1) (hγ_ne0 i 1)
    rw [hγ1_norm i, Complex.ofReal_ofNat] at this
    exact this
  have hγ_ann : ∀ i, IsAnnulusPath (γ i) (u i) (v i) := fun i =>
    { continuous := hcc₁'.comp_continuous ((hφ_cont i).comp hclampI_cont)
        (fun t => (hφ_mem i (clampI t)).1)
      norm_bounds := hγ_bounds i
      eq_start := fun t ht => by
        rw [hu_coe i]
        dsimp only [γ]
        congr 2
        exact Subtype.ext ((clamp01_of_le_zero ht).trans (clamp01_of_le_zero le_rfl).symm)
      eq_end := fun t ht => by
        rw [hv_coe i]
        dsimp only [γ]
        congr 2
        exact Subtype.ext ((clamp01_of_one_le ht).trans (clamp01_of_one_le le_rfl).symm)
      norm_eq_one_iff := fun t => by
        rw [← hc₁'_mem_bdA_iff _ (hφ_mem i (clampI t)).1, hφ_bdA i (clampI t)]
        simp only [clampI, Subtype.ext_iff, Icc.coe_zero]
        exact ⟨fun h => by
          by_contra hgt
          have hpos : 0 < t := not_le.mp hgt
          have : 0 < clamp01 t := by
            unfold clamp01
            exact lt_max_of_lt_right (lt_min hpos zero_lt_one)
          linarith, clamp01_of_le_zero⟩
      norm_eq_two_iff := fun t => by
        rw [← hc₁'_mem_bdB_iff _ (hφ_mem i (clampI t)).1, hφ_bdB i (clampI t)]
        simp only [clampI, Subtype.ext_iff, Icc.coe_one]
        exact ⟨fun h => by
          by_contra hlt
          have hlt1 : t < 1 := not_le.mp hlt
          have : clamp01 t < 1 := by
            unfold clamp01
            exact max_lt zero_lt_one (min_lt_of_left_lt hlt1)
          linarith, clamp01_of_one_le⟩ }
  have hγ_disj : ∀ i j, i ≠ j → ∀ s t, γ i s ≠ γ j t := by
    intro i j hij s t heq
    have := congrArg c₁ heq
    rw [hr₁ (hφ_mem i (clampI s)).1, hr₁ (hφ_mem j (clampI t)).1] at this
    exact hφ_disj i j hij (clampI s) (clampI t) this
  obtain ⟨τ, hτ, hτ_uv⟩ := exists_circle_interp_of_annulus_paths hγ_ann hγ_disj
  have hS2 : ∀ w : Circle, ((2 : ℝ) : ℂ) * w ∈ sphere (0 : ℂ) 2 := fun w => by
    rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, Complex.norm_real]
    norm_num
  let uB : Circle → discBd B := fun w =>
    ⟨c₁ (((2 : ℝ) : ℂ) * w), by rw [← hs₁]; exact mem_image_of_mem c₁ (hS2 w)⟩
  have huBc : Continuous uB :=
    Continuous.subtype_mk (hcc₁.comp_continuous
      (continuous_const.mul continuous_induced_dom) fun w => sphere_subset_closedBall (hS2 w)) _
  have huBi : Function.Injective uB := fun w w' he => by
    have h1 := hi₁ (sphere_subset_closedBall (hS2 w)) (sphere_subset_closedBall (hS2 w'))
      (congrArg Subtype.val he)
    exact Circle.ext (mul_left_cancel₀ (by norm_num) h1)
  have huBs : Function.Surjective uB := fun x => by
    obtain ⟨z, hz, he⟩ : x.1 ∈ c₁ '' sphere 0 2 := by rw [hs₁]; exact x.2
    have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
    refine ⟨unitOf z hz0, Subtype.ext ?_⟩
    show c₁ (((2 : ℝ) : ℂ) * unitOf z hz0) = x.1
    rw [← hzn, norm_mul_unitOf, he]
  let pB : Circle ≃ₜ discBd B :=
    huBc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective uB ⟨huBi, huBs⟩)
  have hpB : ∀ w : Circle, (pB w).1 = c₁ (((2 : ℝ) : ℂ) * w) := fun _ => rfl
  obtain ⟨c₂, c₂', hcc₂, -, hm₂, hm₂', hl₂, hr₂, hin₂, hs₂, hp₂⟩ :=
    exists_disc_collar hB hE hBE pB
  have hi₂ : InjOn c₂ (closedBall 0 2) := hl₂.injOn
  have hE₂ : c₂ '' closedBall 0 2 = E :=
    (hm₂.image_subset).antisymm fun x hx => ⟨_, hm₂' hx, hr₂ hx⟩
  have hcompat : ∀ z : ℂ, ‖z‖ = 2 → c₁ z = c₂ (collarOuterStep z) := by
    intro z hzn
    have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
    have h1 : collarOuterStep z = (unitOf z hz0 : ℂ) := by
      rw [collarOuterStep_two hzn, coe_unitOf, hzn, Complex.real_smul]
      push_cast; ring
    rw [h1, hp₂, hpB, ← hzn, norm_mul_unitOf]
  obtain ⟨c, hcc, hci, hcA, hcB, hcE, hcs, hcinner⟩ :=
    exists_joined_collar_coordinates_eq c₁ c₂ hcc₁ hi₁ hcc₂ hi₂ hin₁ hB₁ hin₂ hE₂ hs₂ hcompat
  let sc : ℂ → ℂ := fun z => (3 / 2 : ℝ) • z
  have hsc : Continuous sc := by fun_prop
  have hsci : Function.Injective sc := smul_right_injective ℂ (by norm_num)
  have hball : ∀ r : ℝ, sc '' closedBall 0 r = closedBall 0 (3 / 2 * r) := fun r => by
    change (3 / 2 : ℝ) • closedBall (0 : ℂ) r = _
    have := _root_.smul_closedBall' (by norm_num : (3 / 2 : ℝ) ≠ 0) (0 : ℂ) r
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using this
  have hsph : sc '' sphere 0 2 = sphere 0 3 := by
    change (3 / 2 : ℝ) • sphere (0 : ℂ) 2 = _
    have := _root_.smul_sphere' (by norm_num : (3 / 2 : ℝ) ≠ 0) (0 : ℂ) 2
    have h2 : |(3 / 2 : ℝ)| * 2 = 3 := by rw [abs_of_pos (by norm_num)]; norm_num
    simpa only [smul_zero, Real.norm_eq_abs, h2] using this
  let d : ℂ → S := fun z => c (sc z)
  have hsub : MapsTo sc (closedBall 0 2) (closedBall 0 3) := fun z hz => by
    have : sc z ∈ sc '' closedBall 0 2 := mem_image_of_mem sc hz
    rw [hball 2] at this
    convert this using 2
    norm_num
  have hdc : ContinuousOn d (closedBall 0 2) := hcc.comp hsc.continuousOn hsub
  have hdi : InjOn d (closedBall 0 2) := fun z hz w hw he => hsci (hci (hsub hz) (hsub hw) he)
  have hdimg : ∀ r r' : ℝ, 3 / 2 * r = r' → d '' closedBall 0 r = c '' closedBall 0 r' :=
    fun r r' he => by rw [← he, ← hball r, image_image]
  have hdE : d '' closedBall 0 2 = E := by rw [hdimg 2 3 (by norm_num), hcE]
  have hdA : d '' closedBall 0 (2 / 3) = A := by rw [hdimg (2 / 3) 1 (by norm_num), hcA]
  have hdB : d '' closedBall 0 (4 / 3) = B := by rw [hdimg (4 / 3) 2 (by norm_num), hcB]
  have hds : d '' sphere 0 2 = discBd E := by rw [← hcs, ← hsph, image_image]
  obtain ⟨d', hdc', hdm', hdl, hdr⟩ := exists_inverse_on_compact (isCompact_closedBall 0 2) hdc hdi
  rw [hdE] at hdc' hdm' hdr
  have hdm : MapsTo d (closedBall 0 2) E := fun z hz => hdE ▸ mem_image_of_mem d hz
  obtain ⟨Θ, hΘfix, hΘscale, hΘball⟩ := exists_radial_disc_resize_scale
    (show (0 : ℝ) < 2 / 3 by norm_num) (show (2 / 3 : ℝ) < 3 / 2 by norm_num)
    (show (0 : ℝ) < 4 / 3 by norm_num) (show (4 / 3 : ℝ) < 3 / 2 by norm_num)
  obtain ⟨e₁, he₁c, he₁fix⟩ :=
    exists_homeomorph_of_collar hman hE hdc hdc' hdm hdm' hdl hdr hds Θ hΘfix
  have he₁_AB : e₁ '' A = B := by
    rw [← hdA, image_image, ← hdB, ← hΘball, image_image]
    exact image_congr fun z hz => he₁c z (closedBall_subset_closedBall (by norm_num) hz)
  have he₁_c₁ : ∀ w : Circle, e₁ (c₁ w) = (pB w).1 := fun w => by
    let z : ℂ := (2 / 3 : ℝ) • (w : ℂ)
    have hz_norm : ‖z‖ = 2 / 3 := by
      dsimp only [z]
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]
    have hz2 : z ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff, hz_norm]; norm_num
    have hdz : d z = c₁ w := by
      dsimp only [d, sc, z]
      rw [smul_smul, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, one_smul,
        hcinner w (by rw [Circle.norm_coe]; norm_num)]
    rw [← hdz, he₁c z hz2, hΘscale z (by rw [hz_norm])]
    dsimp only [d, sc, z]
    rw [smul_smul, smul_smul]
    have h43 : (3 / 2 : ℝ) * (4 / 3 / (2 / 3)) * (2 / 3) = 2 := by norm_num
    rw [h43, hcinner _ (by rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]),
      hpB, Complex.real_smul]
  obtain ⟨e₂, he₂_BB, he₂_pB, he₂_fix⟩ := exists_boundary_twist hman hB hE hBE pB hτ
  refine ⟨e₁.trans e₂, ?_, ?_, ?_⟩
  · change (e₂ ∘ e₁) '' A = B
    rw [image_comp, he₁_AB, he₂_BB]
  · intro x hx
    rw [Homeomorph.trans_apply, he₁fix x hx, he₂_fix x hx]
  · intro i
    have hφ0 : φ i 0 = c₁ (u i : ℂ) := by
      rw [hu_coe i]
      dsimp [γ]
      rw [hclampI_0, hr₁ (hφ_mem i 0).1]
    have hφ1 : φ i 1 = (pB (v i)).1 := by
      rw [hpB]
      have hv1 : ((2 : ℝ) : ℂ) * (v i : ℂ) = γ i 1 := by
        simpa using hv_coe i
      rw [hv1]
      dsimp [γ]
      rw [hclampI_1, hr₁ (hφ_mem i 1).1]
    rw [Homeomorph.trans_apply, hφ0, he₁_c₁ (u i), he₂_pB (u i), hτ_uv i, ← hφ1]

/-! ## 4. Gluing Drawings and Minimal Paths in Sleeves -/

omit [T2Space S] in
/-- When two drawings `Γ₁, Γ₂` meet only in common vertices, their edge sets are disjoint. -/
theorem glue_disjoint_E {Γ₁ Γ₂ : Surface.Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    Disjoint Γ₁.E Γ₂.E := by
  rw [disjoint_left]
  intro e he₁ he₂
  obtain ⟨x, hxe⟩ := he₁.1
  have hx₁ : x ∈ Γ₁.U \ Γ₁.V := he₁.2.1 hxe
  have hx₂ : x ∈ Γ₂.U \ Γ₂.V := he₂.2.1 hxe
  exact hx₁.2 (h ⟨hx₁.1, hx₂.1⟩).1

omit [T2Space S] in
/-- Both parts of `Γ₁.glue Γ₂ h` are subdrawings of `Γ₁.glue Γ₂ h`. -/
theorem isSubdrawing_glue_left {Γ₁ Γ₂ : Surface.Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    Γ₁.IsSubdrawing (Γ₁.glue Γ₂ h) :=
  ⟨subset_union_left, by rw [Drawing.glue_E h]; exact subset_union_left⟩

omit [T2Space S] in
theorem isSubdrawing_glue_right {Γ₁ Γ₂ : Surface.Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    Γ₂.IsSubdrawing (Γ₁.glue Γ₂ h) :=
  ⟨subset_union_right, by rw [Drawing.glue_E h]; exact subset_union_right⟩

omit [T2Space S] in
/-- The abstract graph of `Γ₁.glue Γ₂ h` is `graphUnion Γ₁.toGraph Γ₂.toGraph`. -/
theorem glue_toGraph_eq_graphUnion {Γ₁ Γ₂ : Surface.Drawing S} (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) :
    (Γ₁.glue Γ₂ h).toGraph = graphUnion Γ₁.toGraph Γ₂.toGraph := by
  have hsub₁ := isSubdrawing_glue_left h
  have hsub₂ := isSubdrawing_glue_right h
  have hdisj := glue_disjoint_E h
  refine Graph.ext rfl fun e x y => ?_
  change (Γ₁.glue Γ₂ h).toGraph.IsLink e x y ↔
    Γ₁.toGraph.IsLink e x y ∨ (e ∉ Γ₁.E ∧ Γ₂.toGraph.IsLink e x y)
  constructor
  · intro hl
    have he : e ∈ Γ₁.E ∪ Γ₂.E := Drawing.glue_E h ▸ hl.1
    rcases he with he₁ | he₂
    · exact Or.inl ((hsub₁.isLink_iff he₁).mpr hl)
    · exact Or.inr ⟨disjoint_right.mp hdisj he₂, (hsub₂.isLink_iff he₂).mpr hl⟩
  · rintro (hl₁ | ⟨_, hl₂⟩)
    · exact (hsub₁.isLink_iff hl₁.1).mp hl₁
    · exact (hsub₂.isLink_iff hl₂.1).mp hl₂

/-- Every simple walk in `Γ.toGraph` starting in `B \ subBd B` and hitting `Γ.V ∩ subBd B` only at
its final vertex `b` has all its vertices in `B`, all its edge closures in `B`, and all its edges
disjoint from `subBd B`. -/
theorem walk_in_disc_of_end_only {Γ : Surface.Drawing S} {B : Set S}
    (hB_cl : IsClosed B) (hbd_oArc : IsOArc (subBd B)) (hbd_U : subBd B ⊆ Γ.U)
    {a b : S} (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple)
    (ha : a ∈ B \ subBd B) (hb : b ∈ subBd B)
    (hY : ∀ x ∈ W.support, x ∈ Γ.V ∩ subBd B → x = b) :
    (∀ x ∈ W.support, x ∈ B ∧ (x ∈ subBd B ↔ x = b)) ∧
    (∀ e ∈ W.edges, closure e ⊆ B ∧ Disjoint e (subBd B)) := by
  induction W with
  | nil _ => exact (ha.2 hb).elim
  | @cons u w b e hl r ih =>
    have hnd := List.nodup_cons.mp hW
    have hu_not_r : u ∉ r.support := hnd.1
    have hr_simp : r.IsSimple := hnd.2
    have hub : u ≠ b := fun h => hu_not_r (h ▸ r.end_mem_support)
    have he_disj : Disjoint e (subBd B) := by
      rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
      intro hne
      have he_sub : e ⊆ subBd B := edge_subset_of_oArc' hbd_oArc hbd_U hl.1 hne
      have hcl_sub : closure e ⊆ subBd B :=
        closure_minimal he_sub (isCompact_of_isOArc hbd_oArc).isClosed
      have hu_cl : u ∈ closure e := (hl.2.2.2.symm.subset (Or.inl rfl)).1
      exact ha.2 (hcl_sub hu_cl)
    by_cases hw_int : w ∈ B \ subBd B
    · have he_cl : closure e ⊆ B := by
        rcases edge_closure_subset_or_disjoint_of_oArc_subBd hB_cl hbd_oArc hbd_U hl.1 with
          hsub | hdisj
        · exact hsub
        · exfalso
          have hu_cl : u ∈ closure e := (hl.2.2.2.symm.subset (Or.inl rfl)).1
          have h_eq : B \ subBd B = interior B := by
            rw [subBd_eq_frontier, frontier]
            ext z
            simp only [mem_sdiff, hB_cl.closure_eq]
            exact ⟨fun ⟨hzB, h⟩ => by_contra fun hni => h ⟨hzB, hni⟩,
              fun hz => ⟨interior_subset hz, fun ⟨_, hni⟩ => hni hz⟩⟩
          obtain ⟨z, hz_int, hze⟩ :=
            mem_closure_iff.mp hu_cl (B \ subBd B) (h_eq ▸ isOpen_interior) ha
          exact disjoint_left.mp hdisj hze hz_int.1
      obtain ⟨ihV, ihE⟩ := ih hr_simp hw_int hb (fun x hx => hY x (List.mem_cons_of_mem u hx))
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨ha.1, ⟨fun h => (ha.2 h).elim, fun h => (hub h).elim⟩⟩
        · exact ihV x hx
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨he_cl, he_disj⟩
        · exact ihE f hf
    · obtain ⟨hw_bd, he_cl⟩ := end_mem_subBd_of_isLink_sdiff hB_cl hbd_oArc hbd_U hl ha hw_int
      have hwb : w = b := hY w (List.mem_cons_of_mem u r.start_mem_support) hw_bd
      subst hwb
      have hr_len : r.length = 0 := hr_simp.length_eq_zero
      cases r with
      | nil hwV =>
        refine ⟨fun x hx => ?_, fun f hf => ?_⟩
        · simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ⟨ha.1, ⟨fun h => (ha.2 h).elim, fun h => (hub h).elim⟩⟩
          · exact ⟨hB_cl.closure_eq ▸ hw_bd.2.1, ⟨fun _ => rfl, fun _ => hw_bd.2⟩⟩
        · simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at hf
          subst hf
          exact ⟨he_cl, he_disj⟩
      | cons _ _ => simp at hr_len

/-- For an `IsFromToPathWithEnds` path `Q` in `Γ.toGraph` from `X ⊆ B \ subBd B` to
`Y = Γ.V ∩ subBd B`, the support `U(Q) = V(Q) ∪ ⋃ e ∈ E(Q), closure e` is a line between `a` and `b`
contained in `B`, meeting `subBd B` only at `{b}`, and `Q ≤ (Γ.interSet B).toGraph`. -/
theorem fromToPath_in_disc {Γ : Surface.Drawing S} {B X : Set S}
    (hB_cl : IsClosed B) (hbd_oArc : IsOArc (subBd B)) (hbd_U : subBd B ⊆ Γ.U)
    (hX_sub : X ⊆ B \ subBd B)
    {Q : Graph S (Set S)} {a b : S}
    (hQ : IsFromToPathWithEnds Γ.toGraph Q X (Γ.V ∩ subBd B) a b) :
    let UQ := V(Q) ∪ ⋃ e ∈ E(Q), closure e
    a ≠ b ∧
    IsLineWithEnds UQ a b ∧
    UQ ⊆ B ∧
    UQ ∩ subBd B = {b} ∧
    Q ≤ (Γ.interSet B).toGraph := by
  rcases hQ with ⟨⟨hQ_le, W₀, hW₀_simp, hVQ, hEQ⟩, haX, hbY⟩
  have ha_in_X : a ∈ X := by
    have : a ∈ V(Q) ∩ X := haX.symm ▸ mem_singleton a
    exact this.2
  have hb_in_Y : b ∈ Γ.V ∩ subBd B := by
    have : b ∈ V(Q) ∩ (Γ.V ∩ subBd B) := hbY.symm ▸ mem_singleton b
    exact this.2
  have ha_int : a ∈ B \ subBd B := hX_sub ha_in_X
  have hab : a ≠ b := fun h => ha_int.2 (h ▸ hb_in_Y.2)
  obtain ⟨W, hsW, heW⟩ := W₀.exists_transfer
    (fun e x y _ hl => hQ_le.isLink_mono hl)
    (fun x hx => hQ_le.vertexSet_mono (W₀.mem_vertexSet_of_mem_support hx))
  have hW_simp : W.IsSimple := by
    change W.support.Nodup
    rw [hsW]
    exact hW₀_simp
  have hVQ' : V(Q) = {x | x ∈ W.support} := by rw [hVQ, hsW]
  have hEQ' : E(Q) = {e | e ∈ W.edges} := by rw [hEQ, heW]
  have hx_supp : ∀ {x}, x ∈ V(Q) → x ∈ W.support := fun hx => by rw [hVQ'] at hx; exact hx
  have he_edges : ∀ {e}, e ∈ E(Q) → e ∈ W.edges := fun he => by rw [hEQ'] at he; exact he
  have hY_only : ∀ x ∈ W.support, x ∈ Γ.V ∩ subBd B → x = b := by
    intro x hx hxY
    have hx_VQ : x ∈ V(Q) := by rw [hVQ']; exact hx
    have hx_in : x ∈ V(Q) ∩ (Γ.V ∩ subBd B) := ⟨hx_VQ, hxY⟩
    rwa [hbY, mem_singleton_iff] at hx_in
  obtain ⟨hV_B, hE_B⟩ := walk_in_disc_of_end_only hB_cl hbd_oArc hbd_U W hW_simp ha_int hb_in_Y.2 hY_only
  have hLine : IsLineWithEnds (V(Q) ∪ ⋃ e ∈ E(Q), closure e) a b := by
    rw [hVQ', hEQ']
    exact GM11.walk_isLine Γ W hW_simp hab
  have hUQ_sub : V(Q) ∪ (⋃ e ∈ E(Q), closure e) ⊆ B := by
    refine union_subset (fun x hx => (hV_B x (hx_supp hx)).1) ?_
    exact iUnion₂_subset fun e he => (hE_B e (he_edges he)).1
  have hUQ_bd : (V(Q) ∪ ⋃ e ∈ E(Q), closure e) ∩ subBd B = {b} := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_iUnion, mem_singleton_iff]
    constructor
    · rintro ⟨hxV | ⟨e, heQ, hxe⟩, hx_bd⟩
      · exact (hV_B x (hx_supp hxV)).2.mp hx_bd
      · have heW' : e ∈ W.edges := he_edges heQ
        have heD : e ∈ Γ.E := by
          obtain ⟨u, v, hl⟩ := Q.exists_isLink_of_mem_edgeSet heQ
          exact (hQ_le.isLink_mono hl).1
        by_cases hx_in_V : x ∈ Γ.V
        · obtain ⟨u, v, hlQ⟩ := Q.exists_isLink_of_mem_edgeSet heQ
          have hlD := hQ_le.isLink_mono hlQ
          have hx_uv : x ∈ ({u, v} : Set S) := hlD.2.2.2 ▸ ⟨hxe, hx_in_V⟩
          have hx_VQ : x ∈ V(Q) := by
            rcases hx_uv with rfl | rfl
            · exact hlQ.left_mem
            · exact hlQ.right_mem
          exact (hV_B x (hx_supp hx_VQ)).2.mp hx_bd
        · have hxe' : x ∈ e := (Γ.closure_diff_V heD) ▸ ⟨hxe, hx_in_V⟩
          exact (disjoint_left.mp (hE_B e heW').2 hxe' hx_bd).elim
    · intro hxb
      rw [hxb]
      have hb_VQ : b ∈ V(Q) := by rw [hVQ']; exact W.end_mem_support
      exact ⟨Or.inl hb_VQ, hb_in_Y.2⟩
  have hQ_le_inter : Q ≤ (Γ.interSet B).toGraph := by
    refine ⟨?_, ?_⟩
    · intro x hx
      change x ∈ (Γ.interSet B).V
      rw [interSet_V_eq Γ hB_cl]
      exact ⟨hQ_le.vertexSet_mono hx, (hV_B x (hx_supp hx)).1⟩
    · intro e x y hlQ
      have hlD := hQ_le.isLink_mono hlQ
      have he_cl : closure e ⊆ B := (hE_B e (he_edges hlQ.edge_mem)).1
      have he_inter : e ∈ (Γ.interSet B).E :=
        GM11.mem_interSet_E_iff.mpr ⟨hlD.1, subset_closure.trans he_cl⟩
      have hx_inter : x ∈ (Γ.interSet B).V := by
        rw [interSet_V_eq Γ hB_cl]
        exact ⟨hlD.2.1, (hV_B x (hx_supp hlQ.left_mem)).1⟩
      have hy_inter : y ∈ (Γ.interSet B).V := by
        rw [interSet_V_eq Γ hB_cl]
        exact ⟨hlD.2.2.1, (hV_B y (hx_supp hlQ.right_mem)).1⟩
      refine ⟨he_inter, hx_inter, hy_inter, ?_⟩
      rw [interSet_V_eq Γ hB_cl, ← inter_assoc,
        inter_eq_left.mpr (inter_subset_left.trans he_cl), hlD.2.2.2]
  exact ⟨hab, hLine, hUQ_sub, hUQ_bd, hQ_le_inter⟩

omit [T2Space S] in
/-- Two vertex-disjoint subgraphs of `Γ.toGraph` have disjoint point sets
`V(Qᵢ) ∪ ⋃ e ∈ E(Qᵢ), closure e`. -/
theorem disjoint_subgraph_U_of_disjoint_V {Γ : Surface.Drawing S} {Q₁ Q₂ : Graph S (Set S)}
    (h₁ : Q₁ ≤ Γ.toGraph) (h₂ : Q₂ ≤ Γ.toGraph) (hdisj : Disjoint V(Q₁) V(Q₂)) :
    Disjoint (V(Q₁) ∪ ⋃ e ∈ E(Q₁), closure e) (V(Q₂) ∪ ⋃ e ∈ E(Q₂), closure e) := by
  have hE_disj : Disjoint E(Q₁) E(Q₂) := by
    rw [disjoint_left]
    intro e he₁ he₂
    obtain ⟨x₁, y₁, hl₁⟩ := Q₁.exists_isLink_of_mem_edgeSet he₁
    obtain ⟨x₂, y₂, hl₂⟩ := Q₂.exists_isLink_of_mem_edgeSet he₂
    have hlD₁ := h₁.isLink_mono hl₁
    have hlD₂ := h₂.isLink_mono hl₂
    have hx₁ : x₁ ∈ ({x₂, y₂} : Set S) := hlD₂.2.2.2 ▸ hlD₁.2.2.2 ▸ Or.inl rfl
    rcases hx₁ with rfl | rfl
    · exact disjoint_left.mp hdisj hl₁.left_mem hl₂.left_mem
    · exact disjoint_left.mp hdisj hl₁.left_mem hl₂.right_mem
  have hmem_V : ∀ {Q : Graph S (Set S)}, Q ≤ Γ.toGraph →
      ∀ z ∈ V(Q) ∪ ⋃ e ∈ E(Q), closure e, z ∈ Γ.V → z ∈ V(Q) := by
    intro Q hQ z hz hzV
    rcases hz with hzQ | hzE
    · exact hzQ
    · obtain ⟨e, heQ, hze⟩ := mem_iUnion₂.mp hzE
      obtain ⟨u, v, hlQ⟩ := Q.exists_isLink_of_mem_edgeSet heQ
      have hlD := hQ.isLink_mono hlQ
      have hz_uv : z ∈ ({u, v} : Set S) := hlD.2.2.2 ▸ ⟨hze, hzV⟩
      rcases hz_uv with rfl | rfl
      · exact hlQ.left_mem
      · exact hlQ.right_mem
  rw [disjoint_left]
  intro z hz₁ hz₂
  by_cases hzV : z ∈ Γ.V
  · exact disjoint_left.mp hdisj (hmem_V h₁ z hz₁ hzV) (hmem_V h₂ z hz₂ hzV)
  · rcases hz₁ with hzQ₁ | hzE₁
    · exact hzV (h₁.vertexSet_mono hzQ₁)
    · rcases hz₂ with hzQ₂ | hzE₂
      · exact hzV (h₂.vertexSet_mono hzQ₂)
      · obtain ⟨e₁, he₁, hze₁⟩ := mem_iUnion₂.mp hzE₁
        obtain ⟨e₂, he₂, hze₂⟩ := mem_iUnion₂.mp hzE₂
        obtain ⟨u₁, v₁, hl₁⟩ := Q₁.exists_isLink_of_mem_edgeSet he₁
        obtain ⟨u₂, v₂, hl₂⟩ := Q₂.exists_isLink_of_mem_edgeSet he₂
        have he₁D : e₁ ∈ Γ.E := (h₁.isLink_mono hl₁).1
        have he₂D : e₂ ∈ Γ.E := (h₂.isLink_mono hl₂).1
        have hze₁' : z ∈ e₁ := Γ.closure_diff_V he₁D ▸ ⟨hze₁, hzV⟩
        have hze₂' : z ∈ e₂ := Γ.closure_diff_V he₂D ▸ ⟨hze₂, hzV⟩
        have heq : e₁ = e₂ := Γ.edge_eq_of_mem he₁D he₂D hze₁' hze₂'
        exact disjoint_left.mp hE_disj he₁ (heq ▸ he₂)

omit [T2Space S] in
/-- Universe-polymorphic version of `IsCappedSurface.cuffDisc_eq_discInt`. -/
theorem cuffDisc_eq_discInt_w {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (cap : GM19.IsCappedSurface S Shat)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) :
    cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)) := by
  have hsurf := cap.isSurface
  have hcomp : ∀ Θ' ∈ cuffs S, cap.cuffDisc Θ' ⊆ (range cap.emb)ᶜ := fun Θ' hΘ' x hx => by
    rw [cap.compl_eq]
    exact mem_iUnion₂.mpr ⟨Θ', hΘ', hx⟩
  apply Subset.antisymm
  · intro x hx
    refine ⟨subset_closure hx, fun hb => ?_⟩
    rw [cap.cuffDisc_bd Θ hΘ] at hb
    obtain ⟨y, -, rfl⟩ := hb
    exact hcomp Θ hΘ hx (mem_range_self y)
  · rintro x ⟨hxD, hxb⟩
    by_contra hxc
    by_cases hxr : x ∈ range cap.emb
    · obtain ⟨y, rfl⟩ := hxr
      rw [cap.cuffDisc_bd Θ hΘ] at hxb
      have hyΘ : y ∉ Θ := fun h => hxb (mem_image_of_mem _ h)
      by_cases hy : y ∈ bd S
      · have hΘ' : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
        have hne : connectedComponentIn (bd S) y ≠ Θ := fun h =>
          hyΘ (h ▸ mem_connectedComponentIn hy)
        have hin : cap.emb y ∈ closure (cap.cuffDisc (connectedComponentIn (bd S) y)) := by
          apply Surface.discBd_subset
          rw [cap.cuffDisc_bd _ hΘ']
          exact mem_image_of_mem _ (mem_connectedComponentIn hy)
        exact disjoint_left.mp (cap.cuffDisc_disjoint _ hΘ' _ hΘ hne) hin hxD
      · have hyI : IsInteriorPoint y := by_contra fun hn => hy hn
        obtain ⟨E, hE, hyE⟩ := GM19.exists_disc_around hyI
        obtain ⟨hE', hEb⟩ := GM19.isClosedDisc_image hE cap.isEmbedding
        have hopen : IsOpen (discInt (cap.emb '' E)) := hE'.isOpen_discInt hsurf.2.2
        have hmem : cap.emb y ∈ discInt (cap.emb '' E) := by
          refine ⟨mem_image_of_mem _ hyE.1, fun h => ?_⟩
          rw [hEb] at h
          obtain ⟨z, hz, hzy⟩ := h
          exact hyE.2 (cap.isEmbedding.injective hzy ▸ hz)
        obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hxD _ hopen hmem
        obtain ⟨z, -, rfl⟩ := Surface.discInt_subset _ hw₁
        exact hcomp Θ hΘ hw₂ (mem_range_self z)
    · have hmem : x ∈ ⋃ Θ' ∈ cuffs S, cap.cuffDisc Θ' := by
        rw [← cap.compl_eq]
        exact hxr
      obtain ⟨Θ', hΘ', hx'⟩ := mem_iUnion₂.mp hmem
      by_cases he : Θ' = Θ
      · exact hxc (he ▸ hx')
      · exact disjoint_left.mp (cap.cuffDisc_disjoint _ hΘ' _ hΘ he) (subset_closure hx') hxD

omit [T2Space S] in
/-- Universe-polymorphic version of `IsCappedSurface.closure_cuffDisc`. -/
theorem closure_cuffDisc_w {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (cap : GM19.IsCappedSurface S Shat)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) :
    closure (cap.cuffDisc Θ) = cap.cuffDisc Θ ∪ cap.emb '' Θ := by
  rw [← cap.cuffDisc_bd Θ hΘ]
  ext x
  constructor
  · intro hx
    by_cases hb : x ∈ discBd (closure (cap.cuffDisc Θ))
    · exact Or.inr hb
    · left
      rw [cuffDisc_eq_discInt_w cap hΘ]
      exact ⟨hx, hb⟩
  · rintro (hx | hx)
    · exact subset_closure hx
    · exact Surface.discBd_subset _ hx

omit [T2Space S] in
/-- Universe-polymorphic version of `IsCappedSurface.compl_eq_image`. -/
theorem compl_cuffDisc_eq_image_w {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (cap : GM19.IsCappedSurface S Shat) :
    (⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ))ᶜ = cap.emb '' (bd S)ᶜ := by
  ext y
  constructor
  · intro hy
    have hyr : y ∈ range cap.emb := by
      by_contra hn
      have hn' : y ∈ (range cap.emb)ᶜ := hn
      rw [cap.compl_eq] at hn'
      obtain ⟨Θ, hΘ, hyΘ⟩ := mem_iUnion₂.mp hn'
      exact hy (mem_biUnion hΘ (subset_closure hyΘ))
    obtain ⟨x, rfl⟩ := hyr
    refine ⟨x, fun hxb => ?_, rfl⟩
    rw [← sUnion_cuffs] at hxb
    obtain ⟨Θ, hΘ, hxΘ⟩ := hxb
    refine hy (mem_biUnion hΘ ?_)
    rw [closure_cuffDisc_w cap hΘ]
    exact Or.inr (mem_image_of_mem _ hxΘ)
  · rintro ⟨x, hx, rfl⟩ hy
    obtain ⟨Θ, hΘ, hyΘ⟩ := mem_iUnion₂.mp hy
    rw [closure_cuffDisc_w cap hΘ] at hyΘ
    rcases hyΘ with hy | ⟨z, hz, hzx⟩
    · have : cap.emb x ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_biUnion hΘ hy
      exact this (mem_range_self x)
    · have := cap.isEmbedding.injective hzx
      exact hx (this ▸ sUnion_cuffs (S := S) ▸ ⟨Θ, hΘ, hz⟩)

omit [T2Space S] in
/-- Universe-polymorphic version of `IsCappedSurface.isClosedEmbedding`. -/
theorem isClosedEmbedding_w {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat) :
    IsClosedEmbedding cap.emb := by
  have : CompactSpace S := hS.1
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap cap.isEmbedding.continuous
    cap.isEmbedding.injective cap.isEmbedding.continuous.isClosedMap

omit [T2Space S] in
/-- If `A ⊆ B \ discBd B` are nested closed discs in `Shat`, there is an injection `B → B \ A`. -/
theorem exists_inj_disc_diff {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    {A B : Set Shat} (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ⊆ B \ discBd B) :
    ∃ f : Shat → Shat, (∀ x ∈ B, f x ∈ B \ A) ∧ (∀ x ∉ B, f x = x) ∧ Injective f := by
  obtain ⟨pA⟩ := hA.isOArc_discBd
  obtain ⟨c₁, c₁', _, _, hm₁, hm₁', hl₁, hr₁, hin₁, _, _⟩ := exists_disc_collar hA hB hAB pA
  have hi₁ : InjOn c₁ (closedBall 0 2) := hl₁.injOn
  have hi₁' : InjOn c₁' B := hr₁.injOn
  let w : ℂ → ℂ := fun z => (3 / 2 : ℂ) + (1 / 8 : ℝ) • z
  have hw_inj : Injective w := fun z₁ z₂ h =>
    smul_right_injective ℂ (by norm_num : (1 / 8 : ℝ) ≠ 0) (add_left_cancel h)
  have hw_bounds : ∀ z ∈ closedBall (0 : ℂ) 2, w z ∈ closedBall 0 2 ∧ w z ∉ closedBall 0 1 := by
    intro z hz
    have hzn : ‖z‖ ≤ 2 := mem_closedBall_zero_iff.mp hz
    have hnorm32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    have hnorm_z : ‖(1 / 8 : ℝ) • z‖ ≤ 1 / 4 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
    have hlo : ‖(3 / 2 : ℂ)‖ - ‖(1 / 8 : ℝ) • z‖ ≤ ‖w z‖ := by
      have := norm_sub_norm_le (3 / 2 : ℂ) (-(1 / 8 : ℝ) • z)
      simpa [w] using this
    have hhi : ‖w z‖ ≤ ‖(3 / 2 : ℂ)‖ + ‖(1 / 8 : ℝ) • z‖ := norm_add_le _ _
    refine ⟨mem_closedBall_zero_iff.mpr (by linarith), fun h1 => ?_⟩
    have h1' : ‖w z‖ ≤ 1 := mem_closedBall_zero_iff.mp h1
    linarith
  classical
  let f : Shat → Shat := fun x => if x ∈ B then c₁ (w (c₁' x)) else x
  have hf_in : ∀ x ∈ B, f x ∈ B \ A := by
    intro x hxB
    have hfx : f x = c₁ (w (c₁' x)) := by simp [f, hxB]
    rw [hfx]
    have h_w := hw_bounds (c₁' x) (hm₁' hxB)
    refine ⟨hm₁ h_w.1, ?_⟩
    rw [← hin₁]
    rintro ⟨u, hu1, heq⟩
    have hu2 : u ∈ closedBall (0 : ℂ) 2 := closedBall_subset_closedBall (by norm_num) hu1
    have hwu : u = w (c₁' x) := hi₁ hu2 h_w.1 heq
    exact h_w.2 (hwu ▸ hu1)
  have hf_out : ∀ x ∉ B, f x = x := fun x hxB => by simp [f, hxB]
  refine ⟨f, hf_in, hf_out, fun x₁ x₂ hfx => ?_⟩
  by_cases hx₁B : x₁ ∈ B
  · have hx₂B : x₂ ∈ B := by
      by_contra hx₂B
      rw [hf_out x₂ hx₂B] at hfx
      exact hx₂B (hfx ▸ (hf_in x₁ hx₁B).1)
    have h₁ : f x₁ = c₁ (w (c₁' x₁)) := by simp [f, hx₁B]
    have h₂ : f x₂ = c₁ (w (c₁' x₂)) := by simp [f, hx₂B]
    rw [h₁, h₂] at hfx
    have hw₁ := (hw_bounds (c₁' x₁) (hm₁' hx₁B)).1
    have hw₂ := (hw_bounds (c₁' x₂) (hm₁' hx₂B)).1
    exact hi₁' hx₁B hx₂B (hw_inj (hi₁ hw₁ hw₂ hfx))
  · have hx₂B : x₂ ∉ B := by
      intro hx₂B
      rw [hf_out x₁ hx₁B] at hfx
      exact hx₁B (hfx.symm ▸ (hf_in x₂ hx₂B).1)
    rwa [hf_out x₁ hx₁B, hf_out x₂ hx₂B] at hfx

omit [T2Space S] in
/-- Given sleeves `B C` for all `C ∈ cuffs S` with `closure (cap.cuffDisc C) ⊆ B C \ discBd (B C)`
and pairwise disjoint `B C`, there is an injection `Shat ↪ S`. -/
theorem exists_inj_capped_to_surface {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (cap : GM19.IsCappedSurface S Shat) (B : Set S → Set Shat)
    (hB_disc : ∀ C ∈ cuffs S, IsClosedDisc (B C))
    (hAB : ∀ C ∈ cuffs S, closure (cap.cuffDisc C) ⊆ B C \ discBd (B C))
    (hB_disj : ∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (B C₁) (B C₂)) :
    Nonempty (Shat ↪ S) := by
  classical
  have hex : ∀ C : {C // C ∈ cuffs S}, ∃ f : Shat → Shat,
      (∀ x ∈ B C.1, f x ∈ B C.1 \ closure (cap.cuffDisc C.1)) ∧
      (∀ x ∉ B C.1, f x = x) ∧ Injective f := fun ⟨C, hC⟩ =>
    exists_inj_disc_diff (cap.cuffDisc_closedDisc C hC) (hB_disc C hC) (hAB C hC)
  choose fC hfC_in hfC_out hfC_inj using hex
  let fall : Shat → Shat := fun x =>
    if h : ∃ C : {C // C ∈ cuffs S}, x ∈ B C.1 then
      fC (Classical.choose h) x
    else x
  have hfall_eq : ∀ (C : {C // C ∈ cuffs S}) {x : Shat}, x ∈ B C.1 → fall x = fC C x := by
    intro C x hx
    have hex_x : ∃ C' : {C // C ∈ cuffs S}, x ∈ B C'.1 := ⟨C, hx⟩
    have h_eq : Classical.choose hex_x = C := by
      by_contra hne
      have hne' : (Classical.choose hex_x).1 ≠ C.1 := fun h => hne (Subtype.ext h)
      exact disjoint_left.mp
        (hB_disj _ (Classical.choose hex_x).2 C.1 C.2 hne')
        (Classical.choose_spec hex_x) hx
    simp only [fall, hex_x, ↓reduceDIte, h_eq]
  have hfall_range : ∀ x : Shat, fall x ∈ range cap.emb := by
    intro x
    by_contra hx_not_range
    have hx_compl : fall x ∈ (range cap.emb)ᶜ := hx_not_range
    rw [cap.compl_eq] at hx_compl
    obtain ⟨Θ, hΘ, hxΘ⟩ := mem_iUnion₂.mp hx_compl
    have hxΘ_cl : fall x ∈ closure (cap.cuffDisc Θ) := subset_closure hxΘ
    have hxΘ_B : fall x ∈ B Θ := (hAB Θ hΘ hxΘ_cl).1
    by_cases hex_x : ∃ C : {C // C ∈ cuffs S}, x ∈ B C.1
    · rcases hex_x with ⟨C, hxC⟩
      rw [hfall_eq C hxC] at hxΘ_B hxΘ_cl
      have hin := hfC_in C x hxC
      have hCΘ : C.1 = Θ := by
        by_contra hne
        exact disjoint_left.mp (hB_disj C.1 C.2 Θ hΘ hne) hin.1 hxΘ_B
      exact hin.2 (hCΘ.symm ▸ hxΘ_cl)
    · have hfall_x : fall x = x := dite_eq_right_iff.mpr fun h => (hex_x h).elim
      rw [hfall_x] at hxΘ_B
      exact hex_x ⟨⟨Θ, hΘ⟩, hxΘ_B⟩
  have hfall_inj : Injective fall := by
    intro x₁ x₂ hfx
    have hmem_B : ∀ (C : {C // C ∈ cuffs S}) (x : Shat), x ∈ B C.1 ↔ fall x ∈ B C.1 := by
      intro C x
      constructor
      · intro hx
        rw [hfall_eq C hx]
        exact (hfC_in C x hx).1
      · intro hfx_in
        by_cases hex_x : ∃ C' : {C // C ∈ cuffs S}, x ∈ B C'.1
        · rcases hex_x with ⟨C', hxC'⟩
          rw [hfall_eq C' hxC'] at hfx_in
          have hin := (hfC_in C' x hxC').1
          have hCC' : C' = C := by
            by_contra hne
            have hne' : C'.1 ≠ C.1 := fun h => hne (Subtype.ext h)
            exact disjoint_left.mp (hB_disj C'.1 C'.2 C.1 C.2 hne') hin hfx_in
          exact hCC' ▸ hxC'
        · have hfall_x : fall x = x := dite_eq_right_iff.mpr fun h => (hex_x h).elim
          rw [hfall_x] at hfx_in
          exact hfx_in
    by_cases hex₁ : ∃ C : {C // C ∈ cuffs S}, x₁ ∈ B C.1
    · rcases hex₁ with ⟨C, hx₁C⟩
      have hx₂C : x₂ ∈ B C.1 := (hmem_B C x₂).mpr (hfx ▸ (hmem_B C x₁).mp hx₁C)
      rw [hfall_eq C hx₁C, hfall_eq C hx₂C] at hfx
      exact hfC_inj C hfx
    · have hex₂ : ¬ ∃ C : {C // C ∈ cuffs S}, x₂ ∈ B C.1 := by
        rintro ⟨C, hx₂C⟩
        exact hex₁ ⟨C, (hmem_B C x₁).mpr (hfx.symm ▸ (hmem_B C x₂).mp hx₂C)⟩
      have hf₁ : fall x₁ = x₁ := dite_eq_right_iff.mpr fun h => (hex₁ h).elim
      have hf₂ : fall x₂ = x₂ := dite_eq_right_iff.mpr fun h => (hex₂ h).elim
      rwa [hf₁, hf₂] at hfx
  choose g hg using hfall_range
  refine ⟨⟨g, fun x₁ x₂ hgx => ?_⟩⟩
  apply hfall_inj
  rw [← hg x₁, ← hg x₂, hgx]

omit [TopologicalSpace S] [T2Space S] in
/-- If an edge `e ∈ D.E` has `closure e` meeting `insulatedSet D Y (h₀ + 1)`, then
`closure e ⊆ insulatedSet D Y h₀`. -/
theorem closure_edge_subset_insulatedSet_of_inter {Shat : Type w} [TopologicalSpace Shat]
    [T2Space Shat] {D : Surface.Drawing Shat} {Y : Set Shat} {h₀ : ℕ}
    {e : Set Shat} (he : e ∈ D.E)
    (hinter : (closure e ∩ insulatedSet D Y (h₀ + 1)).Nonempty) :
    closure e ⊆ insulatedSet D Y h₀ := by
  rcases hinter with ⟨z, hz_cl, Δ, hΔ_disc, hΔ_nest, hΔ_ends⟩
  have hpos : 0 < h₀ + 1 := Nat.succ_pos h₀
  obtain ⟨hz_in, hdisj⟩ := hΔ_ends hpos
  let idx : Fin (h₀ + 1) := ⟨h₀, Nat.lt_succ_self h₀⟩
  have hidx_eq : (⟨h₀ + 1 - 1, Nat.sub_lt hpos zero_lt_one⟩ : Fin (h₀ + 1)) = idx := rfl
  rw [hidx_eq] at hz_in
  have hB_cl : IsClosed (Δ idx) := (hΔ_disc idx).1.isCompact.isClosed
  have hB_oArc : IsOArc (subBd (Δ idx)) := by
    rw [(hΔ_disc idx).2.1]
    exact (hΔ_disc idx).1.isOArc_discBd
  have hB_U : subBd (Δ idx) ⊆ D.U := (hΔ_disc idx).2.2
  have he_cl : closure e ⊆ Δ idx := by
    rcases edge_closure_subset_or_disjoint_of_oArc_subBd hB_cl hB_oArc hB_U he with hsub | hdisj_e
    · exact hsub
    · exfalso
      have h_int : Δ idx \ subBd (Δ idx) = interior (Δ idx) :=
        sdiff_subBd_eq_interior hB_cl (subBd_eq_frontier (Δ idx))
      obtain ⟨w, hw_int, hwe⟩ :=
        mem_closure_iff.mp hz_cl (Δ idx \ subBd (Δ idx)) (h_int ▸ isOpen_interior) hz_in
      exact disjoint_left.mp hdisj_e hwe hw_int.1
  intro w hw_cl
  have hw_idx : w ∈ Δ idx := he_cl hw_cl
  rcases Nat.eq_zero_or_pos h₀ with rfl | hh₀
  · exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun h => (Nat.lt_irrefl 0 h).elim⟩
  · refine ⟨fun i : Fin h₀ => Δ ⟨i.1, Nat.lt_succ_of_lt i.2⟩,
      fun i => hΔ_disc ⟨i.1, Nat.lt_succ_of_lt i.2⟩,
      fun i hi => hΔ_nest ⟨i.1, Nat.lt_succ_of_lt i.2⟩ (Nat.lt_succ_of_lt hi),
      fun _ => ⟨?_, hdisj⟩⟩
    have hpred_lt : h₀ - 1 + 1 < h₀ + 1 := by omega
    have hsub := hΔ_nest ⟨h₀ - 1, by omega⟩ hpred_lt
    have h_eq : (⟨h₀ - 1 + 1, hpred_lt⟩ : Fin (h₀ + 1)) = idx := by
      ext; dsimp [idx]; omega
    rw [h_eq] at hsub
    exact hsub hw_idx

omit [TopologicalSpace S] [T2Space S] in
/-- Attaching a family `𝒜` of pairwise vertex-disjoint connected subgraphs `P ≤ G` to `L₀ ≤ G`
where each `P ∈ 𝒜` meets `V(L₀)` only at `{b P hP}` induces a retraction `ρ` preserving
`AreConnectedIn`. -/
theorem areConnectedIn_graphUnion_pendants {G L₀ : Graph S (Set S)}
    {𝒜 : Set (Graph S (Set S))} {b : ∀ P, P ∈ 𝒜 → S}
    (hL₀ : L₀ ≤ G) (h𝒜 : ∀ P ∈ 𝒜, P ≤ G)
    (hDisj : ∀ P₁ ∈ 𝒜, ∀ P₂ ∈ 𝒜, P₁ ≠ P₂ → Disjoint V(P₁) V(P₂))
    (hb_inter : ∀ (P) (hP : P ∈ 𝒜), V(P) ∩ V(L₀) = {b P hP})
    (hconn : ∀ (P) (hP : P ∈ 𝒜), ∀ z ∈ V(P), AreConnectedIn P z (b P hP)) :
    ∃ ρ : S → S,
      (∀ (P) (hP : P ∈ 𝒜), ∀ z ∈ V(P), ρ z = b P hP) ∧
      (∀ z ∈ V(L₀), ρ z = z) ∧
      (∀ z : S, (∀ P ∈ 𝒜, z ∉ V(P)) → ρ z = z) ∧
      (∀ u v : S,
        AreConnectedIn (graphUnion L₀ (subgraphSUnion G 𝒜)) u v ↔
          AreConnectedIn L₀ (ρ u) (ρ v)) := by
  classical
  let ρ : S → S := fun z =>
    if h : ∃ P ∈ 𝒜, z ∈ V(P) then b (Classical.choose h) (Classical.choose_spec h).1 else z
  have hρ_P : ∀ (P) (hP : P ∈ 𝒜), ∀ z ∈ V(P), ρ z = b P hP := by
    intro P hP z hz
    have hex : ∃ Q ∈ 𝒜, z ∈ V(Q) := ⟨P, hP, hz⟩
    have h_eq : Classical.choose hex = P := by
      by_contra hne
      have hQ := Classical.choose_spec hex
      exact disjoint_left.mp (hDisj _ hQ.1 P hP hne) hQ.2 hz
    simp only [ρ, hex, ↓reduceDIte]
    congr 1
  have hρ_not_P : ∀ z : S, (∀ P ∈ 𝒜, z ∉ V(P)) → ρ z = z := by
    intro z hz
    have hex : ¬ ∃ P ∈ 𝒜, z ∈ V(P) := fun ⟨P, hP, hzP⟩ => hz P hP hzP
    exact dite_eq_right_iff.mpr fun h => (hex h).elim
  have hρ_L₀ : ∀ z ∈ V(L₀), ρ z = z := by
    intro z hzL₀
    by_cases hex : ∃ P ∈ 𝒜, z ∈ V(P)
    · rcases hex with ⟨P, hP, hzP⟩
      rw [hρ_P P hP z hzP]
      have hz_in : z ∈ V(P) ∩ V(L₀) := ⟨hzP, hzL₀⟩
      rw [hb_inter P hP, mem_singleton_iff] at hz_in
      exact hz_in.symm
    · exact dite_eq_right_iff.mpr fun h => (hex h).elim
  have hb_mem : ∀ (P) (hP : P ∈ 𝒜), b P hP ∈ V(P) ∧ b P hP ∈ V(L₀) := by
    intro P hP
    have : b P hP ∈ V(P) ∩ V(L₀) := (hb_inter P hP).symm ▸ mem_singleton (b P hP)
    exact this
  let M := subgraphSUnion G 𝒜
  have hMG : M ≤ G := subgraphSUnion_le h𝒜
  have hP_le_M : ∀ P ∈ 𝒜, P ≤ M := by
    intro P hP
    refine ⟨fun v hv => mem_iUnion₂.mpr ⟨P, hP, hv⟩, fun e x y hl => ?_⟩
    have heM : e ∈ E(M) := by
      rw [edgeSet_subgraphSUnion h𝒜]
      exact mem_iUnion₂.mpr ⟨P, hP, hl.edge_mem⟩
    exact (hMG.isLink_iff heM).mpr ((h𝒜 P hP).isLink_mono hl)
  have hcomp : L₀.Compatible M := Compatible.of_le_le hL₀ hMG
  let L'' := graphUnion L₀ M
  have hL₀_le : L₀ ≤ L'' := le_graphUnion_left L₀ M
  have hM_le : M ≤ L'' := le_graphUnion_right hcomp
  refine ⟨ρ, hρ_P, hρ_L₀, hρ_not_P, fun u v => ?_⟩
  constructor
  · intro hconn_uv
    rw [areConnectedIn_iff_walk] at hconn_uv
    rcases hconn_uv with ⟨hu, hv, ⟨W⟩⟩
    have hwalk : ∀ {x y : S}, GraphWalk L'' x y → x ∈ V(L'') → AreConnectedIn L₀ (ρ x) (ρ y) := by
      intro x y Wxy
      induction Wxy with
      | nil hx =>
        intro hx'
        rw [areConnectedIn_self_iff]
        rcases hx' with hxL₀ | hxM
        · rw [hρ_L₀ _ hxL₀]; exact hxL₀
        · rw [vertexSet_subgraphSUnion] at hxM
          obtain ⟨P, hP, hxP⟩ := mem_iUnion₂.mp hxM
          rw [hρ_P P hP _ hxP]
          exact (hb_mem P hP).2
      | @cons x w y e hl rest ih =>
        intro _
        have hstep : AreConnectedIn L₀ (ρ x) (ρ w) := by
          rw [isLink_graphUnion_of_compatible hcomp] at hl
          rcases hl with hl₀ | hlM
          · rw [hρ_L₀ x hl₀.left_mem, hρ_L₀ w hl₀.right_mem, areConnectedIn_iff_walk]
            exact ⟨hl₀.left_mem, hl₀.right_mem, ⟨GraphWalk.cons hl₀ (.nil hl₀.right_mem)⟩⟩
          · have heM : e ∈ E(M) := hlM.edge_mem
            rw [edgeSet_subgraphSUnion h𝒜] at heM
            obtain ⟨P, hP, heP⟩ := mem_iUnion₂.mp heM
            have hlP : P.IsLink e x w := ((hP_le_M P hP).isLink_iff heP).mpr hlM
            rw [hρ_P P hP x hlP.left_mem, hρ_P P hP w hlP.right_mem, areConnectedIn_self_iff]
            exact (hb_mem P hP).2
        exact hstep.trans (ih hl.right_mem)
    exact hwalk W hu
  · intro hconn₀
    have h_to_ρ : ∀ z : S, ρ z ∈ V(L₀) → AreConnectedIn L'' z (ρ z) := by
      intro z hz₀
      by_cases hex : ∃ P ∈ 𝒜, z ∈ V(P)
      · rcases hex with ⟨P, hP, hzP⟩
        rw [hρ_P P hP z hzP]
        exact (hconn P hP z hzP).mono ((hP_le_M P hP).trans hM_le)
      · have hρz : ρ z = z := dite_eq_right_iff.mpr fun h => (hex h).elim
        rw [hρz] at hz₀ ⊢
        exact areConnectedIn_self_iff.mpr (hL₀_le.vertexSet_mono hz₀)
    have h₁ : AreConnectedIn L'' u (ρ u) := h_to_ρ u hconn₀.left_mem
    have h₂ : AreConnectedIn L'' (ρ u) (ρ v) := hconn₀.mono hL₀_le
    have h₃ : AreConnectedIn L'' (ρ v) v := (h_to_ρ v hconn₀.right_mem).symm
    exact (h₁.trans h₂).trans h₃

omit [T2Space S] in
/-- Composing `exists_cuff_sleeve_homeo` across all cuffs `C ∈ cuffs S` yields a single
homeomorphism `α_hat : Shat ≃ₜ Shat` mapping `closure (cap.cuffDisc C)` onto `B C` and sending
`φ C i 0` to `φ C i 1` for every `C ∈ cuffs S` and `i : Fin (k C)`. -/
theorem exists_all_sleeves_homeo {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    (B : Set S → Set Shat) (W₀ : Set Shat)
    (hW₀_open : IsOpen W₀)
    (hB_disc : ∀ C ∈ cuffs S, IsClosedDisc (B C))
    (hAB : ∀ C ∈ cuffs S, closure (cap.cuffDisc C) ⊆ B C \ discBd (B C))
    (hbd_W₀ : ∀ C ∈ cuffs S, discBd (B C) ⊆ W₀)
    (hB_disj : ∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (B C₁) (B C₂))
    (k : Set S → ℕ) (φ : ∀ C : Set S, Fin (k C) → 𝕀 → Shat)
    (hφ_cont : ∀ C ∈ cuffs S, ∀ i, Continuous (φ C i))
    (hφ_mem : ∀ C ∈ cuffs S, ∀ i t, φ C i t ∈ B C \ discInt (closure (cap.cuffDisc C)))
    (hφ_bdA : ∀ C ∈ cuffs S, ∀ i t, φ C i t ∈ discBd (closure (cap.cuffDisc C)) ↔ t = 0)
    (hφ_bdB : ∀ C ∈ cuffs S, ∀ i t, φ C i t ∈ discBd (B C) ↔ t = 1)
    (hφ_disj : ∀ C ∈ cuffs S, ∀ i j, i ≠ j → ∀ s t, φ C i s ≠ φ C j t) :
    ∃ (α_hat : Shat ≃ₜ Shat) (K : Set Shat),
      IsClosed K ∧
      K ⊆ (⋃ C ∈ cuffs S, B C) ∪ W₀ ∧
      (⋃ C ∈ cuffs S, B C) ⊆ K ∧
      (∀ x ∉ K, α_hat x = x) ∧
      (∀ C ∈ cuffs S, α_hat '' closure (cap.cuffDisc C) = B C ∧
        α_hat '' discBd (closure (cap.cuffDisc C)) = discBd (B C) ∧
        ∀ i, α_hat (φ C i 0) = φ C i 1) ∧
      (∀ y ∈ range cap.emb, α_hat y ∉ ⋃ C ∈ cuffs S, (B C \ discBd (B C))) ∧
      (∀ y ∈ K ∩ range cap.emb, α_hat y ∈ W₀) := by
  have hShat : IsSurface Shat := cap.isSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x => hShat.2.2 x
  have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hind : ∀ F ⊆ cuffs S,
      ∃ (α_F : Shat ≃ₜ Shat) (K_F : Set Shat),
        IsClosed K_F ∧
        K_F ⊆ (⋃ C ∈ F, B C) ∪ W₀ ∧
        (⋃ C ∈ F, B C) ⊆ K_F ∧
        (∀ C' ∈ cuffs S \ F, Disjoint K_F (B C')) ∧
        (∀ x ∉ K_F, α_F x = x) ∧
        (∀ C ∈ F, α_F '' closure (cap.cuffDisc C) = B C ∧ ∀ i, α_F (φ C i 0) = φ C i 1) := by
    intro F hF_sub
    have hF_fin : F.Finite := hfin.subset hF_sub
    refine Set.Finite.induction_on F hF_fin ?_ ?_ hF_sub
    · intro _
      refine ⟨Homeomorph.refl Shat, ∅, isClosed_empty, empty_subset _,
        by simp, fun _ _ => disjoint_bot_left, fun _ _ => rfl, fun _ h => h.elim⟩
    · intro C₀ F₀ hC₀_not_F₀ _ ih hins_sub
      have hC₀ : C₀ ∈ cuffs S := hins_sub (mem_insert C₀ F₀)
      have hF₀_sub : F₀ ⊆ cuffs S := (subset_insert C₀ F₀).trans hins_sub
      obtain ⟨α₀, K₀, hK₀_cl, hK₀_sub, hB_K₀, hK₀_disj, hα₀_fix, hα₀_C⟩ := ih hF₀_sub
      have hK₀_disj_C₀ : Disjoint K₀ (B C₀) := hK₀_disj C₀ ⟨hC₀, hC₀_not_F₀⟩
      let R := K₀ ∪ ⋃ C' ∈ cuffs S \ insert C₀ F₀, B C'
      have hR_cl : IsClosed R := by
        refine hK₀_cl.union ?_
        exact (hfin.subset sdiff_subset).isClosed_biUnion
          fun C' hC' => (hB_disc C' hC'.1).isCompact.isClosed
      have hR_disj_C₀ : Disjoint R (B C₀) := by
        refine Disjoint.union_left hK₀_disj_C₀ ?_
        rw [disjoint_iUnion₂_left]
        intro C' hC'
        have hne : C' ≠ C₀ := fun h => hC'.2 (h ▸ mem_insert C₀ F₀)
        exact hB_disj C' hC'.1 C₀ hC₀ hne
      let W_C₀ := W₀ \ R
      have hW_C₀_open : IsOpen W_C₀ := hW₀_open.sdiff hR_cl
      have hbd_W_C₀ : discBd (B C₀) ⊆ W_C₀ :=
        subset_sdiff.mpr ⟨hbd_W₀ C₀ hC₀,
          hR_disj_C₀.symm.mono_left (Surface.discBd_subset (B C₀))⟩
      obtain ⟨E₀, hE₀_disc, hBE₀, hE₀_sub⟩ :=
        Surface.exists_disc_around hman (hB_disc C₀ hC₀)
          (fun x _ => by_contra fun hx => notMem_empty x (cap.bd_empty ▸ hx))
          hW_C₀_open hbd_W_C₀
      have hE₀_disj_R : Disjoint E₀ R := by
        have h₁ : Disjoint (B C₀) R := hR_disj_C₀.symm
        have h₂ : Disjoint W_C₀ R := disjoint_sdiff_left
        exact (h₁.union_left h₂).mono_left hE₀_sub
      have hE₀_disj_K₀ : Disjoint E₀ K₀ :=
        hE₀_disj_R.mono_right subset_union_left
      obtain ⟨e₀, he₀_AB, he₀_fix, he₀_φ⟩ :=
        exists_cuff_sleeve_homeo hman (cap.cuffDisc_closedDisc C₀ hC₀) (hB_disc C₀ hC₀) hE₀_disc
          (hAB C₀ hC₀) hBE₀ (φ C₀) (hφ_cont C₀ hC₀) (hφ_mem C₀ hC₀)
          (hφ_bdA C₀ hC₀) (hφ_bdB C₀ hC₀) (hφ_disj C₀ hC₀)
      have he₀_mem_E₀ : ∀ x ∈ E₀, e₀ x ∈ E₀ := by
        intro x hxE₀
        by_contra hnot
        have hfix := he₀_fix (e₀ x) hnot
        exact hnot ((e₀.injective hfix).symm ▸ hxE₀)
      let α' := e₀.trans α₀
      let K' := K₀ ∪ E₀
      have hα'_on_E₀ : ∀ x ∈ E₀, α' x = e₀ x := by
        intro x hxE₀
        change α₀ (e₀ x) = e₀ x
        exact hα₀_fix (e₀ x) (disjoint_left.mp hE₀_disj_K₀ (he₀_mem_E₀ x hxE₀))
      have hα'_on_K₀ : ∀ x ∈ K₀, α' x = α₀ x := by
        intro x hxK₀
        change α₀ (e₀ x) = α₀ x
        rw [he₀_fix x (disjoint_right.mp hE₀_disj_K₀ hxK₀)]
      refine ⟨α', K', hK₀_cl.union hE₀_disc.isCompact.isClosed, ?_, ?_, ?_, ?_, ?_⟩
      · refine union_subset (hK₀_sub.trans ?_) (hE₀_sub.trans ?_)
        · exact union_subset_union_left W₀ (biUnion_subset_biUnion_left (subset_insert C₀ F₀))
        · refine union_subset ?_ (sdiff_subset.trans subset_union_right)
          exact (subset_biUnion_of_mem (mem_insert C₀ F₀)).trans subset_union_left
      · rw [biUnion_insert]
        exact union_subset ((hBE₀.trans sdiff_subset).trans subset_union_right)
          (hB_K₀.trans subset_union_left)
      · intro C' hC'
        refine Disjoint.union_left (hK₀_disj C' ⟨hC'.1, fun h => hC'.2 (mem_insert_of_mem C₀ h)⟩) ?_
        exact hE₀_disj_R.mono_right (subset_union_of_subset_right (subset_biUnion_of_mem hC') _)
      · intro x hx
        have hxK₀ : x ∉ K₀ := fun h => hx (Or.inl h)
        have hxE₀ : x ∉ E₀ := fun h => hx (Or.inr h)
        change α₀ (e₀ x) = x
        rw [he₀_fix x hxE₀, hα₀_fix x hxK₀]
      · intro C hC_ins
        rcases mem_insert_iff.mp hC_ins with rfl | hC_F₀
        · have hA_sub_E₀ : closure (cap.cuffDisc C) ⊆ E₀ :=
            (hAB C hC₀).trans (sdiff_subset.trans (hBE₀.trans sdiff_subset))
          refine ⟨?_, fun i => ?_⟩
          · rw [← he₀_AB]
            exact image_congr fun x hx => hα'_on_E₀ x (hA_sub_E₀ hx)
          · have h0_E₀ : φ C i 0 ∈ E₀ := by
              have h0_bdA : φ C i 0 ∈ discBd (closure (cap.cuffDisc C)) :=
                (hφ_bdA C hC₀ i 0).mpr rfl
              exact hA_sub_E₀ (Surface.discBd_subset _ h0_bdA)
            rw [hα'_on_E₀ _ h0_E₀, he₀_φ i]
        · have hA_sub_K₀ : closure (cap.cuffDisc C) ⊆ K₀ :=
            (hAB C (hF₀_sub hC_F₀)).trans
              (sdiff_subset.trans ((subset_biUnion_of_mem hC_F₀).trans hB_K₀))
          obtain ⟨hAB_C, hφ_C⟩ := hα₀_C C hC_F₀
          refine ⟨?_, fun i => ?_⟩
          · rw [← hAB_C]
            exact image_congr fun x hx => hα'_on_K₀ x (hA_sub_K₀ hx)
          · have h0_K₀ : φ C i 0 ∈ K₀ := by
              have h0_bdA : φ C i 0 ∈ discBd (closure (cap.cuffDisc C)) :=
                (hφ_bdA C (hF₀_sub hC_F₀) i 0).mpr rfl
              exact hA_sub_K₀ (Surface.discBd_subset _ h0_bdA)
            rw [hα'_on_K₀ _ h0_K₀, hφ_C i]
  obtain ⟨α_hat, K, hK_cl, hK_sub, hB_K, _, hα_fix, hα_C⟩ := hind (cuffs S) Subset.rfl
  have hbd_eq : ∀ C ∈ cuffs S,
      α_hat '' discBd (closure (cap.cuffDisc C)) = discBd (B C) := by
    intro C hC
    have hA_disc := cap.cuffDisc_closedDisc C hC
    have hbd_img := (GM19.isClosedDisc_image hA_disc α_hat.isEmbedding).2
    rwa [(hα_C C hC).1, eq_comm] at hbd_img
  have h_not_intB : ∀ y ∈ range cap.emb, α_hat y ∉ ⋃ C ∈ cuffs S, (B C \ discBd (B C)) := by
    rintro _ ⟨x, rfl⟩ hy
    obtain ⟨C, hC, hyB, hy_not_bd⟩ := mem_iUnion₂.mp hy
    obtain ⟨z, hz_cl, hzx⟩ := (hα_C C hC).1 ▸ hyB
    have hzx' : z = cap.emb x := α_hat.injective hzx
    subst hzx'
    have hz_not_bdA : cap.emb x ∉ discBd (closure (cap.cuffDisc C)) := by
      intro hbdA
      exact hy_not_bd (hbd_eq C hC ▸ mem_image_of_mem α_hat hbdA)
    have hz_intA : cap.emb x ∈ cap.cuffDisc C := by
      rw [cuffDisc_eq_discInt_w cap hC]
      exact ⟨hz_cl, hz_not_bdA⟩
    have : cap.emb x ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_biUnion hC hz_intA
    exact this (mem_range_self x)
  refine ⟨α_hat, K, hK_cl, hK_sub, hB_K, hα_fix,
    fun C hC => ⟨(hα_C C hC).1, hbd_eq C hC, (hα_C C hC).2⟩, h_not_intB, ?_⟩
  rintro y ⟨hyK, hy_range⟩
  have hαy_K : α_hat y ∈ K := by
    by_contra hnot
    have hfix := hα_fix (α_hat y) hnot
    exact hnot ((α_hat.injective hfix).symm ▸ hyK)
  rcases hK_sub hαy_K with hyB_union | hyW₀
  · obtain ⟨C, hC, hyB⟩ := mem_iUnion₂.mp hyB_union
    by_cases hy_bd : α_hat y ∈ discBd (B C)
    · exact hbd_W₀ C hC hy_bd
    · exact (h_not_intB y hy_range (mem_biUnion hC ⟨hyB, hy_bd⟩)).elim
  · exact hyW₀

omit [TopologicalSpace S] [T2Space S] in
/-- Any path `P` in `G` from `a` to `y ∈ Y` contains a subpath `Q` from `a` to some `b ∈ Y`
with `V(Q) ⊆ V(P)`, `E(Q) ⊆ E(P)`, and `IsFromToPathWithEnds G Q {a} Y a b`. -/
theorem exists_fromToPath_of_path {G P : Graph S (Set S)} {Y : Set S} {a y : S}
    (hP : IsGraphPathWithEnds G P a y) (hy : y ∈ Y) :
    ∃ b ∈ Y, ∃ Q : Graph S (Set S),
      V(Q) ⊆ V(P) ∧ E(Q) ⊆ E(P) ∧ IsFromToPathWithEnds G Q {a} Y a b := by
  rcases hP with ⟨hP_le, W₀, hW₀_simp, hVP, hEP⟩
  obtain ⟨W, hsW, heW⟩ := W₀.exists_transfer
    (fun _ _ _ _ hl => hP_le.isLink_mono hl)
    (fun x hx => hP_le.vertexSet_mono (W₀.mem_vertexSet_of_mem_support hx))
  have hW_simp : W.IsSimple := by change W.support.Nodup; rwa [hsW]
  have hind : ∀ {u v : S} (R : GraphWalk G u v), R.IsSimple → v ∈ Y →
      ∃ b ∈ Y, ∃ R' : GraphWalk G u b,
        R'.IsSimple ∧
        (∀ x ∈ R'.support, x ∈ R.support) ∧
        (∀ e ∈ R'.edges, e ∈ R.edges) ∧
        (∀ x ∈ R'.support, x ∈ Y → x = b) := by
    intro u v R
    induction R with
    | @nil u hu =>
      intro _ hvY
      refine ⟨u, hvY, .nil hu, by simp [GraphWalk.IsSimple],
        fun _ h => h, fun _ h => h, ?_⟩
      intro x hx _
      simpa using hx
    | @cons u w v e hl r ih =>
      intro hR_simp hvY
      by_cases huY : u ∈ Y
      · refine ⟨u, huY, .nil hl.left_mem, by simp [GraphWalk.IsSimple],
          fun x hx => by simp at hx; simp [hx],
          fun _ h => by simp at h, ?_⟩
        intro x hx _
        simpa using hx
      · have hnd := List.nodup_cons.mp hR_simp
        obtain ⟨b, hbY, r', hr'_simp, hr'_supp, hr'_edges, hr'_Y⟩ := ih hnd.2 hvY
        refine ⟨b, hbY, .cons hl r', ?_, ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨fun hu_r' => hnd.1 (hr'_supp u hu_r'), hr'_simp⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem u (hr'_supp x hx)
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem e (hr'_edges f hf)
        · intro x hx hxY
          rcases List.mem_cons.mp hx with rfl | hx
          · exact (huY hxY).elim
          · exact hr'_Y x hx hxY
  obtain ⟨b, hbY, W', hW'_simp, hW'_supp, hW'_edges, hW'_Y⟩ := hind W hW_simp hy
  let Q := walkSubgraph W'
  have hQ_path : IsGraphPathWithEnds G Q a b := isGraphPathWithEnds_walkSubgraph hW'_simp
  have hVQ : V(Q) = {x | x ∈ W'.support} := vertexSet_walkSubgraph W'
  have hEQ : E(Q) = {e | e ∈ W'.edges} := edgeSet_walkSubgraph W'
  refine ⟨b, hbY, Q, ?_, ?_, hQ_path, ?_, ?_⟩
  · rw [hVQ, hVP]
    intro x hx
    exact hsW ▸ hW'_supp x hx
  · rw [hEQ, hEP]
    intro e he
    exact heW ▸ hW'_edges e he
  · ext x
    simp only [hVQ, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ W'.start_mem_support, h⟩⟩
  · ext x
    simp only [hVQ, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun ⟨hx, hxY⟩ => hW'_Y x hx hxY, fun h => ⟨h ▸ W'.end_mem_support, h ▸ hbY⟩⟩

/-- Gluing `A₁` and `K_L ≤ K` via **2.5** when `A₁` and `A_L` have the same effect on
`V(A₁) ∩ V(K) = V(A_L) ∩ V(K)`. -/
theorem hasSameEffectOn_graphUnion_of_sameEffect_inter
    {G' L' A₁ A_L K_L K : Graph α β} {Z : Set α}
    (hA_L_le_L' : A_L ≤ L') (hK_L_le_L' : K_L ≤ L') (hK_L_le_K : K_L ≤ K)
    (hVL' : V(L') = V(A_L) ∪ V(K_L)) (hEL' : E(L') = E(A_L) ∪ E(K_L))
    (hComp_A₁_KL : A₁.Compatible K_L)
    (hDisj_EA₁_EK : Disjoint E(A₁) E(K))
    (hDisj_EA_EK : Disjoint E(A_L) E(K))
    (hVA₁_inter_VK : V(A₁) ∩ V(K) = V(A_L) ∩ V(K))
    (hSame_A₁_AL_inter : HasSameEffectOn A₁ A_L (V(A₁) ∩ V(K)))
    (hZK : Z ⊆ V(K)) (_hG' : L' ≤ G') :
    HasSameEffectOn (graphUnion A₁ K_L) L' Z := by
  let L₁ := graphUnion A₁ K_L
  have hDisj_EA₁_EKL : Disjoint E(A₁) E(K_L) :=
    hDisj_EA₁_EK.mono_right hK_L_le_K.edgeSet_mono
  have hDisj_EAL_EKL : Disjoint E(A_L) E(K_L) :=
    hDisj_EA_EK.mono_right hK_L_le_K.edgeSet_mono
  have hVL₁_eq_VL' : V(L₁) ∩ V(K) = V(L') ∩ V(K) := by
    rw [vertexSet_graphUnion, union_inter_distrib_right, hVA₁_inter_VK,
      ← union_inter_distrib_right, ← hVL']
  have hSame_L₁_L'_VL : HasSameEffectOn L₁ L' (V(L₁) ∩ V(K)) := by
    let Z₀ := V(L₁) ∩ V(K)
    have hsep₁ : IsGraphSeparation L₁ A₁ K_L :=
      ⟨le_graphUnion_left A₁ K_L, le_graphUnion_right hComp_A₁_KL, rfl, rfl, hDisj_EA₁_EKL⟩
    have hAB₁_Z₀ : V(A₁) ∩ V(K_L) ⊆ Z₀ :=
      fun _ ⟨hxA₁, hxKL⟩ => ⟨Or.inl hxA₁, hK_L_le_K.vertexSet_mono hxKL⟩
    have hdiv₁ : IsIndexedZDivision L₁ Z₀ (![A₁, K_L] : Fin 2 → Graph α β) :=
      isIndexedZDivision_of_isGraphSeparation hsep₁ hAB₁_Z₀
    have hsep' : IsGraphSeparation L' A_L K_L :=
      ⟨hA_L_le_L', hK_L_le_L', hVL'.symm, hEL'.symm, hDisj_EAL_EKL⟩
    have hAB'_Z₀ : V(A_L) ∩ V(K_L) ⊆ Z₀ := by
      change V(A_L) ∩ V(K_L) ⊆ V(L₁) ∩ V(K)
      rw [hVL₁_eq_VL']
      exact fun _ ⟨hxAL, hxKL⟩ => ⟨hA_L_le_L'.vertexSet_mono hxAL, hK_L_le_K.vertexSet_mono hxKL⟩
    have hdiv' : IsIndexedZDivision L' Z₀ (![A_L, K_L] : Fin 2 → Graph α β) :=
      isIndexedZDivision_of_isGraphSeparation hsep' hAB'_Z₀
    have hZ₀_A₁ : Z₀ ∩ V(A₁) = V(A₁) ∩ V(K) := by
      ext x
      simp only [Z₀, mem_inter_iff]
      exact ⟨fun ⟨⟨_, hxK⟩, hxA⟩ => ⟨hxA, hxK⟩, fun ⟨hxA, hxK⟩ => ⟨⟨Or.inl hxA, hxK⟩, hxA⟩⟩
    have hZ₀_AL : Z₀ ∩ V(A_L) = V(A_L) ∩ V(K) := by
      change (V(L₁) ∩ V(K)) ∩ V(A_L) = V(A_L) ∩ V(K)
      rw [hVL₁_eq_VL']
      ext x
      simp only [mem_inter_iff]
      exact ⟨fun ⟨⟨_, hxK⟩, hxA⟩ => ⟨hxA, hxK⟩,
        fun ⟨hxA, hxK⟩ => ⟨⟨hA_L_le_L'.vertexSet_mono hxA, hxK⟩, hxA⟩⟩
    have h_a : ∀ i : Fin 2,
        (id : α → α) '' (Z₀ ∩ V((![A₁, K_L] : Fin 2 → Graph α β) i)) =
          Z₀ ∩ V((![A_L, K_L] : Fin 2 → Graph α β) i) := by
      intro i
      rw [image_id]
      fin_cases i
      · change Z₀ ∩ V(A₁) = Z₀ ∩ V(A_L)
        rw [hZ₀_A₁, hZ₀_AL, hVA₁_inter_VK]
      · rfl
    have h_b : ∀ u ∈ Z₀, ∀ v ∈ Z₀, u ≠ v → (id : α → α) u = id v →
        ∃ i : Fin 2, u ∈ V((![A₁, K_L] : Fin 2 → Graph α β) i) ∧
          v ∈ V((![A₁, K_L] : Fin 2 → Graph α β) i) :=
      fun _ _ _ _ hne heq => (hne heq).elim
    have h_c : ∀ i : Fin 2,
        ∀ u ∈ Z₀ ∩ V((![A₁, K_L] : Fin 2 → Graph α β) i),
        ∀ v ∈ Z₀ ∩ V((![A₁, K_L] : Fin 2 → Graph α β) i),
        AreConnectedIn ((![A₁, K_L] : Fin 2 → Graph α β) i) u v ↔
          AreConnectedIn (subgraphInter L' L' ((![A_L, K_L] : Fin 2 → Graph α β) i)) u v := by
      intro i u hu v hv
      fin_cases i
      · change AreConnectedIn A₁ u v ↔ AreConnectedIn (subgraphInter L' L' A_L) u v
        have h_inter_AL : subgraphInter L' L' A_L = A_L :=
          le_antisymm (subgraphInter_le_right le_rfl hA_L_le_L')
            (le_subgraphInter le_rfl hA_L_le_L' hA_L_le_L' le_rfl)
        rw [h_inter_AL]
        exact effectOn_eq_iff_areConnectedIn.mp hSame_A₁_AL_inter
          u (hZ₀_A₁ ▸ hu) v (hZ₀_A₁ ▸ hv)
      · change AreConnectedIn K_L u v ↔ AreConnectedIn (subgraphInter L' L' K_L) u v
        have h_inter_KL : subgraphInter L' L' K_L = K_L :=
          le_antisymm (subgraphInter_le_right le_rfl hK_L_le_L')
            (le_subgraphInter le_rfl hK_L_le_L' hK_L_le_L' le_rfl)
        rw [h_inter_KL]
    have ⟨_, hconn_iff⟩ :=
      theorem_2_5_proof le_rfl (hVL₁_eq_VL'.subset.trans inter_subset_left) hdiv'
        inter_subset_left hdiv₁ (fun _ => le_rfl) h_a h_b h_c
    rw [hdiv₁.2.1] at hconn_iff
    exact effectOn_eq_iff_areConnectedIn.mpr hconn_iff
  have hSame_L₁_L'_VK : HasSameEffectOn L₁ L' V(K) := by
    rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
    intro u huK v hvK
    constructor
    · intro hconn
      have hu : u ∈ V(L₁) ∩ V(K) := ⟨hconn.left_mem, huK⟩
      have hv : v ∈ V(L₁) ∩ V(K) := ⟨hconn.right_mem, hvK⟩
      exact (effectOn_eq_iff_areConnectedIn.mp hSame_L₁_L'_VL u hu v hv).mp hconn
    · intro hconn
      have hu : u ∈ V(L₁) ∩ V(K) := hVL₁_eq_VL'.symm ▸ ⟨hconn.left_mem, huK⟩
      have hv : v ∈ V(L₁) ∩ V(K) := hVL₁_eq_VL'.symm ▸ ⟨hconn.right_mem, hvK⟩
      exact (effectOn_eq_iff_areConnectedIn.mp hSame_L₁_L'_VL u hu v hv).mpr hconn
  rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn] at hSame_L₁_L'_VK ⊢
  exact fun u hu v hv => hSame_L₁_L'_VK u (hZK hu) v (hZK hv)

private theorem arcComponentsIn_empty {X : Type*} [TopologicalSpace X] :
    arcComponentsIn (∅ : Set X) = ∅ := by
  ext C
  simp only [arcComponentsIn, mem_ofPred_eq, subset_empty_iff, mem_empty_iff_false, iff_false]
  rintro ⟨hne, hC, _, _⟩
  exact hne.ne_empty hC

/-- Pushforward of a drawing `P : Drawing S₁` along a closed embedding `f : S₁ → S₂`
(without requiring `[Nonempty S₁]`). -/
noncomputable def drawingMapEmb {S₁ S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂]
    [T2Space S₁] {f : S₁ → S₂} (P : Surface.Drawing S₁) (hf : IsClosedEmbedding f) :
    Surface.Drawing S₂ :=
  have harc : ∀ {F : Set S₁}, arcComponentsIn (f '' F) = image f '' arcComponentsIn F := by
    intro F
    rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
    · rw [image_empty, arcComponentsIn_empty, arcComponentsIn_empty, image_empty]
    · have : Nonempty S₁ := ⟨x₀⟩
      have hl : Function.LeftInverse (Function.invFun f) f :=
        Function.leftInverse_invFun hf.injective
      refine GM11.arcComponentsIn_image hf.continuous.continuousOn ?_ fun x _ => hl x
      rw [hf.isInducing.continuousOn_iff]
      refine continuousOn_id.congr ?_
      rintro _ ⟨x, -, rfl⟩
      simp [hl x]
  have hset : f '' P.U \ f '' P.V = f '' (P.U \ P.V) := (image_sdiff hf.injective _ _).symm
  have hcap : ∀ e : Set S₁, closure (f '' e) ∩ f '' P.V = f '' (closure e ∩ P.V) := fun e => by
    rw [hf.closure_image_eq, image_inter hf.injective]
  { U := f '' P.U
    V := f '' P.V
    V_subset_U := image_mono P.V_subset_U
    isClosed_U := hf.isClosedMap _ P.isClosed_U
    finite_V := P.finite_V.image _
    finite_edges := by
      rw [hset, harc]
      exact P.finite_edges.image _
    edge_cond := by
      rw [hset, harc]
      rintro _ ⟨e, he, rfl⟩
      rcases P.edge_cond e he with ⟨u, v, h1, h2, ⟨φ_line, h0, h1_end⟩⟩ | ⟨u, h2, h3⟩
      · refine Or.inl ⟨f u, f v, hf.injective.ne h1, by rw [hcap, h2, image_pair], ?_⟩
        rw [hf.closure_image_eq]
        refine ⟨φ_line.trans (hf.isEmbedding.homeomorphImage (closure e)), ?_, ?_⟩
        · change f (φ_line 0).1 = f u
          rw [h0]
        · change f (φ_line 1).1 = f v
          rw [h1_end]
      · refine Or.inr ⟨f u, by rw [hcap, h2, image_singleton], ?_⟩
        rw [hf.closure_image_eq]
        exact h3.elim fun φ => ⟨φ.trans (hf.isEmbedding.homeomorphImage _)⟩ }

theorem drawingMapEmb_E {S₁ S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂]
    [T2Space S₁] {f : S₁ → S₂} (P : Surface.Drawing S₁) (hf : IsClosedEmbedding f) :
    (drawingMapEmb P hf).E = image f '' P.E := by
  change arcComponentsIn (f '' P.U \ f '' P.V) = image f '' arcComponentsIn (P.U \ P.V)
  rw [← image_sdiff hf.injective]
  rcases (P.U \ P.V).eq_empty_or_nonempty with h_emp | ⟨x₀, _⟩
  · rw [h_emp, image_empty, arcComponentsIn_empty, arcComponentsIn_empty, image_empty]
  · have : Nonempty S₁ := ⟨x₀⟩
    have hl : Function.LeftInverse (Function.invFun f) f :=
      Function.leftInverse_invFun hf.injective
    refine GM11.arcComponentsIn_image hf.continuous.continuousOn ?_ fun x _ => hl x
    rw [hf.isInducing.continuousOn_iff]
    refine continuousOn_id.congr ?_
    rintro _ ⟨x, -, rfl⟩
    simp [hl x]

theorem drawingMapEmb_toGraph_eq {S₁ S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂]
    [T2Space S₁] {f : S₁ → S₂} (P : Surface.Drawing S₁) (hf : IsClosedEmbedding f) :
    (drawingMapEmb P hf).toGraph =
      P.toGraph.mapEmbed ⟨f, hf.injective⟩ ⟨image f, image_injective.mpr hf.injective⟩ := by
  let P' := drawingMapEmb P hf
  have harc : P'.E = image f '' P.E := drawingMapEmb_E P hf
  refine Graph.ext rfl fun e x y => ?_
  constructor
  · rintro ⟨he, ⟨x₀, hx₀, rfl⟩, ⟨y₀, hy₀, rfl⟩, hcap⟩
    rw [harc] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    refine ⟨e₀, x₀, y₀, ⟨he₀, hx₀, hy₀, ?_⟩, rfl, rfl, rfl⟩
    apply image_injective.mpr hf.injective
    have hcap' : closure (f '' e₀) ∩ f '' P.V = {f x₀, f y₀} := hcap
    change f '' (closure e₀ ∩ P.V) = f '' {x₀, y₀}
    rw [image_inter hf.injective, ← hf.closure_image_eq, hcap', image_pair]
  · rintro ⟨e₀, x₀, y₀, ⟨he₀, hx₀, hy₀, hcap⟩, rfl, rfl, rfl⟩
    have he : f '' e₀ ∈ P'.E := harc ▸ mem_image_of_mem _ he₀
    refine ⟨he, mem_image_of_mem _ hx₀, mem_image_of_mem _ hy₀, ?_⟩
    change closure (f '' e₀) ∩ f '' P.V = {f x₀, f y₀}
    rw [hf.closure_image_eq, ← image_inter hf.injective, hcap, image_pair]

theorem areConnectedIn_mapEmbed_iff {α₁ : Type*} {β₁ : Type*} {α₂ : Type*} {β₂ : Type*}
    (ιV : α₁ ↪ α₂) (ιE : β₁ ↪ β₂) (H : Graph α₁ β₁) {u v : α₁} :
    AreConnectedIn (H.mapEmbed ιV ιE) (ιV u) (ιV v) ↔ AreConnectedIn H u v := by
  simp only [AreConnectedIn, mem_graphComponents_mapEmbed_iff]
  constructor
  · rintro ⟨_, ⟨C, hC, rfl⟩, hu, hv⟩
    exact ⟨C, hC, (ιV.injective.mem_set_image).mp hu, (ιV.injective.mem_set_image).mp hv⟩
  · rintro ⟨C, hC, hu, hv⟩
    exact ⟨C.mapEmbed ιV ιE, ⟨C, hC, rfl⟩, mem_image_of_mem ιV hu, mem_image_of_mem ιV hv⟩

/-- Core topological and drawing construction for the proof of **4.2** (Graph Minors XXII,
pages 538–539): constructs the homeomorphism $\alpha \colon \Sigma \to \Sigma_0$, the glued drawing
$\Gamma'' = \Gamma_0 \cup \bigcup_C (\Gamma \cap S(C))$ in $\hat{\Sigma}$, and the subgraph
$L'' = L_0 \cup \bigcup_C M_C'$ with the same effect on $V(\Gamma \cap K) \cup (V(\Gamma) \cap \operatorname{bd}(\Sigma))$
as $L' \cap \Gamma'$. -/
theorem sleeve_variant_pullback {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    (D D' : Surface.Drawing S) (Y₀ : Set S) (hY₀_sub : Y₀ ⊆ D.V)
    (h₀ : ℕ) (_hh₀ : 1 ≤ h₀)
    (hDU_bd : D.U ∩ bd S ⊆ D.V)
    (hDV_bd : D'.V ∩ bd S = D.V ∩ bd S)
    (S_sleeve : Set S → Set Shat)
    (hSleeve : ∀ C ∈ cuffs S, IsSleeve cap D C (S_sleeve C))
    (hSleeve_disj : ∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (S_sleeve C₁) (S_sleeve C₂))
    (hPaths : ∀ C ∈ cuffs S, ∃ P : ↑(D.V ∩ C) → Graph S (Set S),
      (∀ x : ↑(D.V ∩ C), ∃ y ∈ D.V ∩ cap.emb ⁻¹' subBd (S_sleeve C),
        IsGraphPathWithEnds D.toGraph (P x) x.1 y) ∧
      Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂)))
    (hSleeve_T : ∀ C ∈ cuffs S,
      subBd (S_sleeve C) ⊆
        cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' (Y₀ ∪ (D.V ∩ bd S))) (h₀ + 1)) ∧
      Disjoint (S_sleeve C) (cap.emb '' Y₀))
    (hVar : IsVariant D D'
      ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
        cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' (Y₀ ∪ (D.V ∩ bd S))) (h₀ + 1)))
    (H' : Graph S (Set S)) (hH'_le : H' ≤ D'.toGraph)
    (E_K : Set (Set S)) (hEK_sub : E_K ⊆ D.E)
    (hEK_Y₀ : ∀ e₀ ∈ E_K, (closure e₀ ∩ Y₀).Nonempty)
    (hDisj_EH'_EK : Disjoint E(H') E_K) :
    let D_hat := drawingMapEmb D (isClosedEmbedding_w hS cap)
    let Y_S := Y₀ ∪ (D.V ∩ bd S)
    let Y_hat := cap.emb '' Y_S
    ∃ (D''_hat : Surface.Drawing Shat) (H''_hat : Graph Shat (Set Shat)),
      D''_hat.U ⊆ range cap.emb ∧
      IsVariant D_hat D''_hat (insulatedSet D_hat Y_hat h₀) ∧
      Y_hat ⊆ D''_hat.V ∧
      (image cap.emb) '' E_K ⊆ D''_hat.E ∧
      (∀ e₀ ∈ E_K, ∀ x y,
        D''_hat.toGraph.IsLink (cap.emb '' e₀) x y ↔ D_hat.toGraph.IsLink (cap.emb '' e₀) x y) ∧
      H''_hat ≤ D''_hat.toGraph ∧
      Disjoint E(H''_hat) ((image cap.emb) '' E_K) ∧
      V(H''_hat) ∩ Y_hat = cap.emb '' (V(H') ∩ Y_S) ∧
      (∀ u ∈ Y_S, ∀ v ∈ Y_S,
        AreConnectedIn H''_hat (cap.emb u) (cap.emb v) ↔ AreConnectedIn H' u v) ∧
      Nonempty (Shat ↪ S) := by
  classical
  have hcap_emb : IsClosedEmbedding cap.emb := isClosedEmbedding_w hS cap
  let D_hat := drawingMapEmb D hcap_emb
  let Y_S := Y₀ ∪ (D.V ∩ bd S)
  let Y_hat := cap.emb '' Y_S
  let h := h₀ + 1
  let T_hat := insulatedSet D_hat Y_hat h
  let T_hat₀ := insulatedSet D_hat Y_hat h₀
  let T := cap.emb ⁻¹' T_hat
  let S_total := ⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C
  let S_union := ⋃ C ∈ cuffs S, S_sleeve C
  have hShat : IsSurface Shat := cap.isSurface
  have hfin_cuffs : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hB_disc : ∀ C ∈ cuffs S, IsClosedDisc (S_sleeve C) :=
    fun C hC => (hSleeve C hC).isClosedDisc
  have hB_cl : ∀ C ∈ cuffs S, IsClosed (S_sleeve C) :=
    fun C hC => (hB_disc C hC).isCompact.isClosed
  have hSunion_cl : IsClosed S_union :=
    hfin_cuffs.isClosed_biUnion hB_cl
  have hB_bd_eq : ∀ C ∈ cuffs S, subBd (S_sleeve C) = discBd (S_sleeve C) :=
    fun C hC => subBd_eq_discBd_of_bd_eq_empty hShat cap.bd_empty (hB_disc C hC)
  have hT_sub_T₀ : T_hat ⊆ T_hat₀ := by
    intro z ⟨Δ, hΔ_disc, hΔ_nest, hΔ_ends⟩
    have hpos : 0 < h := Nat.succ_pos h₀
    obtain ⟨hz_in, hdisj⟩ := hΔ_ends hpos
    refine ⟨fun i : Fin h₀ => Δ ⟨i.1, Nat.lt_succ_of_lt i.2⟩,
      fun i => hΔ_disc ⟨i.1, Nat.lt_succ_of_lt i.2⟩,
      fun i hi => hΔ_nest ⟨i.1, Nat.lt_succ_of_lt i.2⟩ (Nat.lt_succ_of_lt hi),
      fun hh₀' => ⟨?_, hdisj⟩⟩
    have hpred_lt : h₀ - 1 + 1 < h := by omega
    have hsub := hΔ_nest ⟨h₀ - 1, by omega⟩ hpred_lt
    have h_eq : (⟨h₀ - 1 + 1, hpred_lt⟩ : Fin h) = ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩ := by
      ext; dsimp [h]; omega
    rw [h_eq] at hsub
    exact hsub hz_in.1
  have hY_disj_T₀ : Disjoint Y_hat T_hat₀ :=
    disjoint_insulatedSet D_hat Y_hat _hh₀
  have hY_disj_T : Disjoint Y_hat T_hat :=
    hY_disj_T₀.mono_right hT_sub_T₀
  have hbd_disj_bdS : ∀ C ∈ cuffs S, Disjoint (subBd (S_sleeve C)) (cap.emb '' bd S) := by
    intro C hC
    rw [disjoint_left]
    rintro z hz_bd ⟨x, hx_bdS, rfl⟩
    obtain ⟨u, hu_U, hux⟩ := (hSleeve C hC).bd_subset_U hz_bd
    obtain rfl : u = x := cap.isEmbedding.injective hux
    obtain ⟨w, hw_T, hwx⟩ := (hSleeve_T C hC).1 hz_bd
    obtain rfl : w = u := cap.isEmbedding.injective hwx
    have hx_V : w ∈ D.V := hDU_bd ⟨hu_U, hx_bdS⟩
    have hz_Y : cap.emb w ∈ Y_hat := mem_image_of_mem cap.emb (Or.inr ⟨hx_V, hx_bdS⟩)
    exact disjoint_left.mp hY_disj_T hz_Y hw_T
  have hAB : ∀ C ∈ cuffs S, closure (cap.cuffDisc C) ⊆ S_sleeve C \ discBd (S_sleeve C) := by
    intro C hC
    rw [← hB_bd_eq C hC]
    have hcl_sub : closure (cap.cuffDisc C) ⊆ S_sleeve C :=
      (hB_cl C hC).closure_subset_iff.mpr (hSleeve C hC).cuffDisc_subset
    refine subset_sdiff.mpr ⟨hcl_sub, ?_⟩
    rw [closure_cuffDisc_w cap hC]
    refine Disjoint.union_left ?_ ?_
    · rw [disjoint_left]
      intro z hz_cuff hz_bd
      have hz_compl : z ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_biUnion hC hz_cuff
      obtain ⟨u, _, rfl⟩ := (hSleeve C hC).bd_subset_U hz_bd
      exact hz_compl (mem_range_self u)
    · have hC_sub_bdS : C ⊆ bd S := by
        rw [← sUnion_cuffs]
        exact subset_sUnion_of_mem hC
      exact (hbd_disj_bdS C hC).symm.mono_left (image_mono hC_sub_bdS)
  have hinj_S : Nonempty (Shat ↪ S) :=
    exists_inj_capped_to_surface cap S_sleeve hB_disc hAB hSleeve_disj
  let W₀ := T_hat ∩ (⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ))ᶜ
  have hW₀_open : IsOpen W₀ := by
    refine (isOpen_insulatedSet D_hat Y_hat h).inter ?_
    rw [isOpen_compl_iff]
    exact hfin_cuffs.isClosed_biUnion fun _ _ => isClosed_closure
  have hW₀_eq : W₀ = cap.emb '' (T \ bd S) := by
    dsimp only [W₀]
    rw [compl_cuffDisc_eq_image_w cap]
    ext z
    simp only [mem_inter_iff, mem_image, mem_sdiff, T, mem_preimage]
    constructor
    · rintro ⟨hzT, x, hx_not_bd, rfl⟩
      exact ⟨x, ⟨hzT, hx_not_bd⟩, rfl⟩
    · rintro ⟨x, ⟨hxT, hx_not_bd⟩, rfl⟩
      exact ⟨hxT, x, hx_not_bd, rfl⟩
  have hbd_W₀ : ∀ C ∈ cuffs S, discBd (S_sleeve C) ⊆ W₀ := by
    intro C hC z hz
    rw [← hB_bd_eq C hC] at hz
    rw [hW₀_eq]
    obtain ⟨x, hxT, rfl⟩ := (hSleeve_T C hC).1 hz
    have hx_not_bd : x ∉ bd S := fun hx_bd =>
      disjoint_left.mp (hbd_disj_bdS C hC) hz (mem_image_of_mem cap.emb hx_bd)
    exact ⟨x, ⟨hxT, hx_not_bd⟩, rfl⟩
  -- Set up the minimal paths across each sleeve `S_sleeve C`
  let k : Set S → ℕ := fun C => (D.V ∩ C).ncard
  have hfin_DVC : ∀ C : Set S, Finite ↑(D.V ∩ C) :=
    fun C => D.finite_V.subset inter_subset_left
  let e_V : ∀ C : Set S, Fin (k C) ≃ ↑(D.V ∩ C) :=
    fun C => (Finite.equivFinOfCardEq (Nat.card_coe_set_eq (D.V ∩ C))).symm
  let s : ∀ C : Set S, Fin (k C) → S := fun C i => (e_V C i).1
  let capV : S ↪ Shat := ⟨cap.emb, cap.isEmbedding.injective⟩
  let capE : Set S ↪ Set Shat := ⟨image cap.emb, image_injective.mpr cap.isEmbedding.injective⟩
  have hD_hat_graph : D_hat.toGraph = D.toGraph.mapEmbed capV capE :=
    drawingMapEmb_toGraph_eq D hcap_emb
  have hD_hat_U : D_hat.U = cap.emb '' D.U := rfl
  have hD_hat_E : D_hat.E = (image cap.emb) '' D.E := drawingMapEmb_E D hcap_emb
  have hex_Q : ∀ C ∈ cuffs S, ∃ (s' : Fin (k C) → S) (Q_hat : Fin (k C) → Graph Shat (Set Shat))
      (φ_C : Fin (k C) → 𝕀 → Shat),
      (∀ i, s' i ∈ D.V ∧ cap.emb (s' i) ∈ subBd (S_sleeve C)) ∧
      (∀ i, IsFromToPathWithEnds D_hat.toGraph (Q_hat i)
        {cap.emb (s C i)} (D_hat.V ∩ subBd (S_sleeve C)) (cap.emb (s C i)) (cap.emb (s' i))) ∧
      (∀ i, Q_hat i ≤ (D_hat.interSet (S_sleeve C)).toGraph) ∧
      (∀ i, V(Q_hat i) ⊆ S_sleeve C ∧ V(Q_hat i) ∩ subBd (S_sleeve C) = {cap.emb (s' i)} ∧
        (∀ e ∈ E(Q_hat i), closure e ∩ subBd (S_sleeve C) ⊆ {cap.emb (s' i)})) ∧
      (∀ i j, i ≠ j → Disjoint V(Q_hat i) V(Q_hat j)) ∧
      (∀ i, Continuous (φ_C i) ∧ φ_C i 0 = cap.emb (s C i) ∧ φ_C i 1 = cap.emb (s' i) ∧
        (∀ t, φ_C i t ∈ S_sleeve C \ discInt (closure (cap.cuffDisc C))) ∧
        (∀ t, φ_C i t ∈ discBd (closure (cap.cuffDisc C)) ↔ t = 0) ∧
        (∀ t, φ_C i t ∈ discBd (S_sleeve C) ↔ t = 1)) ∧
      (∀ i j, i ≠ j → ∀ t₁ t₂, φ_C i t₁ ≠ φ_C j t₂) := by
    intro C hC
    obtain ⟨P, hP_ends, hP_disj⟩ := hPaths C hC
    have hex_i : ∀ i : Fin (k C), ∃ (s'_i : S) (Q_i : Graph Shat (Set Shat)),
        (s'_i ∈ D.V ∧ cap.emb s'_i ∈ subBd (S_sleeve C)) ∧
        V(Q_i) ⊆ cap.emb '' V(P (e_V C i)) ∧
        IsFromToPathWithEnds D_hat.toGraph Q_i
          {cap.emb (s C i)} (D_hat.V ∩ subBd (S_sleeve C)) (cap.emb (s C i)) (cap.emb s'_i) := by
      intro i
      obtain ⟨y, ⟨hyV, hy_bd⟩, hP_i⟩ := hP_ends (e_V C i)
      have hP_emb : IsGraphPathWithEnds D_hat.toGraph ((P (e_V C i)).mapEmbed capV capE)
          (cap.emb (s C i)) (cap.emb y) := by
        rw [hD_hat_graph]
        rcases hP_i with ⟨hP_le, W_i, hW_simp, hVP, hEP⟩
        obtain ⟨W_i', hs, he⟩ := mapEmbed_walk capV capE W_i
        refine ⟨mapEmbed_mono capV capE hP_le, W_i', ?_, ?_, ?_⟩
        · change W_i'.support.Nodup
          rw [hs]
          exact hW_simp.map capV.injective
        · ext z
          simp [vertexSet_mapEmbed, hVP, hs]
        · ext e
          simp [edgeSet_mapEmbed, hEP, he]
      have hy_in_Y : cap.emb y ∈ D_hat.V ∩ subBd (S_sleeve C) :=
        ⟨mem_image_of_mem cap.emb hyV, hy_bd⟩
      obtain ⟨b_hat, ⟨⟨s'_i, hs'_V, hs'_eq⟩, hb_bd⟩, Q_i, hVQ_sub, _, hQ_ft⟩ :=
        exists_fromToPath_of_path hP_emb hy_in_Y
      subst hs'_eq
      rw [vertexSet_mapEmbed] at hVQ_sub
      exact ⟨s'_i, Q_i, ⟨hs'_V, hb_bd⟩, hVQ_sub, hQ_ft⟩
    choose s' Q_hat hs' hVQ_sub_P hQ_ft using hex_i
    have hQ_disj : ∀ i j, i ≠ j → Disjoint V(Q_hat i) V(Q_hat j) := by
      intro i j hij
      have hne : e_V C i ≠ e_V C j := fun h => hij ((e_V C).injective h)
      exact (Set.disjoint_image_of_injective cap.isEmbedding.injective (hP_disj hne)).mono
        (hVQ_sub_P i) (hVQ_sub_P j)
    have hB_oArc : IsOArc (subBd (S_sleeve C)) := by
      rw [hB_bd_eq C hC]
      exact (hB_disc C hC).isOArc_discBd
    have hB_U : subBd (S_sleeve C) ⊆ D_hat.U := by
      rw [hD_hat_U]
      exact (hSleeve C hC).bd_subset_U
    have hs_in_intB : ∀ i, ({cap.emb (s C i)} : Set Shat) ⊆ S_sleeve C \ subBd (S_sleeve C) := by
      intro i z hz
      rw [mem_singleton_iff] at hz
      subst hz
      have hs_C : s C i ∈ C := (e_V C i).2.2
      have h_in_cl : cap.emb (s C i) ∈ closure (cap.cuffDisc C) := by
        rw [closure_cuffDisc_w cap hC]
        exact Or.inr (mem_image_of_mem cap.emb hs_C)
      rw [hB_bd_eq C hC]
      exact hAB C hC h_in_cl
    have hQ_disc : ∀ i,
        let UQ := V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e
        cap.emb (s C i) ≠ cap.emb (s' i) ∧
        IsLineWithEnds UQ (cap.emb (s C i)) (cap.emb (s' i)) ∧
        UQ ⊆ S_sleeve C ∧
        UQ ∩ subBd (S_sleeve C) = {cap.emb (s' i)} ∧
        Q_hat i ≤ (D_hat.interSet (S_sleeve C)).toGraph :=
      fun i => fromToPath_in_disc (hB_cl C hC) hB_oArc hB_U (hs_in_intB i) (hQ_ft i)
    have hUQ_inter_C : ∀ i,
        (V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e) ∩ (cap.emb '' C) = {cap.emb (s C i)} := by
      intro i
      have hC_sub_bdS : C ⊆ bd S := by rw [← sUnion_cuffs]; exact subset_sUnion_of_mem hC
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hz_UQ, x, hxC, rfl⟩
        have hx_U : x ∈ D.U := by
          have hz_U : cap.emb x ∈ D_hat.U := by
            rcases hz_UQ with hzV | hzE
            · exact D_hat.V_subset_U ((hQ_ft i).1.1.vertexSet_mono hzV)
            · obtain ⟨e, heQ, hze⟩ := mem_iUnion₂.mp hzE
              obtain ⟨u, v, hl⟩ := (Q_hat i).exists_isLink_of_mem_edgeSet heQ
              have heD : e ∈ D_hat.E := ((hQ_ft i).1.1.isLink_mono hl).1
              have hcl : closure e ⊆ D_hat.U := D_hat.isClosed_U.closure_subset_iff.mpr
                (fun w hw => (heD.2.1 hw).1)
              exact hcl hze
          rw [hD_hat_U] at hz_U
          exact (cap.isEmbedding.injective.mem_set_image).mp hz_U
        have hx_V : x ∈ D.V := hDU_bd ⟨hx_U, hC_sub_bdS hxC⟩
        let j : Fin (k C) := (e_V C).symm ⟨x, hx_V, hxC⟩
        have hj_eq : s C j = x := by
          dsimp [s, j]
          exact congrArg Subtype.val ((e_V C).apply_symm_apply ⟨x, hx_V, hxC⟩)
        have hxj_in_Qj : cap.emb x ∈ V(Q_hat j) := by
          rw [← hj_eq]
          exact (hQ_ft j).1.left_mem
        have hxj_in_Qi : cap.emb x ∈ V(Q_hat i) := by
          rcases hz_UQ with hzV | hzE
          · exact hzV
          · obtain ⟨e, heQ, hze⟩ := mem_iUnion₂.mp hzE
            obtain ⟨u, v, hlQ⟩ := (Q_hat i).exists_isLink_of_mem_edgeSet heQ
            have hlD := (hQ_ft i).1.1.isLink_mono hlQ
            have hx_DhatV : cap.emb x ∈ D_hat.V := mem_image_of_mem cap.emb hx_V
            have : cap.emb x ∈ ({u, v} : Set Shat) := hlD.2.2.2 ▸ ⟨hze, hx_DhatV⟩
            rcases this with rfl | rfl
            · exact hlQ.left_mem
            · exact hlQ.right_mem
        have hij : j = i := by
          by_contra hne
          exact disjoint_left.mp (hQ_disj j i hne) hxj_in_Qj hxj_in_Qi
        rw [← hj_eq, hij]
      · rintro rfl
        exact ⟨Or.inl (hQ_ft i).1.left_mem, mem_image_of_mem cap.emb (e_V C i).2.2⟩
    have hex_φ : ∀ i : Fin (k C), ∃ φ_i : 𝕀 → Shat,
        Continuous φ_i ∧ Injective φ_i ∧
        range φ_i = (V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e) ∧
        φ_i 0 = cap.emb (s C i) ∧ φ_i 1 = cap.emb (s' i) := by
      intro i
      obtain ⟨f, hf0, hf1⟩ := (hQ_disc i).2.1
      refine ⟨fun t => (f t).1, f.continuous.subtype_val, Subtype.val_injective.comp f.injective,
        ?_, hf0, hf1⟩
      ext z
      exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩⟩
    choose φ_C hφ_cont hφ_inj hφ_range hφ_0 hφ_1 using hex_φ
    refine ⟨s', Q_hat, φ_C, hs', hQ_ft, fun i => (hQ_disc i).2.2.2.2, ?_, hQ_disj, ?_, ?_⟩
    · intro i
      refine ⟨subset_union_left.trans (hQ_disc i).2.2.1, ?_, ?_⟩
      · apply Subset.antisymm
        · exact (inter_subset_inter_left _ subset_union_left).trans (hQ_disc i).2.2.2.1.subset
        · rw [singleton_subset_iff]
          exact ⟨(hQ_ft i).1.right_mem, (hs' i).2⟩
      · intro e heQ
        exact (inter_subset_inter_left _
          ((subset_biUnion_of_mem heQ).trans subset_union_right)).trans
          (hQ_disc i).2.2.2.1.subset
    · intro i
      refine ⟨hφ_cont i, hφ_0 i, hφ_1 i, ?_, ?_, ?_⟩
      · intro t
        have ht_UQ : φ_C i t ∈ V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e :=
          hφ_range i ▸ mem_range_self t
        refine ⟨(hQ_disc i).2.2.1 ht_UQ, ?_⟩
        rw [← cuffDisc_eq_discInt_w cap hC]
        intro ht_cuff
        have ht_compl : φ_C i t ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_biUnion hC ht_cuff
        have ht_U : φ_C i t ∈ D_hat.U := by
          rcases ht_UQ with htV | htE
          · exact D_hat.V_subset_U ((hQ_ft i).1.1.vertexSet_mono htV)
          · obtain ⟨e, heQ, hte⟩ := mem_iUnion₂.mp htE
            obtain ⟨u, v, hl⟩ := (Q_hat i).exists_isLink_of_mem_edgeSet heQ
            have heD : e ∈ D_hat.E := ((hQ_ft i).1.1.isLink_mono hl).1
            exact D_hat.isClosed_U.closure_subset_iff.mpr
              (fun w hw => (heD.2.1 hw).1) hte
        rw [hD_hat_U] at ht_U
        rcases ht_U with ⟨x, _, htx⟩
        exact ht_compl ⟨x, htx⟩
      · intro t
        rw [cap.cuffDisc_bd C hC]
        constructor
        · intro ht_C
          have ht_in : φ_C i t ∈ (V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e) ∩ (cap.emb '' C) :=
            ⟨hφ_range i ▸ mem_range_self t, ht_C⟩
          rw [hUQ_inter_C i, mem_singleton_iff, ← hφ_0 i] at ht_in
          exact hφ_inj i ht_in
        · rintro rfl
          rw [hφ_0 i]
          exact mem_image_of_mem cap.emb (e_V C i).2.2
      · intro t
        rw [← hB_bd_eq C hC]
        constructor
        · intro ht_bd
          have ht_in : φ_C i t ∈ (V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e) ∩ subBd (S_sleeve C) :=
            ⟨hφ_range i ▸ mem_range_self t, ht_bd⟩
          rw [(hQ_disc i).2.2.2.1, mem_singleton_iff, ← hφ_1 i] at ht_in
          exact hφ_inj i ht_in
        · rintro rfl
          rw [hφ_1 i]
          exact (hs' i).2
    · intro i j hij t₁ t₂ heq
      have ht₁ : φ_C i t₁ ∈ V(Q_hat i) ∪ ⋃ e ∈ E(Q_hat i), closure e :=
        hφ_range i ▸ mem_range_self t₁
      have ht₂ : φ_C i t₁ ∈ V(Q_hat j) ∪ ⋃ e ∈ E(Q_hat j), closure e :=
        heq ▸ hφ_range j ▸ mem_range_self t₂
      exact disjoint_left.mp
        (disjoint_subgraph_U_of_disjoint_V (hQ_ft i).1.1 (hQ_ft j).1.1 (hQ_disj i j hij))
        ht₁ ht₂
  let s' : ∀ C : Set S, Fin (k C) → S := fun C =>
    if hC : C ∈ cuffs S then (hex_Q C hC).choose else fun i => s C i
  let Q_hat : ∀ C : Set S, Fin (k C) → Graph Shat (Set Shat) := fun C =>
    if hC : C ∈ cuffs S then (hex_Q C hC).choose_spec.choose else fun _ => ⊥
  let φ_all : ∀ C : Set S, Fin (k C) → 𝕀 → Shat := fun C =>
    if hC : C ∈ cuffs S then (hex_Q C hC).choose_spec.choose_spec.choose else fun i _ => cap.emb (s C i)
  have hQ_props : ∀ C (hC : C ∈ cuffs S),
      (∀ i, s' C i ∈ D.V ∧ cap.emb (s' C i) ∈ subBd (S_sleeve C)) ∧
      (∀ i, IsFromToPathWithEnds D_hat.toGraph (Q_hat C i)
        {cap.emb (s C i)} (D_hat.V ∩ subBd (S_sleeve C)) (cap.emb (s C i)) (cap.emb (s' C i))) ∧
      (∀ i, Q_hat C i ≤ (D_hat.interSet (S_sleeve C)).toGraph) ∧
      (∀ i, V(Q_hat C i) ⊆ S_sleeve C ∧ V(Q_hat C i) ∩ subBd (S_sleeve C) = {cap.emb (s' C i)} ∧
        (∀ e ∈ E(Q_hat C i), closure e ∩ subBd (S_sleeve C) ⊆ {cap.emb (s' C i)})) ∧
      (∀ i j, i ≠ j → Disjoint V(Q_hat C i) V(Q_hat C j)) ∧
      (∀ i, Continuous (φ_all C i) ∧ φ_all C i 0 = cap.emb (s C i) ∧ φ_all C i 1 = cap.emb (s' C i) ∧
        (∀ t, φ_all C i t ∈ S_sleeve C \ discInt (closure (cap.cuffDisc C))) ∧
        (∀ t, φ_all C i t ∈ discBd (closure (cap.cuffDisc C)) ↔ t = 0) ∧
        (∀ t, φ_all C i t ∈ discBd (S_sleeve C) ↔ t = 1)) ∧
      (∀ i j, i ≠ j → ∀ t₁ t₂, φ_all C i t₁ ≠ φ_all C j t₂) := by
    intro C hC
    have hs'_eq : s' C = (hex_Q C hC).choose := by simp [s', hC]
    have hQ_eq : Q_hat C = (hex_Q C hC).choose_spec.choose := by simp [Q_hat, hC]
    have hφ_eq : φ_all C = (hex_Q C hC).choose_spec.choose_spec.choose := by simp [φ_all, hC]
    rw [hs'_eq, hQ_eq, hφ_eq]
    exact (hex_Q C hC).choose_spec.choose_spec.choose_spec
  obtain ⟨α_hat, K_supp, hK_cl, hK_sub, hB_K, hα_fix, hα_C, h_not_intB, h_in_W₀⟩ :=
    exists_all_sleeves_homeo hS cap S_sleeve W₀ hW₀_open hB_disc hAB hbd_W₀ hSleeve_disj
      k φ_all
      (fun C hC i => ((hQ_props C hC).2.2.2.2.2.1 i).1)
      (fun C hC i t => ((hQ_props C hC).2.2.2.2.2.1 i).2.2.2.1 t)
      (fun C hC i t => ((hQ_props C hC).2.2.2.2.2.1 i).2.2.2.2.1 t)
      (fun C hC i t => ((hQ_props C hC).2.2.2.2.2.1 i).2.2.2.2.2 t)
      (fun C hC => (hQ_props C hC).2.2.2.2.2.2)
  let f₀ : S → Shat := α_hat ∘ cap.emb
  have hf₀_emb : IsClosedEmbedding f₀ :=
    α_hat.isClosedEmbedding.comp hcap_emb
  have hf₀_range : ∀ x : S, f₀ x ∈ range cap.emb := by
    intro x
    by_cases hxK : cap.emb x ∈ K_supp
    · have hW : f₀ x ∈ W₀ := h_in_W₀ (cap.emb x) ⟨hxK, mem_range_self x⟩
      rw [hW₀_eq] at hW
      rcases hW with ⟨w, _, hwx⟩
      exact ⟨w, hwx⟩
    · change α_hat (cap.emb x) ∈ range cap.emb
      rw [hα_fix (cap.emb x) hxK]
      exact mem_range_self x
  have hf₀_fix : ∀ x ∉ S_total ∪ T, f₀ x = cap.emb x := by
    intro x hx
    apply hα_fix (cap.emb x)
    intro hxK
    rcases hK_sub hxK with hxB | hxW₀
    · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxB
      exact hx (Or.inl (mem_biUnion hC hxC))
    · rw [hW₀_eq] at hxW₀
      rcases hxW₀ with ⟨w, ⟨hwT, _⟩, hwx⟩
      obtain rfl : w = x := cap.isEmbedding.injective hwx
      exact hx (Or.inr hwT)
  have hf₀_in_W₀ : ∀ x ∈ S_total ∪ T, f₀ x ∈ W₀ := by
    intro x hx
    by_cases hxK : cap.emb x ∈ K_supp
    · exact h_in_W₀ (cap.emb x) ⟨hxK, mem_range_self x⟩
    · have hfx : f₀ x = cap.emb x := hα_fix (cap.emb x) hxK
      rw [hfx, hW₀_eq]
      have hx_not_S : x ∉ S_total := by
        intro hxS
        obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxS
        exact hxK (hB_K (mem_biUnion hC hxC))
      have hxT : x ∈ T := hx.resolve_left hx_not_S
      have hx_not_bd : x ∉ bd S := by
        intro hx_bd
        rw [← sUnion_cuffs] at hx_bd
        obtain ⟨C, hC, hxC⟩ := hx_bd
        have h_in_A : cap.emb x ∈ closure (cap.cuffDisc C) := by
          rw [closure_cuffDisc_w cap hC]
          exact Or.inr (mem_image_of_mem cap.emb hxC)
        exact hx_not_S (mem_biUnion hC (hAB C hC h_in_A).1)
      exact ⟨x, ⟨hxT, hx_not_bd⟩, rfl⟩
  have hf₀_in_B_iff : ∀ C ∈ cuffs S, ∀ x : S, f₀ x ∈ S_sleeve C ↔ x ∈ C := by
    intro C hC x
    constructor
    · intro hfx_B
      have hfx_bd : f₀ x ∈ discBd (S_sleeve C) := by
        by_contra hnot_bd
        exact h_not_intB (cap.emb x) (mem_range_self x) (mem_biUnion hC ⟨hfx_B, hnot_bd⟩)
      rw [← (hα_C C hC).2.1, cap.cuffDisc_bd C hC] at hfx_bd
      rcases hfx_bd with ⟨y, ⟨w, hwC, rfl⟩, hxy⟩
      obtain rfl : w = x := cap.isEmbedding.injective (α_hat.injective hxy)
      exact hwC
    · intro hxC
      have h_bdA : cap.emb x ∈ discBd (closure (cap.cuffDisc C)) := by
        rw [cap.cuffDisc_bd C hC]
        exact mem_image_of_mem cap.emb hxC
      exact Surface.discBd_subset (S_sleeve C)
        ((hα_C C hC).2.1 ▸ mem_image_of_mem α_hat h_bdA)
  have hf₀_s : ∀ C (hC : C ∈ cuffs S) (i : Fin (k C)), f₀ (s C i) = cap.emb (s' C i) := by
    intro C hC i
    have h0 := ((hQ_props C hC).2.2.2.2.2.1 i).2.1
    have h1 := ((hQ_props C hC).2.2.2.2.2.1 i).2.2.1
    have hα_φ := (hα_C C hC).2.2 i
    change α_hat (cap.emb (s C i)) = cap.emb (s' C i)
    rw [← h0, hα_φ, h1]
  -- Construct `D_0`, `D_sleeves`, and `D''_hat`
  let D₀ := drawingMapEmb D' hf₀_emb
  let bd_union := ⋃ C ∈ cuffs S, subBd (S_sleeve C)
  let V_sleeves : Set Shat :=
    (D_hat.V ∩ (S_union \ bd_union)) ∪
      ⋃ C ∈ cuffs S, range (fun i : Fin (k C) => cap.emb (s' C i))
  let E_sleeves : Set (Set Shat) :=
    {e ∈ D_hat.E | e ⊆ S_union \ bd_union ∧ closure e ∩ D_hat.V ⊆ V_sleeves}
  let D_sleeves := D_hat.span V_sleeves E_sleeves
  have hbd_union_sub_T : bd_union ⊆ T_hat := by
    rintro z hz
    obtain ⟨C, hC, hzC⟩ := mem_iUnion₂.mp hz
    obtain ⟨w, hwT, rfl⟩ := (hSleeve_T C hC).1 hzC
    exact hwT
  have hV_sleeves_sub : V_sleeves ⊆ D_hat.V ∩ S_union := by
    rintro z (⟨hzV, hzS, _⟩ | hz_range)
    · exact ⟨hzV, hzS⟩
    · obtain ⟨C, hC, i, rfl⟩ := mem_iUnion₂.mp hz_range
      have hs'_prop := (hQ_props C hC).1 i
      exact ⟨mem_image_of_mem cap.emb hs'_prop.1,
        mem_biUnion hC (Surface.discBd_subset _ (hB_bd_eq C hC ▸ hs'_prop.2))⟩
  have hD₀_U : D₀.U = f₀ '' D'.U := rfl
  have hD₀_E : D₀.E = (image f₀) '' D'.E := drawingMapEmb_E D' hf₀_emb
  have hD_sleeves_V : D_sleeves.V = V_sleeves := by
    change (V_sleeves ∩ D_hat.V) ∪ (⋃ e ∈ E_sleeves ∩ D_hat.E, closure e ∩ D_hat.V) = V_sleeves
    refine Subset.antisymm (union_subset inter_subset_left ?_)
      (fun z hz => Or.inl ⟨hz, (hV_sleeves_sub hz).1⟩)
    exact iUnion₂_subset fun e he => he.1.2.2
  have hD_sleeves_E : D_sleeves.E = E_sleeves := by
    rw [D_hat.span_E]
    exact inter_eq_self_of_subset_left fun _ h => h.1
  have hD_sleeves_sub : D_sleeves.IsSubdrawing D_hat :=
    ⟨hD_sleeves_V ▸ fun z hz => (hV_sleeves_sub hz).1,
      hD_sleeves_E ▸ fun _ h => h.1⟩
  have hD_sleeves_U_sub : D_sleeves.U ⊆ S_union := by
    change D_sleeves.V ∪ (⋃ e ∈ E_sleeves ∩ D_hat.E, closure e) ⊆ S_union
    rw [hD_sleeves_V]
    refine union_subset (fun z hz => (hV_sleeves_sub hz).2) ?_
    exact iUnion₂_subset fun e he =>
      hSunion_cl.closure_subset_iff.mpr (he.1.2.1.trans sdiff_subset)
  have hD_sleeves_U_bd : D_sleeves.U ∩ bd_union ⊆ V_sleeves := by
    rintro z ⟨hzU, hz_bd⟩
    change z ∈ D_sleeves.V ∪ ⋃ e ∈ E_sleeves ∩ D_hat.E, closure e at hzU
    rw [hD_sleeves_V] at hzU
    rcases hzU with hzV | hzE
    · exact hzV
    · obtain ⟨e, ⟨heE, heD⟩, hze⟩ := mem_iUnion₂.mp hzE
      have hz_not_e : z ∉ e := fun h => (heE.2.1 h).2 hz_bd
      have hz_V : z ∈ D_hat.V :=
        by_contra fun hz_not_V => hz_not_e (D_hat.closure_diff_V heD ▸ ⟨hze, hz_not_V⟩)
      exact heE.2.2 ⟨hze, hz_V⟩
  have hmeet : D₀.U ∩ D_sleeves.U ⊆ D₀.V ∩ D_sleeves.V := by
    rintro z ⟨hz₀, hzs⟩
    have hz_S : z ∈ S_union := hD_sleeves_U_sub hzs
    obtain ⟨C, hC, hzC⟩ := mem_iUnion₂.mp hz_S
    rw [hD₀_U] at hz₀
    rcases hz₀ with ⟨x, _, rfl⟩
    have hxC : x ∈ C := (hf₀_in_B_iff C hC x).mp hzC
    have h_bdA : cap.emb x ∈ discBd (closure (cap.cuffDisc C)) := by
      rw [cap.cuffDisc_bd C hC]
      exact mem_image_of_mem cap.emb hxC
    have hz_bdC : f₀ x ∈ subBd (S_sleeve C) := by
      rw [hB_bd_eq C hC, ← (hα_C C hC).2.1]
      exact mem_image_of_mem α_hat h_bdA
    have hz_bd : f₀ x ∈ bd_union := mem_biUnion hC hz_bdC
    have hz_V : f₀ x ∈ V_sleeves := hD_sleeves_U_bd ⟨hzs, hz_bd⟩
    refine ⟨?_, hD_sleeves_V ▸ hz_V⟩
    rcases hz_V with ⟨_, _, hnot_bd⟩ | hz_range
    · exact (hnot_bd hz_bd).elim
    · obtain ⟨C₁, hC₁, i, h_eq⟩ := mem_iUnion₂.mp hz_range
      dsimp only at h_eq
      rw [← hf₀_s C₁ hC₁ i] at h_eq
      have hs_V : s C₁ i ∈ D.V ∩ bd S :=
        ⟨(e_V C₁ i).2.1, by rw [← sUnion_cuffs]; exact subset_sUnion_of_mem hC₁ (e_V C₁ i).2.2⟩
      rw [← hDV_bd] at hs_V
      exact h_eq ▸ mem_image_of_mem f₀ hs_V.1
  let D''_hat := D₀.glue D_sleeves hmeet
  have hD''_U_range : D''_hat.U ⊆ range cap.emb := by
    change D₀.U ∪ D_sleeves.U ⊆ range cap.emb
    refine union_subset ?_ ?_
    · rw [hD₀_U]
      rintro _ ⟨x, _, rfl⟩
      exact hf₀_range x
    · exact hD_sleeves_sub.U_subset.trans (hD_hat_U ▸ image_subset_range cap.emb D.U)
  -- Prove `IsVariant D_hat D''_hat T_hat₀`
  have hVar_hat : IsVariant D_hat D''_hat T_hat₀ := by
    refine ⟨?_, ?_, ?_⟩
    · ext z
      simp only [mem_sdiff]
      constructor
      · rintro ⟨⟨x, hxV, rfl⟩, hz_not_T₀⟩
        refine ⟨?_, hz_not_T₀⟩
        change cap.emb x ∈ D₀.V ∪ D_sleeves.V
        by_cases hxS : x ∈ S_total
        · right
          rw [hD_sleeves_V]
          obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxS
          exact Or.inl ⟨mem_image_of_mem cap.emb hxV, mem_biUnion hC hxC,
            fun hbd => hz_not_T₀ (hT_sub_T₀ (hbd_union_sub_T hbd))⟩
        · left
          have hx_not_T : x ∉ T := fun hxT => hz_not_T₀ (hT_sub_T₀ hxT)
          have hx_diff : x ∈ D.V \ (S_total ∪ T) := ⟨hxV, fun h => h.elim hxS hx_not_T⟩
          rw [hVar.V_diff_eq] at hx_diff
          rw [← hf₀_fix x hx_diff.2]
          exact mem_image_of_mem f₀ hx_diff.1
      · rintro ⟨hzV'', hz_not_T₀⟩
        refine ⟨?_, hz_not_T₀⟩
        rcases hzV'' with ⟨x, hxV', rfl⟩ | hzs
        · by_cases hx_ST : x ∈ S_total ∪ T
          · have hW : f₀ x ∈ W₀ := hf₀_in_W₀ x hx_ST
            exact (hz_not_T₀ (hT_sub_T₀ hW.1)).elim
          · have hx_diff : x ∈ D'.V \ (S_total ∪ T) := ⟨hxV', hx_ST⟩
            rw [← hVar.V_diff_eq] at hx_diff
            rw [hf₀_fix x hx_ST]
            exact mem_image_of_mem cap.emb hx_diff.1
        · exact (hV_sleeves_sub (hD_sleeves_V ▸ hzs)).1
    · rintro e ⟨he_Dhat, he_not_D''⟩
      rw [hD_hat_E] at he_Dhat
      rcases he_Dhat with ⟨e₀, he₀D, rfl⟩
      have he₀_Dhat : cap.emb '' e₀ ∈ D_hat.E := hD_hat_E ▸ mem_image_of_mem (image cap.emb) he₀D
      by_contra hnot_T₀
      have hdisj_T : Disjoint (closure (cap.emb '' e₀)) T_hat := by
        rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
        intro hne
        exact hnot_T₀ (closure_edge_subset_insulatedSet_of_inter he₀_Dhat hne)
      have hdisj_S : Disjoint (closure (cap.emb '' e₀)) S_union := by
        rw [disjoint_iUnion₂_right]
        intro C hC
        have hB_oArc : IsOArc (subBd (S_sleeve C)) :=
          hB_bd_eq C hC ▸ (hB_disc C hC).isOArc_discBd
        have hB_U : subBd (S_sleeve C) ⊆ D_hat.U := hD_hat_U ▸ (hSleeve C hC).bd_subset_U
        rcases edge_closure_subset_or_disjoint_of_oArc_subBd (hB_cl C hC) hB_oArc hB_U
          he₀_Dhat with hsub | hdisj_e
        · exfalso
          apply he_not_D''
          rw [Drawing.glue_E hmeet]
          right
          rw [hD_sleeves_E]
          have hsub_Su : closure (cap.emb '' e₀) ⊆ S_union \ bd_union :=
            fun w hw => ⟨mem_biUnion hC (hsub hw),
              fun hbd => disjoint_left.mp hdisj_T hw (hbd_union_sub_T hbd)⟩
          exact ⟨he₀_Dhat, subset_closure.trans hsub_Su,
            fun w ⟨hw_cl, hw_V⟩ => Or.inl ⟨hw_V, hsub_Su hw_cl⟩⟩
        · rw [disjoint_left]
          intro z hz_cl hz_B
          by_cases hz_bd : z ∈ subBd (S_sleeve C)
          · have hz_T : z ∈ T_hat := by
              obtain ⟨w, hwT, rfl⟩ := (hSleeve_T C hC).1 hz_bd
              exact hwT
            exact disjoint_left.mp hdisj_T hz_cl hz_T
          · have h_int : S_sleeve C \ subBd (S_sleeve C) = interior (S_sleeve C) :=
              sdiff_subBd_eq_interior (hB_cl C hC) (subBd_eq_frontier _)
            obtain ⟨w, hw_int, hwe⟩ :=
              mem_closure_iff.mp hz_cl (S_sleeve C \ subBd (S_sleeve C))
                (h_int ▸ isOpen_interior) ⟨hz_B, hz_bd⟩
            exact disjoint_left.mp hdisj_e hwe hw_int.1
      have hdisj_ST : Disjoint (closure e₀) (S_total ∪ T) := by
        rw [disjoint_left]
        intro x hx_cl hx_ST
        have hcx : cap.emb x ∈ closure (cap.emb '' e₀) := by
          rw [hcap_emb.closure_image_eq e₀]
          exact mem_image_of_mem cap.emb hx_cl
        rcases hx_ST with hxS | hxT
        · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxS
          exact disjoint_left.mp hdisj_S hcx (mem_biUnion hC hxC)
        · exact disjoint_left.mp hdisj_T hcx hxT
      have he₀_D' : e₀ ∈ D'.E := by
        by_contra he₀_not_D'
        obtain ⟨u, v, hl₀⟩ := D.toGraph.exists_isLink_of_mem_edgeSet he₀D
        have hu_cl : u ∈ closure e₀ := (hl₀.2.2.2.symm.subset (Or.inl rfl)).1
        have hcl_sub := hVar.edge_subset_of_mem_diff_left e₀ ⟨he₀D, he₀_not_D'⟩
        exact disjoint_left.mp hdisj_ST hu_cl (hcl_sub hu_cl)
      have he_eq : f₀ '' e₀ = cap.emb '' e₀ :=
        image_congr fun x hx => hf₀_fix x (disjoint_left.mp hdisj_ST (subset_closure hx))
      apply he_not_D''
      rw [Drawing.glue_E hmeet]
      left
      rw [hD₀_E]
      exact he_eq ▸ mem_image_of_mem (image f₀) he₀_D'
    · rintro e' ⟨he'_D'', he'_not_Dhat⟩
      rw [Drawing.glue_E hmeet] at he'_D''
      have he'_D₀ : e' ∈ D₀.E :=
        he'_D''.resolve_right fun hes => he'_not_Dhat (hD_sleeves_sub.2 hes)
      rw [hD₀_E] at he'_D₀
      rcases he'_D₀ with ⟨e₁, he₁D', rfl⟩
      rw [hf₀_emb.closure_image_eq e₁]
      by_cases hcl_ST : closure e₁ ⊆ S_total ∪ T
      · rintro _ ⟨x, hx_cl, rfl⟩
        exact hT_sub_T₀ (hf₀_in_W₀ x (hcl_ST hx_cl)).1
      · have he₁D : e₁ ∈ D.E :=
          by_contra fun hnot => hcl_ST (hVar.edge_subset_of_mem_diff_right e₁ ⟨he₁D', hnot⟩)
        have he₁_Dhat : cap.emb '' e₁ ∈ D_hat.E :=
          hD_hat_E ▸ mem_image_of_mem (image cap.emb) he₁D
        have hne_T : (closure (cap.emb '' e₁) ∩ T_hat).Nonempty := by
          by_contra h_empty
          rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h_empty
          have hdisj_S : Disjoint (closure (cap.emb '' e₁)) S_union := by
            rw [disjoint_iUnion₂_right]
            intro C hC
            have hB_oArc : IsOArc (subBd (S_sleeve C)) :=
              hB_bd_eq C hC ▸ (hB_disc C hC).isOArc_discBd
            have hB_U : subBd (S_sleeve C) ⊆ D_hat.U := hD_hat_U ▸ (hSleeve C hC).bd_subset_U
            rcases edge_closure_subset_or_disjoint_of_oArc_subBd (hB_cl C hC) hB_oArc hB_U
              he₁_Dhat with hsub | hdisj_e
            · exfalso
              apply hcl_ST
              intro x hx_cl
              left
              refine mem_biUnion hC ?_
              apply hsub
              rw [hcap_emb.closure_image_eq e₁]
              exact mem_image_of_mem cap.emb hx_cl
            · rw [disjoint_left]
              intro z hz_cl hz_B
              by_cases hz_bd : z ∈ subBd (S_sleeve C)
              · obtain ⟨w, hwT, rfl⟩ := (hSleeve_T C hC).1 hz_bd
                exact disjoint_left.mp h_empty hz_cl hwT
              · have h_int : S_sleeve C \ subBd (S_sleeve C) = interior (S_sleeve C) :=
                  sdiff_subBd_eq_interior (hB_cl C hC) (subBd_eq_frontier _)
                obtain ⟨w, hw_int, hwe⟩ :=
                  mem_closure_iff.mp hz_cl (S_sleeve C \ subBd (S_sleeve C))
                    (h_int ▸ isOpen_interior) ⟨hz_B, hz_bd⟩
                exact disjoint_left.mp hdisj_e hwe hw_int.1
          have he_eq : f₀ '' e₁ = cap.emb '' e₁ := by
            refine image_congr fun x hx => hf₀_fix x ?_
            intro hx_ST
            have hcx : cap.emb x ∈ closure (cap.emb '' e₁) :=
              subset_closure (mem_image_of_mem cap.emb hx)
            rcases hx_ST with hxS | hxT
            · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxS
              exact disjoint_left.mp hdisj_S hcx (mem_biUnion hC hxC)
            · exact disjoint_left.mp h_empty hcx hxT
          exact he'_not_Dhat (he_eq ▸ he₁_Dhat)
        have hcl_T₀ : closure (cap.emb '' e₁) ⊆ T_hat₀ :=
          closure_edge_subset_insulatedSet_of_inter he₁_Dhat hne_T
        rintro _ ⟨x, hx_cl, rfl⟩
        by_cases hx_ST : x ∈ S_total ∪ T
        · exact hT_sub_T₀ (hf₀_in_W₀ x hx_ST).1
        · rw [hf₀_fix x hx_ST]
          apply hcl_T₀
          rw [hcap_emb.closure_image_eq e₁]
          exact mem_image_of_mem cap.emb hx_cl
  -- Claim (1) (page 538): `Y₀ ⊆ S \ (S_total ∪ T)`, `Y_hat ⊆ D''_hat.V`, and `(image cap.emb) '' E_K ⊆ D''_hat.E`
  have hY₀_not_ST : ∀ y ∈ Y₀, y ∉ S_total ∪ T := by
    intro y hyY₀ hy_ST
    rcases hy_ST with hyS | hyT
    · obtain ⟨C, hC, hyC⟩ := mem_iUnion₂.mp hyS
      exact disjoint_left.mp (hSleeve_T C hC).2 hyC (mem_image_of_mem cap.emb hyY₀)
    · exact disjoint_left.mp hY_disj_T (mem_image_of_mem cap.emb (Or.inl hyY₀)) hyT
  have hY_hat_sub_V'' : Y_hat ⊆ D''_hat.V := by
    rintro _ ⟨y, hy_YS, rfl⟩
    have hy_DV : y ∈ D.V := hy_YS.elim (fun h => hY₀_sub h) (fun h => h.1)
    have hcy_not_T₀ : cap.emb y ∉ T_hat₀ :=
      disjoint_left.mp hY_disj_T₀ (mem_image_of_mem cap.emb hy_YS)
    have hcy_diff : cap.emb y ∈ D_hat.V \ T_hat₀ :=
      ⟨mem_image_of_mem cap.emb hy_DV, hcy_not_T₀⟩
    rw [hVar_hat.V_diff_eq] at hcy_diff
    exact hcy_diff.1
  have hEK_not_T₀ : ∀ e₀ ∈ E_K, ¬ (closure (cap.emb '' e₀) ⊆ T_hat₀) := by
    intro e₀ he₀ hsub
    obtain ⟨y, hy_cl, hy_Y₀⟩ := hEK_Y₀ e₀ he₀
    have hcy_cl : cap.emb y ∈ closure (cap.emb '' e₀) := by
      rw [hcap_emb.closure_image_eq e₀]
      exact mem_image_of_mem cap.emb hy_cl
    exact disjoint_left.mp hY_disj_T₀
      (mem_image_of_mem cap.emb (Or.inl hy_Y₀)) (hsub hcy_cl)
  have hV_diff_T : D_hat.V \ T_hat = D''_hat.V \ T_hat := by
    ext z
    simp only [mem_sdiff]
    constructor
    · rintro ⟨⟨x, hxV, rfl⟩, hz_not_T⟩
      refine ⟨?_, hz_not_T⟩
      change cap.emb x ∈ D₀.V ∪ D_sleeves.V
      by_cases hxS : x ∈ S_total
      · right
        rw [hD_sleeves_V]
        obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxS
        exact Or.inl ⟨mem_image_of_mem cap.emb hxV, mem_biUnion hC hxC,
          fun hbd => hz_not_T (hbd_union_sub_T hbd)⟩
      · left
        have hx_diff : x ∈ D.V \ (S_total ∪ T) := ⟨hxV, fun h => h.elim hxS hz_not_T⟩
        rw [hVar.V_diff_eq] at hx_diff
        rw [← hf₀_fix x hx_diff.2]
        exact mem_image_of_mem f₀ hx_diff.1
    · rintro ⟨hzV'', hz_not_T⟩
      refine ⟨?_, hz_not_T⟩
      rcases hzV'' with ⟨x, hxV', rfl⟩ | hzs
      · by_cases hx_ST : x ∈ S_total ∪ T
        · exact (hz_not_T (hf₀_in_W₀ x hx_ST).1).elim
        · have hx_diff : x ∈ D'.V \ (S_total ∪ T) := ⟨hxV', hx_ST⟩
          rw [← hVar.V_diff_eq] at hx_diff
          rw [hf₀_fix x hx_ST]
          exact mem_image_of_mem cap.emb hx_diff.1
      · exact (hV_sleeves_sub (hD_sleeves_V ▸ hzs)).1
  have hEK_sub_D'' : (image cap.emb) '' E_K ⊆ D''_hat.E := by
    rintro _ ⟨e₀, he₀, rfl⟩
    by_contra hnot
    have he₀_Dhat : cap.emb '' e₀ ∈ D_hat.E :=
      hD_hat_E ▸ mem_image_of_mem (image cap.emb) (hEK_sub he₀)
    exact hEK_not_T₀ e₀ he₀
      (hVar_hat.edge_subset_of_mem_diff_left _ ⟨he₀_Dhat, hnot⟩)
  have hEK_isLink : ∀ e₀ ∈ E_K, ∀ x y,
      D''_hat.toGraph.IsLink (cap.emb '' e₀) x y ↔ D_hat.toGraph.IsLink (cap.emb '' e₀) x y := by
    intro e₀ he₀ x y
    have he₀_Dhat : cap.emb '' e₀ ∈ D_hat.E :=
      hD_hat_E ▸ mem_image_of_mem (image cap.emb) (hEK_sub he₀)
    have he₀_D'' : cap.emb '' e₀ ∈ D''_hat.E :=
      hEK_sub_D'' (mem_image_of_mem (image cap.emb) he₀)
    have hdisj_T : Disjoint (closure (cap.emb '' e₀)) T_hat := by
      rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
      intro hne
      exact hEK_not_T₀ e₀ he₀ (closure_edge_subset_insulatedSet_of_inter he₀_Dhat hne)
    have hcl_V : closure (cap.emb '' e₀) ∩ D''_hat.V = closure (cap.emb '' e₀) ∩ D_hat.V := by
      ext z
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨hz_cl, hz_V''⟩
        have hz_not_T : z ∉ T_hat := disjoint_left.mp hdisj_T hz_cl
        have hz_diff : z ∈ D''_hat.V \ T_hat := ⟨hz_V'', hz_not_T⟩
        rw [← hV_diff_T] at hz_diff
        exact ⟨hz_cl, hz_diff.1⟩
      · rintro ⟨hz_cl, hz_V⟩
        have hz_not_T : z ∉ T_hat := disjoint_left.mp hdisj_T hz_cl
        have hz_diff : z ∈ D_hat.V \ T_hat := ⟨hz_V, hz_not_T⟩
        rw [hV_diff_T] at hz_diff
        exact ⟨hz_cl, hz_diff.1⟩
    change (cap.emb '' e₀ ∈ D''_hat.E ∧ x ∈ D''_hat.V ∧ y ∈ D''_hat.V ∧
        closure (cap.emb '' e₀) ∩ D''_hat.V = {x, y}) ↔
      (cap.emb '' e₀ ∈ D_hat.E ∧ x ∈ D_hat.V ∧ y ∈ D_hat.V ∧
        closure (cap.emb '' e₀) ∩ D_hat.V = {x, y})
    rw [hcl_V]
    constructor
    · rintro ⟨_, _, _, hcap⟩
      have hx : x ∈ closure (cap.emb '' e₀) ∩ D_hat.V := hcap.symm ▸ Or.inl rfl
      have hy : y ∈ closure (cap.emb '' e₀) ∩ D_hat.V := hcap.symm ▸ Or.inr rfl
      exact ⟨he₀_Dhat, hx.2, hy.2, hcap⟩
    · rintro ⟨_, _, _, hcap⟩
      have hx : x ∈ closure (cap.emb '' e₀) ∩ D''_hat.V := hcl_V ▸ hcap.symm ▸ Or.inl rfl
      have hy : y ∈ closure (cap.emb '' e₀) ∩ D''_hat.V := hcl_V ▸ hcap.symm ▸ Or.inr rfl
      exact ⟨he₀_D'', hx.2, hy.2, hcap⟩
  -- Construct `L₀` and `H''_hat` by attaching active paths `Q_hat C i`
  let f₀V : S ↪ Shat := ⟨f₀, hf₀_emb.injective⟩
  let f₀E : Set S ↪ Set Shat := ⟨image f₀, image_injective.mpr hf₀_emb.injective⟩
  let L₀ := H'.mapEmbed f₀V f₀E
  have hD₀_graph : D₀.toGraph = D'.toGraph.mapEmbed f₀V f₀E :=
    drawingMapEmb_toGraph_eq D' hf₀_emb
  have hL₀_le_D₀ : L₀ ≤ D₀.toGraph := by
    rw [hD₀_graph]
    exact mapEmbed_mono f₀V f₀E hH'_le
  have hD''_graph : D''_hat.toGraph = graphUnion D₀.toGraph D_sleeves.toGraph :=
    glue_toGraph_eq_graphUnion hmeet
  have hL₀_le_D'' : L₀ ≤ D''_hat.toGraph := by
    rw [hD''_graph]
    exact hL₀_le_D₀.trans (le_graphUnion_left _ _)
  have hQ_le_sleeves : ∀ C (hC : C ∈ cuffs S) (i : Fin (k C)),
      Q_hat C i ≤ D_sleeves.toGraph := by
    intro C hC i
    have hQ_sub := (hQ_props C hC).2.2.1 i
    have hVQ_S := ((hQ_props C hC).2.2.2.1 i).1
    have hVQ_bd := ((hQ_props C hC).2.2.2.1 i).2.1
    have hEQ_bd := ((hQ_props C hC).2.2.2.1 i).2.2
    have hQ_Dhat : Q_hat C i ≤ D_hat.toGraph := ((hQ_props C hC).2.1 i).1.1
    have hVQ_V : V(Q_hat C i) ⊆ V_sleeves := by
      intro z hz
      by_cases hz_bd : z ∈ bd_union
      · obtain ⟨C₁, hC₁, hzC₁⟩ := mem_iUnion₂.mp hz_bd
        have hz_S₁ : z ∈ S_sleeve C₁ :=
          Surface.discBd_subset _ (hB_bd_eq C₁ hC₁ ▸ hzC₁)
        have hC₁_eq : C₁ = C :=
          by_contra fun hne => disjoint_left.mp (hSleeve_disj C₁ hC₁ C hC hne) hz_S₁ (hVQ_S hz)
        rw [hC₁_eq] at hzC₁
        have hz_eq : z = cap.emb (s' C i) :=
          mem_singleton_iff.mp (hVQ_bd ▸ ⟨hz, hzC₁⟩)
        exact Or.inr (mem_biUnion hC ⟨i, hz_eq.symm⟩)
      · exact Or.inl ⟨hQ_Dhat.vertexSet_mono hz, mem_biUnion hC (hVQ_S hz), hz_bd⟩
    refine ⟨by change V(Q_hat C i) ⊆ D_sleeves.V; rwa [hD_sleeves_V], fun e x y hl => ?_⟩
    have hlD : D_hat.toGraph.IsLink e x y := hQ_Dhat.isLink_mono hl
    have he_inter : e ∈ (D_hat.interSet (S_sleeve C)).E := hQ_sub.edgeSet_mono hl.edge_mem
    have he_S : e ⊆ S_sleeve C := (GM11.mem_interSet_E_iff.mp he_inter).2
    have he_E : e ∈ D_sleeves.E := by
      rw [hD_sleeves_E]
      refine ⟨hlD.1, fun w hw => ⟨mem_biUnion hC (he_S hw), fun hw_bd => ?_⟩, ?_⟩
      · obtain ⟨C₁, hC₁, hwC₁⟩ := mem_iUnion₂.mp hw_bd
        have hw_S₁ : w ∈ S_sleeve C₁ :=
          Surface.discBd_subset _ (hB_bd_eq C₁ hC₁ ▸ hwC₁)
        have hC₁_eq : C₁ = C :=
          by_contra fun hne => disjoint_left.mp (hSleeve_disj C₁ hC₁ C hC hne) hw_S₁ (he_S hw)
        rw [hC₁_eq] at hwC₁
        have hw_eq : w = cap.emb (s' C i) :=
          mem_singleton_iff.mp (hEQ_bd e hl.edge_mem ⟨subset_closure hw, hwC₁⟩)
        exact (hlD.1.2.1 hw).2 (hw_eq ▸ mem_image_of_mem cap.emb ((hQ_props C hC).1 i).1)
      · rw [hlD.2.2.2]
        rintro w (rfl | rfl)
        · exact hVQ_V hl.left_mem
        · exact hVQ_V hl.right_mem
    exact (hD_sleeves_sub.isLink_iff he_E).mpr hlD
  have hQ_le_D'' : ∀ C (hC : C ∈ cuffs S) (i : Fin (k C)),
      Q_hat C i ≤ D''_hat.toGraph := by
    intro C hC i
    rw [hD''_graph]
    have hcomp := Compatible.of_le_le
      (isSubdrawing_glue_left hmeet).toGraph_le (isSubdrawing_glue_right hmeet).toGraph_le
    exact (hQ_le_sleeves C hC i).trans (le_graphUnion_right hcomp)
  let 𝒜 : Set (Graph Shat (Set Shat)) :=
    {P | ∃ C, ∃ (hC : C ∈ cuffs S), ∃ i : Fin (k C), s C i ∈ V(H') ∧ P = Q_hat C i}
  have h𝒜_le : ∀ P ∈ 𝒜, P ≤ D''_hat.toGraph := by
    rintro _ ⟨C, hC, i, _, rfl⟩
    exact hQ_le_D'' C hC i
  have hQ_disj_all : ∀ C₁ (hC₁ : C₁ ∈ cuffs S) (i₁ : Fin (k C₁))
      C₂ (hC₂ : C₂ ∈ cuffs S) (i₂ : Fin (k C₂)),
      (C₁ = C₂ → HEq i₁ i₂ → False) → Disjoint V(Q_hat C₁ i₁) V(Q_hat C₂ i₂) := by
    intro C₁ hC₁ i₁ C₂ hC₂ i₂ hne
    by_cases hC_eq : C₁ = C₂
    · subst hC_eq
      exact (hQ_props C₁ hC₁).2.2.2.2.1 i₁ i₂ (fun hi => hne rfl (heq_of_eq hi))
    · exact (hSleeve_disj C₁ hC₁ C₂ hC₂ hC_eq).mono
        ((hQ_props C₁ hC₁).2.2.2.1 i₁).1 ((hQ_props C₂ hC₂).2.2.2.1 i₂).1
  have h𝒜_disj : ∀ P₁ ∈ 𝒜, ∀ P₂ ∈ 𝒜, P₁ ≠ P₂ → Disjoint V(P₁) V(P₂) := by
    rintro _ ⟨C₁, hC₁, i₁, _, rfl⟩ _ ⟨C₂, hC₂, i₂, _, rfl⟩ hne
    refine hQ_disj_all C₁ hC₁ i₁ C₂ hC₂ i₂ (fun hC_eq h_heq => ?_)
    subst hC_eq
    subst h_heq
    exact hne rfl
  have hVQ_inter_L₀ : ∀ C (hC : C ∈ cuffs S) (i : Fin (k C)),
      s C i ∈ V(H') → V(Q_hat C i) ∩ V(L₀) = {cap.emb (s' C i)} := by
    intro C hC i hsi_H'
    have hQ_B := ((hQ_props C hC).2.2.2.1 i).1
    have hQ_bd := ((hQ_props C hC).2.2.2.1 i).2.1
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, L₀, vertexSet_mapEmbed, mem_image]
    constructor
    · rintro ⟨hzQ, x, hxH', rfl⟩
      change f₀ x ∈ V(Q_hat C i) at hzQ
      change f₀ x = cap.emb (s' C i)
      have hxC : x ∈ C := (hf₀_in_B_iff C hC x).mp (hQ_B hzQ)
      have hC_sub_bdS : C ⊆ bd S := by rw [← sUnion_cuffs]; exact subset_sUnion_of_mem hC
      have hx_V' : x ∈ D'.V := hH'_le.vertexSet_mono hxH'
      have hx_V : x ∈ D.V := (by rw [← hDV_bd]; exact ⟨hx_V', hC_sub_bdS hxC⟩ : x ∈ D.V ∩ bd S).1
      let j : Fin (k C) := (e_V C).symm ⟨x, hx_V, hxC⟩
      have hj_eq : s C j = x :=
        congrArg Subtype.val ((e_V C).apply_symm_apply ⟨x, hx_V, hxC⟩)
      rw [← hj_eq, hf₀_s C hC j] at hzQ ⊢
      have hs'j_bd : cap.emb (s' C j) ∈ subBd (S_sleeve C) := ((hQ_props C hC).1 j).2
      have hin : cap.emb (s' C j) ∈ V(Q_hat C i) ∩ subBd (S_sleeve C) := ⟨hzQ, hs'j_bd⟩
      rwa [hQ_bd, mem_singleton_iff] at hin
    · rintro rfl
      refine ⟨((hQ_props C hC).2.1 i).1.right_mem, s C i, hsi_H', hf₀_s C hC i⟩
  let b_map : ∀ P, P ∈ 𝒜 → Shat := fun P hP =>
    let C := Classical.choose hP
    let hC := Classical.choose (Classical.choose_spec hP)
    let i := Classical.choose (Classical.choose_spec (Classical.choose_spec hP))
    cap.emb (s' C i)
  have hb_eq : ∀ C (hC : C ∈ cuffs S) (i : Fin (k C)) (hsi : s C i ∈ V(H'))
      (hP : Q_hat C i ∈ 𝒜),
      b_map (Q_hat C i) hP = cap.emb (s' C i) := by
    intro C hC i hsi hP
    let C₁ := Classical.choose hP
    let hC₁ := Classical.choose (Classical.choose_spec hP)
    let i₁ := Classical.choose (Classical.choose_spec (Classical.choose_spec hP))
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hP))
    have hQ_eq : Q_hat C i = Q_hat C₁ i₁ := hspec.2
    have hV_inter : V(Q_hat C₁ i₁) ∩ V(L₀) = {cap.emb (s' C i)} :=
      hQ_eq ▸ hVQ_inter_L₀ C hC i hsi
    rw [hVQ_inter_L₀ C₁ hC₁ i₁ hspec.1] at hV_inter
    exact singleton_eq_singleton_iff.mp hV_inter
  have hb_inter : ∀ (P) (hP : P ∈ 𝒜), V(P) ∩ V(L₀) = {b_map P hP} := by
    rintro _ ⟨C, hC, i, hsi, rfl⟩
    rw [hb_eq C hC i hsi]
    exact hVQ_inter_L₀ C hC i hsi
  have h𝒜_conn : ∀ (P) (hP : P ∈ 𝒜), ∀ z ∈ V(P), AreConnectedIn P z (b_map P hP) := by
    rintro _ ⟨C, hC, i, hsi, rfl⟩ z hz
    rw [hb_eq C hC i hsi]
    rcases ((hQ_props C hC).2.1 i).1 with ⟨_, W₀, _, hVQ, _⟩
    have hz_supp : z ∈ W₀.support := by rwa [hVQ] at hz
    obtain ⟨_, W₂, _⟩ := W₀.exists_append_of_mem hz_supp
    rw [areConnectedIn_iff_walk]
    exact ⟨hz, W₂.mem_vertexSet_of_mem_support W₂.end_mem_support, ⟨W₂⟩⟩
  obtain ⟨ρ, hρ_P, hρ_L₀, hρ_not_P, hρ_conn⟩ :=
    areConnectedIn_graphUnion_pendants hL₀_le_D'' h𝒜_le h𝒜_disj hb_inter h𝒜_conn
  let H''_hat := graphUnion L₀ (subgraphSUnion D''_hat.toGraph 𝒜)
  have hcomp_L₀_M : L₀.Compatible (subgraphSUnion D''_hat.toGraph 𝒜) :=
    Compatible.of_le_le hL₀_le_D'' (subgraphSUnion_le h𝒜_le)
  have hH''_le : H''_hat ≤ D''_hat.toGraph := by
    refine ⟨union_subset hL₀_le_D''.vertexSet_mono (subgraphSUnion_le h𝒜_le).vertexSet_mono,
      fun e x y hl => ?_⟩
    rw [isLink_graphUnion_of_compatible hcomp_L₀_M] at hl
    exact hl.elim (fun h => hL₀_le_D''.isLink_mono h)
      (fun h => (subgraphSUnion_le h𝒜_le).isLink_mono h)
  -- Disjointness `Disjoint E(H''_hat) ((image cap.emb) '' E_K)`
  have hDisj_EH''_EK : Disjoint E(H''_hat) ((image cap.emb) '' E_K) := by
    rw [edgeSet_graphUnion, edgeSet_subgraphSUnion h𝒜_le]
    refine Disjoint.union_left ?_ ?_
    · rw [disjoint_left]
      rintro _ ⟨e₁, he₁H', rfl⟩ ⟨e₀, he₀K, heq⟩
      have he₀D : e₀ ∈ D.E := hEK_sub he₀K
      have he₀_Dhat : cap.emb '' e₀ ∈ D_hat.E :=
        hD_hat_E ▸ mem_image_of_mem (image cap.emb) he₀D
      have he₀_not_D'' : ¬ (closure (cap.emb '' e₀) ⊆ T_hat₀) := hEK_not_T₀ e₀ he₀K
      have hdisj_T : Disjoint (closure (cap.emb '' e₀)) T_hat := by
        rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
        intro hne
        exact he₀_not_D'' (closure_edge_subset_insulatedSet_of_inter he₀_Dhat hne)
      have hdisj_S : Disjoint (closure (cap.emb '' e₀)) S_union := by
        rw [disjoint_iUnion₂_right]
        intro C hC
        obtain ⟨y, hy_cl, hy_Y₀⟩ := hEK_Y₀ e₀ he₀K
        have hcy_cl : cap.emb y ∈ closure (cap.emb '' e₀) := by
          rw [hcap_emb.closure_image_eq e₀]
          exact mem_image_of_mem cap.emb hy_cl
        have hcy_not_B : cap.emb y ∉ S_sleeve C :=
          disjoint_right.mp (hSleeve_T C hC).2 (mem_image_of_mem cap.emb hy_Y₀)
        have hB_oArc : IsOArc (subBd (S_sleeve C)) :=
          hB_bd_eq C hC ▸ (hB_disc C hC).isOArc_discBd
        have hB_U : subBd (S_sleeve C) ⊆ D_hat.U := hD_hat_U ▸ (hSleeve C hC).bd_subset_U
        have hdisj_e := (edge_closure_subset_or_disjoint_of_oArc_subBd (hB_cl C hC) hB_oArc hB_U
          he₀_Dhat).resolve_left fun hsub => hcy_not_B (hsub hcy_cl)
        rw [disjoint_left]
        intro z hz_cl hz_B
        by_cases hz_bd : z ∈ subBd (S_sleeve C)
        · obtain ⟨w, hwT, rfl⟩ := (hSleeve_T C hC).1 hz_bd
          exact disjoint_left.mp hdisj_T hz_cl hwT
        · have h_int : S_sleeve C \ subBd (S_sleeve C) = interior (S_sleeve C) :=
            sdiff_subBd_eq_interior (hB_cl C hC) (subBd_eq_frontier _)
          obtain ⟨w, hw_int, hwe⟩ :=
            mem_closure_iff.mp hz_cl (S_sleeve C \ subBd (S_sleeve C))
              (h_int ▸ isOpen_interior) ⟨hz_B, hz_bd⟩
          exact disjoint_left.mp hdisj_e hwe hw_int.1
      have he₀_eq : f₀ '' e₀ = cap.emb '' e₀ := by
        refine image_congr fun x hx => hf₀_fix x ?_
        have hcx : cap.emb x ∈ closure (cap.emb '' e₀) :=
          subset_closure (mem_image_of_mem cap.emb hx)
        rintro (hxS | hxT)
        · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxS
          exact disjoint_left.mp hdisj_S hcx (mem_biUnion hC hxC)
        · exact disjoint_left.mp hdisj_T hcx hxT
      have he₁_eq_e₀ : e₁ = e₀ :=
        f₀E.injective (heq.symm.trans he₀_eq.symm)
      exact disjoint_left.mp hDisj_EH'_EK he₁H' (he₁_eq_e₀ ▸ he₀K)
    · rw [disjoint_iUnion₂_left]
      rintro _ ⟨C, hC, i, _, rfl⟩
      rw [disjoint_left]
      rintro _ heQ ⟨e₀, he₀K, rfl⟩
      obtain ⟨y, hy_cl, hy_Y₀⟩ := hEK_Y₀ e₀ he₀K
      have hcy_cl : cap.emb y ∈ closure (cap.emb '' e₀) := by
        rw [hcap_emb.closure_image_eq e₀]
        exact mem_image_of_mem cap.emb hy_cl
      have he_inter : cap.emb '' e₀ ∈ (D_hat.interSet (S_sleeve C)).E :=
        ((hQ_props C hC).2.2.1 i).edgeSet_mono heQ
      have he_sub_B : cap.emb '' e₀ ⊆ S_sleeve C :=
        (GM11.mem_interSet_E_iff.mp he_inter).2
      have hcl_sub_B : closure (cap.emb '' e₀) ⊆ S_sleeve C :=
        (hB_cl C hC).closure_subset_iff.mpr he_sub_B
      exact disjoint_left.mp (hSleeve_T C hC).2 (hcl_sub_B hcy_cl) (mem_image_of_mem cap.emb hy_Y₀)
  -- Action of `ρ` on `cap.emb u` for `u ∈ Y_S`
  have hρ_on_YS : ∀ u ∈ Y_S,
      (u ∈ V(H') → ρ (cap.emb u) = f₀ u) ∧
      (u ∉ V(H') → ρ (cap.emb u) ∉ V(L₀)) := by
    intro u hu
    rcases hu with huY₀ | ⟨huV, hubd⟩
    · have hu_not_ST : u ∉ S_total ∪ T := hY₀_not_ST u huY₀
      have hcu_not_P : ∀ P ∈ 𝒜, cap.emb u ∉ V(P) := by
        rintro _ ⟨C, hC, i, _, rfl⟩ hcu_Q
        have hcu_B : cap.emb u ∈ S_sleeve C := ((hQ_props C hC).2.2.2.1 i).1 hcu_Q
        exact hu_not_ST (Or.inl (mem_biUnion hC hcu_B))
      have hρ_u : ρ (cap.emb u) = f₀ u := by
        rw [hρ_not_P (cap.emb u) hcu_not_P, hf₀_fix u hu_not_ST]
      refine ⟨fun _ => hρ_u, fun hu_not_H' => ?_⟩
      rw [hρ_u]
      rintro ⟨x, hxH', hfx⟩
      obtain rfl : x = u := hf₀_emb.injective hfx
      exact hu_not_H' hxH'
    · rw [← sUnion_cuffs] at hubd
      obtain ⟨C, hC, huC⟩ := hubd
      let i : Fin (k C) := (e_V C).symm ⟨u, huV, huC⟩
      have hi_eq : s C i = u :=
        congrArg Subtype.val ((e_V C).apply_symm_apply ⟨u, huV, huC⟩)
      by_cases huH' : u ∈ V(H')
      · refine ⟨fun _ => ?_, fun h => (h huH').elim⟩
        have hP_in_𝒜 : Q_hat C i ∈ 𝒜 := ⟨C, hC, i, hi_eq ▸ huH', rfl⟩
        have hcu_in_Q : cap.emb u ∈ V(Q_hat C i) :=
          hi_eq ▸ ((hQ_props C hC).2.1 i).1.left_mem
        rw [hρ_P (Q_hat C i) hP_in_𝒜 (cap.emb u) hcu_in_Q,
          hb_eq C hC i (hi_eq ▸ huH') hP_in_𝒜, ← hi_eq, hf₀_s C hC i]
      · refine ⟨fun h => (huH' h).elim, fun _ => ?_⟩
        have hcu_not_P : ∀ P ∈ 𝒜, cap.emb u ∉ V(P) := by
          rintro _ ⟨C₁, hC₁, i₁, hsi₁, rfl⟩ hcu_Q₁
          have hcu_in_Q : cap.emb u ∈ V(Q_hat C i) :=
            hi_eq ▸ ((hQ_props C hC).2.1 i).1.left_mem
          have hne : C = C₁ → HEq i i₁ → False := by
            intro hC_eq h_heq
            subst hC_eq
            subst h_heq
            exact huH' (hi_eq ▸ hsi₁)
          exact disjoint_left.mp (hQ_disj_all C hC i C₁ hC₁ i₁ hne) hcu_in_Q hcu_Q₁
        rw [hρ_not_P (cap.emb u) hcu_not_P]
        rintro ⟨x, hxH', hfx⟩
        have hcu_in_B : cap.emb u ∈ S_sleeve C := by
          have : cap.emb u ∈ closure (cap.cuffDisc C) := by
            rw [closure_cuffDisc_w cap hC]
            exact Or.inr (mem_image_of_mem cap.emb huC)
          exact (hAB C hC this).1
        have hcu_not_bdB : cap.emb u ∉ discBd (S_sleeve C) := by
          rw [← hB_bd_eq C hC]
          intro hbd
          have hC_sub_bdS : C ⊆ bd S := by rw [← sUnion_cuffs]; exact subset_sUnion_of_mem hC
          exact disjoint_left.mp (hbd_disj_bdS C hC) hbd
            (mem_image_of_mem cap.emb (hC_sub_bdS huC))
        exact h_not_intB (cap.emb x) (mem_range_self x)
          (mem_biUnion hC ⟨hfx ▸ hcu_in_B, hfx ▸ hcu_not_bdB⟩)
  have hConn_iff : ∀ u ∈ Y_S, ∀ v ∈ Y_S,
      AreConnectedIn H''_hat (cap.emb u) (cap.emb v) ↔ AreConnectedIn H' u v := by
    intro u hu v hv
    rw [hρ_conn (cap.emb u) (cap.emb v)]
    by_cases huH' : u ∈ V(H')
    · by_cases hvH' : v ∈ V(H')
      · rw [(hρ_on_YS u hu).1 huH', (hρ_on_YS v hv).1 hvH']
        exact areConnectedIn_mapEmbed_iff f₀V f₀E H'
      · constructor
        · intro hconn
          exact ((hρ_on_YS v hv).2 hvH' hconn.right_mem).elim
        · intro hconn
          exact (hvH' hconn.right_mem).elim
    · constructor
      · intro hconn
        exact ((hρ_on_YS u hu).2 huH' hconn.left_mem).elim
      · intro hconn
        exact (huH' hconn.left_mem).elim
  have hVH''_inter_Y : V(H''_hat) ∩ Y_hat = cap.emb '' (V(H') ∩ Y_S) := by
    ext z
    simp only [mem_inter_iff, Y_hat, mem_image]
    constructor
    · rintro ⟨hzH'', u, huYS, rfl⟩
      have hconn_self : AreConnectedIn H''_hat (cap.emb u) (cap.emb u) :=
        areConnectedIn_self_iff.mpr hzH''
      have huH' : u ∈ V(H') :=
        areConnectedIn_self_iff.mp ((hConn_iff u huYS u huYS).mp hconn_self)
      exact ⟨u, ⟨huH', huYS⟩, rfl⟩
    · rintro ⟨u, ⟨huH', huYS⟩, rfl⟩
      have hconn_self : AreConnectedIn H''_hat (cap.emb u) (cap.emb u) :=
        (hConn_iff u huYS u huYS).mpr (areConnectedIn_self_iff.mpr huH')
      exact ⟨areConnectedIn_self_iff.mp hconn_self, u, huYS, rfl⟩
  exact ⟨D''_hat, H''_hat, hD''_U_range, hVar_hat, hY_hat_sub_V'', hEK_sub_D'', hEK_isLink,
    hH''_le, hDisj_EH''_EK, hVH''_inter_Y, hConn_iff, hinj_S⟩

/-- Functoriality of `Graph.mapEmbed` under composition of embeddings. -/
theorem mapEmbed_mapEmbed {α₁ β₁ α₂ β₂ α₃ β₃ : Type*}
    (fV : α₁ ↪ α₂) (fE : β₁ ↪ β₂) (gV : α₂ ↪ α₃) (gE : β₂ ↪ β₃) (H : Graph α₁ β₁) :
    (H.mapEmbed fV fE).mapEmbed gV gE = H.mapEmbed (fV.trans gV) (fE.trans gE) := by
  refine Graph.ext (by ext; simp [vertexSet_mapEmbed, mem_image]) fun e x y => ?_
  constructor
  · rintro ⟨_, _, _, ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    exact ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
  · rintro ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
    exact ⟨fE e₀, fV x₀, fV y₀, ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

omit [T2Space S] in
/-- Given `ιV : S ↪ α`, `ιE : Set S ↪ β`, and `g_S : Shat ↪ S`, constructs embeddings
`ιV_hat : Shat ↪ α ⊕ α` and `ιE_hat : Set Shat ↪ β ⊕ β` extending `Sum.inl ∘ ιV` on `range cap.emb`
and `Sum.inl ∘ ιE` on `range (image cap.emb)`. -/
theorem exists_capped_embeddings {Shat : Type w} [TopologicalSpace Shat]
    (cap : GM19.IsCappedSurface S Shat) (g_S : Shat ↪ S)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    ∃ (ιV_hat : Shat ↪ α ⊕ α) (ιE_hat : Set Shat ↪ β ⊕ β),
      (∀ x : S, ιV_hat (cap.emb x) = Sum.inl (ιV x)) ∧
      (∀ z : Shat, z ∉ range cap.emb → ιV_hat z ∈ range Sum.inr) ∧
      (∀ e₀ : Set S, ιE_hat (cap.emb '' e₀) = Sum.inl (ιE e₀)) ∧
      (∀ e : Set Shat, e ∉ range (image cap.emb) → ιE_hat e ∈ range Sum.inr) := by
  classical
  let fV : Shat → α ⊕ α := fun z =>
    if hz : z ∈ range cap.emb then Sum.inl (ιV (Classical.choose hz))
    else Sum.inr (ιV (g_S z))
  have hfV_cap : ∀ x : S, fV (cap.emb x) = Sum.inl (ιV x) := by
    intro x
    have hz : cap.emb x ∈ range cap.emb := mem_range_self x
    have h_eq : Classical.choose hz = x := cap.isEmbedding.injective (Classical.choose_spec hz)
    simp only [fV, hz, ↓reduceDIte, h_eq]
  have hfV_inj : Injective fV := by
    intro z₁ z₂ h
    by_cases hz₁ : z₁ ∈ range cap.emb <;> by_cases hz₂ : z₂ ∈ range cap.emb
    · rcases hz₁ with ⟨x₁, rfl⟩
      rcases hz₂ with ⟨x₂, rfl⟩
      rw [hfV_cap x₁, hfV_cap x₂, Sum.inl.injEq] at h
      rw [ιV.injective h]
    · rcases hz₁ with ⟨x₁, rfl⟩
      rw [hfV_cap x₁] at h
      simp only [fV, hz₂, ↓reduceDIte, reduceCtorEq] at h
    · rcases hz₂ with ⟨x₂, rfl⟩
      rw [hfV_cap x₂] at h
      simp only [fV, hz₁, ↓reduceDIte, reduceCtorEq] at h
    · simp only [fV, hz₁, hz₂, ↓reduceDIte, Sum.inr.injEq] at h
      exact g_S.injective (ιV.injective h)
  let fE : Set Shat → β ⊕ β := fun e =>
    if he : e ∈ range (image cap.emb) then Sum.inl (ιE (Classical.choose he))
    else Sum.inr (ιE (g_S '' e))
  have hfE_cap : ∀ e₀ : Set S, fE (cap.emb '' e₀) = Sum.inl (ιE e₀) := by
    intro e₀
    have he : cap.emb '' e₀ ∈ range (image cap.emb) := mem_range_self e₀
    have h_eq : Classical.choose he = e₀ :=
      image_injective.mpr cap.isEmbedding.injective (Classical.choose_spec he)
    simp only [fE, he, ↓reduceDIte, h_eq]
  have hfE_inj : Injective fE := by
    intro e₁ e₂ h
    by_cases he₁ : e₁ ∈ range (image cap.emb) <;> by_cases he₂ : e₂ ∈ range (image cap.emb)
    · rcases he₁ with ⟨s₁, rfl⟩
      rcases he₂ with ⟨s₂, rfl⟩
      rw [hfE_cap s₁, hfE_cap s₂, Sum.inl.injEq] at h
      rw [ιE.injective h]
    · rcases he₁ with ⟨s₁, rfl⟩
      rw [hfE_cap s₁] at h
      simp only [fE, he₂, ↓reduceDIte, reduceCtorEq] at h
    · rcases he₂ with ⟨s₂, rfl⟩
      rw [hfE_cap s₂] at h
      simp only [fE, he₁, ↓reduceDIte, reduceCtorEq] at h
    · simp only [fE, he₁, he₂, ↓reduceDIte, Sum.inr.injEq] at h
      exact image_injective.mpr g_S.injective (ιE.injective h)
  refine ⟨⟨fV, hfV_inj⟩, ⟨fE, hfE_inj⟩, hfV_cap, ?_, hfE_cap, ?_⟩
  · intro z hz
    change fV z ∈ range Sum.inr
    simp only [fV, hz, ↓reduceDIte, mem_range_self]
  · intro e he
    change fE e ∈ range Sum.inr
    simp only [fE, he, ↓reduceDIte, mem_range_self]

/-- Normalized version of **4.2** under the assumption `ιV ⁻¹' V(K) ⊆ D.V` and `ιE ⁻¹' E(K) ⊆ D.E`
(Graph Minors XXII, page 538: "Without loss of generality, we may assume that
$V(K) \cap \Sigma \subseteq V(\Gamma)$"). -/
theorem lemma_4_2_normalized {Shat : Type w} [TopologicalSpace Shat] [T2Space Shat]
    {p h₀ : ℕ} (hh₀ : 1 ≤ h₀)
    (h41 : ∀ (S_hat : Type w) [TopologicalSpace S_hat] [T2Space S_hat], IsSurface S_hat →
      ∀ (G Γ K G' Γ' L' : Graph (α ⊕ α) (β ⊕ β)),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Surface.Drawing S_hat) (ιV : S_hat ↪ α ⊕ α) (ιE : Set S_hat ↪ β ⊕ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      IsVariant D D' (insulatedSet D (ιV ⁻¹' (V(Γ) ∩ V(K))) h₀) →
      ∀ (Z : Set (α ⊕ α)), Z ⊆ V(K) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L')
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    (G Γ K G' Γ' L' : Graph α β)
    (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hΓG : Γ ≤ G) (hKG : K ≤ G)
    (hVG_union : V(G) = V(Γ) ∪ V(K)) (hEG_union : E(G) = E(Γ) ∪ E(K))
    (hΓ'G' : Γ' ≤ G') (hKG' : K ≤ G')
    (hVG'_union : V(G') = V(Γ') ∪ V(K)) (hEG'_union : E(G') = E(Γ') ∪ E(K))
    (_hInter : subgraphInter G Γ K = subgraphInter G' Γ' K)
    (D D' : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    (hΓ : Γ = D.toEmbeddedGraph ιV ιE) (hΓ' : Γ' = D'.toEmbeddedGraph ιV ιE)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hDU_bd : D.U ∩ bd S ⊆ D.V)
    (hDV_bd : D'.V ∩ bd S = D.V ∩ bd S)
    (S_sleeve : Set S → Set Shat)
    (hSleeve : ∀ C ∈ cuffs S, IsSleeve cap D C (S_sleeve C))
    (hSleeve_disj : ∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (S_sleeve C₁) (S_sleeve C₂))
    (hPaths : ∀ C ∈ cuffs S, ∃ P : ↑(D.V ∩ C) → Graph S (Set S),
      (∀ x : ↑(D.V ∩ C), ∃ y ∈ D.V ∩ cap.emb ⁻¹' subBd (S_sleeve C),
        IsGraphPathWithEnds D.toGraph (P x) x.1 y) ∧
      Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂)))
    (hSleeve_T : ∀ C ∈ cuffs S,
      subBd (S_sleeve C) ⊆
        cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) (h₀ + 1)) ∧
      Disjoint (S_sleeve C) (cap.emb '' (ιV ⁻¹' (V(Γ) ∩ V(K)))))
    (hVar : IsVariant D D'
      ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
        cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) (h₀ + 1)))
    (Z : Set α) (hZ : Z ⊆ V(K) ∪ ιV '' (D.V ∩ bd S)) (hZp : Z.ncard ≤ p) (hL' : L' ≤ G') :
    ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' := by
  classical
  have hcap_emb : IsClosedEmbedding cap.emb := isClosedEmbedding_w hS cap
  let D_hat := drawingMapEmb D hcap_emb
  let Y₀ := ιV ⁻¹' (V(Γ) ∩ V(K))
  let Y_S := Y₀ ∪ (D.V ∩ bd S)
  let Y_hat := cap.emb '' Y_S
  let E_K := ιE ⁻¹' (E(Γ) ∩ E(K))
  have hVΓ_eq : V(Γ) = ιV '' D.V := by rw [hΓ]; rfl
  have hEΓ_eq : E(Γ) = ιE '' D.E := by rw [hΓ]; rfl
  have hY₀_eq : Y₀ = ιV ⁻¹' V(K) := by
    ext x
    simp only [Y₀, mem_preimage, mem_inter_iff, hVΓ_eq, ιV.injective.mem_set_image]
    exact ⟨fun h => h.2, fun hx => ⟨hVK hx, hx⟩⟩
  have hY₀_sub : Y₀ ⊆ D.V := hY₀_eq ▸ hVK
  have hEK_eq : E_K = ιE ⁻¹' E(K) := by
    ext e₀
    simp only [E_K, mem_preimage, mem_inter_iff, hEΓ_eq, ιE.injective.mem_set_image]
    exact ⟨fun h => h.2, fun he => ⟨hEK he, he⟩⟩
  have hEK_sub : E_K ⊆ D.E := hEK_eq ▸ hEK
  have hEK_Y₀ : ∀ e₀ ∈ E_K, (closure e₀ ∩ Y₀).Nonempty := by
    intro e₀ he₀
    have he₀D : e₀ ∈ D.E := hEK_sub he₀
    obtain ⟨u, v, hl₀⟩ := D.toGraph.exists_isLink_of_mem_edgeSet he₀D
    have hu_cl : u ∈ closure e₀ := (hl₀.2.2.2.symm.subset (Or.inl rfl)).1
    have hlΓ : Γ.IsLink (ιE e₀) (ιV u) (ιV v) := by
      rw [hΓ, toEmbeddedGraph_eq_mapEmbed]
      exact (isLink_mapEmbed_iff ιV ιE D.toGraph).mpr hl₀
    have hlG : G.IsLink (ιE e₀) (ιV u) (ιV v) := hΓG.isLink_mono hlΓ
    have hlK : K.IsLink (ιE e₀) (ιV u) (ιV v) := (hKG.isLink_iff he₀.2).mpr hlG
    exact ⟨u, hu_cl, hlΓ.left_mem, hlK.left_mem⟩
  -- Augment `K` with the isolated vertices `B_bd = ιV '' (D.V ∩ bd S)`
  let B_bd : Set α := ιV '' (D.V ∩ bd S)
  let K_p : Graph α β := addIsolatedVerts K B_bd
  have hVK_p : V(K_p) = V(K) ∪ B_bd := rfl
  have hEK_p : E(K_p) = E(K) := rfl
  have hB_sub_Γ : B_bd ⊆ V(Γ) := by
    rw [hVΓ_eq]
    exact image_mono inter_subset_left
  have hB_sub_Γ' : B_bd ⊆ V(Γ') := by
    change ιV '' (D.V ∩ bd S) ⊆ V(Γ')
    rw [← hDV_bd, hΓ']
    exact image_mono inter_subset_left
  have hK_le_Kp : K ≤ K_p := ⟨subset_union_left, fun _ _ _ h => h⟩
  have hKp_le_G : K_p ≤ G :=
    ⟨union_subset hKG.vertexSet_mono (hB_sub_Γ.trans hΓG.vertexSet_mono),
      fun _ _ _ h => hKG.isLink_mono h⟩
  have hKp_le_G' : K_p ≤ G' :=
    ⟨union_subset hKG'.vertexSet_mono (hB_sub_Γ'.trans hΓ'G'.vertexSet_mono),
      fun _ _ _ h => hKG'.isLink_mono h⟩
  have hVG_union_p : V(G) = V(Γ) ∪ V(K_p) := by
    rw [hVK_p, ← union_assoc, union_right_comm, union_eq_self_of_subset_right hB_sub_Γ, hVG_union]
  have hVG'_union_p : V(G') = V(Γ') ∪ V(K_p) := by
    rw [hVK_p, ← union_assoc, union_right_comm, union_eq_self_of_subset_right hB_sub_Γ', hVG'_union]
  have hYS_pre : ιV ⁻¹' V(K_p) = Y_S := by
    change ιV ⁻¹' (V(K) ∪ ιV '' (D.V ∩ bd S)) = Y₀ ∪ (D.V ∩ bd S)
    rw [preimage_union, ← hY₀_eq, preimage_image_eq _ ιV.injective]
  have hVΓ_inter_Kp : V(Γ) ∩ V(K_p) = ιV '' Y_S := by
    rw [hVΓ_eq, ← hYS_pre]
    ext w
    simp only [mem_inter_iff, mem_image, mem_preimage]
    constructor
    · rintro ⟨⟨x, _, rfl⟩, hxKp⟩
      exact ⟨x, hxKp, rfl⟩
    · rintro ⟨x, hxKp, rfl⟩
      have hxYS : x ∈ Y_S := hYS_pre ▸ hxKp
      exact ⟨⟨x, (union_subset hY₀_sub inter_subset_left) hxYS, rfl⟩, hxKp⟩
  -- Decompose `L' ≤ G'` into `M'_G ≤ Γ'` and `K_L = subgraphInter G' L' K_p`
  let K_L := subgraphInter G' L' K_p
  let M'_G := (subgraphInter G' L' Γ').deleteEdges E(K_p)
  have hM'_le_Γ' : M'_G ≤ Γ' :=
    deleteEdges_le.trans (subgraphInter_le_right hL' hΓ'G')
  have hM'_le_L' : M'_G ≤ L' :=
    deleteEdges_le.trans (subgraphInter_le_left hL' hΓ'G')
  have hKL_le_L' : K_L ≤ L' := subgraphInter_le_left hL' hKp_le_G'
  have hKL_le_Kp : K_L ≤ K_p := subgraphInter_le_right hL' hKp_le_G'
  have hVL'_split : V(L') = V(M'_G) ∪ V(K_L) := by
    change V(L') = (V(L') ∩ V(Γ')) ∪ (V(L') ∩ V(K_p))
    rw [← inter_union_distrib_left, ← hVG'_union_p,
      inter_eq_self_of_subset_left hL'.vertexSet_mono]
  have hEL'_split : E(L') = E(M'_G) ∪ E(K_L) := by
    refine Subset.antisymm ?_ (union_subset hM'_le_L'.edgeSet_mono hKL_le_L'.edgeSet_mono)
    intro e he
    obtain ⟨x, y, hl⟩ := L'.exists_isLink_of_mem_edgeSet he
    have hlG' : G'.IsLink e x y := hL'.isLink_mono hl
    by_cases heK : e ∈ E(K_p)
    · have hlK : K_p.IsLink e x y := (hKp_le_G'.isLink_iff heK).mpr hlG'
      have hl_KL : K_L.IsLink e x y := by
        unfold K_L subgraphInter
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨he, heK⟩, hlG', ⟨hl.left_mem, hlK.left_mem⟩, ⟨hl.right_mem, hlK.right_mem⟩⟩
      exact Or.inr hl_KL.edge_mem
    · have heΓ' : e ∈ E(Γ') := (hEG'_union ▸ hlG'.edge_mem).resolve_right heK
      have hlΓ' : Γ'.IsLink e x y := (hΓ'G'.isLink_iff heΓ').mpr hlG'
      have hl_inter : (subgraphInter G' L' Γ').IsLink e x y := by
        unfold subgraphInter
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨he, heΓ'⟩, hlG', ⟨hl.left_mem, hlΓ'.left_mem⟩, ⟨hl.right_mem, hlΓ'.right_mem⟩⟩
      have hl_M' : M'_G.IsLink e x y := by
        unfold M'_G
        rw [deleteEdges_isLink]
        exact ⟨hl_inter, heK⟩
      exact Or.inl hl_M'.edge_mem
  have hDisj_EM'_EKp : Disjoint E(M'_G) E(K_p) := disjoint_sdiff_left
  -- Pull `M'_G` back to `H' ≤ D'.toGraph`
  have hM'_sub_D' : M'_G ≤ D'.toGraph.mapEmbed ιV ιE := by
    rwa [← toEmbeddedGraph_eq_mapEmbed, ← hΓ']
  obtain ⟨hH'_map, hH'_le⟩ := mapEmbed_comapEmbed_of_le ιV ιE hM'_sub_D'
  let H' := M'_G.comapEmbed ιV ιE
  have hDisj_EH'_EK : Disjoint E(H') E_K := by
    rw [disjoint_left]
    intro e₀ he₀H' he₀K
    have he_M' : ιE e₀ ∈ E(M'_G) := hH'_map ▸ mem_image_of_mem ιE he₀H'
    exact disjoint_left.mp hDisj_EM'_EKp he_M' he₀K.2
  -- Apply `sleeve_variant_pullback`
  obtain ⟨D''_hat, H''_hat, hD''_U_range, hVar_hat, hY_hat_sub_V'', hEK_sub_D'', hEK_isLink,
      hH''_le, hDisj_EH''_EK, hVH''_inter_Y, hConn_iff, ⟨g_S⟩⟩ :=
    sleeve_variant_pullback hS cap D D' Y₀ hY₀_sub h₀ hh₀ hDU_bd hDV_bd
      S_sleeve hSleeve hSleeve_disj hPaths hSleeve_T hVar H' hH'_le E_K hEK_sub hEK_Y₀
      hDisj_EH'_EK
  -- Pull `D''_hat.toGraph` and `H''_hat` back to `S` via `capV, capE` and push to `α, β` via `ιV, ιE`
  let capV : S ↪ Shat := ⟨cap.emb, cap.isEmbedding.injective⟩
  let capE : Set S ↪ Set Shat := ⟨image cap.emb, image_injective.mpr cap.isEmbedding.injective⟩
  have hVD''_range : V(D''_hat.toGraph) ⊆ range capV :=
    D''_hat.V_subset_U.trans hD''_U_range
  have hED''_range : E(D''_hat.toGraph) ⊆ range capE := by
    intro e he
    have he_sub : e ⊆ range cap.emb := fun z hz => hD''_U_range (he.2.1 hz).1
    exact ⟨cap.emb ⁻¹' e, image_preimage_eq_of_subset he_sub⟩
  let J'' : Graph S (Set S) := D''_hat.toGraph.comapEmbed capV capE
  have hJ''_map : J''.mapEmbed capV capE = D''_hat.toGraph := by
    refine Graph.ext (image_preimage_eq_of_subset hVD''_range) fun e x y => ?_
    constructor
    · rintro ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
      exact hl
    · intro hl
      obtain ⟨e₀, rfl⟩ := hED''_range hl.edge_mem
      obtain ⟨x₀, rfl⟩ := hVD''_range hl.left_mem
      obtain ⟨y₀, rfl⟩ := hVD''_range hl.right_mem
      exact ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
  obtain ⟨hH''_map, hH''_le_J''⟩ :=
    mapEmbed_comapEmbed_of_le capV capE (hJ''_map.symm ▸ hH''_le)
  let H'' : Graph S (Set S) := H''_hat.comapEmbed capV capE
  let Γ'' : Graph α β := J''.mapEmbed ιV ιE
  let M'' : Graph α β := H''.mapEmbed ιV ιE
  have hM''_le_Γ'' : M'' ≤ Γ'' := mapEmbed_mono ιV ιE hH''_le_J''
  -- Properties of `M''` and `Γ''` on `K_p`
  have hDisj_EM''_EKp : Disjoint E(M'') E(K_p) := by
    rw [disjoint_left]
    rintro _ ⟨e₀, he₀H'', rfl⟩ heK
    have he₀_EK : e₀ ∈ E_K := hEK_eq.symm ▸ heK
    exact disjoint_left.mp hDisj_EH''_EK
      (hH''_map ▸ mem_image_of_mem capE he₀H'') (mem_image_of_mem capE he₀_EK)
  have hComp_M''_KL : M''.Compatible K_L :=
    Compatible.of_disjoint_edgeSet (hDisj_EM''_EKp.mono_right hKL_le_Kp.edgeSet_mono)
  have hVM''_inter_Kp : V(M'') ∩ V(K_p) = V(M'_G) ∩ V(K_p) := by
    have hVH''_YS : V(H'') ∩ Y_S = V(H') ∩ Y_S := by
      apply image_injective.mpr capV.injective
      change cap.emb '' (V(H'') ∩ Y_S) = cap.emb '' (V(H') ∩ Y_S)
      rw [image_inter cap.isEmbedding.injective, ← hVH''_inter_Y]
      congr 1
      exact congrArg Graph.vertexSet hH''_map
    ext w
    constructor
    · rintro ⟨⟨x, hxH'', rfl⟩, hxKp⟩
      have hxYS : x ∈ Y_S := hYS_pre ▸ hxKp
      have hx_in : x ∈ V(H'') ∩ Y_S := ⟨hxH'', hxYS⟩
      rw [hVH''_YS] at hx_in
      exact ⟨hH'_map ▸ mem_image_of_mem ιV hx_in.1, hxKp⟩
    · rintro ⟨hwM', hwKp⟩
      rw [← hH'_map] at hwM'
      rcases hwM' with ⟨x, hxH', rfl⟩
      have hxYS : x ∈ Y_S := hYS_pre ▸ hwKp
      have hx_in : x ∈ V(H') ∩ Y_S := ⟨hxH', hxYS⟩
      rw [← hVH''_YS] at hx_in
      exact ⟨mem_image_of_mem ιV hx_in.1, hwKp⟩
  have hSame_M''_M' : HasSameEffectOn M'' M'_G (V(M'') ∩ V(K_p)) := by
    rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
    rintro _ ⟨⟨u, huH'', rfl⟩, huKp⟩ _ ⟨⟨v, hvH'', rfl⟩, hvKp⟩
    have huYS : u ∈ Y_S := hYS_pre ▸ huKp
    have hvYS : v ∈ Y_S := hYS_pre ▸ hvKp
    rw [areConnectedIn_mapEmbed_iff ιV ιE H'', ← hH'_map, areConnectedIn_mapEmbed_iff ιV ιE H']
    have h1 : AreConnectedIn H'' u v ↔ AreConnectedIn H''_hat (cap.emb u) (cap.emb v) := by
      rw [← hH''_map]
      exact (areConnectedIn_mapEmbed_iff capV capE H'').symm
    exact h1.trans (hConn_iff u huYS v hvYS)
  let L₁ : Graph α β := graphUnion M'' K_L
  have hSame_L₁_L' : HasSameEffectOn L₁ L' Z :=
    hasSameEffectOn_graphUnion_of_sameEffect_inter hM'_le_L' hKL_le_L' hKL_le_Kp
      hVL'_split hEL'_split hComp_M''_KL hDisj_EM''_EKp hDisj_EM'_EKp
      hVM''_inter_Kp hSame_M''_M' hZ hL'
  -- Set up `G'' = graphUnion Γ'' K_p` and compatibility of `Γ''` and `K_p`
  have hVΓ''_inter_Kp : V(Γ'') ∩ V(K_p) = V(Γ) ∩ V(K_p) := by
    rw [hVΓ_inter_Kp]
    ext w
    constructor
    · rintro ⟨⟨x, _, rfl⟩, hxKp⟩
      exact mem_image_of_mem ιV (hYS_pre ▸ hxKp)
    · rintro ⟨x, hxYS, rfl⟩
      have hcx_V'' : cap.emb x ∈ D''_hat.V := hY_hat_sub_V'' (mem_image_of_mem cap.emb hxYS)
      have hxKp : x ∈ ιV ⁻¹' V(K_p) := hYS_pre.symm ▸ hxYS
      exact ⟨mem_image_of_mem ιV hcx_V'', hxKp⟩
  have hΓ''_isLink_iff : ∀ e ∈ E(K_p), ∀ x y, Γ''.IsLink e x y ↔ Γ.IsLink e x y := by
    intro e heK x y
    rw [hΓ, toEmbeddedGraph_eq_mapEmbed]
    constructor
    · rintro ⟨e₀, x₀, y₀, hlJ, rfl, rfl, rfl⟩
      have he₀_EK : e₀ ∈ E_K := hEK_eq.symm ▸ heK
      have hlD'' : D''_hat.toGraph.IsLink (capE e₀) (capV x₀) (capV y₀) :=
        hJ''_map ▸ (isLink_mapEmbed_iff capV capE J'').mpr hlJ
      have hlDhat : D_hat.toGraph.IsLink (capE e₀) (capV x₀) (capV y₀) :=
        (hEK_isLink e₀ he₀_EK (capV x₀) (capV y₀)).mp hlD''
      have hlD : D.toGraph.IsLink e₀ x₀ y₀ :=
        (isLink_mapEmbed_iff capV capE D.toGraph).mp (drawingMapEmb_toGraph_eq D hcap_emb ▸ hlDhat)
      exact ⟨e₀, x₀, y₀, hlD, rfl, rfl, rfl⟩
    · rintro ⟨e₀, x₀, y₀, hlD, rfl, rfl, rfl⟩
      have he₀_EK : e₀ ∈ E_K := hEK_eq.symm ▸ heK
      have hlDhat : D_hat.toGraph.IsLink (capE e₀) (capV x₀) (capV y₀) :=
        (drawingMapEmb_toGraph_eq D hcap_emb).symm ▸ (isLink_mapEmbed_iff capV capE D.toGraph).mpr hlD
      have hlD'' : D''_hat.toGraph.IsLink (capE e₀) (capV x₀) (capV y₀) :=
        (hEK_isLink e₀ he₀_EK (capV x₀) (capV y₀)).mpr hlDhat
      have hlJ : J''.IsLink e₀ x₀ y₀ :=
        (isLink_mapEmbed_iff capV capE J'').mp (hJ''_map.symm ▸ hlD'')
      exact ⟨e₀, x₀, y₀, hlJ, rfl, rfl, rfl⟩
  have hComp_Γ''_Kp : Γ''.Compatible K_p := by
    intro e heΓ'' heKp x y
    obtain ⟨u, v, hl₁⟩ := Γ''.exists_isLink_of_mem_edgeSet heΓ''
    have heΓ : e ∈ E(Γ) := ((hΓ''_isLink_iff e heKp u v).mp hl₁).edge_mem
    exact (hΓ''_isLink_iff e heKp x y).trans ((Compatible.of_le_le hΓG hKp_le_G) heΓ heKp x y)
  let G'' : Graph α β := graphUnion Γ'' K_p
  have hΓ''_le_G'' : Γ'' ≤ G'' := le_graphUnion_left Γ'' K_p
  have hKp_le_G'' : K_p ≤ G'' := le_graphUnion_right hComp_Γ''_Kp
  have hL₁_le_G'' : L₁ ≤ G'' := by
    refine ⟨union_subset (hM''_le_Γ''.vertexSet_mono.trans subset_union_left)
      (hKL_le_Kp.vertexSet_mono.trans subset_union_right), fun e x y hl => ?_⟩
    rw [isLink_graphUnion_of_compatible hComp_M''_KL] at hl
    exact hl.elim (fun h => hΓ''_le_G''.isLink_mono (hM''_le_Γ''.isLink_mono h))
      (fun h => hKp_le_G''.isLink_mono (hKL_le_Kp.isLink_mono h))
  have hInter_G'' : subgraphInter G Γ K_p = subgraphInter G'' Γ'' K_p := by
    refine Graph.ext hVΓ''_inter_Kp.symm fun e x y => ?_
    unfold subgraphInter
    rw [restrict_isLink, induce_isLink, restrict_isLink, induce_isLink]
    constructor
    · rintro ⟨⟨heΓ, heKp⟩, hlG, hx, hy⟩
      have hlΓ : Γ.IsLink e x y := (hΓG.isLink_iff heΓ).mpr hlG
      have hlΓ'' : Γ''.IsLink e x y := (hΓ''_isLink_iff e heKp x y).mpr hlΓ
      exact ⟨⟨hlΓ''.edge_mem, heKp⟩, hΓ''_le_G''.isLink_mono hlΓ'',
        hVΓ''_inter_Kp.symm ▸ hx, hVΓ''_inter_Kp.symm ▸ hy⟩
    · rintro ⟨⟨heΓ'', heKp⟩, hlG'', hx, hy⟩
      have hlΓ'' : Γ''.IsLink e x y := (hΓ''_le_G''.isLink_iff heΓ'').mpr hlG''
      have hlΓ : Γ.IsLink e x y := (hΓ''_isLink_iff e heKp x y).mp hlΓ''
      exact ⟨⟨hlΓ.edge_mem, heKp⟩, hΓG.isLink_mono hlΓ,
        hVΓ''_inter_Kp ▸ hx, hVΓ''_inter_Kp ▸ hy⟩
  -- Embed into `α ⊕ α` and `β ⊕ β` and apply `h41` on `Shat`
  obtain ⟨ιV_hat, ιE_hat, hfV_cap, hfV_inr, hfE_cap, _⟩ :=
    exists_capped_embeddings cap g_S ιV ιE
  let inlV : α ↪ α ⊕ α := Embedding.inl
  let inlE : β ↪ β ⊕ β := Embedding.inl
  have hV_trans : ιV.trans inlV = capV.trans ιV_hat := by
    ext x; exact (hfV_cap x).symm
  have hE_trans : ιE.trans inlE = capE.trans ιE_hat := by
    ext e₀; exact (hfE_cap e₀).symm
  have hΓ_hat_eq : Γ.mapEmbed inlV inlE = D_hat.toEmbeddedGraph ιV_hat ιE_hat := by
    rw [hΓ, toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed,
      mapEmbed_mapEmbed, hV_trans, hE_trans, ← mapEmbed_mapEmbed,
      drawingMapEmb_toGraph_eq D hcap_emb]
  have hΓ''_hat_eq : Γ''.mapEmbed inlV inlE = D''_hat.toEmbeddedGraph ιV_hat ιE_hat := by
    rw [toEmbeddedGraph_eq_mapEmbed, mapEmbed_mapEmbed, hV_trans, hE_trans,
      ← mapEmbed_mapEmbed, hJ''_map]
  have hY_hat_pre :
      ιV_hat ⁻¹' (V(Γ.mapEmbed inlV inlE) ∩ V(K_p.mapEmbed inlV inlE)) = Y_hat := by
    rw [vertexSet_mapEmbed, vertexSet_mapEmbed, ← image_inter inlV.injective, hVΓ_inter_Kp]
    ext z
    simp only [mem_preimage, mem_image, Y_hat]
    constructor
    · rintro ⟨w, ⟨x, hxYS, rfl⟩, hzx⟩
      have hzx' : ιV_hat (cap.emb x) = ιV_hat z := by rw [hfV_cap x]; exact hzx
      exact ⟨x, hxYS, ιV_hat.injective hzx'⟩
    · rintro ⟨x, hxYS, rfl⟩
      exact ⟨ιV x, ⟨x, hxYS, rfl⟩, (hfV_cap x).symm⟩
  have hVar_hat' : IsVariant D_hat D''_hat
      (insulatedSet D_hat (ιV_hat ⁻¹' (V(Γ.mapEmbed inlV inlE) ∩ V(K_p.mapEmbed inlV inlE))) h₀) := by
    rwa [hY_hat_pre]
  have hInter_inl :
      subgraphInter (G.mapEmbed inlV inlE) (Γ.mapEmbed inlV inlE) (K_p.mapEmbed inlV inlE) =
        subgraphInter (G''.mapEmbed inlV inlE) (Γ''.mapEmbed inlV inlE) (K_p.mapEmbed inlV inlE) := by
    rw [← mapEmbed_subgraphInter, ← mapEmbed_subgraphInter, hInter_G'']
  have hVG''_fin : V(G'').Finite :=
    ((D''_hat.finite_V.preimage cap.isEmbedding.injective.injOn).image ιV).union
      ((hVG.subset hKG.vertexSet_mono).union ((D.finite_V.subset inter_subset_left).image ιV))
  have hEJ''_sub : E(J'') ⊆ (image cap.emb) ⁻¹' D''_hat.E :=
    fun _ ⟨_, _, hl⟩ => hl.edge_mem
  have hEG''_fin : E(G'').Finite :=
    (((D''_hat.finite_edges.preimage (image_injective.mpr cap.isEmbedding.injective).injOn).subset
      hEJ''_sub).image ιE).union (hEG.subset hKG.edgeSet_mono)
  obtain ⟨L_inl, hL_inl_le, hSame_inl, hInter_inl_le⟩ :=
    h41 Shat cap.isSurface
      (G.mapEmbed inlV inlE) (Γ.mapEmbed inlV inlE) (K_p.mapEmbed inlV inlE)
      (G''.mapEmbed inlV inlE) (Γ''.mapEmbed inlV inlE) (L₁.mapEmbed inlV inlE)
      (hVG.image inlV) (hEG.image inlE) (hVG''_fin.image inlV) (hEG''_fin.image inlE)
      (mapEmbed_mono inlV inlE hΓG) (mapEmbed_mono inlV inlE hKp_le_G)
      (by change inlV '' V(G) = inlV '' V(Γ) ∪ inlV '' V(K_p); rw [← image_union, hVG_union_p])
      (by change inlE '' E(G) = inlE '' E(Γ) ∪ inlE '' E(K); rw [← image_union, hEG_union])
      (mapEmbed_mono inlV inlE hΓ''_le_G'') (mapEmbed_mono inlV inlE hKp_le_G'')
      (by change inlV '' (V(Γ'') ∪ V(K_p)) = inlV '' V(Γ'') ∪ inlV '' V(K_p); exact image_union _ _ _)
      (by change inlE '' (E(Γ'') ∪ E(K_p)) = inlE '' E(Γ'') ∪ inlE '' E(K_p); exact image_union _ _ _)
      hInter_inl D_hat D''_hat ιV_hat ιE_hat hΓ_hat_eq hΓ''_hat_eq hVar_hat'
      (inlV '' Z) (image_mono hZ) ((ncard_image_of_injective Z inlV.injective).symm ▸ hZp)
      (mapEmbed_mono inlV inlE hL₁_le_G'')
  obtain ⟨hL_map, hL_le⟩ := mapEmbed_comapEmbed_of_le inlV inlE hL_inl_le
  let L := L_inl.comapEmbed inlV inlE
  have hSame_L_L₁ : HasSameEffectOn L L₁ Z := by
    rw [← hL_map] at hSame_inl
    exact (hasSameEffectOn_mapEmbed_iff inlV inlE).mp hSame_inl
  have hInter_L_Kp : subgraphInter G L K_p ≤ L₁ := by
    apply (mapEmbed_le_iff inlV inlE).mp
    rw [mapEmbed_subgraphInter, hL_map]
    exact hInter_inl_le
  refine ⟨L, hL_le, hSame_L_L₁.trans hSame_L₁_L', ?_⟩
  refine ⟨?_, fun e x y hl => ?_⟩
  · intro v ⟨hvL, hvK⟩
    have hv_in : v ∈ V(subgraphInter G L K_p) := ⟨hvL, Or.inl hvK⟩
    rcases hInter_L_Kp.vertexSet_mono hv_in with hvM'' | hvKL
    · have hv_inter : v ∈ V(M'') ∩ V(K_p) := ⟨hvM'', Or.inl hvK⟩
      rw [hVM''_inter_Kp] at hv_inter
      exact hM'_le_L'.vertexSet_mono hv_inter.1
    · exact hvKL.1
  · have hl_Kp : (subgraphInter G L K_p).IsLink e x y := by
      unfold subgraphInter at hl ⊢
      rw [restrict_isLink, induce_isLink] at hl ⊢
      exact ⟨⟨hl.1.1, hl.1.2⟩, hl.2.1,
        ⟨hl.2.2.1.1, Or.inl hl.2.2.1.2⟩, ⟨hl.2.2.2.1, Or.inl hl.2.2.2.2⟩⟩
    have hl_L₁ : L₁.IsLink e x y := hInter_L_Kp.isLink_mono hl_Kp
    rw [isLink_graphUnion_of_compatible hComp_M''_KL] at hl_L₁
    rcases hl_L₁ with hlM'' | hlKL
    · exact (disjoint_left.mp hDisj_EM''_EKp hlM''.edge_mem hl.1.2).elim
    · exact hKL_le_L'.isLink_mono hlKL

/-- **4.2** (Graph Minors XXII, page 538):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a drawing in a surface $\Sigma$, and let
$$Z \subseteq V(K) \cup (V(\Gamma) \cap \text{bd}(\Sigma)),$$
with $|Z| \le p$. For each cuff $C$ of $\Sigma$ let $S(C)$ be a sleeve for $C$ in $\Gamma$, so that
$S(C_1) \cap S(C_2) = \emptyset$ for all distinct cuffs $C_1, C_2$. Let $S$ be the union of
$\Sigma \cap S(C)$ over all cuffs $C$, and let $T$ be the set of all points of $\Sigma$ that are
$h$-insulated in $\hat{\Sigma}$ from $V(\Gamma \cap K) \cup (V(\Gamma) \cap \text{bd}(\Sigma))$ by
$\Gamma$. Suppose that
(i) for each cuff $C$ there are $|V(\Gamma) \cap C|$ mutually vertex-disjoint paths of $\Gamma$
between $V(\Gamma) \cap C$ and $V(\Gamma) \cap \text{bd}(S(C))$,
(ii) for each cuff $C$, $\text{bd}(S(C)) \subseteq T$ and $S(C) \cap V(\Gamma \cap K) = \emptyset$.
Then for every $(S \cup T)$-variant $\Gamma'$ of $\Gamma$ with $\Gamma' \cap K = \Gamma \cap K$ and
$V(\Gamma') \cap \text{bd}(\Sigma) = V(\Gamma) \cap \text{bd}(\Sigma)$, and for every
$L' \subseteq \Gamma' \cup K$, there exists $L \subseteq \Gamma \cup K$ with the same effect on $Z$
as $L'$, with $L \cap K \subseteq L'$." -/
theorem theorem_4_2_proof  (p : ℕ) :
    ∃ h ≥ 1, ∀ (S Shat : Type w) [TopologicalSpace S] [T2Space S]
      [TopologicalSpace Shat] [T2Space Shat],
      (hS : IsSurface S) → (cap : GM19.IsCappedSurface S Shat) →
      ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      D.U ∩ bd S ⊆ D.V → D'.V ∩ bd S = D.V ∩ bd S →
      ∀ (S_sleeve : Set S → Set Shat),
      (∀ C ∈ cuffs S, IsSleeve cap D C (S_sleeve C)) →
      (∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (S_sleeve C₁) (S_sleeve C₂)) →
      (∀ C ∈ cuffs S, ∃ P : ↑(D.V ∩ C) → Graph S (Set S),
        (∀ x : ↑(D.V ∩ C), ∃ y ∈ D.V ∩ cap.emb ⁻¹' subBd (S_sleeve C),
          IsGraphPathWithEnds D.toGraph (P x) x.1 y) ∧
        Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂))) →
      (∀ C ∈ cuffs S,
        subBd (S_sleeve C) ⊆
          cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
            (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) ∧
        Disjoint (S_sleeve C) (cap.emb '' (ιV ⁻¹' (V(Γ) ∩ V(K))))) →
      IsVariant D D'
        ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
          cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
            (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) →
      ∀ (Z : Set α), Z ⊆ V(K) ∪ ιV '' (D.V ∩ bd S) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' := by
  classical
  obtain ⟨h₀, hh₀, h41⟩ := theorem_4_1_proof.{u, v, w} p
  refine ⟨h₀ + 1, by omega, ?_⟩
  intro S Shat _ _ _ _ hS cap α β G Γ K G' Γ' L' hVG hEG _hVG' _hEG'
    hΓG hKG hVG_union hEG_union hΓ'G' hKG' hVG'_union hEG'_union hInter
    D D' ιV ιE hΓ hΓ' hDU_bd hDV_bd
    S_sleeve hSleeve hSleeve_disj hPaths hSleeve_T hVar Z hZ hZp hL'
  let jV : α ↪ α ⊕ α :=
    { toFun := fun x => if x ∈ V(K) \ V(Γ) then Sum.inr x else Sum.inl x
      inj' := by
        intro x y hxy
        by_cases hx : x ∈ V(K) \ V(Γ) <;> by_cases hy : y ∈ V(K) \ V(Γ) <;>
          simp only [hx, hy, ↓reduceIte, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at hxy <;>
          exact hxy }
  let jE : β ↪ β ⊕ β :=
    { toFun := fun e => if e ∈ E(K) \ E(Γ) then Sum.inr e else Sum.inl e
      inj' := by
        intro e₁ e₂ he
        by_cases h₁ : e₁ ∈ E(K) \ E(Γ) <;> by_cases h₂ : e₂ ∈ E(K) \ E(Γ) <;>
          simp only [h₁, h₂, ↓reduceIte, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at he <;>
          exact he }
  let ιV' : S ↪ α ⊕ α := ιV.trans Embedding.inl
  let ιE' : Set S ↪ β ⊕ β := ιE.trans Embedding.inl
  have hV_inter : V(Γ) ∩ V(K) = V(Γ') ∩ V(K) := congrArg Graph.vertexSet hInter
  have hjV_Γ : ∀ x ∈ V(Γ), jV x = Sum.inl x := by
    intro x hx
    change (if x ∈ V(K) \ V(Γ) then Sum.inr x else Sum.inl x) = Sum.inl x
    have hn : x ∉ V(K) \ V(Γ) := fun h => h.2 hx
    simp only [hn, ↓reduceIte]
  have hjE_Γ : ∀ e ∈ E(Γ), jE e = Sum.inl e := by
    intro e he
    change (if e ∈ E(K) \ E(Γ) then Sum.inr e else Sum.inl e) = Sum.inl e
    have hn : e ∉ E(K) \ E(Γ) := fun h => h.2 he
    simp only [hn, ↓reduceIte]
  have hjV_Γ' : ∀ x ∈ V(Γ'), jV x = Sum.inl x := by
    intro x hx
    change (if x ∈ V(K) \ V(Γ) then Sum.inr x else Sum.inl x) = Sum.inl x
    have hn : x ∉ V(K) \ V(Γ) := by
      rintro ⟨hxK, hx_not_Γ⟩
      have hx_in : x ∈ V(Γ') ∩ V(K) := ⟨hx, hxK⟩
      rw [← hV_inter] at hx_in
      exact hx_not_Γ hx_in.1
    simp only [hn, ↓reduceIte]
  have hjE_Γ' : ∀ e ∈ E(Γ'), jE e = Sum.inl e := by
    intro e he
    change (if e ∈ E(K) \ E(Γ) then Sum.inr e else Sum.inl e) = Sum.inl e
    have hn : e ∉ E(K) \ E(Γ) := by
      rintro ⟨heK, he_not_Γ⟩
      obtain ⟨x, y, hlΓ'⟩ := Γ'.exists_isLink_of_mem_edgeSet he
      have hlG' : G'.IsLink e x y := hΓ'G'.isLink_mono hlΓ'
      have hlK : K.IsLink e x y := (hKG'.isLink_iff heK).mpr hlG'
      have hl_inter' : (subgraphInter G' Γ' K).IsLink e x y := by
        unfold subgraphInter
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨he, heK⟩, hlG', ⟨hlΓ'.left_mem, hlK.left_mem⟩, ⟨hlΓ'.right_mem, hlK.right_mem⟩⟩
      rw [← hInter] at hl_inter'
      exact he_not_Γ ((subgraphInter_le_left hΓG hKG).isLink_mono hl_inter').edge_mem
    simp only [hn, ↓reduceIte]
  have hΓ_map : Γ.mapEmbed jV jE = D.toEmbeddedGraph ιV' ιE' := by
    rw [hΓ, toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed]
    refine Graph.ext ?_ fun e x y => ?_
    · ext z
      simp only [vertexSet_mapEmbed, mem_image]
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, (hjV_Γ (ιV v) (hΓ ▸ mem_image_of_mem ιV hv)).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨ιV v, ⟨v, hv, rfl⟩, hjV_Γ (ιV v) (hΓ ▸ mem_image_of_mem ιV hv)⟩
    · constructor
      · rintro ⟨e₁, x₁, y₁, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
        exact ⟨e₀, x₀, y₀, hl₀,
          (hjE_Γ (ιE e₀) (hΓ ▸ mem_image_of_mem ιE hl₀.1)).symm,
          (hjV_Γ (ιV x₀) (hΓ ▸ mem_image_of_mem ιV hl₀.left_mem)).symm,
          (hjV_Γ (ιV y₀) (hΓ ▸ mem_image_of_mem ιV hl₀.right_mem)).symm⟩
      · rintro ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
        exact ⟨ιE e₀, ιV x₀, ιV y₀, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩,
          hjE_Γ (ιE e₀) (hΓ ▸ mem_image_of_mem ιE hl₀.1),
          hjV_Γ (ιV x₀) (hΓ ▸ mem_image_of_mem ιV hl₀.left_mem),
          hjV_Γ (ιV y₀) (hΓ ▸ mem_image_of_mem ιV hl₀.right_mem)⟩
  have hΓ'_map : Γ'.mapEmbed jV jE = D'.toEmbeddedGraph ιV' ιE' := by
    rw [hΓ', toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed]
    refine Graph.ext ?_ fun e x y => ?_
    · ext z
      simp only [vertexSet_mapEmbed, mem_image]
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, (hjV_Γ' (ιV v) (hΓ' ▸ mem_image_of_mem ιV hv)).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨ιV v, ⟨v, hv, rfl⟩, hjV_Γ' (ιV v) (hΓ' ▸ mem_image_of_mem ιV hv)⟩
    · constructor
      · rintro ⟨e₁, x₁, y₁, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
        exact ⟨e₀, x₀, y₀, hl₀,
          (hjE_Γ' (ιE e₀) (hΓ' ▸ mem_image_of_mem ιE hl₀.1)).symm,
          (hjV_Γ' (ιV x₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.left_mem)).symm,
          (hjV_Γ' (ιV y₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.right_mem)).symm⟩
      · rintro ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
        exact ⟨ιE e₀, ιV x₀, ιV y₀, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩,
          hjE_Γ' (ιE e₀) (hΓ' ▸ mem_image_of_mem ιE hl₀.1),
          hjV_Γ' (ιV x₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.left_mem),
          hjV_Γ' (ιV y₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.right_mem)⟩
  have hVK' : ιV' ⁻¹' V(K.mapEmbed jV jE) ⊆ D.V := by
    rintro v ⟨y, hyK, hy_eq⟩
    change (if y ∈ V(K) \ V(Γ) then Sum.inr y else Sum.inl y) = Sum.inl (ιV v) at hy_eq
    by_cases hy_diff : y ∈ V(K) \ V(Γ)
    · simp only [hy_diff, ↓reduceIte, reduceCtorEq] at hy_eq
    · simp only [hy_diff, ↓reduceIte, Sum.inl.injEq] at hy_eq
      subst hy_eq
      have hvΓ : ιV v ∈ V(Γ) := by_contra fun hn => hy_diff ⟨hyK, hn⟩
      rw [hΓ] at hvΓ
      exact (ιV.injective.mem_set_image).mp hvΓ
  have hEK' : ιE' ⁻¹' E(K.mapEmbed jV jE) ⊆ D.E := by
    rintro e ⟨b, hbK, hb_eq⟩
    change (if b ∈ E(K) \ E(Γ) then Sum.inr b else Sum.inl b) = Sum.inl (ιE e) at hb_eq
    by_cases hb_diff : b ∈ E(K) \ E(Γ)
    · simp only [hb_diff, ↓reduceIte, reduceCtorEq] at hb_eq
    · simp only [hb_diff, ↓reduceIte, Sum.inl.injEq] at hb_eq
      subst hb_eq
      have heΓ : ιE e ∈ E(Γ) := by_contra fun hn => hb_diff ⟨hbK, hn⟩
      rw [hΓ] at heΓ
      exact (ιE.injective.mem_set_image).mp heΓ
  have hY_eq' : ιV' ⁻¹' (V(Γ.mapEmbed jV jE) ∩ V(K.mapEmbed jV jE)) =
      ιV ⁻¹' (V(Γ) ∩ V(K)) := by
    ext v
    simp only [mem_preimage, mem_inter_iff, vertexSet_mapEmbed]
    constructor
    · rintro ⟨⟨x, hxΓ, hx_eq⟩, ⟨y, hyK, hy_eq⟩⟩
      have hxy : y = x := jV.injective (hy_eq.trans hx_eq.symm)
      subst y
      rw [hjV_Γ x hxΓ] at hx_eq
      obtain rfl : x = ιV v := Sum.inl.inj hx_eq
      exact ⟨hxΓ, hyK⟩
    · rintro ⟨hvΓ, hvK⟩
      have h_eq : jV (ιV v) = ιV' v := hjV_Γ (ιV v) hvΓ
      exact ⟨⟨ιV v, hvΓ, h_eq⟩, ⟨ιV v, hvK, h_eq⟩⟩
  have hSleeve_T' : ∀ C ∈ cuffs S,
      subBd (S_sleeve C) ⊆
        cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' ((ιV' ⁻¹' (V(Γ.mapEmbed jV jE) ∩ V(K.mapEmbed jV jE))) ∪ (D.V ∩ bd S))) (h₀ + 1)) ∧
      Disjoint (S_sleeve C) (cap.emb '' (ιV' ⁻¹' (V(Γ.mapEmbed jV jE) ∩ V(K.mapEmbed jV jE)))) := by
    rw [hY_eq']
    exact hSleeve_T
  have hVar' : IsVariant D D'
      ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
        cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' ((ιV' ⁻¹' (V(Γ.mapEmbed jV jE) ∩ V(K.mapEmbed jV jE))) ∪ (D.V ∩ bd S))) (h₀ + 1)) := by
    rwa [hY_eq']
  have hZ' : jV '' Z ⊆ V(K.mapEmbed jV jE) ∪ ιV' '' (D.V ∩ bd S) := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hZ hz with hzK | ⟨v, hv, rfl⟩
    · exact Or.inl (mem_image_of_mem jV hzK)
    · right
      have hvΓ : ιV v ∈ V(Γ) := hΓ ▸ mem_image_of_mem ιV hv.1
      rw [hjV_Γ (ιV v) hvΓ]
      exact ⟨v, hv, rfl⟩
  have hInter_map :
      subgraphInter (G.mapEmbed jV jE) (Γ.mapEmbed jV jE) (K.mapEmbed jV jE) =
        subgraphInter (G'.mapEmbed jV jE) (Γ'.mapEmbed jV jE) (K.mapEmbed jV jE) := by
    rw [← mapEmbed_subgraphInter, ← mapEmbed_subgraphInter, hInter]
  obtain ⟨L_img, hL_img_le, hSame_img, hInter_img⟩ :=
    lemma_4_2_normalized (α := α ⊕ α) (β := β ⊕ β) hh₀
      (fun S_hat _ _ hS_hat => @h41 S_hat _ _ hS_hat ((α ⊕ α) ⊕ (α ⊕ α)) ((β ⊕ β) ⊕ (β ⊕ β)))
      hS cap
      (G.mapEmbed jV jE) (Γ.mapEmbed jV jE) (K.mapEmbed jV jE)
      (G'.mapEmbed jV jE) (Γ'.mapEmbed jV jE) (L'.mapEmbed jV jE)
      (hVG.image jV) (hEG.image jE)
      (mapEmbed_mono jV jE hΓG) (mapEmbed_mono jV jE hKG)
      (by rw [vertexSet_mapEmbed, vertexSet_mapEmbed, vertexSet_mapEmbed, ← image_union, hVG_union])
      (by rw [edgeSet_mapEmbed, edgeSet_mapEmbed, edgeSet_mapEmbed, ← image_union, hEG_union])
      (mapEmbed_mono jV jE hΓ'G') (mapEmbed_mono jV jE hKG')
      (by rw [vertexSet_mapEmbed, vertexSet_mapEmbed, vertexSet_mapEmbed, ← image_union, hVG'_union])
      (by rw [edgeSet_mapEmbed, edgeSet_mapEmbed, edgeSet_mapEmbed, ← image_union, hEG'_union])
      hInter_map D D' ιV' ιE' hΓ_map hΓ'_map hVK' hEK' hDU_bd hDV_bd
      S_sleeve hSleeve hSleeve_disj hPaths hSleeve_T' hVar'
      (jV '' Z) hZ' ((ncard_image_of_injective Z jV.injective).symm ▸ hZp)
      (mapEmbed_mono jV jE hL')
  obtain ⟨hL_map, hL_le⟩ := mapEmbed_comapEmbed_of_le jV jE hL_img_le
  let L := L_img.comapEmbed jV jE
  refine ⟨L, hL_le, ?_, ?_⟩
  · rw [← hL_map] at hSame_img
    exact (hasSameEffectOn_mapEmbed_iff jV jE).mp hSame_img
  · apply (mapEmbed_le_iff jV jE).mp
    rw [mapEmbed_subgraphInter, hL_map]
    exact hInter_img



end GraphMinor.GM22
