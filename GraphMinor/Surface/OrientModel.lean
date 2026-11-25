module

public import GraphMinor.Surface.OrientCocycle
public import GraphMinor.Surface.HoleLoop
public import GraphMinor.Surface.CutParallel
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Orientation cocycle on model surfaces and cuttings

This file evaluates the first Stiefel-Whitney local cocycle `w1 A` on a model surface presented by
the normal word `ew a b c` and under cuttings `ψ : Y → S` along a proper `I`-arc:

1. **Holomorphic/antiholomorphic exponential maps**: `isPosLocal_exp`, `isPosLocal_exp_affine`,
   and `not_isPosLocal_exp_affine_conj`.
2. **Explicit charts on `Presents (sW (ew a b c)) f`**:
   - `intChart_ew`: interior chart on `pmap f '' ball 0 1`;
   - `pairMidChart_ew`: interior chart across the midpoint of a pair of pasted sides `(p, q)`;
   - `freeMidChart_ew`: boundary chart at the midpoint of a free (hole) side `4a + 2b + 3i + 1`.
3. **Evaluation of `w1 A` on `ew a b c`**:
   - `side_const_w1`: across pasted sides `(p, q)`, any primitive `g` of `w1 A` jumps by `1` iff
     `sgn p = sgn q` (crosscap gluing) and by `0` iff `sgn p ≠ sgn q` (handle/tether gluing);
   - `lval_w1_ew`: `lval a b c g k = 0` for handle labels `k < 2a` and `= 1` for crosscap labels
     `2a ≤ k < 2a + b`;
   - `cohRel_w1_zero_iff`: `CohRel (w1 A) 0 ↔ b = 0`, and `cohRel_w1_zero_iff_of_homeo`;
   - `orient_cuffSign_const`: when `b = 0` and `w1 A = δ h`, `cuffSign A φ_i x - h x` is the
     same constant across all cuffs `i < c`.
4. **Pullback along a cutting**: for `IsCutting ψ F`, `cutOrientDiff AY AS ψ : Y → ZMod 2` gives
   an explicit coboundary `w1 AS (ψ y₁) (ψ y₂) - w1 AY y₁ y₂ = h y₂ - h y₁` near the diagonal
   (`cohRel_w1_cut`) compatible with `cuffSign` on `bd Y \ ψ ⁻¹' F` (`cutOrientDiff_cuff`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Function

universe u v

/-- Every point lies in its atlas chart's open domain. -/
theorem SurfAtlas.mem_chart {S : Type u} [TopologicalSpace S] (A : SurfAtlas S) (x : S) :
    x ∈ (A.chart (A.idx x)).U :=
  A.hV_sub (A.idx x) (subset_closure (A.hidx x))

/-- An open rectangle `Ioo a b ×ℂ Ioo c d` in `ℂ` is preconnected. -/
private theorem isPreconnected_reProdIm_Ioo (a b c d : ℝ) :
    IsPreconnected (Ioo a b ×ℂ Ioo c d) := by
  have heq : Ioo a b ×ℂ Ioo c d = Complex.equivRealProdCLM.symm '' (Ioo a b ×ˢ Ioo c d) := by
    ext z; simp only [Complex.mem_reProdIm, mem_image, mem_prod]
    constructor
    · intro hz; exact ⟨(z.re, z.im), hz, Complex.ext rfl rfl⟩
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩; exact hxy
  rw [heq]
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _
    Complex.equivRealProdCLM.symm.continuous.continuousOn

/-! ### Local orientation of exponential maps -/

section ExpOrient

/-- `Complex.exp` is locally orientation-preserving everywhere. -/
theorem isPosLocal_exp (z₀ : ℂ) : IsPosLocal Complex.exp z₀ := by
  have hpi := Real.pi_pos
  have hc : ContinuousOn Complex.exp (closedBall z₀ (1 / 4)) := Complex.continuous_exp.continuousOn
  have hi : InjOn Complex.exp (closedBall z₀ (1 / 4)) := by
    intro a ha b hb he
    rw [Complex.exp_eq_exp_iff_exists_int] at he
    obtain ⟨k, hk⟩ := he
    have hd : ‖a - b‖ ≤ 1 / 2 := by
      have h1 : ‖a - z₀‖ ≤ 1 / 4 := by simpa [mem_closedBall, dist_eq_norm] using ha
      have h2 : ‖b - z₀‖ ≤ 1 / 4 := by simpa [mem_closedBall, dist_eq_norm] using hb
      calc ‖a - b‖ = ‖(a - z₀) - (b - z₀)‖ := by ring_nf
        _ ≤ ‖a - z₀‖ + ‖b - z₀‖ := norm_sub_le _ _
        _ ≤ 1 / 2 := by linarith
    have hk_eq : a - b = (k : ℂ) * (2 * Real.pi * Complex.I) := by linear_combination hk
    have hnorm : ‖a - b‖ = |(k : ℝ)| * (2 * Real.pi) := by
      rw [hk_eq, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hpi]
    have hk0 : k = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have : (1 : ℤ) ≤ |k| := Int.one_le_abs hne
        exact_mod_cast this
      have h2 : 2 * Real.pi ≤ ‖a - b‖ := by rw [hnorm]; nlinarith
      have := Real.pi_gt_three
      linarith
    rw [hk0] at hk_eq; simp at hk_eq; exact sub_eq_zero.mp hk_eq
  rw [isPosLocal_iff_wind_pos (r := 1 / 4) (by norm_num) hc hi]
  let r : ℝ := 1 / 4
  have hr_eq : r = 1 / 4 := rfl
  have hr : 0 < r := by norm_num [hr_eq]
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  let F : ℝ → Circle → ℂ := fun u w =>
    Complex.exp z₀ + Complex.exp z₀ *
      (((1 - cl u : ℝ) : ℂ) * (Complex.exp ((r : ℂ) * (w : ℂ)) - 1) +
        ((cl u : ℝ) : ℂ) * ((r : ℂ) * (w : ℂ)))
  have hFc : Continuous fun q : ℝ × Circle => F q.1 q.2 := by unfold F cl; fun_prop
  have hne : ∀ u w, F u w ≠ Complex.exp z₀ := by
    intro u w h
    have h1 : Complex.exp z₀ *
        (((1 - cl u : ℝ) : ℂ) * (Complex.exp ((r : ℂ) * (w : ℂ)) - 1) +
          ((cl u : ℝ) : ℂ) * ((r : ℂ) * (w : ℂ))) = 0 := by linear_combination h
    have h2 : ((1 - cl u : ℝ) : ℂ) * (Complex.exp ((r : ℂ) * (w : ℂ)) - 1) +
        ((cl u : ℝ) : ℂ) * ((r : ℂ) * (w : ℂ)) = 0 :=
      (mul_eq_zero.mp h1).resolve_left (Complex.exp_ne_zero z₀)
    set ζ : ℂ := (r : ℂ) * (w : ℂ)
    have hζ : ‖ζ‖ = r := by
      simp [ζ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe]
    have hrem : ‖Complex.exp ζ - 1 - ζ‖ ≤ r ^ 2 := by
      have := Complex.norm_exp_sub_one_sub_id_le (x := ζ) (by rw [hζ, hr_eq]; norm_num)
      rwa [hζ] at this
    have hrew : ((1 - cl u : ℝ) : ℂ) * (Complex.exp ζ - 1) + ((cl u : ℝ) : ℂ) * ζ =
        ζ + ((1 - cl u : ℝ) : ℂ) * (Complex.exp ζ - 1 - ζ) := by push_cast; ring
    have h2' : ζ + ((1 - cl u : ℝ) : ℂ) * (Complex.exp ζ - 1 - ζ) = 0 := by
      rw [← hrew]; exact h2
    have hcl0 : 0 ≤ 1 - cl u := by
      have : cl u ≤ 1 := max_le zero_le_one (min_le_right _ _)
      linarith
    have hcl1 : 1 - cl u ≤ 1 := by
      have : 0 ≤ cl u := le_max_left _ _
      linarith
    have hnorm_eq : ‖ζ‖ = ‖((1 - cl u : ℝ) : ℂ) * (Complex.exp ζ - 1 - ζ)‖ := by
      have hneg : ζ = -(((1 - cl u : ℝ) : ℂ) * (Complex.exp ζ - 1 - ζ)) := eq_neg_of_add_eq_zero_left h2'
      exact (congrArg norm hneg).trans (norm_neg _)
    have hle : ‖((1 - cl u : ℝ) : ℂ) * (Complex.exp ζ - 1 - ζ)‖ ≤ r ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcl0]
      nlinarith [norm_nonneg (Complex.exp ζ - 1 - ζ)]
    rw [hζ] at hnorm_eq
    rw [← hnorm_eq, hr_eq] at hle
    norm_num at hle
  have hhom := wind_eq_of_family hFc continuous_const hne 0 1
  have h0 : cl 0 = 0 := by simp [cl]
  have h1 : cl 1 = 1 := by simp [cl]
  have hF0 : F 0 = fun w : Circle => Complex.exp (z₀ + (r : ℂ) * (w : ℂ)) := by
    funext w; simp only [F, h0, sub_zero, Complex.ofReal_one, one_mul, Complex.ofReal_zero,
      zero_mul, add_zero, mul_sub, mul_one, ← Complex.exp_add]; ring
  have hF1 : F 1 = fun w : Circle => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (w : ℂ) := by
    funext w; simp only [F, h1, sub_self, Complex.ofReal_zero, zero_mul, zero_add,
      Complex.ofReal_one, one_mul]; ring
  rw [hF0, hF1] at hhom
  have haff : IsPosLocal (fun z : ℂ => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (z - z₀)) z₀ := by
    have : (fun z : ℂ => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (z - z₀)) =
        fun z => (Complex.exp z₀ * (r : ℂ)) * z + (Complex.exp z₀ - Complex.exp z₀ * (r : ℂ) * z₀) := by
      funext z; ring
    rw [this]
    exact isPosLocal_affine (mul_ne_zero (Complex.exp_ne_zero z₀) (Complex.ofReal_ne_zero.mpr hr.ne')) _ z₀
  have hca : ContinuousOn (fun z : ℂ => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (z - z₀)) (closedBall z₀ 1) := by fun_prop
  have hia : InjOn (fun z : ℂ => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (z - z₀)) (closedBall z₀ 1) := fun a _ b _ he => by
    have hmul : (Complex.exp z₀ * (r : ℂ)) * (a - z₀) = (Complex.exp z₀ * (r : ℂ)) * (b - z₀) := by
      linear_combination he
    have hsub := mul_left_cancel₀ (mul_ne_zero (Complex.exp_ne_zero z₀) (Complex.ofReal_ne_zero.mpr hr.ne')) hmul
    linear_combination hsub
  have hw_pos := (isPosLocal_iff_wind_pos one_pos hca hia).mp haff
  have hw_simp : wind (fun w : Circle => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (w : ℂ)) (Complex.exp z₀) =
      wind (fun w : Circle => Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (z₀ + ((1 : ℝ) : ℂ) * (w : ℂ) - z₀))
        (Complex.exp z₀ + (Complex.exp z₀ * (r : ℂ)) * (z₀ - z₀)) := by
    congr 1
    · funext w; simp
    · simp
  change 0 < wind (fun w : Circle => Complex.exp (z₀ + (r : ℂ) * (w : ℂ))) (Complex.exp z₀)
  rw [hhom, hw_simp]
  exact hw_pos

/-- Helper: `Complex.exp` is injective on any ball of radius `1 / 2`. -/
private theorem injOn_exp_ball (w₀ : ℂ) : InjOn Complex.exp (ball w₀ (1 / 2)) := by
  intro x hx y hy he
  rw [Complex.exp_eq_exp_iff_exists_int] at he
  obtain ⟨k, hk⟩ := he
  have hd : ‖x - y‖ < 1 := by
    have h1' : ‖x - w₀‖ < 1 / 2 := by simpa [mem_ball, dist_eq_norm] using hx
    have h2' : ‖y - w₀‖ < 1 / 2 := by simpa [mem_ball, dist_eq_norm] using hy
    calc ‖x - y‖ = ‖(x - w₀) - (y - w₀)‖ := by ring_nf
      _ ≤ ‖x - w₀‖ + ‖y - w₀‖ := norm_sub_le _ _
      _ < 1 := by linarith
  have hk_eq : x - y = (k : ℂ) * (2 * Real.pi * Complex.I) := by linear_combination hk
  have hnorm : ‖x - y‖ = |(k : ℝ)| * (2 * Real.pi) := by
    rw [hk_eq, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hk0 : k = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast (Int.one_le_abs hne)
    have := Real.pi_gt_three
    nlinarith
  rw [hk0] at hk_eq; simp at hk_eq; exact sub_eq_zero.mp hk_eq

/-- `z ↦ c * Complex.exp (a * z) + d` (`c ≠ 0, a ≠ 0`) is locally orientation-preserving everywhere. -/
theorem isPosLocal_exp_affine_add {c a : ℂ} (hc : c ≠ 0) (ha : a ≠ 0) (d z₀ : ℂ) :
    IsPosLocal (fun z => c * Complex.exp (a * z) + d) z₀ := by
  have h1' : IsPosLocal (fun z => a * z) z₀ := by simpa using isPosLocal_affine ha 0 z₀
  have h2 : IsPosLocal Complex.exp (a * z₀) := isPosLocal_exp (a * z₀)
  have h3 : IsPosLocal (fun w => c * w + d) (Complex.exp (a * z₀)) := isPosLocal_affine hc d _
  have ha_inj : Injective (fun z : ℂ => a * z) := fun x y h => mul_left_cancel₀ ha h
  have hc_inj : Injective (fun w : ℂ => c * w + d) := fun x y h => mul_left_cancel₀ hc (by linear_combination h)
  let U : Set ℂ := (fun z : ℂ => a * z) ⁻¹' ball (a * z₀) (1 / 2)
  have hU : IsOpen U := isOpen_ball.preimage (continuous_const.mul continuous_id)
  have hzU : z₀ ∈ U := mem_ball_self (by norm_num)
  have h12 : IsPosLocal (Complex.exp ∘ fun z => a * z) z₀ :=
    (isPosLocal_comp hU (by fun_prop) ha_inj.injOn (image_preimage_subset _ _)
      Complex.continuous_exp.continuousOn (injOn_exp_ball (a * z₀)) hzU).mpr ⟨fun _ => h1', fun _ => h2⟩
  have h12_inj : InjOn (Complex.exp ∘ fun z => a * z) U := fun x hx y hy he =>
    ha_inj (injOn_exp_ball (a * z₀) hx hy he)
  have h123 : IsPosLocal ((fun w => c * w + d) ∘ (Complex.exp ∘ fun z => a * z)) z₀ :=
    (isPosLocal_comp hU (by fun_prop) h12_inj (subset_univ _)
      (by fun_prop) hc_inj.injOn hzU).mpr ⟨fun _ => h12, fun _ => h3⟩
  simpa [Function.comp_def] using h123

/-- `z ↦ c * Complex.exp (a * conj z) + d` (`c ≠ 0, a ≠ 0`) is locally orientation-reversing everywhere. -/
theorem not_isPosLocal_exp_affine_conj_add {c a : ℂ} (hc : c ≠ 0) (ha : a ≠ 0) (d z₀ : ℂ) :
    ¬ IsPosLocal (fun z => c * Complex.exp (a * starRingEnd ℂ z) + d) z₀ := by
  have hconj : ¬ IsPosLocal (starRingEnd ℂ) z₀ := not_isPosLocal_conj z₀
  have hexp : IsPosLocal (fun w => c * Complex.exp (a * w) + d) (starRingEnd ℂ z₀) :=
    isPosLocal_exp_affine_add hc ha d (starRingEnd ℂ z₀)
  let V : Set ℂ := (fun w : ℂ => a * w) ⁻¹' ball (a * starRingEnd ℂ z₀) (1 / 2)
  have hV : IsOpen V := isOpen_ball.preimage (continuous_const.mul continuous_id)
  have hinjV : InjOn (fun w => c * Complex.exp (a * w) + d) V := fun x hx y hy he =>
    mul_left_cancel₀ ha (injOn_exp_ball (a * starRingEnd ℂ z₀) hx hy
      (mul_left_cancel₀ hc (by linear_combination he)))
  have hcomp := isPosLocal_comp (hV.preimage Complex.continuous_conj)
    Complex.continuous_conj.continuousOn Complex.conjCLE.injective.injOn
    (image_preimage_subset _ _) (by fun_prop) hinjV
    (show starRingEnd ℂ z₀ ∈ V from mem_ball_self (by norm_num))
  intro h
  exact hconj ((hcomp.mp h).mp hexp)

end ExpOrient

/-! ### Explicit charts on a surface presented by `ew a b c` -/

section EWCharts

variable {a b c : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] {f : ℕ × ℂ → Y}

/-- The polygon map `pmap f` restricted to `closedBall 0 1` is a quotient map onto `Y`. -/
theorem pmap_isQuotientMap (hf : Presents (sW (ew a b c)) f) :
    IsQuotientMap (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) := by
  have : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : Continuous (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) :=
    continuousOn_iff_continuous_domRestrict.mp (pmap_cont hf)
  have hs : Surjective (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) := fun y => by
    have : y ∈ pmap f '' closedBall (0 : ℂ) 1 := by rw [pmap_image hf]; exact mem_univ y
    obtain ⟨z, hz, rfl⟩ := this
    exact ⟨⟨z, hz⟩, rfl⟩
  exact hc.isClosedMap.isQuotientMap hc hs

/-- A set `U ⊆ Y` is open iff `pmap f ⁻¹' U ∩ closedBall 0 1` is open in `closedBall 0 1`
(equivalently, equals `V ∩ closedBall 0 1` for some open `V ⊆ ℂ`). -/
theorem isOpen_of_pmap_preimage (hf : Presents (sW (ew a b c)) f) {U : Set Y} {V : Set ℂ}
    (hV : IsOpen V) (heq : pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 = V ∩ closedBall (0 : ℂ) 1) :
    IsOpen U := by
  rw [← (pmap_isQuotientMap hf).isOpen_preimage]
  have hsub : (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) ⁻¹' U =
      Subtype.val ⁻¹' V := by
    ext ⟨z, hz⟩
    simp only [mem_preimage]
    have h1 : z ∈ pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 ↔ z ∈ V ∩ closedBall (0 : ℂ) 1 := by rw [heq]
    simpa [hz] using h1
  rw [hsub]
  exact hV.preimage continuous_subtype_val

/-- Points in `ball 0 1` have `pmap f`-fibers of size 1 inside `closedBall 0 1`. -/
theorem pmap_eq_of_ball {Y : Type u} [TopologicalSpace Y] {f : ℕ × ℂ → Y}
    (hf : Presents (sW (ew a b c)) f) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1) (he : pmap f z = pmap f w) :
    z = w := by
  have hmz : ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) := ⟨(ew_mem_dsk a b c).1, by simpa using ball_subset_closedBall hz⟩
  have hmw : ((0 : ℕ), w) ∈ Dsk (sW (ew a b c)) := ⟨(ew_mem_dsk a b c).1, by simpa using hw⟩
  have hrel := (hf.2.2 _ hmz _ hmw).mp he
  have hlt : ‖((0 : ℕ), z).2‖ < 1 := by simpa [mem_ball] using hz
  exact (Prod.mk.inj (PRel.eq_of_lt hrel hlt)).2.symm

/-- Every point of `pmap f '' ball 0 1` lies in the interior `Y \ bd Y`. -/
theorem pmap_ball_not_mem_bd (hf : Presents (sW (ew a b c)) f) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    pmap f z ∉ bd Y := by
  have hbd := (surface_of_presents (finW_sW _) (isPaired_ew a b c) hf).2
  rw [hbd]
  rintro ⟨x, ⟨i, p, u, hp, _, hu, rfl⟩, hfx⟩
  have hi : i = 0 := by
    by_contra hne; simp [sW, hne, nW] at hp
  subst hi
  have hxD : spt (sW (ew a b c)) 0 p u ∈ Dsk (sW (ew a b c)) := by
    rw [spt_ew]; exact ⟨(ew_mem_dsk a b c).1, by simp [norm_per]⟩
  have hzD : ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) :=
    ⟨(ew_mem_dsk a b c).1, by simpa using ball_subset_closedBall hz⟩
  have hrel := (hf.2.2 _ hzD _ hxD).mp hfx.symm
  have heq := PRel.eq_of_lt hrel (by simpa [mem_ball] using hz)
  have h1 : ‖(spt (sW (ew a b c)) 0 p u).2‖ = 1 := by rw [spt_ew]; exact norm_per _ _
  have h2 : ‖z‖ < 1 := by simpa [mem_ball] using hz
  rw [heq] at h1; linarith

/-- Explicit interior `SurfChart` on `pmap f '' ball 0 1` with `O = ball 2 1` and `k w = pmap f (w - 2)`. -/
noncomputable def intChart_ew (hf : Presents (sW (ew a b c)) f) : SurfChart Y := by
  classical
  let U : Set Y := pmap f '' ball (0 : ℂ) 1
  have hU_pre : pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 = ball (0 : ℂ) 1 ∩ closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_inter_iff, mem_preimage, U, mem_image]
    constructor
    · rintro ⟨⟨w, hw, he⟩, hz⟩
      exact ⟨(pmap_eq_of_ball hf hw hz he) ▸ hw, hz⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨⟨z, hz, rfl⟩, hz'⟩
  have hU : IsOpen U := isOpen_of_pmap_preimage hf isOpen_ball hU_pre
  let O : Set ℂ := ball (2 : ℂ) 1
  have hO : IsOpen O := isOpen_ball
  have hO_sub : O ⊆ halfPlane := fun w hw => by
    have h1 : ‖w - 2‖ < 1 := by simpa [O, mem_ball, dist_eq_norm] using hw
    have h2 : |(w - 2).re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm _) h1
    rw [Complex.sub_re, abs_lt] at h2
    show 0 ≤ w.re; norm_num at h2; linarith
  have hO_inter : O ∩ halfPlane = O := inter_eq_left.mpr hO_sub
  let k : ℂ → Y := fun w => pmap f (w - 2)
  have hmem_ball : ∀ w ∈ O, w - 2 ∈ ball (0 : ℂ) 1 := fun w hw => by
    simpa [O, mem_ball, dist_eq_norm] using hw
  have hk : ContinuousOn k (O ∩ halfPlane) := by
    rw [hO_inter]
    exact (pmap_cont hf).comp (continuous_id.sub continuous_const).continuousOn
      (fun w hw => ball_subset_closedBall (hmem_ball w hw))
  have hk_maps : ∀ w ∈ O ∩ halfPlane, k w ∈ U := fun w hw =>
    ⟨w - 2, hmem_ball w hw.1, rfl⟩
  let j : Y → ℂ := fun y => if hy : y ∈ U then hy.choose + 2 else 0
  have hj_eq : ∀ z ∈ ball (0 : ℂ) 1, j (pmap f z) = z + 2 := fun z hz => by
    have hy : pmap f z ∈ U := ⟨z, hz, rfl⟩
    simp only [j, dite_eq_left hy]
    have hch := hy.choose_spec
    rw [pmap_eq_of_ball hf hch.1 (ball_subset_closedBall hz) hch.2]
  have hjm : ∀ y ∈ U, j y ∈ O ∩ halfPlane := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hj_eq z hz, hO_inter]
    simpa [O, mem_ball, dist_eq_norm] using hz
  have hjl : ∀ y ∈ U, k (j y) = y := by
    rintro _ ⟨z, hz, rfl⟩
    simp [k, hj_eq z hz]
  have hjr : ∀ w ∈ O ∩ halfPlane, j (k w) = w := fun w hw => by
    simp [k, hj_eq (w - 2) (hmem_ball w hw.1)]
  have hj : ContinuousOn j U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hq := (pmap_isQuotientMap hf).restrictPreimage_isOpen hU
    refine hq.continuous_iff.mpr ?_
    have hfun : (U.domRestrict j) ∘ (U.restrictPreimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1)) =
        fun x => x.1.1 + 2 := by
      funext ⟨⟨z, hz⟩, hzu⟩
      have hzb : z ∈ ball (0 : ℂ) 1 := by
        have : z ∈ pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 := ⟨hzu, hz⟩
        rw [hU_pre] at this; exact this.1
      exact hj_eq z hzb
    rw [hfun]
    fun_prop
  exact ⟨U, O, j, k, hU, hO, hj, hk, hjm, hk_maps, hjl, hjr⟩

theorem intChart_ew_U (hf : Presents (sW (ew a b c)) f) :
    (intChart_ew hf).U = pmap f '' ball (0 : ℂ) 1 := rfl

theorem intChart_ew_k (hf : Presents (sW (ew a b c)) f) (w : ℂ) :
    (intChart_ew hf).k w = pmap f (w - 2) := rfl

theorem intChart_ew_j (hf : Presents (sW (ew a b c)) f) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (intChart_ew hf).j (pmap f z) = z + 2 := by
  have hy : pmap f z ∈ pmap f '' ball (0 : ℂ) 1 := ⟨z, hz, rfl⟩
  have h1 : (intChart_ew hf).k (z + 2) = pmap f z := by simp [intChart_ew_k]
  have h2 : z + 2 ∈ (intChart_ew hf).O ∩ halfPlane := by
    refine ⟨by simpa [intChart_ew, mem_ball, dist_eq_norm] using hz, ?_⟩
    have hlt : ‖z‖ < 1 := by simpa [mem_ball] using hz
    have hre := lt_of_le_of_lt (Complex.abs_re_le_norm z) hlt
    rw [abs_lt] at hre
    show 0 ≤ (z + 2).re; simp; linarith
  rw [← h1, (intChart_ew hf).hr h2]

/-- Helper: `per n (p + 1/2 + y) = per n (p + 1/2) * exp (i * (2π/n) * y)`. -/
theorem per_shift_exp (n : ℕ) (x y : ℝ) :
    per n (x + y) = per n x * Complex.exp (((2 * Real.pi / n * y : ℝ) : ℂ) * Complex.I) := by
  simp only [per, cis', ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Helper: polar wedge `W_p` in `closedBall 0 1` around `per n (p + 1/2)` with radial log-depth `< δ`
and angular half-width `< δ` (for `δ = 1/8` and `n ≥ 2`). -/
private noncomputable def polarWedge (n p : ℕ) (δ : ℝ) : Set ℂ :=
  {z : ℂ | Real.exp (-(2 * Real.pi / n * δ)) < ‖z‖ ∧
    0 < (z / per n (p + 1 / 2)).re ∧
    |(Complex.log (z / per n (p + 1 / 2))).im| < 2 * Real.pi / n * δ}

private theorem isOpen_polarWedge (n p : ℕ) (δ : ℝ) : IsOpen (polarWedge n p δ) := by
  have hne : per n (p + 1 / 2) ≠ 0 := by
    intro h; have := norm_per n (p + 1 / 2); rw [h, norm_zero] at this; norm_num at this
  have h1 : IsOpen {z : ℂ | Real.exp (-(2 * Real.pi / n * δ)) < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {z : ℂ | 0 < (z / per n (p + 1 / 2)).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.div_const _))
  have h3 : IsOpen ({z : ℂ | 0 < (z / per n (p + 1 / 2)).re} ∩
      {z : ℂ | |(Complex.log (z / per n (p + 1 / 2))).im| < 2 * Real.pi / n * δ}) := by
    refine ContinuousOn.isOpen_inter_preimage
      (f := fun z : ℂ => |(Complex.log (z / per n (p + 1 / 2))).im|) ?_ h2
      (isOpen_lt continuous_id continuous_const)
    intro z hz
    have hslit : z / per n (p + 1 / 2) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (.inl hz)
    have h1' : ContinuousAt (fun w : ℂ => Complex.log (w / per n (p + 1 / 2))) z :=
      ContinuousAt.comp (f := fun w : ℂ => w / per n (p + 1 / 2)) (continuousAt_clog hslit)
        (continuousAt_id.div_const _)
    exact (Complex.continuous_im.continuousAt.comp h1').abs.continuousWithinAt
  have heq : polarWedge n p δ = {z : ℂ | Real.exp (-(2 * Real.pi / n * δ)) < ‖z‖} ∩
      ({z : ℂ | 0 < (z / per n (p + 1 / 2)).re} ∩
        {z : ℂ | |(Complex.log (z / per n (p + 1 / 2))).im| < 2 * Real.pi / n * δ}) := by
    ext z; simp [polarWedge]
  rw [heq]; exact h1.inter h3

/-- Characterization of `polarWedge n p δ ∩ closedBall 0 1` via the exponential parameterization
`ζ ↦ per n (p + 1/2) * exp ((2π/n) * ζ)` for `ζ ∈ Ioc (-δ) 0 ×ℂ Ioo (-δ) δ`. -/
private theorem mem_polarWedge_iff {n p : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    z ∈ polarWedge n p δ ↔
      ∃ ζ : ℂ, ζ.re ∈ Ioc (-δ) 0 ∧ ζ.im ∈ Ioo (-δ) δ ∧
        z = per n (p + 1 / 2) * Complex.exp ((2 * Real.pi / n : ℝ) * ζ) := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hα : 0 < 2 * Real.pi / n := by positivity
  have hαδ_lt : 2 * Real.pi / n * δ < Real.pi / 2 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 2 * Real.pi / n ≤ Real.pi := by rw [div_le_iff₀ hn0]; nlinarith
    nlinarith
  have hne : per n (p + 1 / 2) ≠ 0 := by
    intro h; have := norm_per n (p + 1 / 2); rw [h, norm_zero] at this; norm_num at this
  constructor
  · rintro ⟨hnorm, hre, him⟩
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; linarith [Real.exp_pos (-(2 * Real.pi / n * δ))]
    set w := z / per n (p + 1 / 2)
    have hw0 : w ≠ 0 := div_ne_zero hz0 hne
    have hwnorm : ‖w‖ = ‖z‖ := by simp [w, norm_per]
    set L := Complex.log w
    have hLre : L.re = Real.log ‖z‖ := by simp [L, Complex.log_re, hwnorm]
    have hzeq : z = per n (p + 1 / 2) * Complex.exp L := by
      rw [Complex.exp_log hw0]; exact (mul_div_cancel₀ z hne).symm
    set ζ : ℂ := ((n / (2 * Real.pi) : ℝ) : ℂ) * L
    have hζre : ζ.re = n / (2 * Real.pi) * L.re := by
      simp only [ζ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hζim : ζ.im = n / (2 * Real.pi) * L.im := by
      simp only [ζ, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have hαζ : (2 * Real.pi / n : ℝ) * ζ = L := by
      simp only [ζ, ← mul_assoc]
      have : ((2 * Real.pi / n : ℝ) : ℂ) * ((n / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul]; field_simp [hn0.ne', hpi.ne']; simp
      rw [this, one_mul]
    have hnorm_le : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
    have hLre_hi : L.re ≤ 0 := by rw [hLre]; exact Real.log_nonpos (norm_nonneg z) hnorm_le
    have hLre_lo : -(2 * Real.pi / n * δ) < L.re := by
      rw [hLre, ← Real.log_exp (-(2 * Real.pi / n * δ))]
      exact Real.log_lt_log (Real.exp_pos _) hnorm
    refine ⟨ζ, ⟨?_, ?_⟩, ?_, by rw [hαζ]; exact hzeq⟩
    · rw [hζre]
      have h1 : n / (2 * Real.pi) * (-(2 * Real.pi / n * δ)) = -δ := by field_simp [hn0.ne', hpi.ne']
      rw [← h1]
      exact mul_lt_mul_of_pos_left hLre_lo (by positivity)
    · rw [hζre]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hLre_hi
    · rw [mem_Ioo, ← abs_lt, hζim, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n / (2 * Real.pi))]
      have h1 : n / (2 * Real.pi) * (2 * Real.pi / n * δ) = δ := by field_simp [hn0.ne', hpi.ne']
      rw [← h1]
      exact mul_lt_mul_of_pos_left him (by positivity)
  · rintro ⟨ζ, hζre, hζim, rfl⟩
    have hnorm : ‖per n (p + 1 / 2) * Complex.exp ((2 * Real.pi / n : ℝ) * ζ)‖ =
        Real.exp (2 * Real.pi / n * ζ.re) := by
      rw [norm_mul, norm_per, one_mul, Complex.norm_exp]; simp
    have hdiv : per n (p + 1 / 2) * Complex.exp ((2 * Real.pi / n : ℝ) * ζ) / per n (p + 1 / 2) =
        Complex.exp ((2 * Real.pi / n : ℝ) * ζ) := mul_div_cancel_left₀ _ hne
    have him_eq : (((2 * Real.pi / n : ℝ) : ℂ) * ζ).im = 2 * Real.pi / n * ζ.im := by simp
    have him_abs : |2 * Real.pi / n * ζ.im| < 2 * Real.pi / n * δ := by
      rw [abs_mul, abs_of_pos hα]
      exact mul_lt_mul_of_pos_left (abs_lt.mpr hζim) hα
    have him_bound : -Real.pi < (((2 * Real.pi / n : ℝ) : ℂ) * ζ).im ∧
        (((2 * Real.pi / n : ℝ) : ℂ) * ζ).im ≤ Real.pi := by
      rw [him_eq]
      have := abs_lt.mp him_abs
      exact ⟨by linarith, by linarith⟩
    have hlog : Complex.log (Complex.exp ((2 * Real.pi / n : ℝ) * ζ)) = (2 * Real.pi / n : ℝ) * ζ :=
      Complex.log_exp him_bound.1 him_bound.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hnorm]
      apply Real.exp_lt_exp.mpr
      have := mul_lt_mul_of_pos_left hζre.1 hα
      linarith
    · rw [hdiv, Complex.exp_re]
      refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
      rw [him_eq]
      have := abs_lt.mp him_abs
      exact ⟨by linarith, by linarith⟩
    · rw [hdiv, hlog, him_eq]; exact him_abs

/-- Two wedges `polarWedge n p δ` and `polarWedge n q δ` for `p ≠ q < n` (`δ ≤ 1/4`) are disjoint
inside `closedBall 0 1`. -/
private theorem disjoint_polarWedge {n p q : ℕ} (hn : 2 ≤ n) (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    Disjoint (polarWedge n p δ ∩ closedBall (0 : ℂ) 1) (polarWedge n q δ ∩ closedBall (0 : ℂ) 1) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzp, hzb⟩ ⟨hzq, -⟩
  obtain ⟨ζ₁, -, h1im, rfl⟩ := (mem_polarWedge_iff hn hδ0 hδ hzb).mp hzp
  obtain ⟨ζ₂, -, h2im, heq⟩ := (mem_polarWedge_iff hn hδ0 hδ hzb).mp hzq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : per n (p + 1 / 2) * Complex.exp ((2 * Real.pi / n : ℝ) * ζ₁) =
      ((Real.exp (2 * Real.pi / n * ζ₁.re) : ℝ) : ℂ) * per n (p + (1 / 2 + ζ₁.im)) := by
    rw [show (p : ℝ) + (1 / 2 + ζ₁.im) = (p + 1 / 2) + ζ₁.im by ring, per_shift_exp n (p + 1 / 2) ζ₁.im]
    have hsplit : ((2 * Real.pi / n : ℝ) : ℂ) * ζ₁ =
        ((2 * Real.pi / n * ζ₁.re : ℝ) : ℂ) + ((2 * Real.pi / n * ζ₁.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
    ring
  have h2 : per n (q + 1 / 2) * Complex.exp ((2 * Real.pi / n : ℝ) * ζ₂) =
      ((Real.exp (2 * Real.pi / n * ζ₂.re) : ℝ) : ℂ) * per n (q + (1 / 2 + ζ₂.im)) := by
    rw [show (q : ℝ) + (1 / 2 + ζ₂.im) = (q + 1 / 2) + ζ₂.im by ring, per_shift_exp n (q + 1 / 2) ζ₂.im]
    have hsplit : ((2 * Real.pi / n : ℝ) : ℂ) * ζ₂ =
        ((2 * Real.pi / n * ζ₂.re : ℝ) : ℂ) + ((2 * Real.pi / n * ζ₂.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
    ring
  rw [h1, h2] at heq
  have hnorm_eq : Real.exp (2 * Real.pi / n * ζ₁.re) = Real.exp (2 * Real.pi / n * ζ₂.re) := by
    have := congrArg norm heq
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_per, mul_one] at this
    exact this
  rw [hnorm_eq] at heq
  have hper_eq : per n (p + (1 / 2 + ζ₁.im)) = per n (q + (1 / 2 + ζ₂.im)) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') heq
  have hsu := side_unique hp hq
    (show 1 / 2 + ζ₁.im ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [h1im.1], by linarith [h1im.2]⟩)
    (show 1 / 2 + ζ₂.im ∈ Icc (0 : ℝ) 1 from ⟨by linarith [h2im.1], by linarith [h2im.2]⟩)
    hper_eq
  exact hpq hsu.1

set_option maxHeartbeats 400000 in
/-- An explicit interior `SurfChart` across the midpoint of a pair of pasted sides `(p, q)` of `ew a b c`,
together with its transition signs against `intChart_ew` on the `p`-side and the `q`-side. -/
theorem exists_pairMidChart_ew (hf : Presents (sW (ew a b c)) f) {p q : ℕ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (hq : q < 4 * a + 2 * b + 3 * c + 2)
    (hpq : p ≠ q) (hlab : lab a b c p = lab a b c q) :
    let n := 4 * a + 2 * b + 3 * c + 2
    let α := 2 * Real.pi / n
    ∃ c₀ : SurfChart Y,
      pmap f (per n (p + 1 / 2)) ∈ c₀.U ∧
      (∀ t ∈ Ioo (0 : ℝ) (1 / 8),
        pmap f (per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ c₀.U ∧
        pmap f (per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ c₀.U ∧
        chartSign (intChart_ew hf) c₀ (pmap f (per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ)))) = 0 ∧
        chartSign (intChart_ew hf) c₀ (pmap f (per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ)))) =
          if sgn a b c p = sgn a b c q then 1 else 0) := by
  classical
  set n := 4 * a + 2 * b + 3 * c + 2 with hn_def
  set α := 2 * Real.pi / n with hα_def
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpi := Real.pi_pos
  have hα : 0 < α := by positivity
  obtain ⟨δ, hδ_eq⟩ : ∃ δ : ℝ, δ = 1 / 8 := ⟨1 / 8, rfl⟩
  have hδ0 : 0 < δ := by linarith
  have hδ4 : δ ≤ 1 / 4 := by linarith
  -- Open domain `O = Ioo (2 - δ) (2 + δ) ×ℂ Ioo (-δ) δ ⊆ {Re > 0}`:
  let O : Set ℂ := Ioo (2 - δ) (2 + δ) ×ℂ Ioo (-δ) δ
  have hO : IsOpen O := (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hO_sub : O ⊆ halfPlane := fun w hw => by
    have := (Complex.mem_reProdIm.mp hw).1.1; show 0 ≤ w.re; linarith [hδ_eq]
  have hO_inter : O ∩ halfPlane = O := inter_eq_left.mpr hO_sub
  -- Parameterization on the `p`-half (`w.re ≤ 2`) and `q`-half (`w.re ≥ 2`):
  let ζp : ℂ → ℂ := fun w => w - 2
  let ζq : ℂ → ℂ := fun w => if sgn a b c p = sgn a b c q then -starRingEnd ℂ (w - 2) else -(w - 2)
  have hζq_re : ∀ w : ℂ, (ζq w).re = 2 - w.re := fun w => by
    by_cases hs : sgn a b c p = sgn a b c q <;> simp [ζq, hs]
  have hζq_im : ∀ w : ℂ, (ζq w).im = if sgn a b c p = sgn a b c q then w.im else -w.im := fun w => by
    by_cases hs : sgn a b c p = sgn a b c q <;> simp [ζq, hs]
  let kp : ℂ → ℂ := fun w => per n (p + 1 / 2) * Complex.exp ((α : ℂ) * ζp w)
  let kq : ℂ → ℂ := fun w => per n (q + 1 / 2) * Complex.exp ((α : ℂ) * ζq w)
  let k : ℂ → Y := fun w => if w.re ≤ 2 then pmap f (kp w) else pmap f (kq w)
  have hkp_norm : ∀ w : ℂ, ‖kp w‖ = Real.exp (α * (w.re - 2)) := fun w => by
    simp [kp, ζp, norm_per, Complex.norm_exp]
  have hkq_norm : ∀ w : ℂ, ‖kq w‖ = Real.exp (α * (2 - w.re)) := fun w => by
    simp only [kq, norm_mul, norm_per, one_mul, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hζq_re]
  have hkp_ball : ∀ w : ℂ, w.re ≤ 2 → kp w ∈ closedBall (0 : ℂ) 1 := fun w hw => by
    rw [mem_closedBall_zero_iff, hkp_norm]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hkq_ball : ∀ w : ℂ, 2 ≤ w.re → kq w ∈ closedBall (0 : ℂ) 1 := fun w hw => by
    rw [mem_closedBall_zero_iff, hkq_norm]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hkp_lt : ∀ w : ℂ, w.re < 2 → kp w ∈ ball (0 : ℂ) 1 := fun w hw => by
    rw [mem_ball_zero_iff, hkp_norm]; exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hkq_lt : ∀ w : ℂ, 2 < w.re → kq w ∈ ball (0 : ℂ) 1 := fun w hw => by
    rw [mem_ball_zero_iff, hkq_norm]; exact Real.exp_lt_one_iff.mpr (by nlinarith)
  -- Agreement on the seam `w.re = 2`:
  have hkq_per_eq : ∀ w : ℂ, w.re = 2 → kq w = per n (q + (1 / 2 + if sgn a b c p = sgn a b c q then w.im else -w.im)) := by
    intro w hre
    rw [show (q : ℝ) + (1 / 2 + if sgn a b c p = sgn a b c q then w.im else -w.im) =
      (q + 1 / 2) + (if sgn a b c p = sgn a b c q then w.im else -w.im) by ring,
      per_shift_exp n (q + 1 / 2) (if sgn a b c p = sgn a b c q then w.im else -w.im)]
    have hζ_eq : ζq w = ((if sgn a b c p = sgn a b c q then w.im else -w.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp [hζq_re, hre]) (by simp [hζq_im])
    simp only [kq, hζ_eq, hα_def]; congr 2; push_cast; ring
  have hseam : ∀ w ∈ O, w.re = 2 → pmap f (kp w) = pmap f (kq w) := by
    intro w hw hre
    have him : w.im ∈ Ioo (-δ) δ := (Complex.mem_reProdIm.mp hw).2
    have hζp_eq : ζp w = (w.im : ℂ) * Complex.I := Complex.ext (by simp [ζp, hre]) (by simp [ζp])
    have hkp_per : kp w = per n (p + (1 / 2 + w.im)) := by
      rw [show (p : ℝ) + (1 / 2 + w.im) = (p + 1 / 2) + w.im by ring, per_shift_exp n (p + 1 / 2) w.im]
      simp only [kp, hζp_eq, hα_def]; congr 2; push_cast; ring
    have hflp_eq : flp (sgn a b c p) (sgn a b c q) (1 / 2 + w.im) =
        1 / 2 + (if sgn a b c p = sgn a b c q then w.im else -w.im) := by
      unfold flp; by_cases hs : sgn a b c p = sgn a b c q <;> simp [hs]; ring
    rw [hkp_per, hkq_per_eq w hre, ← hflp_eq]
    exact (pair_F hf hp hq hpq hlab (show 1 / 2 + w.im ∈ Icc (0 : ℝ) 1 from ⟨by linarith [him.1, hδ_eq], by linarith [him.2, hδ_eq]⟩)).symm
  -- Continuity of `k` on `O`:
  have hkp_cont : Continuous kp := continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)))
  have hζq_cont : Continuous ζq := by
    by_cases hs : sgn a b c p = sgn a b c q
    · have : ζq = fun w => -starRingEnd ℂ (w - 2) := by funext w; simp [ζq, hs]
      rw [this]; exact (Complex.continuous_conj.comp (continuous_id.sub continuous_const)).neg
    · have : ζq = fun w => -(w - 2) := by funext w; simp [ζq, hs]
      rw [this]; exact (continuous_id.sub continuous_const).neg
  have hkq_cont : Continuous kq := continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul hζq_cont))
  have hk_cont : ContinuousOn k O := by
    have h1 : ContinuousOn (fun w => pmap f (kp w)) (O ∩ {w : ℂ | w.re ≤ 2}) :=
      (pmap_cont hf).comp hkp_cont.continuousOn (fun w hw => hkp_ball w hw.2)
    have h2 : ContinuousOn (fun w => pmap f (kq w)) (O ∩ {w : ℂ | 2 ≤ w.re}) :=
      (pmap_cont hf).comp hkq_cont.continuousOn (fun w hw => hkq_ball w hw.2)
    have hk_le : ∀ z : ℂ, z.re ≤ 2 → k z = pmap f (kp z) := fun z hz => ite_eq_left hz
    have hk_gt : ∀ z : ℂ, 2 < z.re → k z = pmap f (kq z) := fun z hz => ite_eq_right (not_le.mpr hz)
    intro w hw
    by_cases hre : w.re < 2
    · have hnhd : O ∩ {z : ℂ | z.re < 2} ∈ 𝓝[O] w :=
        inter_mem_nhdsWithin O ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hre)
      have heq : k =ᶠ[𝓝[O] w] fun z => pmap f (kp z) :=
        Filter.mem_of_superset hnhd fun z hz => hk_le z (le_of_lt hz.2)
      have hsub1 : O ∩ {z : ℂ | z.re < 2} ⊆ O ∩ {z : ℂ | z.re ≤ 2} :=
        fun z hz => ⟨hz.1, show z.re ≤ 2 from le_of_lt hz.2⟩
      have hc1 : ContinuousWithinAt (fun z => pmap f (kp z)) (O ∩ {z : ℂ | z.re < 2}) w :=
        (h1.mono hsub1) w ⟨hw, hre⟩
      exact (hc1.mono_of_mem_nhdsWithin hnhd).congr_of_eventuallyEq heq (hk_le w hre.le)
    · by_cases hre2 : 2 < w.re
      · have hnhd : O ∩ {z : ℂ | 2 < z.re} ∈ 𝓝[O] w :=
          inter_mem_nhdsWithin O ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre2)
        have heq : k =ᶠ[𝓝[O] w] fun z => pmap f (kq z) :=
          Filter.mem_of_superset hnhd fun z hz => hk_gt z hz.2
        have hsub2 : O ∩ {z : ℂ | 2 < z.re} ⊆ O ∩ {z : ℂ | 2 ≤ z.re} :=
          fun z hz => ⟨hz.1, show 2 ≤ z.re from le_of_lt hz.2⟩
        have hc2 : ContinuousWithinAt (fun z => pmap f (kq z)) (O ∩ {z : ℂ | 2 < z.re}) w :=
          (h2.mono hsub2) w ⟨hw, hre2⟩
        exact (hc2.mono_of_mem_nhdsWithin hnhd).congr_of_eventuallyEq heq (hk_gt w hre2)
      · have hweq : w.re = 2 := by linarith
        have hka : ContinuousWithinAt k (O ∩ {z : ℂ | z.re ≤ 2}) w :=
          (h1 w ⟨hw, hweq.le⟩).congr (fun z hz => hk_le z hz.2) (hk_le w hweq.le)
        have hkb : ContinuousWithinAt k (O ∩ {z : ℂ | 2 ≤ z.re}) w :=
          (h2 w ⟨hw, hweq.ge⟩).congr (fun z hz => by
            by_cases hz2 : z.re ≤ 2
            · rw [hk_le z hz2]; exact hseam z hz.1 (le_antisymm hz2 hz.2)
            · exact hk_gt z (lt_of_not_ge hz2)) (by rw [hk_le w hweq.le]; exact hseam w hw hweq)
        have hun : O ∩ {z : ℂ | z.re ≤ 2} ∪ O ∩ {z : ℂ | 2 ≤ z.re} = O := by
          ext z; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
          exact ⟨fun h => h.elim And.left And.left, fun h => (le_total z.re 2).imp (⟨h, ·⟩) (⟨h, ·⟩)⟩
        rw [← hun]
        exact hka.union hkb
  -- Open set `U = k '' O` via its preimage `W_p ∪ W_q` in `closedBall 0 1`:
  let Wp := polarWedge n p δ
  let Wq := polarWedge n q δ
  have hWp_open : IsOpen Wp := isOpen_polarWedge n p δ
  have hWq_open : IsOpen Wq := isOpen_polarWedge n q δ
  have hdisj : Disjoint (Wp ∩ closedBall (0 : ℂ) 1) (Wq ∩ closedBall (0 : ℂ) 1) :=
    disjoint_polarWedge hn2 hp hq hpq hδ0 hδ4
  let U : Set Y := k '' O
  have hWp_param : ∀ z ∈ Wp ∩ closedBall (0 : ℂ) 1,
      ∃ w ∈ O, w.re ≤ 2 ∧ kp w = z ∧ k w = pmap f z := by
    intro z ⟨hzp, hzb⟩
    obtain ⟨ζ, hζre, hζim, rfl⟩ := (mem_polarWedge_iff hn2 hδ0 hδ4 hzb).mp hzp
    have hre_le : (ζ + 2).re ≤ 2 := by simp; linarith [hζre.2]
    refine ⟨ζ + 2, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hζre.1], by simp; linarith [hζre.2]⟩,
      by simpa using hζim⟩, hre_le, by simp [kp, ζp, hα_def], ?_⟩
    simp only [k, hre_le, ↓reduceIte, kp, ζp, add_sub_cancel_right, hα_def]
  have hWq_param : ∀ z ∈ Wq ∩ closedBall (0 : ℂ) 1,
      ∃ w ∈ O, 2 ≤ w.re ∧ kq w = z ∧ k w = pmap f z := by
    intro z ⟨hzq, hzb⟩
    obtain ⟨ζ, hζre, hζim, rfl⟩ := (mem_polarWedge_iff hn2 hδ0 hδ4 hzb).mp hzq
    let w : ℂ := if sgn a b c p = sgn a b c q then 2 - starRingEnd ℂ ζ else 2 - ζ
    have hwre : w.re = 2 - ζ.re := by by_cases hs : sgn a b c p = sgn a b c q <;> simp [w, hs]
    have hwim : w.im = if sgn a b c p = sgn a b c q then ζ.im else -ζ.im := by
      by_cases hs : sgn a b c p = sgn a b c q <;> simp [w, hs]
    have hwO : w ∈ O := Complex.mem_reProdIm.mpr
      ⟨⟨by linarith [hζre.2], by linarith [hζre.1]⟩,
       by rw [hwim]; by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
         exact ⟨by linarith [hζim.1, hζim.2], by linarith [hζim.1, hζim.2]⟩⟩
    have hζq_eq : ζq w = ζ := by
      by_cases hs : sgn a b c p = sgn a b c q <;> simp [ζq, w, hs]
    have hkq_eq : kq w = per n (q + 1 / 2) * Complex.exp ((2 * Real.pi / n : ℝ) * ζ) := by
      simp [kq, hζq_eq, hα_def]
    refine ⟨w, hwO, by linarith [hζre.2], hkq_eq, ?_⟩
    by_cases h2 : w.re ≤ 2
    · have hweq : w.re = 2 := le_antisymm h2 (by linarith [hζre.2])
      simp only [k, h2, ↓reduceIte]
      rw [hseam w hwO hweq, hkq_eq]
    · simp only [k, h2, ↓reduceIte, hkq_eq]
  -- Preimage of `U` in `closedBall 0 1` is `(Wp ∪ Wq) ∩ closedBall 0 1`!
  have hU_pre : pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 = (Wp ∪ Wq) ∩ closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_union]
    constructor
    · rintro ⟨⟨w, hwO, hkw⟩, hzb⟩
      refine ⟨?_, hzb⟩
      have hwre := (Complex.mem_reProdIm.mp hwO).1
      have hwim := (Complex.mem_reProdIm.mp hwO).2
      by_cases hlt : w.re < 2
      · have hkw' : pmap f (kp w) = pmap f z := by simpa [k, hlt.le] using hkw
        have hzeq := pmap_eq_of_ball hf (hkp_lt w hlt) hzb hkw'
        left; rw [← hzeq]
        exact (mem_polarWedge_iff hn2 hδ0 hδ4 (ball_subset_closedBall (hkp_lt w hlt))).mpr
          ⟨ζp w, ⟨by simp [ζp]; linarith [hwre.1], by simp [ζp]; linarith⟩, by simpa [ζp] using hwim,
           by simp [kp, hα_def]⟩
      · by_cases hgt : 2 < w.re
        · have hkw' : pmap f (kq w) = pmap f z := by simpa [k, not_le.mpr hgt] using hkw
          have hzeq := pmap_eq_of_ball hf (hkq_lt w hgt) hzb hkw'
          right; rw [← hzeq]
          exact (mem_polarWedge_iff hn2 hδ0 hδ4 (ball_subset_closedBall (hkq_lt w hgt))).mpr
            ⟨ζq w,
             ⟨by rw [hζq_re]; linarith [hwre.2], by rw [hζq_re]; linarith⟩,
             by rw [hζq_im]; by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
               exact ⟨by linarith [hwim.1, hwim.2], by linarith [hwim.1, hwim.2]⟩,
             by simp [kq, hα_def]⟩
        · have hweq : w.re = 2 := by linarith
          have hkw' : pmap f (kp w) = pmap f z := by simpa [k, hweq.le] using hkw
          have hkp_per : kp w = per n (p + (1 / 2 + w.im)) := by
            rw [show (p : ℝ) + (1 / 2 + w.im) = (p + 1 / 2) + w.im by ring, per_shift_exp n (p + 1 / 2) w.im]
            have hζp_eq : ζp w = (w.im : ℂ) * Complex.I := Complex.ext (by simp [ζp, hweq]) (by simp [ζp])
            simp only [kp, hζp_eq, hα_def]; congr 2; push_cast; ring
          have hzD : ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) := ⟨(ew_mem_dsk a b c).1, by simpa using hzb⟩
          have hpD : ((0 : ℕ), kp w) ∈ Dsk (sW (ew a b c)) := ⟨(ew_mem_dsk a b c).1, by simpa using hkp_ball w hweq.le⟩
          have hrel := (hf.2.2 (0, kp w) hpD (0, z) hzD).mp hkw'
          have hgetp : (sW (ew a b c) 0)[p]? = some (lab a b c p, sgn a b c p) := by
            rw [sW_zero]; exact ew_get a b c hp
          have hgetq : (sW (ew a b c) 0)[q]? = some (lab a b c p, sgn a b c q) := by
            rw [sW_zero, hlab]; exact ew_get a b c hq
          have huIoo : 1 / 2 + w.im ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hwim.1, hδ_eq], by linarith [hwim.2, hδ_eq]⟩
          rw [hkp_per, ← spt_ew] at hrel
          rcases PRel.eq_or_stp (isPaired_ew a b c) hgetp huIoo hrel with h_eq | h_stp
          · left
            have hze : z = kp w := by
              rw [hkp_per]; have := (Prod.mk.inj h_eq).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
            rw [hze]
            exact (mem_polarWedge_iff hn2 hδ0 hδ4 (hkp_ball w hweq.le)).mpr
              ⟨ζp w, ⟨by simp [ζp, hweq]; linarith, by simp [ζp, hweq]⟩, by simpa [ζp] using hwim,
               by simp [kp, hα_def]⟩
          · right
            obtain ⟨j', q', e', hget', hne', hzeq⟩ := stp_of_side (isPaired_ew a b c) hgetp huIoo h_stp
            have hthird := (isPaired_ew a b c).third hgetp hgetq hget' (fun h => hpq (Prod.mk.inj h).2)
            rcases hthird with h3 | h3
            · exact absurd h3.symm hne'
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3.symm
              rw [hgetq] at hget'
              obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hget')
              have hz_eq : z = per n (q + flp (sgn a b c p) (sgn a b c q) (1 / 2 + w.im)) := by
                have := (Prod.mk.inj hzeq).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
              have hflp_eq : flp (sgn a b c p) (sgn a b c q) (1 / 2 + w.im) =
                  1 / 2 + (if sgn a b c p = sgn a b c q then w.im else -w.im) := by
                unfold flp; by_cases hs : sgn a b c p = sgn a b c q <;> simp [hs]; ring
              rw [hz_eq, hflp_eq, ← hkq_per_eq w hweq]
              exact (mem_polarWedge_iff hn2 hδ0 hδ4 (hkq_ball w hweq.ge)).mpr
                ⟨ζq w,
                 ⟨by rw [hζq_re, hweq]; linarith, by rw [hζq_re, hweq]; linarith⟩,
                 by rw [hζq_im]; by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
                   exact ⟨by linarith [hwim.1, hwim.2], by linarith [hwim.1, hwim.2]⟩,
                 by simp [kq, hα_def]⟩
    · rintro ⟨hzp | hzq, hzb⟩
      · obtain ⟨w, hwO, -, -, hkw⟩ := hWp_param z ⟨hzp, hzb⟩
        exact ⟨⟨w, hwO, hkw⟩, hzb⟩
      · obtain ⟨w, hwO, -, -, hkw⟩ := hWq_param z ⟨hzq, hzb⟩
        exact ⟨⟨w, hwO, hkw⟩, hzb⟩
  have hU : IsOpen U := isOpen_of_pmap_preimage hf (hWp_open.union hWq_open) hU_pre
  -- Inverse map `j : Y → ℂ` defined via `Complex.log` on `Wp` and `Wq`:
  let jp : ℂ → ℂ := fun z => 2 + ((n / (2 * Real.pi) : ℝ) : ℂ) * Complex.log (z / per n (p + 1 / 2))
  let jq : ℂ → ℂ := fun z =>
    let ζ := ((n / (2 * Real.pi) : ℝ) : ℂ) * Complex.log (z / per n (q + 1 / 2))
    if sgn a b c p = sgn a b c q then 2 - starRingEnd ℂ ζ else 2 - ζ
  have hjp_kp : ∀ w ∈ O, jp (kp w) = w := fun w hw => by
    have him := (Complex.mem_reProdIm.mp hw).2
    have hne : per n (p + 1 / 2) ≠ 0 := by
      intro h; have := norm_per n (p + 1 / 2); rw [h, norm_zero] at this; norm_num at this
    have hdiv : kp w / per n (p + 1 / 2) = Complex.exp ((α : ℂ) * ζp w) := mul_div_cancel_left₀ _ hne
    have him_eq : ((α : ℂ) * ζp w).im = α * w.im := by simp [ζp]
    have hαδ_lt : α * δ < Real.pi / 2 := by
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have h1 : α ≤ Real.pi := by rw [hα_def, div_le_iff₀ hn0]; nlinarith
      nlinarith [hδ_eq]
    have him_b : -Real.pi < ((α : ℂ) * ζp w).im ∧ ((α : ℂ) * ζp w).im ≤ Real.pi := by
      rw [him_eq]
      have h1 : -(α * δ) < α * w.im := by nlinarith [him.1, hα]
      have h2 : α * w.im < α * δ := by nlinarith [him.2, hα]
      exact ⟨by linarith, by linarith⟩
    simp only [jp, hdiv, Complex.log_exp him_b.1 him_b.2, ← mul_assoc]
    have h1 : ((n / (2 * Real.pi) : ℝ) : ℂ) * (α : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hα_def]; field_simp [hn0.ne', hpi.ne']; simp
    rw [h1, one_mul]; simp [ζp]
  have hjq_kq : ∀ w ∈ O, jq (kq w) = w := fun w hw => by
    have him := (Complex.mem_reProdIm.mp hw).2
    have hne : per n (q + 1 / 2) ≠ 0 := by
      intro h; have := norm_per n (q + 1 / 2); rw [h, norm_zero] at this; norm_num at this
    have hdiv : kq w / per n (q + 1 / 2) = Complex.exp ((α : ℂ) * ζq w) := mul_div_cancel_left₀ _ hne
    have hαδ_lt : α * δ < Real.pi / 2 := by
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have h1 : α ≤ Real.pi := by rw [hα_def, div_le_iff₀ hn0]; nlinarith
      nlinarith [hδ_eq]
    have him_eq : ((α : ℂ) * ζq w).im = α * (if sgn a b c p = sgn a b c q then w.im else -w.im) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hζq_im]
    have him_b : -Real.pi < ((α : ℂ) * ζq w).im ∧ ((α : ℂ) * ζq w).im ≤ Real.pi := by
      rw [him_eq]
      have h1 : -(α * δ) < α * w.im := by nlinarith [him.1, hα]
      have h2 : α * w.im < α * δ := by nlinarith [him.2, hα]
      by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
        exact ⟨by linarith, by linarith⟩
    have h1 : ((n / (2 * Real.pi) : ℝ) : ℂ) * (α : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hα_def]; field_simp [hn0.ne', hpi.ne']; simp
    dsimp only [jq]
    rw [hdiv, Complex.log_exp him_b.1 him_b.2, ← mul_assoc, h1, one_mul]
    by_cases hs : sgn a b c p = sgn a b c q <;> simp [ζq, hs]
  -- Check `jp` and `jq` agree on `pmap f`-fibers in `(Wp ∪ Wq) ∩ closedBall 0 1`!
  let jpre : ℂ → ℂ := fun z => if z ∈ Wp then jp z else jq z
  have hjpre_eq : ∀ w ∈ O, ∀ z ∈ closedBall (0 : ℂ) 1, pmap f z = k w → jpre z = w := by
    intro w hw z hzb hfz
    have hzmem : z ∈ (Wp ∪ Wq) ∩ closedBall (0 : ℂ) 1 := by
      rw [← hU_pre]; exact ⟨⟨w, hw, hfz.symm⟩, hzb⟩
    rcases hzmem.1 with hzp | hzq
    · simp only [jpre, hzp, ↓reduceIte]
      obtain ⟨w', hw'O, hw'le, hkp', hkw'⟩ := hWp_param z ⟨hzp, hzb⟩
      rw [← hkp', hjp_kp w' hw'O]
      by_cases hlt : w'.re < 2
      · have hkw_eq : pmap f (kp w') = k w := by simpa [k, hlt.le] using hkw'.trans hfz
        by_cases hwle : w.re ≤ 2
        · have hkw2 : pmap f (kp w') = pmap f (kp w) := by simpa [k, hwle] using hkw_eq
          have h1 := pmap_eq_of_ball hf (hkp_lt w' hlt) (hkp_ball w hwle) hkw2
          rw [← hjp_kp w' hw'O, ← hjp_kp w hw, h1]
        · have hkw2 : pmap f (kp w') = pmap f (kq w) := by simpa [k, hwle] using hkw_eq
          have h1 := pmap_eq_of_ball hf (hkp_lt w' hlt) (hkq_ball w (le_of_not_ge hwle)) hkw2
          exfalso
          have hzq' : kq w ∈ Wq ∩ closedBall (0 : ℂ) 1 :=
            ⟨(mem_polarWedge_iff hn2 hδ0 hδ4 (hkq_ball w (le_of_not_ge hwle))).mpr
              ⟨ζq w,
               ⟨by rw [hζq_re]; linarith [(Complex.mem_reProdIm.mp hw).1.2], by rw [hζq_re]; linarith⟩,
               by rw [hζq_im]; by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
                 exact ⟨by linarith [(Complex.mem_reProdIm.mp hw).2.1, (Complex.mem_reProdIm.mp hw).2.2],
                        by linarith [(Complex.mem_reProdIm.mp hw).2.1, (Complex.mem_reProdIm.mp hw).2.2]⟩,
               by simp [kq, hα_def]⟩,
             hkq_ball w (le_of_not_ge hwle)⟩
          exact Set.disjoint_left.mp hdisj ⟨hkp' ▸ hzp, hkp' ▸ hzb⟩ (h1 ▸ hzq')
      · have hw'eq : w'.re = 2 := le_antisymm hw'le (not_lt.mp hlt)
        have hweq : w.re = 2 := by
          by_contra hne2
          rcases lt_or_gt_of_ne hne2 with hlt2 | hgt2
          · have hkw2 : pmap f (kp w) = pmap f (kp w') := by
              have := (hkw'.trans hfz).symm; simpa [k, hlt2.le, hw'eq.le] using this
            have h1 := pmap_eq_of_ball hf (hkp_lt w hlt2) (hkp_ball w' hw'eq.le) hkw2
            have hn1 : ‖kp w‖ < 1 := by simpa [mem_ball] using hkp_lt w hlt2
            have hn2' : ‖kp w'‖ = 1 := by rw [hkp_norm, hw'eq]; simp
            rw [h1] at hn1; linarith
          · have hkw2 : pmap f (kq w) = pmap f (kp w') := by
              have := (hkw'.trans hfz).symm; simpa [k, not_le.mpr hgt2, hw'eq.le] using this
            have h1 := pmap_eq_of_ball hf (hkq_lt w hgt2) (hkp_ball w' hw'eq.le) hkw2
            have hn1 : ‖kq w‖ < 1 := by simpa [mem_ball] using hkq_lt w hgt2
            have hn2' : ‖kp w'‖ = 1 := by rw [hkp_norm, hw'eq]; simp
            rw [h1] at hn1; linarith
        have hkw2 : pmap f (kp w') = pmap f (kp w) := by
          have := hkw'.trans hfz; simpa [k, hw'eq.le, hweq.le] using this
        have hrel := (hf.2.2 (0, kp w') ⟨(ew_mem_dsk a b c).1, by simpa using hkp_ball w' hw'eq.le⟩
          (0, kp w) ⟨(ew_mem_dsk a b c).1, by simpa using hkp_ball w hweq.le⟩).mp hkw2
        have hkp1 : kp w' = per n (p + (1 / 2 + w'.im)) := by
          rw [show (p : ℝ) + (1 / 2 + w'.im) = (p + 1 / 2) + w'.im by ring, per_shift_exp n (p + 1 / 2) w'.im]
          have : ζp w' = (w'.im : ℂ) * Complex.I := Complex.ext (by simp [ζp, hw'eq]) (by simp [ζp])
          simp only [kp, this, hα_def]; congr 2; push_cast; ring
        have hkp2 : kp w = per n (p + (1 / 2 + w.im)) := by
          rw [show (p : ℝ) + (1 / 2 + w.im) = (p + 1 / 2) + w.im by ring, per_shift_exp n (p + 1 / 2) w.im]
          have : ζp w = (w.im : ℂ) * Complex.I := Complex.ext (by simp [ζp, hweq]) (by simp [ζp])
          simp only [kp, this, hα_def]; congr 2; push_cast; ring
        have hgetp : (sW (ew a b c) 0)[p]? = some (lab a b c p, sgn a b c p) := by
          rw [sW_zero]; exact ew_get a b c hp
        have hu1 : 1 / 2 + w'.im ∈ Ioo (0 : ℝ) 1 :=
          ⟨by linarith [(Complex.mem_reProdIm.mp hw'O).2.1, hδ_eq], by linarith [(Complex.mem_reProdIm.mp hw'O).2.2, hδ_eq]⟩
        rw [hkp1, hkp2, ← spt_ew] at hrel
        rcases PRel.eq_or_stp (isPaired_ew a b c) hgetp hu1 hrel with he | hstp
        · have hper_eq : per n (p + (1 / 2 + w.im)) = per n (p + (1 / 2 + w'.im)) := by
            have := (Prod.mk.inj he).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
          have hsu := side_unique hp hp hu1
            ⟨by linarith [(Complex.mem_reProdIm.mp hw).2.1, hδ_eq], by linarith [(Complex.mem_reProdIm.mp hw).2.2, hδ_eq]⟩
            hper_eq.symm
          exact Complex.ext (hw'eq.trans hweq.symm) (by linarith [hsu.2])
        · obtain ⟨j', q', e', hget', hne', hpeq⟩ := stp_of_side (isPaired_ew a b c) hgetp hu1 hstp
          have hgetq : (sW (ew a b c) 0)[q]? = some (lab a b c p, sgn a b c q) := by
            rw [sW_zero, hlab]; exact ew_get a b c hq
          rcases (isPaired_ew a b c).third hgetp hgetq hget' (fun h => hpq (Prod.mk.inj h).2) with h3 | h3
          · exact absurd h3.symm hne'
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3.symm
            have hper_eq : per n (p + (1 / 2 + w.im)) = per n (q + flp (sgn a b c p) e' (1 / 2 + w'.im)) := by
              have := (Prod.mk.inj hpeq).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
            have hsu := side_unique hp hq
              ⟨by linarith [(Complex.mem_reProdIm.mp hw).2.1, hδ_eq], by linarith [(Complex.mem_reProdIm.mp hw).2.2, hδ_eq]⟩
              (flp_mem (Ioo_subset_Icc_self hu1)) hper_eq
            exact absurd hsu.1 hpq
    · have hnotp : z ∉ Wp := fun hzp => Set.disjoint_left.mp hdisj ⟨hzp, hzb⟩ ⟨hzq, hzb⟩
      simp only [jpre, hnotp, ↓reduceIte]
      obtain ⟨w', hw'O, hw'ge, hkq', hkw'⟩ := hWq_param z ⟨hzq, hzb⟩
      rw [← hkq', hjq_kq w' hw'O]
      by_cases hgt : 2 < w'.re
      · have hkw_eq : pmap f (kq w') = k w := by simpa [k, not_le.mpr hgt] using hkw'.trans hfz
        by_cases hwle : w.re ≤ 2
        · have hkw2 : pmap f (kq w') = pmap f (kp w) := by simpa [k, hwle] using hkw_eq
          have h1 := pmap_eq_of_ball hf (hkq_lt w' hgt) (hkp_ball w hwle) hkw2
          exfalso
          have hzp' : kp w ∈ Wp ∩ closedBall (0 : ℂ) 1 :=
            ⟨(mem_polarWedge_iff hn2 hδ0 hδ4 (hkp_ball w hwle)).mpr
              ⟨ζp w, ⟨by simp [ζp]; linarith [(Complex.mem_reProdIm.mp hw).1.1], by simp [ζp]; linarith⟩,
               by simpa [ζp] using (Complex.mem_reProdIm.mp hw).2, by simp [kp, hα_def]⟩,
             hkp_ball w hwle⟩
          exact Set.disjoint_left.mp hdisj (h1 ▸ hzp') ⟨hkq' ▸ hzq, hkq' ▸ hzb⟩
        · have hkw2 : pmap f (kq w') = pmap f (kq w) := by simpa [k, hwle] using hkw_eq
          have h1 := pmap_eq_of_ball hf (hkq_lt w' hgt) (hkq_ball w (le_of_not_ge hwle)) hkw2
          rw [← hjq_kq w' hw'O, ← hjq_kq w hw, h1]
      · have hw'eq : w'.re = 2 := le_antisymm (not_lt.mp hgt) hw'ge
        have hweq : w.re = 2 := by
          by_contra hne2
          rcases lt_or_gt_of_ne hne2 with hlt2 | hgt2
          · have hkw2 : pmap f (kp w) = pmap f (kq w') := by
              have h1' : k w = k w' := (hkw'.trans hfz).symm
              simpa [k, hlt2.le, hw'eq.le, hseam w' hw'O hw'eq] using h1'
            have h1 := pmap_eq_of_ball hf (hkp_lt w hlt2) (hkq_ball w' hw'eq.ge) hkw2
            have hn1 : ‖kp w‖ < 1 := by simpa [mem_ball] using hkp_lt w hlt2
            have hn2' : ‖kq w'‖ = 1 := by rw [hkq_norm, hw'eq]; simp
            rw [h1] at hn1; linarith
          · have hkw2 : pmap f (kq w) = pmap f (kq w') := by
              have h1' : k w = k w' := (hkw'.trans hfz).symm
              simpa [k, not_le.mpr hgt2, hw'eq.le, hseam w' hw'O hw'eq] using h1'
            have h1 := pmap_eq_of_ball hf (hkq_lt w hgt2) (hkq_ball w' hw'eq.ge) hkw2
            have hn1 : ‖kq w‖ < 1 := by simpa [mem_ball] using hkq_lt w hgt2
            have hn2' : ‖kq w'‖ = 1 := by rw [hkq_norm, hw'eq]; simp
            rw [h1] at hn1; linarith
        have hkw2 : pmap f (kq w') = pmap f (kq w) := by
          have := hkw'.trans hfz
          simpa [k, hw'eq.le, hweq.le, hseam w' hw'O hw'eq, hseam w hw hweq] using this
        have hrel := (hf.2.2 (0, kq w') ⟨(ew_mem_dsk a b c).1, by simpa using hkq_ball w' hw'eq.ge⟩
          (0, kq w) ⟨(ew_mem_dsk a b c).1, by simpa using hkq_ball w hweq.ge⟩).mp hkw2
        have hgetq : (sW (ew a b c) 0)[q]? = some (lab a b c q, sgn a b c q) := by
          rw [sW_zero]; exact ew_get a b c hq
        have hgetp : (sW (ew a b c) 0)[p]? = some (lab a b c q, sgn a b c p) := by
          rw [sW_zero, ← hlab]; exact ew_get a b c hp
        have hu1 : 1 / 2 + (if sgn a b c p = sgn a b c q then w'.im else -w'.im) ∈ Ioo (0 : ℝ) 1 := by
          by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
            exact ⟨by linarith [(Complex.mem_reProdIm.mp hw'O).2.1, (Complex.mem_reProdIm.mp hw'O).2.2, hδ_eq],
                   by linarith [(Complex.mem_reProdIm.mp hw'O).2.1, (Complex.mem_reProdIm.mp hw'O).2.2, hδ_eq]⟩
        have hu2 : 1 / 2 + (if sgn a b c p = sgn a b c q then w.im else -w.im) ∈ Ioo (0 : ℝ) 1 := by
          by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] <;>
            exact ⟨by linarith [(Complex.mem_reProdIm.mp hw).2.1, (Complex.mem_reProdIm.mp hw).2.2, hδ_eq],
                   by linarith [(Complex.mem_reProdIm.mp hw).2.1, (Complex.mem_reProdIm.mp hw).2.2, hδ_eq]⟩
        rw [hkq_per_eq w' hw'eq, hkq_per_eq w hweq, ← spt_ew] at hrel
        rcases PRel.eq_or_stp (isPaired_ew a b c) hgetq hu1 hrel with he | hstp
        · have hper_eq : per n (q + (1 / 2 + if sgn a b c p = sgn a b c q then w.im else -w.im)) =
              per n (q + (1 / 2 + if sgn a b c p = sgn a b c q then w'.im else -w'.im)) := by
            have := (Prod.mk.inj he).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
          have hsu := side_unique hq hq hu1 (Ioo_subset_Icc_self hu2) hper_eq.symm
          have him_eq : w'.im = w.im := by
            by_cases hs : sgn a b c p = sgn a b c q <;> simp only [hs, ↓reduceIte] at hsu <;> linarith [hsu.2]
          exact Complex.ext (hw'eq.trans hweq.symm) him_eq
        · obtain ⟨j', p', e', hget', hne', hpeq⟩ := stp_of_side (isPaired_ew a b c) hgetq hu1 hstp
          rcases (isPaired_ew a b c).third hgetq hgetp hget' (fun h => hpq (Prod.mk.inj h).2.symm) with h3 | h3
          · exact absurd h3.symm hne'
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3.symm
            have hper_eq : per n (q + (1 / 2 + if sgn a b c p = sgn a b c q then w.im else -w.im)) =
                per n (p + flp (sgn a b c q) e' (1 / 2 + if sgn a b c p = sgn a b c q then w'.im else -w'.im)) := by
              have := (Prod.mk.inj hpeq).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
            have hsu := side_unique hq hp hu2 (flp_mem (Ioo_subset_Icc_self hu1)) hper_eq
            exact absurd hsu.1.symm hpq
  -- Define `j : Y → ℂ` on `U`:
  let j : Y → ℂ := fun y => if hy : y ∈ U then hy.choose else 0
  have hj_eq : ∀ w ∈ O, j (k w) = w := fun w hw => by
    have hy : k w ∈ U := ⟨w, hw, rfl⟩
    simp only [j, dite_eq_left hy]
    set w' := hy.choose
    obtain ⟨hw', hkw'⟩ := hy.choose_spec
    have hz : (if w'.re ≤ 2 then kp w' else kq w') ∈ closedBall (0 : ℂ) 1 := by
      by_cases h : w'.re ≤ 2
      · rw [ite_eq_left h]; exact hkp_ball w' h
      · rw [ite_eq_right h]; exact hkq_ball w' (le_of_not_ge h)
    have hfz' : pmap f (if w'.re ≤ 2 then kp w' else kq w') = k w' := by
      by_cases h : w'.re ≤ 2
      · simp only [k, h, ↓reduceIte]
      · simp only [k, h, ↓reduceIte]
    exact (hjpre_eq w' hw' _ hz hfz').symm.trans (hjpre_eq w hw _ hz (hfz'.trans hkw'))
  have hj_pmap : ∀ z ∈ (Wp ∪ Wq) ∩ closedBall (0 : ℂ) 1, j (pmap f z) = jpre z := by
    intro z hz
    have hzu : pmap f z ∈ U := by
      have : z ∈ pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 := hU_pre.symm ▸ hz
      exact this.1
    obtain ⟨w, hw, hkw⟩ := hzu
    rw [← hkw, hj_eq w hw, hjpre_eq w hw z hz.2 hkw.symm]
  have hj_cont : ContinuousOn j U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hq := (pmap_isQuotientMap hf).restrictPreimage_isOpen hU
    refine hq.continuous_iff.mpr ?_
    have hfun : (U.domRestrict j) ∘ (U.restrictPreimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1)) =
        fun x => jpre x.1.1 := by
      funext ⟨⟨z, hz⟩, hzu⟩
      exact hj_pmap z (hU_pre ▸ ⟨hzu, hz⟩)
    rw [hfun, continuous_iff_continuousAt]
    rintro ⟨⟨z, hz⟩, hzu⟩
    have hzmem : z ∈ (Wp ∪ Wq) ∩ closedBall (0 : ℂ) 1 := hU_pre ▸ ⟨hzu, hz⟩
    rcases hzmem.1 with hzp | hzq
    · have hnhd : {x : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) | x.1.1 ∈ Wp} ∈
          𝓝 (⟨⟨z, hz⟩, hzu⟩ : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1)) :=
        (hWp_open.preimage (continuous_subtype_val.comp continuous_subtype_val)).mem_nhds hzp
      have hev : (fun x : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) => jpre x.1.1) =ᶠ[𝓝 ⟨⟨z, hz⟩, hzu⟩]
          fun x => jp x.1.1 :=
        Filter.mem_of_superset hnhd fun x hx => ite_eq_left (show x.1.1 ∈ Wp from hx)
      refine ContinuousAt.congr ?_ hev.symm
      have hslit : z / per n (p + 1 / 2) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (.inl hzp.2.1)
      have hlog_p : ContinuousAt (fun w : ℂ => Complex.log (w / per n (p + 1 / 2))) z :=
        ContinuousAt.comp (f := fun w : ℂ => w / per n (p + 1 / 2)) (continuousAt_clog hslit)
          (continuousAt_id.div_const _)
      have hjp_at : ContinuousAt jp z := continuousAt_const.add (continuousAt_const.mul hlog_p)
      exact ContinuousAt.comp (g := jp) hjp_at (continuous_subtype_val.comp continuous_subtype_val).continuousAt
    · have hnhd : {x : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) | x.1.1 ∈ Wq} ∈
          𝓝 (⟨⟨z, hz⟩, hzu⟩ : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1)) :=
        (hWq_open.preimage (continuous_subtype_val.comp continuous_subtype_val)).mem_nhds hzq
      have hev : (fun x : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) => jpre x.1.1) =ᶠ[𝓝 ⟨⟨z, hz⟩, hzu⟩]
          fun x => jq x.1.1 :=
        Filter.mem_of_superset hnhd fun x hx => by
          have hnp : x.1.1 ∉ Wp := fun hp' => Set.disjoint_left.mp hdisj ⟨hp', x.1.2⟩ ⟨hx, x.1.2⟩
          exact ite_eq_right hnp
      refine ContinuousAt.congr ?_ hev.symm
      have hslit : z / per n (q + 1 / 2) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (.inl hzq.2.1)
      have hlog_q : ContinuousAt (fun w : ℂ => Complex.log (w / per n (q + 1 / 2))) z :=
        ContinuousAt.comp (f := fun w : ℂ => w / per n (q + 1 / 2)) (continuousAt_clog hslit)
          (continuousAt_id.div_const _)
      have hlog_z : ContinuousAt (fun w : ℂ =>
          ((n / (2 * Real.pi) : ℝ) : ℂ) * Complex.log (w / per n (q + 1 / 2))) z :=
        continuousAt_const.mul hlog_q
      have hlog : ContinuousAt (fun x : U.preimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1) =>
          ((n / (2 * Real.pi) : ℝ) : ℂ) * Complex.log (x.1.1 / per n (q + 1 / 2))) ⟨⟨z, hz⟩, hzu⟩ :=
        ContinuousAt.comp (g := fun w : ℂ => ((n / (2 * Real.pi) : ℝ) : ℂ) * Complex.log (w / per n (q + 1 / 2)))
          hlog_z (continuous_subtype_val.comp continuous_subtype_val).continuousAt
      unfold jq; split_ifs
      · exact continuousAt_const.sub (Complex.continuous_conj.continuousAt.comp hlog)
      · exact continuousAt_const.sub hlog
  let c₀ : SurfChart Y :=
    ⟨U, O, j, k, hU, hO, hj_cont, hO_inter.symm ▸ hk_cont,
     by rintro _ ⟨w, hw, rfl⟩; rw [hj_eq w hw, hO_inter]; exact hw,
     fun w hw => ⟨w, hw.1, rfl⟩,
     by rintro _ ⟨w, hw, rfl⟩; rw [hj_eq w hw],
     fun w hw => hj_eq w hw.1⟩
  refine ⟨c₀, ?_, fun t ht => ?_⟩
  · refine ⟨(2 : ℂ), Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩, ?_⟩
    simp [k, kp, ζp]
  · set wp : ℂ := ((2 - t : ℝ) : ℂ)
    set wq : ℂ := ((2 + t : ℝ) : ℂ)
    have hwpO : wp ∈ O := Complex.mem_reProdIm.mpr
      ⟨⟨by simp [wp]; linarith [ht.2, hδ_eq], by simp [wp]; linarith [ht.1]⟩, ⟨by simp [wp]; linarith, by simp [wp]; linarith⟩⟩
    have hwqO : wq ∈ O := Complex.mem_reProdIm.mpr
      ⟨⟨by simp [wq]; linarith [ht.1], by simp [wq]; linarith [ht.2, hδ_eq]⟩, ⟨by simp [wq]; linarith, by simp [wq]; linarith⟩⟩
    have hzp_eq : kp wp = per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ)) := by
      simp only [kp, ζp, wp]; congr 2; push_cast; ring
    have hzq_eq : kq wq = per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ)) := by
      have hζwq : ζq wq = -(t : ℂ) := Complex.ext (by simp [hζq_re, wq]) (by simp [hζq_im, wq])
      simp only [kq, hζwq]; congr 2; push_cast; ring
    have hkwp : c₀.k wp = pmap f (per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ))) := by
      show k wp = _; simp only [k, show wp.re ≤ 2 by simp [wp]; linarith [ht.1], ↓reduceIte, hzp_eq]
    have hkwq : c₀.k wq = pmap f (per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ))) := by
      show k wq = _; simp only [k, show ¬ wq.re ≤ 2 by simp [wq]; linarith [ht.1], ↓reduceIte, hzq_eq]
    have hmpU : pmap f (per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ c₀.U := hkwp ▸ ⟨wp, hwpO, rfl⟩
    have hmqU : pmap f (per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ c₀.U := hkwq ▸ ⟨wq, hwqO, rfl⟩
    have hzp_b : per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ)) ∈ ball (0 : ℂ) 1 :=
      hzp_eq ▸ hkp_lt wp (by simp [wp]; exact ht.1)
    have hzq_b : per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ)) ∈ ball (0 : ℂ) 1 :=
      hzq_eq ▸ hkq_lt wq (by simp [wq]; exact ht.1)
    have hmpI : pmap f (per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ (intChart_ew hf).U := ⟨_, hzp_b, rfl⟩
    have hmqI : pmap f (per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ (intChart_ew hf).U := ⟨_, hzq_b, rfl⟩
    have hne_p : per n (p + 1 / 2) ≠ 0 := by
      intro h; have := norm_per n (p + 1 / 2); rw [h, norm_zero] at this; norm_num at this
    have hne_q : per n (q + 1 / 2) ≠ 0 := by
      intro h; have := norm_per n (q + 1 / 2); rw [h, norm_zero] at this; norm_num at this
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hpos_p : chartPos c₀ (intChart_ew hf) (c₀.k wp) := by
      have hW : IsOpen (c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | w.re < 2})) :=
        c₀.hj.isOpen_inter_preimage c₀.hU (hO.inter (isOpen_lt Complex.continuous_re continuous_const))
      have hxW : c₀.k wp ∈ c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | w.re < 2}) := by
        refine ⟨⟨wp, hwpO, rfl⟩, ?_⟩
        show c₀.j (c₀.k wp) ∈ O ∩ {w : ℂ | w.re < 2}
        rw [c₀.hr ⟨hwpO, hO_sub hwpO⟩]; exact ⟨hwpO, by simp [wp]; exact ht.1⟩
      have hWsub : c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | w.re < 2}) ⊆ c₀.U ∩ (intChart_ew hf).U := fun y hy => by
        refine ⟨hy.1, ?_⟩
        have hre : (c₀.j y).re < 2 := hy.2.2
        have hky : y = pmap f (kp (c₀.j y)) := by
          have := (c₀.hl hy.1).symm; simpa [c₀, k, hre.le] using this
        rw [hky]; exact ⟨kp (c₀.j y), hkp_lt _ hre, rfl⟩
      have hconn : IsPreconnected (c₀.j '' ((c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | w.re < 2})) ∩ (bd Y)ᶜ)) := by
        have heq : c₀.j '' ((c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | w.re < 2})) ∩ (bd Y)ᶜ) = O ∩ {w : ℂ | w.re < 2} := by
          ext w; constructor
          · rintro ⟨y, ⟨⟨_, hy2⟩, _⟩, rfl⟩; exact hy2
          · rintro ⟨hwO', hwlt⟩
            refine ⟨c₀.k w, ⟨⟨⟨w, hwO', rfl⟩, ?_⟩, ?_⟩, c₀.hr ⟨hwO', hO_sub hwO'⟩⟩
            · show c₀.j (c₀.k w) ∈ O ∩ {w : ℂ | w.re < 2}; rw [c₀.hr ⟨hwO', hO_sub hwO'⟩]; exact ⟨hwO', hwlt⟩
            · have : c₀.k w = pmap f (kp w) := by simp [c₀, k, (show w.re < 2 from hwlt).le]
              rw [this]; exact pmap_ball_not_mem_bd hf (hkp_lt w hwlt)
        rw [heq]
        have hrect : O ∩ {w : ℂ | w.re < 2} = Ioo (2 - δ) 2 ×ℂ Ioo (-δ) δ := by
          ext w; simp only [O, mem_inter_iff, Complex.mem_reProdIm, mem_Ioo, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨⟨h1, _⟩, h3⟩, hlt⟩; exact ⟨⟨h1, hlt⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, by linarith⟩, h3⟩, h2⟩
        rw [hrect]
        exact isPreconnected_reProdIm_Ioo (2 - δ) 2 (-δ) δ
      rw [chartPos_iff_of_int hW hxW hxW (hkwp.symm ▸ pmap_ball_not_mem_bd hf hzp_b) hWsub hconn,
        c₀.hr ⟨hwpO, hO_sub hwpO⟩]
      have hev : ((intChart_ew hf).j ∘ c₀.k) =ᶠ[𝓝 wp] fun w =>
          (per n (p + 1 / 2) * Complex.exp (-((2 : ℂ) * (α : ℂ)))) * Complex.exp ((α : ℂ) * w) + 2 := by
        filter_upwards [(hO.inter (isOpen_lt Complex.continuous_re (continuous_const (y := (2 : ℝ))))).mem_nhds
          ⟨hwpO, show wp.re < 2 by simp [wp]; exact ht.1⟩] with w ⟨_, hwlt⟩
        show (intChart_ew hf).j (c₀.k w) = _
        have hkw' : c₀.k w = pmap f (kp w) := by simp [c₀, k, (show w.re < 2 from hwlt).le]
        rw [hkw', intChart_ew_j hf (hkp_lt w hwlt)]
        simp only [kp, ζp]
        rw [mul_assoc, ← Complex.exp_add]
        congr 3; ring
      rw [isPosLocal_congr hev]
      exact isPosLocal_exp_affine_add (mul_ne_zero hne_p (Complex.exp_ne_zero _)) hαc 2 wp
    have hpos_q : chartPos c₀ (intChart_ew hf) (c₀.k wq) ↔ sgn a b c p ≠ sgn a b c q := by
      have hW : IsOpen (c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 2 < w.re})) :=
        c₀.hj.isOpen_inter_preimage c₀.hU (hO.inter (isOpen_lt continuous_const Complex.continuous_re))
      have hxW : c₀.k wq ∈ c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 2 < w.re}) := by
        refine ⟨⟨wq, hwqO, rfl⟩, ?_⟩
        show c₀.j (c₀.k wq) ∈ O ∩ {w : ℂ | 2 < w.re}
        rw [c₀.hr ⟨hwqO, hO_sub hwqO⟩]; exact ⟨hwqO, by simp [wq]; exact ht.1⟩
      have hWsub : c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 2 < w.re}) ⊆ c₀.U ∩ (intChart_ew hf).U := fun y hy => by
        refine ⟨hy.1, ?_⟩
        have hre : 2 < (c₀.j y).re := hy.2.2
        have hky : y = pmap f (kq (c₀.j y)) := by
          have := (c₀.hl hy.1).symm; simpa [c₀, k, not_le.mpr hre] using this
        rw [hky]; exact ⟨kq (c₀.j y), hkq_lt _ hre, rfl⟩
      have hconn : IsPreconnected (c₀.j '' ((c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 2 < w.re})) ∩ (bd Y)ᶜ)) := by
        have heq : c₀.j '' ((c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 2 < w.re})) ∩ (bd Y)ᶜ) = O ∩ {w : ℂ | 2 < w.re} := by
          ext w; constructor
          · rintro ⟨y, ⟨⟨_, hy2⟩, _⟩, rfl⟩; exact hy2
          · rintro ⟨hwO', hwgt⟩
            refine ⟨c₀.k w, ⟨⟨⟨w, hwO', rfl⟩, ?_⟩, ?_⟩, c₀.hr ⟨hwO', hO_sub hwO'⟩⟩
            · show c₀.j (c₀.k w) ∈ O ∩ {w : ℂ | 2 < w.re}; rw [c₀.hr ⟨hwO', hO_sub hwO'⟩]; exact ⟨hwO', hwgt⟩
            · have : c₀.k w = pmap f (kq w) := by simp [c₀, k, not_le.mpr (show 2 < w.re from hwgt)]
              rw [this]; exact pmap_ball_not_mem_bd hf (hkq_lt w hwgt)
        rw [heq]
        have hrect : O ∩ {w : ℂ | 2 < w.re} = Ioo 2 (2 + δ) ×ℂ Ioo (-δ) δ := by
          ext w; simp only [O, mem_inter_iff, Complex.mem_reProdIm, mem_Ioo, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨⟨_, h2⟩, h3⟩, hgt⟩; exact ⟨⟨hgt, h2⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by linarith, h2⟩, h3⟩, h1⟩
        rw [hrect]
        exact isPreconnected_reProdIm_Ioo 2 (2 + δ) (-δ) δ
      rw [chartPos_iff_of_int hW hxW hxW (hkwq.symm ▸ pmap_ball_not_mem_bd hf hzq_b) hWsub hconn,
        c₀.hr ⟨hwqO, hO_sub hwqO⟩]
      by_cases hsgn : sgn a b c p = sgn a b c q
      · have hev : ((intChart_ew hf).j ∘ c₀.k) =ᶠ[𝓝 wq] fun w =>
            (per n (q + 1 / 2) * Complex.exp ((2 : ℂ) * (α : ℂ))) *
              Complex.exp (-(α : ℂ) * starRingEnd ℂ w) + 2 := by
          filter_upwards [(hO.inter (isOpen_lt (continuous_const (y := (2 : ℝ))) Complex.continuous_re)).mem_nhds
            ⟨hwqO, show 2 < wq.re by simp [wq]; exact ht.1⟩] with w ⟨_, hwgt⟩
          show (intChart_ew hf).j (c₀.k w) = _
          have hkw' : c₀.k w = pmap f (kq w) := by simp [c₀, k, not_le.mpr (show 2 < w.re from hwgt)]
          rw [hkw', intChart_ew_j hf (hkq_lt w hwgt)]
          simp only [kq, ζq, hsgn, ↓reduceIte, map_sub, map_ofNat]
          rw [mul_assoc, ← Complex.exp_add]
          congr 3; ring
        rw [isPosLocal_congr hev]
        exact iff_of_false (not_isPosLocal_exp_affine_conj_add
          (mul_ne_zero hne_q (Complex.exp_ne_zero _)) (neg_ne_zero.mpr hαc) 2 wq) (not_not.mpr hsgn)
      · have hev : ((intChart_ew hf).j ∘ c₀.k) =ᶠ[𝓝 wq] fun w =>
            (per n (q + 1 / 2) * Complex.exp ((2 : ℂ) * (α : ℂ))) *
              Complex.exp (-(α : ℂ) * w) + 2 := by
          filter_upwards [(hO.inter (isOpen_lt (continuous_const (y := (2 : ℝ))) Complex.continuous_re)).mem_nhds
            ⟨hwqO, show 2 < wq.re by simp [wq]; exact ht.1⟩] with w ⟨_, hwgt⟩
          show (intChart_ew hf).j (c₀.k w) = _
          have hkw' : c₀.k w = pmap f (kq w) := by simp [c₀, k, not_le.mpr (show 2 < w.re from hwgt)]
          rw [hkw', intChart_ew_j hf (hkq_lt w hwgt)]
          simp only [kq, ζq, hsgn, ↓reduceIte]
          rw [mul_assoc, ← Complex.exp_add]
          congr 3; ring
        rw [isPosLocal_congr hev]
        exact iff_of_true (isPosLocal_exp_affine_add
          (mul_ne_zero hne_q (Complex.exp_ne_zero _)) (neg_ne_zero.mpr hαc) 2 wq) hsgn
    refine ⟨hmpU, hmqU, ?_, ?_⟩
    · rw [← hkwp, chartSign_symm (hkwp ▸ hmpU) (hkwp ▸ hmpI)]
      simp [chartSign, hpos_p]
    · rw [← hkwq, chartSign_symm (hkwq ▸ hmqU) (hkwq ▸ hmqI)]
      simp only [chartSign, hpos_q]
      by_cases hsgn : sgn a b c p = sgn a b c q <;> simp [hsgn]

/-- An explicit boundary `SurfChart` at the midpoint of the free side `r = 4a + 2b + 3i + 1` of
hole `i < c`, compatible with `intChart_ew` (`chartSign = 0`) and opposite to `holeP i` (`¬ cuffPos`). -/
theorem exists_freeMidChart_ew (hf : Presents (sW (ew a b c)) f) {i : ℕ} (hi : i < c) :
    let n := 4 * a + 2 * b + 3 * c + 2
    let r := 4 * a + 2 * b + 3 * i + 1
    let α := 2 * Real.pi / n
    ∃ c₀ : SurfChart Y,
      holeP a b c f i (1 / 2) ∈ c₀.U ∧
      (∀ t ∈ Ioo (0 : ℝ) (1 / 8),
        pmap f (per n (r + 1 / 2) * Complex.exp (-(α * t : ℝ))) ∈ c₀.U ∧
        chartSign (intChart_ew hf) c₀ (pmap f (per n (r + 1 / 2) * Complex.exp (-(α * t : ℝ)))) = 0) ∧
      (∀ φ : Circle ≃ₜ holeC a b c f i,
        (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee u)).1 = holeP a b c f i u) →
        ¬ cuffPos c₀ φ (holeP a b c f i (1 / 2))) := by
  classical
  set n := 4 * a + 2 * b + 3 * c + 2 with hn_def
  set r := 4 * a + 2 * b + 3 * i + 1 with hr_def
  set α := 2 * Real.pi / n with hα_def
  have hrn : r < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpi := Real.pi_pos
  have hα : 0 < α := by positivity
  obtain ⟨δ, hδ_eq⟩ : ∃ δ : ℝ, δ = 1 / 8 := ⟨1 / 8, rfl⟩
  have hδ0 : 0 < δ := by linarith
  have hδ4 : δ ≤ 1 / 4 := by linarith
  let O : Set ℂ := Ioo (-δ) δ ×ℂ Ioo (-δ) δ
  have hO : IsOpen O := (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  let kr : ℂ → ℂ := fun w => per n (r + 1 / 2) * Complex.exp (-(α : ℂ) * w)
  let k : ℂ → Y := fun w => pmap f (kr w)
  have hkr_norm : ∀ w : ℂ, ‖kr w‖ = Real.exp (-(α * w.re)) := fun w => by
    simp [kr, norm_per, Complex.norm_exp]
  have hkr_ball : ∀ w ∈ halfPlane, kr w ∈ closedBall (0 : ℂ) 1 := fun w hw => by
    rw [mem_closedBall_zero_iff, hkr_norm]; exact Real.exp_le_one_iff.mpr (by nlinarith [show 0 ≤ w.re from hw])
  have hkr_lt : ∀ w : ℂ, 0 < w.re → kr w ∈ ball (0 : ℂ) 1 := fun w hw => by
    rw [mem_ball_zero_iff, hkr_norm]; exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hk_cont : ContinuousOn k (O ∩ halfPlane) :=
    (pmap_cont hf).comp (by unfold kr; fun_prop) (fun w hw => hkr_ball w hw.2)
  let Wr := polarWedge n r δ
  have hWr_open : IsOpen Wr := isOpen_polarWedge n r δ
  let U : Set Y := k '' (O ∩ halfPlane)
  have hWr_param : ∀ z ∈ Wr ∩ closedBall (0 : ℂ) 1,
      ∃ w ∈ O ∩ halfPlane, kr w = z ∧ k w = pmap f z := by
    intro z ⟨hzr, hzb⟩
    obtain ⟨ζ, hζre, hζim, rfl⟩ := (mem_polarWedge_iff hn2 hδ0 hδ4 hzb).mp hzr
    refine ⟨-ζ, ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hζre.2], by simp; linarith [hζre.1]⟩,
      ⟨by simp; linarith [hζim.2], by simp; linarith [hζim.1]⟩⟩,
      show 0 ≤ (-ζ).re by simp; linarith [hζre.2]⟩, by simp [kr, hα_def], by simp [k, kr, hα_def]⟩
  have hfree := freeSide_hole (a := a) (b := b) hi
  have hgetr : (sW (ew a b c) 0)[r]? = some (lab a b c r, sgn a b c r) := by
    rw [sW_zero]; exact ew_get a b c hrn
  have hkr_per_eq : ∀ w : ℂ, w.re = 0 → kr w = per n (r + (1 / 2 - w.im)) := by
    intro w h0
    rw [show (r : ℝ) + (1 / 2 - w.im) = (r + 1 / 2) + (-w.im) by ring, per_shift_exp n (r + 1 / 2) (-w.im)]
    have hw_eq : -(α : ℂ) * w = ((2 * Real.pi / n * (-w.im) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [h0]
      · simp [hα_def]
    simp only [kr, hw_eq]
  have hU_pre : pmap f ⁻¹' U ∩ closedBall (0 : ℂ) 1 = Wr ∩ closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨w, ⟨hwO, hwh⟩, hkw⟩, hzb⟩
      refine ⟨?_, hzb⟩
      have hwre := (Complex.mem_reProdIm.mp hwO).1
      have hwim := (Complex.mem_reProdIm.mp hwO).2
      have hre0 : 0 ≤ w.re := hwh
      rcases eq_or_lt_of_le hre0 with h0 | hpos
      · have hkr_per := hkr_per_eq w h0.symm
        have hrel := (hf.2.2 (0, kr w) ⟨(ew_mem_dsk a b c).1, by simpa using hkr_ball w hwh⟩
          (0, z) ⟨(ew_mem_dsk a b c).1, by simpa using hzb⟩).mp (show f (0, kr w) = f (0, z) from hkw)
        have hu : 1 / 2 - w.im ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hwim.2, hδ_eq], by linarith [hwim.1, hδ_eq]⟩
        rw [hkr_per, ← spt_ew] at hrel
        rcases PRel.eq_or_stp (isPaired_ew a b c) hgetr hu hrel with he | hstp
        · have hze : z = kr w := by rw [hkr_per]; have := (Prod.mk.inj he).2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this
          rw [hze]
          exact (mem_polarWedge_iff hn2 hδ0 hδ4 (hkr_ball w hwh)).mpr
            ⟨-w, ⟨by simp; linarith [hwre.2], by simp; linarith⟩,
             ⟨by simp; linarith [hwim.2], by simp; linarith [hwim.1]⟩, by simp [kr, hα_def]⟩
        · obtain ⟨j', q', e', hget', hne', -⟩ := stp_of_side (isPaired_ew a b c) hgetr hu hstp
          exact absurd (hfree j' q' _ _ _ hgetr hget') hne'
      · have hze := pmap_eq_of_ball hf (hkr_lt w hpos) hzb hkw
        rw [← hze]
        exact (mem_polarWedge_iff hn2 hδ0 hδ4 (ball_subset_closedBall (hkr_lt w hpos))).mpr
          ⟨-w, ⟨by simp; linarith [hwre.2], by simp; linarith⟩,
           ⟨by simp; linarith [hwim.2], by simp; linarith [hwim.1]⟩, by simp [kr, hα_def]⟩
    · rintro ⟨hzr, hzb⟩
      obtain ⟨w, hw, -, hkw⟩ := hWr_param z ⟨hzr, hzb⟩
      exact ⟨⟨w, hw, hkw⟩, hzb⟩
  have hU : IsOpen U := isOpen_of_pmap_preimage hf hWr_open hU_pre
  let jr : ℂ → ℂ := fun z => -(((n / (2 * Real.pi) : ℝ) : ℂ) * Complex.log (z / per n (r + 1 / 2)))
  have hjr_kr : ∀ w ∈ O, jr (kr w) = w := fun w hw => by
    have him := (Complex.mem_reProdIm.mp hw).2
    have hne : per n (r + 1 / 2) ≠ 0 := by
      intro h; have := norm_per n (r + 1 / 2); rw [h, norm_zero] at this; norm_num at this
    have hdiv : kr w / per n (r + 1 / 2) = Complex.exp (-(α : ℂ) * w) := mul_div_cancel_left₀ _ hne
    have hαδ_lt : α * δ < Real.pi / 2 := by
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have h1 : α ≤ Real.pi := by rw [hα_def, div_le_iff₀ hn0]; nlinarith
      nlinarith [hδ_eq]
    have him_b : -Real.pi < (-(α : ℂ) * w).im ∧ (-(α : ℂ) * w).im ≤ Real.pi := by
      simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have h1 : -(α * δ) < α * w.im := by nlinarith [him.1, hα]
      have h2 : α * w.im < α * δ := by nlinarith [him.2, hα]
      exact ⟨by linarith, by linarith⟩
    have h1 : ((n / (2 * Real.pi) : ℝ) : ℂ) * (α : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hα_def]; field_simp [hn0.ne', hpi.ne']; simp
    dsimp only [jr]
    rw [hdiv, Complex.log_exp him_b.1 him_b.2]
    simp only [neg_mul, mul_neg, neg_neg, ← mul_assoc, h1, one_mul]
  have hkinj : InjOn k (O ∩ halfPlane) := by
    intro w₁ hw₁ w₂ hw₂ he
    have hrel := (hf.2.2 (0, kr w₁) ⟨(ew_mem_dsk a b c).1, by simpa using hkr_ball w₁ hw₁.2⟩
      (0, kr w₂) ⟨(ew_mem_dsk a b c).1, by simpa using hkr_ball w₂ hw₂.2⟩).mp (show f (0, kr w₁) = f (0, kr w₂) from he)
    have hkr_eq : kr w₁ = kr w₂ := by
      rcases eq_or_lt_of_le (show 0 ≤ w₁.re from hw₁.2) with h0 | hpos
      · have hkr1 := hkr_per_eq w₁ h0.symm
        have hu : 1 / 2 - w₁.im ∈ Ioo (0 : ℝ) 1 :=
          ⟨by linarith [(Complex.mem_reProdIm.mp hw₁.1).2.2, hδ_eq], by linarith [(Complex.mem_reProdIm.mp hw₁.1).2.1, hδ_eq]⟩
        rw [hkr1, ← spt_ew] at hrel
        rcases PRel.eq_or_stp (isPaired_ew a b c) hgetr hu hrel with h' | hstp
        · rw [hkr1]; have := (Prod.mk.inj h').2; simpa [spt_ew, sW_zero, ew_length, hn_def] using this.symm
        · obtain ⟨j', q', e', hget', hne', -⟩ := stp_of_side (isPaired_ew a b c) hgetr hu hstp
          exact absurd (hfree j' q' _ _ _ hgetr hget') hne'
      · exact (Prod.mk.inj (PRel.eq_of_lt hrel (by simpa [mem_ball] using hkr_lt w₁ hpos))).2.symm
    rw [← hjr_kr w₁ hw₁.1, ← hjr_kr w₂ hw₂.1, hkr_eq]
  let j : Y → ℂ := fun y => if hy : y ∈ U then hy.choose else 0
  have hj_eq : ∀ w ∈ O ∩ halfPlane, j (k w) = w := fun w hw => by
    have hy : k w ∈ U := ⟨w, hw, rfl⟩
    simp only [j, dite_eq_left hy]
    exact hkinj hy.choose_spec.1 hw hy.choose_spec.2
  have hj_pmap : ∀ z ∈ Wr ∩ closedBall (0 : ℂ) 1, j (pmap f z) = jr z := by
    intro z hz
    obtain ⟨w, hw, hkr, hkw⟩ := hWr_param z hz
    rw [← hkw, hj_eq w hw, ← hkr, hjr_kr w hw.1]
  have hj_cont : ContinuousOn j U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hq := (pmap_isQuotientMap hf).restrictPreimage_isOpen hU
    refine hq.continuous_iff.mpr ?_
    have hfun : (U.domRestrict j) ∘ (U.restrictPreimage (fun z : closedBall (0 : ℂ) 1 => pmap f z.1)) =
        fun x => jr x.1.1 := by
      funext ⟨⟨z, hz⟩, hzu⟩
      exact hj_pmap z (hU_pre ▸ ⟨hzu, hz⟩)
    rw [hfun, continuous_iff_continuousAt]
    rintro ⟨⟨z, hz⟩, hzu⟩
    have hzr : z ∈ Wr := (show z ∈ Wr ∩ closedBall 0 1 from
      hU_pre ▸ (show z ∈ pmap f ⁻¹' U ∩ closedBall 0 1 from ⟨hzu, hz⟩)).1
    have hslit : z / per n (r + 1 / 2) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (.inl hzr.2.1)
    have hlog_r : ContinuousAt (fun w : ℂ => Complex.log (w / per n (r + 1 / 2))) z :=
      ContinuousAt.comp (f := fun w : ℂ => w / per n (r + 1 / 2)) (continuousAt_clog hslit)
        (continuousAt_id.div_const _)
    have hjr_at : ContinuousAt jr z := (continuousAt_const.mul hlog_r).neg
    exact ContinuousAt.comp (g := jr) hjr_at (continuous_subtype_val.comp continuous_subtype_val).continuousAt
  let c₀ : SurfChart Y :=
    ⟨U, O, j, k, hU, hO, hj_cont, hk_cont,
     by rintro _ ⟨w, hw, rfl⟩; rw [hj_eq w hw]; exact hw,
     fun w hw => ⟨w, hw, rfl⟩,
     by rintro _ ⟨w, hw, rfl⟩; rw [hj_eq w hw],
     fun w hw => hj_eq w hw⟩
  have hmid : holeP a b c f i (1 / 2) = c₀.k 0 := by
    show pmap f (per n (r + 1 / 2)) = pmap f (per n (r + 1 / 2) * Complex.exp (-(α : ℂ) * 0))
    simp
  have h0_mem : (0 : ℂ) ∈ O ∩ halfPlane :=
    ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩,
     by simp [halfPlane]⟩
  refine ⟨c₀, hmid ▸ ⟨0, h0_mem, rfl⟩, fun t ht => ?_, fun φ hφ => ?_⟩
  · set wt : ℂ := (t : ℂ)
    have hwt : wt ∈ O ∩ halfPlane :=
      ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp [wt]; linarith [ht.1], by simp [wt]; linarith [ht.2, hδ_eq]⟩,
        ⟨by simp [wt]; linarith, by simp [wt]; linarith⟩⟩,
       by simp [halfPlane, wt, ht.1.le]⟩
    have hkwt : c₀.k wt = pmap f (per n (r + 1 / 2) * Complex.exp (-(α * t : ℝ))) := by
      show pmap f (per n (r + 1 / 2) * Complex.exp (-(α : ℂ) * (t : ℂ))) = _
      congr 2; congr 1; push_cast; ring
    have hzt_b : per n (r + 1 / 2) * Complex.exp (-(α * t : ℝ)) ∈ ball (0 : ℂ) 1 := by
      have : kr wt = per n (r + 1 / 2) * Complex.exp (-(α * t : ℝ)) := by simp only [kr, wt]; congr 2; push_cast; ring
      rw [← this]; exact hkr_lt wt (by simp [wt]; exact ht.1)
    have hmtU : c₀.k wt ∈ c₀.U := ⟨wt, hwt, rfl⟩
    have hmtI : c₀.k wt ∈ (intChart_ew hf).U := hkwt ▸ ⟨_, hzt_b, rfl⟩
    refine ⟨hkwt ▸ hmtU, ?_⟩
    rw [← hkwt, chartSign_symm hmtU hmtI]
    have hne_r : per n (r + 1 / 2) ≠ 0 := by
      intro h; have := norm_per n (r + 1 / 2); rw [h, norm_zero] at this; norm_num at this
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hpos : chartPos c₀ (intChart_ew hf) (c₀.k wt) := by
      have hW : IsOpen (c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 0 < w.re})) :=
        c₀.hj.isOpen_inter_preimage c₀.hU (hO.inter (isOpen_lt continuous_const Complex.continuous_re))
      have hxW : c₀.k wt ∈ c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 0 < w.re}) := by
        refine ⟨hmtU, ?_⟩
        show c₀.j (c₀.k wt) ∈ O ∩ {w : ℂ | 0 < w.re}; rw [c₀.hr hwt]; exact ⟨hwt.1, by simp [wt]; exact ht.1⟩
      have hWsub : c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 0 < w.re}) ⊆ c₀.U ∩ (intChart_ew hf).U := fun y hy => by
        refine ⟨hy.1, ?_⟩
        have hky : y = pmap f (kr (c₀.j y)) := (c₀.hl hy.1).symm
        rw [hky]; exact ⟨kr (c₀.j y), hkr_lt _ hy.2.2, rfl⟩
      have hconn : IsPreconnected (c₀.j '' ((c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 0 < w.re})) ∩ (bd Y)ᶜ)) := by
        have heq : c₀.j '' ((c₀.U ∩ c₀.j ⁻¹' (O ∩ {w : ℂ | 0 < w.re})) ∩ (bd Y)ᶜ) = O ∩ {w : ℂ | 0 < w.re} := by
          ext w; constructor
          · rintro ⟨y, ⟨⟨_, hy2⟩, _⟩, rfl⟩; exact hy2
          · rintro ⟨hwO', hwpos⟩
            have hwh : w ∈ O ∩ halfPlane := ⟨hwO', (show 0 < w.re from hwpos).le⟩
            refine ⟨c₀.k w, ⟨⟨⟨w, hwh, rfl⟩, ?_⟩, ?_⟩, c₀.hr hwh⟩
            · show c₀.j (c₀.k w) ∈ O ∩ {w : ℂ | 0 < w.re}; rw [c₀.hr hwh]; exact ⟨hwO', hwpos⟩
            · exact pmap_ball_not_mem_bd hf (hkr_lt w hwpos)
        rw [heq]
        have hrect : O ∩ {w : ℂ | 0 < w.re} = Ioo 0 δ ×ℂ Ioo (-δ) δ := by
          ext w; simp only [O, mem_inter_iff, Complex.mem_reProdIm, mem_Ioo, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨⟨_, h2⟩, h3⟩, hpos⟩; exact ⟨⟨hpos, h2⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by linarith, h2⟩, h3⟩, h1⟩
        rw [hrect]
        exact isPreconnected_reProdIm_Ioo 0 δ (-δ) δ
      rw [chartPos_iff_of_int hW hxW hxW (pmap_ball_not_mem_bd hf (hkr_lt wt (by simp [wt]; exact ht.1))) hWsub hconn, c₀.hr hwt]
      have hev : ((intChart_ew hf).j ∘ c₀.k) =ᶠ[𝓝 wt] fun w =>
          per n (r + 1 / 2) * Complex.exp (-(α : ℂ) * w) + 2 := by
        filter_upwards [(hO.inter (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds
          ⟨hwt.1, by simp [wt]; exact ht.1⟩] with w ⟨_, hwpos⟩
        exact intChart_ew_j hf (hkr_lt w hwpos)
      rw [isPosLocal_congr hev]
      exact isPosLocal_exp_affine_add hne_r (neg_ne_zero.mpr hαc) 2 wt
    simp [chartSign, hpos]
  · -- Show `¬ cuffPos c₀ φ (holeP a b c f i (1 / 2))`:
    rintro ⟨u₁, δ₁, hδ₁, hu₁, -, hmono⟩
    have h0_eq : (φ (ee (1 / 2))).1 = holeP a b c f i (1 / 2) := hφ (1 / 2) (by norm_num)
    obtain ⟨m, hm⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext (hu₁.trans h0_eq.symm)))
    have heq : ∀ s, (φ (ee (u₁ + s))).1 = (φ (ee (1 / 2 + s))).1 := fun s => by
      have : ee (u₁ + s) = ee (1 / 2 + s) := ee_eq_iff.mpr ⟨m, by linarith⟩
      rw [this]
    set η := min δ₁ (δ / 2)
    have hη : 0 < η := lt_min hδ₁ (half_pos hδ0)
    have hη_le1 : η ≤ δ₁ := min_le_left _ _
    have hη_le : η ≤ δ / 2 := min_le_right _ _
    have hval : ∀ s ∈ Icc (-η) η, c₀.j (φ (ee (1 / 2 + s))).1 = (-s : ℂ) * Complex.I := by
      intro s hs
      have hsI : 1 / 2 + s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1, hη_le, hδ_eq], by linarith [hs.2, hη_le, hδ_eq]⟩
      rw [hφ _ hsI]
      have hmem : (-s : ℂ) * Complex.I ∈ O ∩ halfPlane :=
        ⟨Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith, by simp; linarith⟩,
          ⟨by simp; linarith [hs.2, hη_le, hδ0], by simp; linarith [hs.1, hη_le, hδ0]⟩⟩,
         by simp [halfPlane]⟩
      have hkeq : c₀.k ((-s : ℂ) * Complex.I) = holeP a b c f i (1 / 2 + s) := by
        show pmap f (per n (r + 1 / 2) * Complex.exp (-(α : ℂ) * ((-s : ℂ) * Complex.I))) =
          pmap f (per n (r + (1 / 2 + s)))
        rw [show (r : ℝ) + (1 / 2 + s) = (r + 1 / 2) + s by ring, per_shift_exp n (r + 1 / 2) s]
        congr 2; congr 1; simp only [hα_def]; push_cast; ring
      rw [← hkeq, c₀.hr hmem]
    have hlt := hmono ⟨by linarith, hδ₁.le⟩ ⟨by linarith, hη_le1⟩ hη
    have h0' : (φ (ee u₁)).1 = (φ (ee (1 / 2 + 0))).1 := by simpa using heq 0
    simp only [add_zero] at h0'
    have him0 : (c₀.j (φ (ee u₁)).1).im = 0 := by
      rw [h0', show (1 / 2 : ℝ) = 1 / 2 + 0 by ring, hval 0 ⟨by linarith, hη.le⟩]; simp
    have himη : (c₀.j (φ (ee (u₁ + η))).1).im = -η := by
      rw [heq η, hval η ⟨by linarith, le_rfl⟩]; simp
    change (c₀.j (φ (ee (u₁ + 0))).1).im < (c₀.j (φ (ee (u₁ + η))).1).im at hlt
    rw [add_zero, him0, himη] at hlt
    linarith

end EWCharts

/-! ### Evaluation of `w1` on `ew a b c` -/

section W1Eval

/-- In any chart `c` around `x`, near `x` the orientation cocycle `w1 A x y` equals the change in
`chartSign c (A.chart (A.idx ·))`. -/
theorem w1_eq_chartSign_sub {S : Type u} [TopologicalSpace S] (A : SurfAtlas S) (c : SurfChart S)
    {x : S} (hx : x ∈ c.U) :
    ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ W ⊆ c.U ∧
      ∀ y ∈ W, w1 A x y =
        chartSign c (A.chart (A.idx y)) y - chartSign c (A.chart (A.idx x)) x := by
  classical
  let W₀ : Set S := c.U ∩
    (⋂ i : Fin A.m, if x ∈ closure (A.V i) then (A.chart i).U else (closure (A.V i))ᶜ)
  have hW₀_open : IsOpen W₀ := by
    refine c.hU.inter (isOpen_iInter_of_finite fun i => ?_)
    split_ifs
    · exact (A.chart i).hU
    · exact isClosed_closure.isOpen_compl
  have hxW₀ : x ∈ W₀ := by
    refine ⟨hx, mem_iInter.mpr fun i => ?_⟩
    split_ifs with h
    · exact A.hV_sub i h
    · exact h
  obtain ⟨r, hr, -, -, hW_open, hxW, hWsub, hWne, hWconn⟩ :=
    c.exists_ball_nbhd hW₀_open hxW₀ (fun _ h => h.1)
  set W : Set S := c.U ∩ c.j ⁻¹' ball (c.j x) r
  have hW_c : W ⊆ c.U := inter_subset_left
  refine ⟨W, hW_open, hxW, hW_c, fun y hyW => ?_⟩
  have hidx_in : ∀ z ∈ W, x ∈ closure (A.V (A.idx z)) := fun z hz => by
    by_contra hnot
    have hmem := mem_iInter.mp (hWsub hz).2 (A.idx z)
    simp only [hnot, ↓reduceIte] at hmem
    exact hmem (subset_closure (A.hidx z))
  have hsub_idx : ∀ z ∈ W, W ⊆ c.U ∩ (A.chart (A.idx z)).U := fun z hz w hw => by
    refine ⟨hW_c hw, ?_⟩
    have hmem := mem_iInter.mp (hWsub hw).2 (A.idx z)
    simpa [hidx_in z hz] using hmem
  have hsub_x := hsub_idx x hxW
  have hsub_y := hsub_idx y hyW
  have h1 : chartSign c (A.chart (A.idx y)) x = chartSign c (A.chart (A.idx y)) y :=
    chartSign_eq_of_ball hW_open hsub_y hWne hWconn hxW hyW
  have htr := chartSign_trans (hsub_x hxW).2 (hW_c hxW) (hsub_y hxW).2
  have hsym := chartSign_symm (hsub_x hxW).2 (hW_c hxW)
  unfold w1
  rw [← htr, hsym, h1]
  have hneg : ∀ a : ZMod 2, -a = a := fun a => by fin_cases a <;> rfl
  rw [sub_eq_add_neg, hneg, add_comm]

variable {a b c : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] {f : ℕ × ℂ → Y}

/-- On `ball 0 1`, a primitive `g` of `w1 A` equals `chartSign (intChart_ew hf) (A.chart (A.idx (pmap f z)))`
up to a global constant. -/
theorem prim_w1_ball_diff (hf : Presents (sW (ew a b c)) f) (A : SurfAtlas Y) {g : ℂ → ZMod 2}
    (hg : IsPrim (w1 A) (pmap f) g) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ ball (0 : ℂ) 1) (hz₂ : z₂ ∈ ball (0 : ℂ) 1) :
    g z₂ - g z₁ =
      chartSign (intChart_ew hf) (A.chart (A.idx (pmap f z₂))) (pmap f z₂) -
      chartSign (intChart_ew hf) (A.chart (A.idx (pmap f z₁))) (pmap f z₁) := by
  obtain ⟨ε, hε, hprim⟩ := hg
  let cI := intChart_ew hf
  let v : ℂ → ZMod 2 := fun z => g z - chartSign cI (A.chart (A.idx (pmap f z))) (pmap f z)
  -- `v` is locally constant on `ball 0 1`:
  have hloc : ∀ z ∈ ball (0 : ℂ) 1, ∃ δ > 0, ∀ w ∈ ball z δ ∩ ball (0 : ℂ) 1, v w = v z := by
    intro z hz
    obtain ⟨W, hWo, hzW, -, hW⟩ := w1_eq_chartSign_sub A cI (show pmap f z ∈ cI.U from ⟨z, hz, rfl⟩)
    have hcont : ContinuousAt (fun w : ℂ => pmap f w) z :=
      (pmap_cont hf).continuousAt (closedBall_mem_nhds_of_mem hz)
    obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (hWo.mem_nhds hzW))
    refine ⟨min δ₁ ε, lt_min hδ₁ hε, fun w ⟨hw1, hw2⟩ => ?_⟩
    have hdist : ‖z - w‖ < ε := by
      have : dist w z < min δ₁ ε := mem_ball.mp hw1
      rw [dist_comm, dist_eq_norm] at this
      exact lt_of_lt_of_le this (min_le_right _ _)
    have hwW : pmap f w ∈ W := hδ₁sub (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw1) (min_le_left _ _)))
    have hpr := hprim z (ball_subset_closedBall hz) w (ball_subset_closedBall hw2) hdist
    have hcs := hW (pmap f w) hwW
    rw [hcs] at hpr
    dsimp only [v]
    linear_combination -hpr
  -- A locally constant function on the connected open set `ball 0 1` is constant!
  let S₀ : Set ℂ := {z ∈ ball (0 : ℂ) 1 | v z = v z₁}
  let S₁ : Set ℂ := {z ∈ ball (0 : ℂ) 1 | v z ≠ v z₁}
  have hS₀_open : IsOpen S₀ := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hz, hzv⟩
    obtain ⟨δ, hδ, hconst⟩ := hloc z hz
    obtain ⟨δ', hδ', hsub'⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
    refine ⟨min δ δ', lt_min hδ hδ', fun w hw => ?_⟩
    have hwb : w ∈ ball (0 : ℂ) 1 := hsub' (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _)))
    exact ⟨hwb, (hconst w ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)), hwb⟩).trans hzv⟩
  have hS₁_open : IsOpen S₁ := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hz, hzv⟩
    obtain ⟨δ, hδ, hconst⟩ := hloc z hz
    obtain ⟨δ', hδ', hsub'⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
    refine ⟨min δ δ', lt_min hδ hδ', fun w hw => ?_⟩
    have hwb : w ∈ ball (0 : ℂ) 1 := hsub' (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _)))
    refine ⟨hwb, fun heq => hzv ?_⟩
    exact (hconst w ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)), hwb⟩).symm.trans heq
  have hv_eq : v z₂ = v z₁ := by
    by_contra hne
    have hcov : ball (0 : ℂ) 1 ⊆ S₀ ∪ S₁ := fun z hz => by
      by_cases h : v z = v z₁
      · exact .inl ⟨hz, h⟩
      · exact .inr ⟨hz, h⟩
    have hconn : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
    obtain ⟨w, -, hw0, hw1⟩ := hconn S₀ S₁ hS₀_open hS₁_open hcov ⟨z₁, hz₁, hz₁, rfl⟩ ⟨z₂, hz₂, hz₂, hne⟩
    exact hw1.2 hw0.2
  dsimp only [v] at hv_eq
  linear_combination hv_eq

/-- Across a pair of pasted sides `(p, q)` of `ew a b c`, any primitive `g` of `w1 A` jumps by `1`
if `sgn p = sgn q` (crosscap gluing) and by `0` if `sgn p ≠ sgn q` (handle/tether gluing). -/
theorem side_const_w1 (hf : Presents (sW (ew a b c)) f) (A : SurfAtlas Y) {g : ℂ → ZMod 2}
    (hg : IsPrim (w1 A) (pmap f) g) {p q : ℕ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (hq : q < 4 * a + 2 * b + 3 * c + 2)
    (hpq : p ≠ q) (hlab : lab a b c p = lab a b c q) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    g (per (4 * a + 2 * b + 3 * c + 2) (q + flp (sgn a b c p) (sgn a b c q) u)) -
      g (per (4 * a + 2 * b + 3 * c + 2) (p + u)) =
      if sgn a b c p = sgn a b c q then 1 else 0 := by
  set n := 4 * a + 2 * b + 3 * c + 2 with hn_def
  set α := 2 * Real.pi / n with hα_def
  have hα : 0 < α := by positivity
  obtain ⟨c', hc'⟩ := side_const hf hg hp hq hpq hlab
  have hmid_val : g (per n (q + flp (sgn a b c p) (sgn a b c q) u)) - g (per n (p + u)) =
      g (per n (q + 1 / 2)) - g (per n (p + 1 / 2)) := by
    have h1 := hc' u hu
    have h2 := hc' (1 / 2) (by norm_num)
    have hflp_half : flp (sgn a b c p) (sgn a b c q) (1 / 2) = 1 / 2 := by
      unfold flp; split_ifs <;> norm_num
    rw [hflp_half] at h2
    linear_combination h1 - h2
  rw [hmid_val]
  obtain ⟨ε, hε, hprim⟩ := id hg
  obtain ⟨c₀, hmidU, hmid⟩ := exists_pairMidChart_ew hf hp hq hpq hlab
  obtain ⟨W, hWo, hmidW, hWsub, hW⟩ := w1_eq_chartSign_sub A c₀ hmidU
  set zp : ℝ → ℂ := fun t => per n (p + 1 / 2) * Complex.exp (-(α * t : ℝ))
  set zq : ℝ → ℂ := fun t => per n (q + 1 / 2) * Complex.exp (-(α * t : ℝ))
  have hm_eq : pmap f (per n (q + 1 / 2)) = pmap f (per n (p + 1 / 2)) := by
    have hflp_half : flp (sgn a b c p) (sgn a b c q) (1 / 2) = 1 / 2 := by
      unfold flp; split_ifs <;> norm_num
    have := pair_F hf hp hq hpq hlab (u := 1 / 2) (by norm_num)
    rwa [hflp_half] at this
  have hzp_cont : Continuous zp := continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hzq_cont : Continuous zq := continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hzp0 : zp 0 = per n (p + 1 / 2) := by simp [zp]
  have hzq0 : zq 0 = per n (q + 1 / 2) := by simp [zq]
  have hmem_p : (fun t => pmap f (zp t)) ⁻¹' W ∈ 𝓝[Ici (0 : ℝ)] 0 := by
    have hc : ContinuousWithinAt (fun t => pmap f (zp t)) (Ici 0) 0 :=
      ((pmap_cont hf).continuousWithinAt (by rw [hzp0]; exact mem_ball_per n _)).comp hzp_cont.continuousWithinAt
        (fun t ht => by
          rw [mem_closedBall_zero_iff]
          simp only [zp, norm_mul, norm_per, one_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
          exact Real.exp_le_one_iff.mpr (by nlinarith [show 0 ≤ t from ht]))
    exact hc.preimage_mem_nhdsWithin (hWo.mem_nhds (by simpa [hzp0] using hmidW))
  have hmem_q : (fun t => pmap f (zq t)) ⁻¹' W ∈ 𝓝[Ici (0 : ℝ)] 0 := by
    have hc : ContinuousWithinAt (fun t => pmap f (zq t)) (Ici 0) 0 :=
      ((pmap_cont hf).continuousWithinAt (by rw [hzq0]; exact mem_ball_per n _)).comp hzq_cont.continuousWithinAt
        (fun t ht => by
          rw [mem_closedBall_zero_iff]
          simp only [zq, norm_mul, norm_per, one_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
          exact Real.exp_le_one_iff.mpr (by nlinarith [show 0 ≤ t from ht]))
    exact hc.preimage_mem_nhdsWithin (hWo.mem_nhds (by rw [hzq0, hm_eq]; exact hmidW))
  have hmem_ep : zp ⁻¹' ball (per n (p + 1 / 2)) ε ∈ 𝓝 (0 : ℝ) :=
    hzp_cont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hzp0]; exact mem_ball_self hε))
  have hmem_eq : zq ⁻¹' ball (per n (q + 1 / 2)) ε ∈ 𝓝 (0 : ℝ) :=
    hzq_cont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hzq0]; exact mem_ball_self hε))
  have hall : (fun t => pmap f (zp t)) ⁻¹' W ∩ (fun t => pmap f (zq t)) ⁻¹' W ∩
      zp ⁻¹' ball (per n (p + 1 / 2)) ε ∩ zq ⁻¹' ball (per n (q + 1 / 2)) ε ∈ 𝓝[Ici (0 : ℝ)] 0 :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hmem_p hmem_q)
      (nhdsWithin_le_nhds hmem_ep)) (nhdsWithin_le_nhds hmem_eq)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hall
  set t := min (r / 2) (1 / 16)
  have ht0 : 0 < t := lt_min (half_pos hr) (by norm_num)
  have ht8 : t ∈ Ioo (0 : ℝ) (1 / 8) := ⟨ht0, lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have htr : t ∈ ball (0 : ℝ) r ∩ Ici (0 : ℝ) :=
    ⟨by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr), ht0.le⟩
  obtain ⟨⟨⟨hpW, hqW⟩, hpε⟩, hqε⟩ := hrsub htr
  have hzp_b : zp t ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; simp only [zp, norm_mul, norm_per, one_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hzq_b : zq t ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; simp only [zq, norm_mul, norm_per, one_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hdist_p : ‖per n (p + 1 / 2) - zp t‖ < ε := by
    have := mem_ball.mp hpε; rwa [dist_comm, dist_eq_norm] at this
  have hdist_q : ‖per n (q + 1 / 2) - zq t‖ < ε := by
    have := mem_ball.mp hqε; rwa [dist_comm, dist_eq_norm] at this
  have hpr_p := hprim (per n (p + 1 / 2)) (mem_ball_per n _) (zp t) (ball_subset_closedBall hzp_b) hdist_p
  have hpr_q := hprim (per n (q + 1 / 2)) (mem_ball_per n _) (zq t) (ball_subset_closedBall hzq_b) hdist_q
  rw [hm_eq] at hpr_q
  have hWp := hW (pmap f (zp t)) hpW
  have hWq := hW (pmap f (zq t)) hqW
  have hdiff_ball := prim_w1_ball_diff hf A hg hzp_b hzq_b
  obtain ⟨hpU, hqU, hcs_p, hcs_q⟩ := hmid t ht8
  have htr_p := chartSign_trans (show pmap f (zp t) ∈ (intChart_ew hf).U from ⟨zp t, hzp_b, rfl⟩)
    hpU (A.mem_chart (pmap f (zp t)))
  have htr_q := chartSign_trans (show pmap f (zq t) ∈ (intChart_ew hf).U from ⟨zq t, hzq_b, rfl⟩)
    hqU (A.mem_chart (pmap f (zq t)))
  rw [hWp] at hpr_p
  rw [hWq] at hpr_q
  -- Combine all equations in `ZMod 2`:
  have hcomb : g (per n (q + 1 / 2)) - g (per n (p + 1 / 2)) =
      chartSign (intChart_ew hf) c₀ (pmap f (zq t)) - chartSign (intChart_ew hf) c₀ (pmap f (zp t)) := by
    linear_combination hdiff_ball + hpr_q - hpr_p - htr_q + htr_p
  rw [hcomb, hcs_p, hcs_q, sub_zero]

/-- Values of `lval a b c g k` for any primitive `g` of `w1 A` on `ew a b c`:
`0` on every handle label `k < 2a`, and `1` on every crosscap label `2a ≤ k < 2a + b`. -/
theorem lval_w1_ew (hf : Presents (sW (ew a b c)) f) (A : SurfAtlas Y) {g : ℂ → ZMod 2}
    (hg : IsPrim (w1 A) (pmap f) g) {k : ℕ} (hk : k < 2 * a + b) :
    lval a b c g k = if k < 2 * a then 0 else 1 := by
  set n := 4 * a + 2 * b + 3 * c + 2 with hn_def
  by_cases h1 : k < 2 * a
  · rw [ite_eq_left h1]
    set i := k / 2
    have hi : i < a := by omega
    have hlab0 : lab a b c (4 * i + 0) = lab a b c (4 * i + 2) := by
      rw [lab_h hi (by omega), lab_h hi (by omega)]
    have hlab1 : lab a b c (4 * i + 1) = lab a b c (4 * i + 3) := by
      rw [lab_h hi (by omega), lab_h hi (by omega)]
    have hsgn0 : sgn a b c (4 * i) = true := by simpa using sgn_h hi (by omega : 0 < 4)
    have hsgn1 : sgn a b c (4 * i + 1) = true := by simpa using sgn_h hi (by omega : 1 < 4)
    have hsgn2 : sgn a b c (4 * i + 2) = false := by simpa using sgn_h hi (by omega : 2 < 4)
    have hsgn3 : sgn a b c (4 * i + 3) = false := by simpa using sgn_h hi (by omega : 3 < 4)
    have heq0_0 := side_const_w1 hf A hg (p := 4 * i + 0) (q := 4 * i + 2) (by omega) (by omega) (by omega) hlab0 (u := 0) (by norm_num)
    have heq0_1 := side_const_w1 hf A hg (p := 4 * i + 0) (q := 4 * i + 2) (by omega) (by omega) (by omega) hlab0 (u := 1) (by norm_num)
    have heq1_0 := side_const_w1 hf A hg (p := 4 * i + 1) (q := 4 * i + 3) (by omega) (by omega) (by omega) hlab1 (u := 0) (by norm_num)
    have heq1_1 := side_const_w1 hf A hg (p := 4 * i + 1) (q := 4 * i + 3) (by omega) (by omega) (by omega) hlab1 (u := 1) (by norm_num)
    simp only [add_zero, hsgn0, hsgn1, hsgn2, hsgn3, flp, Bool.true_eq_false, ↓reduceIte, sub_zero, sub_self] at heq0_0 heq0_1 heq1_0 heq1_1
    have hper_cor : ∀ m : ℕ, per n (m : ℝ) = cor a b c m := fun _ => rfl
    have hper_succ : ∀ m : ℕ, per n ((m : ℝ) + 1) = cor a b c (m + 1) := fun m => by
      simp [cor, hn_def]
    rw [hper_succ (4 * i + 2), hper_cor (4 * i)] at heq0_0
    rw [hper_cor (4 * i + 2), hper_succ (4 * i)] at heq0_1
    rw [hper_succ (4 * i + 3), hper_cor (4 * i + 1)] at heq1_0
    rw [hper_cor (4 * i + 3), hper_succ (4 * i + 1)] at heq1_1
    have h01 : g (cor a b c (4 * i + 1)) - g (cor a b c (4 * i)) = 0 := by
      linear_combination heq0_0 - heq1_1 - heq0_1
    have h12 : g (cor a b c (4 * i + 2)) - g (cor a b c (4 * i + 1)) = 0 := by
      linear_combination heq0_1
    have hrep : rep a b c k = 4 * i + k % 2 := by simp [rep, h1, i]
    rw [lval, hrep, volt]
    have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hmod with hm | hm
    · rw [hm]
      simp only [en, st, add_zero, hsgn0, ↓reduceIte]
      exact h01
    · rw [hm]
      simp only [en, st, hsgn1, ↓reduceIte]
      exact h12
  · rw [ite_eq_right h1]
    set j := k - 2 * a
    have hj : j < b := by omega
    have hlab : lab a b c (4 * a + 2 * j) = lab a b c (4 * a + 2 * j + 1) := by
      rw [← add_zero (4 * a + 2 * j), lab_c hj (by omega), add_zero, lab_c hj (by omega)]
    have hsgn0 : sgn a b c (4 * a + 2 * j) = true := by
      rw [← add_zero (4 * a + 2 * j)]; exact sgn_c hj (by omega)
    have hsgn1 : sgn a b c (4 * a + 2 * j + 1) = true := sgn_c hj (by omega)
    have heq := side_const_w1 hf A hg (p := 4 * a + 2 * j) (q := 4 * a + 2 * j + 1)
      (by omega) (by omega) (by omega) hlab (u := 0) (by norm_num)
    simp only [hsgn0, hsgn1, flp, ↓reduceIte, add_zero] at heq
    have hrep : rep a b c k = 4 * a + 2 * j := by simp [rep, h1, hk, j]
    rw [lval, hrep, volt]
    simp only [en, st, hsgn0, ↓reduceIte]
    exact heq

/-- On a surface presented by `ew a b c`, the orientation cocycle `w1 A` is cohomologous to `0`
if and only if the surface is orientable (`b = 0`). -/
theorem cohRel_w1_zero_iff (hf : Presents (sW (ew a b c)) f) (A : SurfAtlas Y) :
    CohRel (w1 A) (fun _ _ => (0 : ZMod 2)) ↔ b = 0 := by
  have hY : IsSurface Y := (surface_of_presents (finW_sW _) (isPaired_ew a b c) hf).1
  have hcoc : IsCoc (w1 A) := isCoc_w1 hY A
  have hcoc0 : IsCoc (fun _ _ : Y => (0 : ZMod 2)) :=
    ⟨univ, fun _ => Filter.univ_mem, fun _ _ _ _ _ => by simp⟩
  have hbd : BdTriv (w1 A) := bdTriv_w1 hY A
  have hbd0 : BdTriv (fun _ _ : Y => (0 : ZMod 2)) :=
    ⟨fun _ => 0, univ, fun _ => Filter.univ_mem, fun _ _ _ _ _ => by simp⟩
  obtain ⟨g, hg⟩ := exists_prim hcoc (pmap_cont hf)
  have hg0 : IsPrim (fun _ _ : Y => (0 : ZMod 2)) (pmap f) (fun _ => 0) :=
    ⟨1, one_pos, fun _ _ _ _ _ => by simp⟩
  constructor
  · intro hrel
    by_contra hb
    have hlt : 2 * a < 2 * a + b := by omega
    have h1 := lval_rel hf hg hg0 hrel hlt
    rw [lval_w1_ew hf A hg hlt, ite_eq_right (lt_irrefl _)] at h1
    simp [lval, volt] at h1
  · rintro rfl
    refine cohRel_of_lval hf hcoc hcoc0 hbd hbd0 hg hg0 fun k hk => ?_
    have hk' : k < 2 * a := by omega
    rw [lval_w1_ew hf A hg hk, ite_eq_left hk']
    simp [lval, volt]

/-- For any connected surface `S` homeomorphic to `SurfaceModel a b c`, `CohRel (w1 A) 0 ↔ b = 0`. -/
theorem cohRel_w1_zero_iff_of_homeo {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    (A : SurfAtlas S) (e : S ≃ₜ SurfaceModel a b c) :
    CohRel (w1 A) (fun _ _ => (0 : ZMod 2)) ↔ b = 0 := by
  have : T2Space S := hS.2.1
  obtain ⟨-, f₀, hf₀⟩ := presents_ew a b c
  have hf : Presents (sW (ew a b c)) (e.symm ∘ f₀) := presents_comp hf₀ e.symm
  exact cohRel_w1_zero_iff hf A

/-- When `b = 0` and `h : Y → ZMod 2` globally trivializes `w1 A`, the quantity
`cuffSign A φ_i x - h x` takes the EXACT SAME constant value across ALL cuffs `i < c`
(where `φ_i` parameterizes cuff `i` via `holeP a 0 c f i`). -/
theorem orient_cuffSign_const (hf : Presents (sW (ew a 0 c)) f) (A : SurfAtlas Y)
    {h : Y → ZMod 2} {N : Set (Y × Y)} (hN : NearDiag N)
    (hh : ∀ x y, (x, y) ∈ N → w1 A x y = -h x + h y) :
    ∃ C₀ : ZMod 2, ∀ i < c, ∀ (φ : Circle ≃ₜ holeC a 0 c f i),
      (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee u)).1 = holeP a 0 c f i u) →
      ∀ x ∈ holeC a 0 c f i, cuffSign A φ x - h x = C₀ := by
  have hY : IsSurface Y := (surface_of_presents (finW_sW _) (isPaired_ew a 0 c) hf).1
  set n := 4 * a + 2 * 0 + 3 * c + 2 with hn_def
  set α := 2 * Real.pi / n with hα_def
  have hα : 0 < α := by positivity
  -- `g := h ∘ pmap f` is a primitive of `w1 A` on `closedBall 0 1`!
  obtain ⟨ε, hε, hεN⟩ := exists_eps (isCompact_closedBall 0 1) (pmap_cont hf) hN
  have hg : IsPrim (w1 A) (pmap f) (fun z => h (pmap f z)) :=
    ⟨ε, hε, fun z₁ hz₁ z₂ hz₂ hdist => hh _ _ (hεN z₁ hz₁ z₂ hz₂ hdist)⟩
  let cI := intChart_ew hf
  let C₀ : ZMod 2 := 1 + chartSign cI (A.chart (A.idx (pmap f 0))) (pmap f 0) - h (pmap f 0)
  refine ⟨C₀, fun i hi φ hφ => ?_⟩
  set r := 4 * a + 2 * 0 + 3 * i + 1 with hr_def
  have hCbd : holeC a 0 c f i ⊆ bd Y := by
    have hcuffs := cuffs_eq_holeC hf
    have hmem : holeC a 0 c f i ∈ cuffs Y := hcuffs ▸ ⟨i, hi, rfl⟩
    obtain ⟨z, -, hEq⟩ := hmem
    exact hEq ▸ connectedComponentIn_subset _ _
  -- First compute `cuffSign A φ m_i - h m_i = C₀` at the midpoint `m_i = holeP a 0 c f i (1/2)`:
  obtain ⟨c₀, hmidU, hmid_int, hnot_pos⟩ := exists_freeMidChart_ew hf hi
  obtain ⟨W, hWo, hmidW, -, hW⟩ := w1_eq_chartSign_sub A c₀ hmidU
  set zr : ℝ → ℂ := fun t => per n (r + 1 / 2) * Complex.exp (-(α * t : ℝ))
  have hzr_cont : Continuous zr := continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hzr0 : zr 0 = per n (r + 1 / 2) := by simp [zr]
  have hmid_def : holeP a 0 c f i (1 / 2) = pmap f (per n (r + 1 / 2)) := rfl
  have hmem_W : (fun t => pmap f (zr t)) ⁻¹' W ∈ 𝓝[Ici (0 : ℝ)] 0 := by
    have hc : ContinuousWithinAt (fun t => pmap f (zr t)) (Ici 0) 0 :=
      ((pmap_cont hf).continuousWithinAt (by rw [hzr0]; exact mem_ball_per n _)).comp hzr_cont.continuousWithinAt
        (fun t ht => by
          rw [mem_closedBall_zero_iff]
          simp only [zr, norm_mul, norm_per, one_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
          exact Real.exp_le_one_iff.mpr (by nlinarith [show 0 ≤ t from ht]))
    exact hc.preimage_mem_nhdsWithin (hWo.mem_nhds (by rw [hzr0, ← hmid_def]; exact hmidW))
  have hmem_e : zr ⁻¹' ball (per n (r + 1 / 2)) ε ∈ 𝓝 (0 : ℝ) :=
    hzr_cont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hzr0]; exact mem_ball_self hε))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hmem_W (nhdsWithin_le_nhds hmem_e))
  set t := min (ρ / 2) (1 / 16)
  have ht0 : 0 < t := lt_min (half_pos hρ) (by norm_num)
  have ht8 : t ∈ Ioo (0 : ℝ) (1 / 8) := ⟨ht0, lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  obtain ⟨htW, htε⟩ := hρsub ⟨by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ), ht0.le⟩
  have hzr_b : zr t ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; simp only [zr, norm_mul, norm_per, one_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have h0_b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hdist : ‖per n (r + 1 / 2) - zr t‖ < ε := by
    have := mem_ball.mp htε; rwa [dist_comm, dist_eq_norm] at this
  have hpr := hh _ _ (hεN (per n (r + 1 / 2)) (mem_ball_per n _) (zr t) (ball_subset_closedBall hzr_b) hdist)
  rw [← hmid_def, hW (pmap f (zr t)) htW] at hpr
  have hball := prim_w1_ball_diff hf A hg h0_b hzr_b
  obtain ⟨htU, hcs0⟩ := hmid_int t ht8
  have htr := chartSign_trans (show pmap f (zr t) ∈ cI.U from ⟨zr t, hzr_b, rfl⟩) htU (A.mem_chart (pmap f (zr t)))
  have hmid_inC : holeP a 0 c f i (1 / 2) ∈ holeC a 0 c f i := ⟨1 / 2, by norm_num, rfl⟩
  have hch := cuffSignChart_change hCbd φ hmid_inC hmidU (A.mem_chart _)
  have hcs_mid : cuffSignChart c₀ φ (holeP a 0 c f i (1 / 2)) = 1 := by
    unfold cuffSignChart; rw [ite_eq_right (hnot_pos φ hφ)]
  have hmid_C0 : cuffSign A φ (holeP a 0 c f i (1 / 2)) - h (holeP a 0 c f i (1 / 2)) = C₀ := by
    have hsign : cuffSign A φ (holeP a 0 c f i (1 / 2)) =
        1 + chartSign c₀ (A.chart (A.idx (holeP a 0 c f i (1 / 2)))) (holeP a 0 c f i (1 / 2)) := by
      unfold cuffSign; linear_combination hch + hcs_mid
    rw [hsign]
    dsimp only [C₀]
    linear_combination -hball - hpr + htr - hcs0
  -- Now show `cuffSign A φ x - h x` is constant along the connected cuff `holeC a 0 c f i`!
  obtain ⟨N₁, hN₁, hdiff⟩ := cuffSign_diff hY A hCbd φ
  have hN_inter : NearDiag (N ∩ N₁) := fun x => Filter.inter_mem (hN x) (hN₁ x)
  -- Pull back along `u ↦ (φ (ee u)).1` on `[0, 1]`:
  have hcont_u : ContinuousOn (fun u : ℝ => (φ (ee u)).1) (Icc 0 1) :=
    (continuous_subtype_val.comp (φ.continuous.comp continuous_ee)).continuousOn
  -- Find `δ > 0` so `|u₁ - u₂| < δ` implies `((φ (ee u₁)).1, (φ (ee u₂)).1) ∈ N ∩ N₁`:
  have hδ_ex : ∃ δ > 0, ∀ u₁ ∈ Icc (0 : ℝ) 1, ∀ u₂ ∈ Icc (0 : ℝ) 1, |u₁ - u₂| < δ →
      ((φ (ee u₁)).1, (φ (ee u₂)).1) ∈ N ∩ N₁ := by
    have hcp : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
    let γ : Icc (0 : ℝ) 1 → Y := fun u => (φ (ee u.1)).1
    have hγc : Continuous γ := continuous_subtype_val.comp (φ.continuous.comp (continuous_ee.comp continuous_subtype_val))
    let M : Set (Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) := (fun p => (γ p.1, γ p.2)) ⁻¹' (N ∩ N₁)
    have hM : M ∈ 𝓝ˢ (diagonal (Icc (0 : ℝ) 1)) := by
      rw [mem_nhdsSet_iff_forall]
      rintro ⟨u, v⟩ h
      have : u = v := h; subst this
      exact ((hγc.comp continuous_fst).prodMk (hγc.comp continuous_snd)).continuousAt.preimage_mem_nhds (hN_inter (γ u))
    rw [nhdsSet_diagonal_eq_uniformity, Metric.mem_uniformity_dist] at hM
    obtain ⟨δ, hδ, h1⟩ := hM
    exact ⟨δ, hδ, fun u₁ hu₁ u₂ hu₂ hlt => h1 (a := ⟨u₁, hu₁⟩) (b := ⟨u₂, hu₂⟩)
      (by simpa [Subtype.dist_eq, Real.dist_eq] using hlt)⟩
  obtain ⟨δ, hδ, hδ_mem⟩ := hδ_ex
  have hconst_u := const_of_near (v := fun u => cuffSign A φ (φ (ee u)).1 - h (φ (ee u)).1) hδ
    (fun s hs t ht hst => by
      have hpair := hδ_mem t ht s hs (by rwa [abs_sub_comm])
      have e1 := hh _ _ hpair.1
      have e2 := hdiff _ (φ _).2 _ (φ _).2 hpair.2
      rw [e1] at e2
      have hneg : ∀ z : ZMod 2, -z = z := fun z => by fin_cases z <;> rfl
      have e3 : cuffSign A φ (φ (ee s)).1 - h (φ (ee s)).1 - (cuffSign A φ (φ (ee t)).1 - h (φ (ee t)).1) =
          (cuffSign A φ (φ (ee s)).1 - cuffSign A φ (φ (ee t)).1) - (-h (φ (ee t)).1 + h (φ (ee s)).1) := by
        simp only [sub_eq_add_neg, hneg]; ring_nf
      rw [← sub_eq_zero, e3, e2, sub_self])
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hx_eq : holeP a 0 c f i u = (φ (ee u)).1 := (hφ u hu).symm
  have hm_eq' : holeP a 0 c f i (1 / 2) = (φ (ee (1 / 2))).1 := (hφ (1 / 2) (by norm_num)).symm
  change cuffSign A φ (holeP a 0 c f i u) - h (holeP a 0 c f i u) = C₀
  rw [hx_eq, hconst_u u hu, ← hconst_u (1 / 2) (by norm_num), ← hm_eq', hmid_C0]

end W1Eval

/-! ### Pullback of `w1` along a cutting -/

section Cutting

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- Whether a cutting `ψ : Y → S` is locally orientation-preserving at `y ∈ cY.U` (with `ψ y ∈ cS.U`)
from chart `cY` of `Y` to chart `cS` of `S`. -/
def cutChartPos (cY : SurfChart Y) (cS : SurfChart S) (ψ : Y → S) (y : Y) : Prop :=
  ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ W ⊆ cY.U ∩ ψ ⁻¹' cS.U ∧
    ∀ y' ∈ W ∩ (bd Y)ᶜ, IsPosLocal (cS.j ∘ ψ ∘ cY.k) (cY.j y')

/-- Local orientation sign in `ZMod 2` of a cutting `ψ : Y → S` between charts `cY` and `cS`. -/
noncomputable def cutChartSign (cY : SurfChart Y) (cS : SurfChart S) (ψ : Y → S) (y : Y) : ZMod 2 :=
  open Classical in if cutChartPos cY cS ψ y then 0 else 1

/-- Explicit coboundary witness `Y → ZMod 2` comparing `pbk ψ (w1 AS)` and `w1 AY`. -/
noncomputable def cutOrientDiff (AY : SurfAtlas Y) (AS : SurfAtlas S) (ψ : Y → S) (y : Y) : ZMod 2 :=
  cutChartSign (AY.chart (AY.idx y)) (AS.chart (AS.idx (ψ y))) ψ y

/-- Helper: for a cutting `ψ : Y → S` along closed `F`, `ψ` maps `Y \ bd Y` injectively into `S \ bd S`. -/
private theorem cutting_int_maps [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) :
    InjOn ψ (bd Y)ᶜ ∧ MapsTo ψ (bd Y)ᶜ (bd S)ᶜ := by
  have hsub : (bd Y)ᶜ ⊆ ψ ⁻¹' Fᶜ := fun y hy hyF => hy (hψ.2.2.2.2 hyF)
  refine ⟨hψ.2.2.1.mono hsub, fun y hy hbd => ?_⟩
  exact hy (bd_lift hψ hF hbd (hsub hy))

/-- On an open set `W ⊆ cY.U ∩ ψ ⁻¹' cS.U` whose interior image in `cY` is connected,
`cutChartPos cY cS ψ y` is equivalent to `IsPosLocal (cS.j ∘ ψ ∘ cY.k) (cY.j y₀)` at any single
interior point `y₀ ∈ W \ bd Y`. -/
theorem cutChartPos_iff_of_int [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) {cY : SurfChart Y} {cS : SurfChart S}
    {y y₀ : Y} {W : Set Y} (hW : IsOpen W) (hyW : y ∈ W) (hy₀W : y₀ ∈ W) (hy₀ : y₀ ∉ bd Y)
    (hWsub : W ⊆ cY.U ∩ ψ ⁻¹' cS.U) (hconn : IsPreconnected (cY.j '' (W ∩ (bd Y)ᶜ))) :
    cutChartPos cY cS ψ y ↔ IsPosLocal (cS.j ∘ ψ ∘ cY.k) (cY.j y₀) := by
  obtain ⟨hinj_int, hmaps_int⟩ := cutting_int_maps hψ hF
  have hWint_open : IsOpen (cY.j '' (W ∩ (bd Y)ᶜ)) := by
    have h1 : cY.j '' (W ∩ (bd Y)ᶜ) = (cY.O ∩ {z : ℂ | 0 < z.re}) ∩ cY.k ⁻¹' (W ∩ (bd Y)ᶜ) := by
      ext z; constructor
      · rintro ⟨w, ⟨hwW, hwI⟩, rfl⟩
        refine ⟨⟨(cY.hm (hWsub hwW).1).1, (cY.not_mem_bd_iff (hWsub hwW).1).mp hwI⟩, ?_⟩
        show cY.k (cY.j w) ∈ W ∩ (bd Y)ᶜ
        rw [cY.hl (hWsub hwW).1]; exact ⟨hwW, hwI⟩
      · rintro ⟨⟨hzO, hzre⟩, hzk⟩
        exact ⟨cY.k z, hzk, cY.hr ⟨hzO, (show 0 < z.re from hzre).le⟩⟩
    rw [h1]
    exact (cY.hk.mono (fun z hz => ⟨hz.1, (show 0 < z.re from hz.2).le⟩)).isOpen_inter_preimage
      (cY.hO.inter (isOpen_lt continuous_const Complex.continuous_re))
      (hW.inter (isClosed_bd Y).isOpen_compl)
  have hfc : ContinuousOn (cS.j ∘ ψ ∘ cY.k) (cY.j '' (W ∩ (bd Y)ᶜ)) := by
    have h1 : ContinuousOn cY.k (cY.j '' (W ∩ (bd Y)ᶜ)) :=
      cY.hk.mono (by rintro _ ⟨w, ⟨hwW, _⟩, rfl⟩; exact cY.hm (hWsub hwW).1)
    have h2 : ContinuousOn (ψ ∘ cY.k) (cY.j '' (W ∩ (bd Y)ᶜ)) := hψ.1.comp_continuousOn h1
    refine cS.hj.comp h2 ?_
    rintro _ ⟨w, ⟨hwW, _⟩, rfl⟩
    show ψ (cY.k (cY.j w)) ∈ cS.U
    rw [cY.hl (hWsub hwW).1]; exact (hWsub hwW).2
  have hfi : InjOn (cS.j ∘ ψ ∘ cY.k) (cY.j '' (W ∩ (bd Y)ᶜ)) := by
    rintro _ ⟨w₁, ⟨hw₁W, hw₁I⟩, rfl⟩ _ ⟨w₂, ⟨hw₂W, hw₂I⟩, rfl⟩ he
    dsimp only [Function.comp_apply] at he
    rw [cY.hl (hWsub hw₁W).1, cY.hl (hWsub hw₂W).1] at he
    have hψeq := cS.injOn_j (hWsub hw₁W).2 (hWsub hw₂W).2 he
    have hweq := hinj_int hw₁I hw₂I hψeq
    rw [hweq]
  constructor
  · rintro ⟨W', hW', hyW', hW'sub, hpos⟩
    obtain ⟨r, -, -, -, -, -, hBsub, ⟨y₁, hy₁B, hy₁I⟩, -⟩ :=
      cY.exists_ball_nbhd (hW.inter hW') ⟨hyW, hyW'⟩ (fun w hw => (hWsub hw.1).1)
    have h1 := hpos y₁ ⟨(hBsub hy₁B).2, hy₁I⟩
    exact (isPosLocal_const_of_isPreconnected hWint_open hconn hfc hfi
      ⟨y₁, ⟨(hBsub hy₁B).1, hy₁I⟩, rfl⟩ ⟨y₀, ⟨hy₀W, hy₀⟩, rfl⟩).mp h1
  · intro hpos
    refine ⟨W, hW, hyW, hWsub, fun y' hy' => ?_⟩
    exact (isPosLocal_const_of_isPreconnected hWint_open hconn hfc hfi
      ⟨y₀, ⟨hy₀W, hy₀⟩, rfl⟩ ⟨y', hy', rfl⟩).mp hpos

/-- Change of charts in `Y` or `S` adds the corresponding `chartSign` to `cutChartSign`. -/
theorem cutChartSign_change [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F)
    {cY₁ cY₂ : SurfChart Y} {cS₁ cS₂ : SurfChart S} {y : Y}
    (hy₁ : y ∈ cY₁.U) (hy₂ : y ∈ cY₂.U) (hψ₁ : ψ y ∈ cS₁.U) (hψ₂ : ψ y ∈ cS₂.U) :
    cutChartSign cY₂ cS₂ ψ y =
      chartSign cY₂ cY₁ y + cutChartSign cY₁ cS₁ ψ y + chartSign cS₁ cS₂ (ψ y) := by
  obtain ⟨hinj_int, hmaps_int⟩ := cutting_int_maps hψ hF
  let U₀ : Set Y := cY₁.U ∩ cY₂.U ∩ ψ ⁻¹' (cS₁.U ∩ cS₂.U)
  have hU₀ : IsOpen U₀ := (cY₁.hU.inter cY₂.hU).inter ((cS₁.hU.inter cS₂.hU).preimage hψ.1)
  have hyU₀ : y ∈ U₀ := ⟨⟨hy₁, hy₂⟩, ⟨hψ₁, hψ₂⟩⟩
  obtain ⟨r₂, -, -, -, hW₂o, hyW₂, hW₂sub, ⟨y₀, hy₀W₂, hy₀I⟩, hW₂conn⟩ :=
    cY₂.exists_ball_nbhd hU₀ hyU₀ (fun _ h => h.1.2)
  set W₂ := cY₂.U ∩ cY₂.j ⁻¹' ball (cY₂.j y) r₂
  have hy₀U₀ : y₀ ∈ U₀ := hW₂sub hy₀W₂
  have hψy₀I : ψ y₀ ∉ bd S := hmaps_int hy₀I
  -- Also take ball neighborhoods of `y₀` in `cY₁` and `ψ y₀` in `cS₁`? No, we just compare at `y₀` directly!
  have h1 : cutChartPos cY₂ cS₂ ψ y ↔ IsPosLocal (cS₂.j ∘ ψ ∘ cY₂.k) (cY₂.j y₀) :=
    cutChartPos_iff_of_int hψ hF hW₂o hyW₂ hy₀W₂ hy₀I (fun w hw => ⟨(hW₂sub hw).1.2, (hW₂sub hw).2.2⟩) hW₂conn
  have h2 : chartPos cY₂ cY₁ y ↔ IsPosLocal (cY₁.j ∘ cY₂.k) (cY₂.j y₀) :=
    chartPos_iff_of_int hW₂o hyW₂ hy₀W₂ hy₀I (fun w hw => ⟨(hW₂sub hw).1.2, (hW₂sub hw).1.1⟩) hW₂conn
  -- For `cutChartPos cY₁ cS₁ ψ y` and `chartPos cS₁ cS₂ (ψ y)`, use ball neighborhoods around `y` in `cY₁` and `ψ y` in `cS₁`
  -- containing `y₀` (shrink `W₂` to lie inside BOTH of those ball neighborhoods!):
  obtain ⟨r₁, -, -, -, hW₁o, hyW₁, hW₁sub, -, hW₁conn⟩ :=
    cY₁.exists_ball_nbhd hU₀ hyU₀ (fun _ h => h.1.1)
  set W₁ := cY₁.U ∩ cY₁.j ⁻¹' ball (cY₁.j y) r₁
  obtain ⟨rS, -, -, -, hWSo, hψyWS, hWSsub, -, hWSconn⟩ :=
    cS₁.exists_ball_nbhd (cS₁.hU.inter cS₂.hU) ⟨hψ₁, hψ₂⟩ (fun _ h => h.1)
  set WS := cS₁.U ∩ cS₁.j ⁻¹' ball (cS₁.j (ψ y)) rS
  -- Pick `y₁ ∈ W₂ ∩ W₁ ∩ ψ ⁻¹' WS ∩ (bd Y)ᶜ`:
  have hWint_o : IsOpen (W₂ ∩ W₁ ∩ ψ ⁻¹' WS) := (hW₂o.inter hW₁o).inter (hWSo.preimage hψ.1)
  have hy_Wint : y ∈ W₂ ∩ W₁ ∩ ψ ⁻¹' WS := ⟨⟨hyW₂, hyW₁⟩, hψyWS⟩
  obtain ⟨r', -, -, -, -, -, hB'sub, ⟨y₁, hy₁B', hy₁I⟩, -⟩ :=
    cY₂.exists_ball_nbhd hWint_o hy_Wint (fun w hw => (hW₂sub hw.1.1).1.2)
  have hy₁W₂ : y₁ ∈ W₂ := (hB'sub hy₁B').1.1
  have hy₁W₁ : y₁ ∈ W₁ := (hB'sub hy₁B').1.2
  have hψy₁WS : ψ y₁ ∈ WS := (hB'sub hy₁B').2
  have hψy₁I : ψ y₁ ∉ bd S := hmaps_int hy₁I
  have hc22 : cutChartPos cY₂ cS₂ ψ y ↔ IsPosLocal (cS₂.j ∘ ψ ∘ cY₂.k) (cY₂.j y₁) :=
    cutChartPos_iff_of_int hψ hF hW₂o hyW₂ hy₁W₂ hy₁I (fun w hw => ⟨(hW₂sub hw).1.2, (hW₂sub hw).2.2⟩) hW₂conn
  have hc21 : chartPos cY₂ cY₁ y ↔ IsPosLocal (cY₁.j ∘ cY₂.k) (cY₂.j y₁) :=
    chartPos_iff_of_int hW₂o hyW₂ hy₁W₂ hy₁I (fun w hw => ⟨(hW₂sub hw).1.2, (hW₂sub hw).1.1⟩) hW₂conn
  have hc11 : cutChartPos cY₁ cS₁ ψ y ↔ IsPosLocal (cS₁.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁) :=
    cutChartPos_iff_of_int hψ hF hW₁o hyW₁ hy₁W₁ hy₁I (fun w hw => ⟨(hW₁sub hw).1.1, (hW₁sub hw).2.1⟩) hW₁conn
  have hcS : chartPos cS₁ cS₂ (ψ y) ↔ IsPosLocal (cS₂.j ∘ cS₁.k) (cS₁.j (ψ y₁)) :=
    chartPos_iff_of_int hWSo hψyWS hψy₁WS hψy₁I hWSsub hWSconn
  -- Chain rule at `y₁`:
  -- `cS₂.j ∘ ψ ∘ cY₂.k = (cS₂.j ∘ cS₁.k) ∘ (cS₁.j ∘ ψ ∘ cY₁.k) ∘ (cY₁.j ∘ cY₂.k)` near `cY₂.j y₁`!
  let U2 := cY₂.j '' ((W₂ ∩ W₁ ∩ ψ ⁻¹' WS) ∩ (bd Y)ᶜ)
  let U1 := cY₁.j '' ((W₁ ∩ ψ ⁻¹' WS) ∩ (bd Y)ᶜ)
  let US := cS₁.j '' (WS ∩ (bd S)ᶜ)
  have hopen_img : ∀ (c : SurfChart Y) (V : Set Y), IsOpen V → V ⊆ c.U → IsOpen (c.j '' (V ∩ (bd Y)ᶜ)) := by
    intro c V hVo hVsub
    have h_eq : c.j '' (V ∩ (bd Y)ᶜ) = (c.O ∩ {z : ℂ | 0 < z.re}) ∩ c.k ⁻¹' (V ∩ (bd Y)ᶜ) := by
      ext z; constructor
      · rintro ⟨w, ⟨hwV, hwI⟩, rfl⟩
        refine ⟨⟨(c.hm (hVsub hwV)).1, (c.not_mem_bd_iff (hVsub hwV)).mp hwI⟩, ?_⟩
        show c.k (c.j w) ∈ V ∩ (bd Y)ᶜ; rw [c.hl (hVsub hwV)]; exact ⟨hwV, hwI⟩
      · rintro ⟨⟨hzO, hzre⟩, hzk⟩; exact ⟨c.k z, hzk, c.hr ⟨hzO, (show 0 < z.re from hzre).le⟩⟩
    rw [h_eq]
    exact (c.hk.mono (fun z hz => ⟨hz.1, (show 0 < z.re from hz.2).le⟩)).isOpen_inter_preimage
      (c.hO.inter (isOpen_lt continuous_const Complex.continuous_re)) (hVo.inter (isClosed_bd Y).isOpen_compl)
  have hU2_open : IsOpen U2 := hopen_img cY₂ _ hWint_o (fun w hw => (hW₂sub hw.1.1).1.2)
  have hU1_open : IsOpen U1 := hopen_img cY₁ _ (hW₁o.inter (hWSo.preimage hψ.1)) (fun w hw => (hW₁sub hw.1).1.1)
  have hUS_open : IsOpen US := by
    have h_eq : US = (cS₁.O ∩ {z : ℂ | 0 < z.re}) ∩ cS₁.k ⁻¹' (WS ∩ (bd S)ᶜ) := by
      ext z; constructor
      · rintro ⟨w, ⟨hwW, hwI⟩, rfl⟩
        refine ⟨⟨(cS₁.hm (hWSsub hwW).1).1, (cS₁.not_mem_bd_iff (hWSsub hwW).1).mp hwI⟩, ?_⟩
        show cS₁.k (cS₁.j w) ∈ WS ∩ (bd S)ᶜ; rw [cS₁.hl (hWSsub hwW).1]; exact ⟨hwW, hwI⟩
      · rintro ⟨⟨hzO, hzre⟩, hzk⟩; exact ⟨cS₁.k z, hzk, cS₁.hr ⟨hzO, (show 0 < z.re from hzre).le⟩⟩
    rw [h_eq]
    exact (cS₁.hk.mono (fun z hz => ⟨hz.1, (show 0 < z.re from hz.2).le⟩)).isOpen_inter_preimage
      (cS₁.hO.inter (isOpen_lt continuous_const Complex.continuous_re)) (hWSo.inter (isClosed_bd S).isOpen_compl)
  have hfc21 : ContinuousOn (cY₁.j ∘ cY₂.k) U2 :=
    cY₁.hj.comp (cY₂.hk.mono (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; exact cY₂.hm (hW₂sub hw.1.1).1.2))
      (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; show cY₂.k (cY₂.j w) ∈ cY₁.U; rw [cY₂.hl (hW₂sub hw.1.1).1.2]; exact (hW₂sub hw.1.1).1.1)
  have hfi21 : InjOn (cY₁.j ∘ cY₂.k) U2 := by
    rintro _ ⟨w₁, ⟨hw₁, _⟩, rfl⟩ _ ⟨w₂, ⟨hw₂, _⟩, rfl⟩ he
    dsimp only [Function.comp_apply] at he
    rw [cY₂.hl (hW₂sub hw₁.1.1).1.2, cY₂.hl (hW₂sub hw₂.1.1).1.2] at he
    rw [cY₁.injOn_j (hW₂sub hw₁.1.1).1.1 (hW₂sub hw₂.1.1).1.1 he]
  have hmap21 : MapsTo (cY₁.j ∘ cY₂.k) U2 U1 := by
    rintro _ ⟨w, ⟨⟨⟨hw2, hw1⟩, hwS⟩, hwI⟩, rfl⟩
    show cY₁.j (cY₂.k (cY₂.j w)) ∈ U1
    rw [cY₂.hl (hW₂sub hw2).1.2]
    exact ⟨w, ⟨⟨hw1, hwS⟩, hwI⟩, rfl⟩
  have hfc11 : ContinuousOn (cS₁.j ∘ ψ ∘ cY₁.k) U1 :=
    cS₁.hj.comp (hψ.1.comp_continuousOn (cY₁.hk.mono (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; exact cY₁.hm (hW₁sub hw.1).1.1)))
      (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; show ψ (cY₁.k (cY₁.j w)) ∈ cS₁.U; rw [cY₁.hl (hW₁sub hw.1).1.1]; exact (hW₁sub hw.1).2.1)
  have hfi11 : InjOn (cS₁.j ∘ ψ ∘ cY₁.k) U1 := by
    rintro _ ⟨w₁, ⟨hw₁, hw₁I⟩, rfl⟩ _ ⟨w₂, ⟨hw₂, hw₂I⟩, rfl⟩ he
    dsimp only [Function.comp_apply] at he
    rw [cY₁.hl (hW₁sub hw₁.1).1.1, cY₁.hl (hW₁sub hw₂.1).1.1] at he
    rw [hinj_int hw₁I hw₂I (cS₁.injOn_j (hW₁sub hw₁.1).2.1 (hW₁sub hw₂.1).2.1 he)]
  have hmap11 : MapsTo (cS₁.j ∘ ψ ∘ cY₁.k) U1 US := by
    rintro _ ⟨w, ⟨⟨hw1, hwS⟩, hwI⟩, rfl⟩
    show cS₁.j (ψ (cY₁.k (cY₁.j w))) ∈ US
    rw [cY₁.hl (hW₁sub hw1).1.1]
    exact ⟨ψ w, ⟨hwS, hmaps_int hwI⟩, rfl⟩
  have hfcS : ContinuousOn (cS₂.j ∘ cS₁.k) US :=
    cS₂.hj.comp (cS₁.hk.mono (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; exact cS₁.hm (hWSsub hw).1))
      (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; show cS₁.k (cS₁.j w) ∈ cS₂.U; rw [cS₁.hl (hWSsub hw).1]; exact (hWSsub hw).2)
  have hfiS : InjOn (cS₂.j ∘ cS₁.k) US := by
    rintro _ ⟨w₁, ⟨hw₁, _⟩, rfl⟩ _ ⟨w₂, ⟨hw₂, _⟩, rfl⟩ he
    dsimp only [Function.comp_apply] at he
    rw [cS₁.hl (hWSsub hw₁).1, cS₁.hl (hWSsub hw₂).1] at he
    rw [cS₂.injOn_j (hWSsub hw₁).2 (hWSsub hw₂).2 he]
  have hz2_in : cY₂.j y₁ ∈ U2 := ⟨y₁, ⟨⟨⟨hy₁W₂, hy₁W₁⟩, hψy₁WS⟩, hy₁I⟩, rfl⟩
  have hz1_in : cY₁.j y₁ ∈ U1 := ⟨y₁, ⟨⟨hy₁W₁, hψy₁WS⟩, hy₁I⟩, rfl⟩
  have hcomp1 := isPosLocal_comp hU1_open hfc11 hfi11 hmap11.image_subset hfcS hfiS hz1_in
  have hev1 : ((cS₂.j ∘ cS₁.k) ∘ (cS₁.j ∘ ψ ∘ cY₁.k)) =ᶠ[𝓝 (cY₁.j y₁)] (cS₂.j ∘ ψ ∘ cY₁.k) := by
    filter_upwards [hU1_open.mem_nhds hz1_in] with z hz
    obtain ⟨w, ⟨⟨hw1, hwS⟩, _⟩, rfl⟩ := hz
    show cS₂.j (cS₁.k (cS₁.j (ψ (cY₁.k (cY₁.j w))))) = cS₂.j (ψ (cY₁.k (cY₁.j w)))
    rw [cY₁.hl (hW₁sub hw1).1.1, cS₁.hl (hWSsub hwS).1]
  rw [isPosLocal_congr hev1] at hcomp1
  have hcomp1' : IsPosLocal (cS₂.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁) ↔
      (IsPosLocal (cS₁.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁) ↔ IsPosLocal (cS₂.j ∘ cS₁.k) (cS₁.j (ψ y₁))) := by
    have h1' : IsPosLocal (cS₂.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁) ↔
        (IsPosLocal (cS₂.j ∘ cS₁.k) (cS₁.j (ψ y₁)) ↔ IsPosLocal (cS₁.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁)) := by
      simpa [cY₁.hl (hW₁sub hy₁W₁).1.1] using hcomp1
    exact h1'.trans iff_comm
  have hfc12 : ContinuousOn (cS₂.j ∘ ψ ∘ cY₁.k) U1 :=
    cS₂.hj.comp (hψ.1.comp_continuousOn (cY₁.hk.mono (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; exact cY₁.hm (hW₁sub hw.1).1.1)))
      (by rintro _ ⟨w, ⟨hw, _⟩, rfl⟩; show ψ (cY₁.k (cY₁.j w)) ∈ cS₂.U; rw [cY₁.hl (hW₁sub hw.1).1.1]; exact (hW₁sub hw.1).2.2)
  have hfi12 : InjOn (cS₂.j ∘ ψ ∘ cY₁.k) U1 := by
    rintro _ ⟨w₁, ⟨hw₁, hw₁I⟩, rfl⟩ _ ⟨w₂, ⟨hw₂, hw₂I⟩, rfl⟩ he
    dsimp only [Function.comp_apply] at he
    rw [cY₁.hl (hW₁sub hw₁.1).1.1, cY₁.hl (hW₁sub hw₂.1).1.1] at he
    rw [hinj_int hw₁I hw₂I (cS₂.injOn_j (hW₁sub hw₁.1).2.2 (hW₁sub hw₂.1).2.2 he)]
  have hcomp2 := isPosLocal_comp hU2_open hfc21 hfi21 hmap21.image_subset hfc12 hfi12 hz2_in
  have hev2 : ((cS₂.j ∘ ψ ∘ cY₁.k) ∘ (cY₁.j ∘ cY₂.k)) =ᶠ[𝓝 (cY₂.j y₁)] (cS₂.j ∘ ψ ∘ cY₂.k) := by
    filter_upwards [hU2_open.mem_nhds hz2_in] with z hz
    obtain ⟨w, ⟨⟨⟨hw2, hw1⟩, _⟩, _⟩, rfl⟩ := hz
    show cS₂.j (ψ (cY₁.k (cY₁.j (cY₂.k (cY₂.j w))))) = cS₂.j (ψ (cY₂.k (cY₂.j w)))
    rw [cY₂.hl (hW₂sub hw2).1.2, cY₁.hl (hW₁sub hw1).1.1]
  rw [isPosLocal_congr hev2] at hcomp2
  have hcomp2' : IsPosLocal (cS₂.j ∘ ψ ∘ cY₂.k) (cY₂.j y₁) ↔
      (IsPosLocal (cY₁.j ∘ cY₂.k) (cY₂.j y₁) ↔ IsPosLocal (cS₂.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁)) := by
    have h2' : IsPosLocal (cS₂.j ∘ ψ ∘ cY₂.k) (cY₂.j y₁) ↔
        (IsPosLocal (cS₂.j ∘ ψ ∘ cY₁.k) (cY₁.j y₁) ↔ IsPosLocal (cY₁.j ∘ cY₂.k) (cY₂.j y₁)) := by
      simpa [cY₂.hl (hW₂sub hy₁W₂).1.2] using hcomp2
    exact h2'.trans iff_comm
  have hiff : cutChartPos cY₂ cS₂ ψ y ↔ (chartPos cY₂ cY₁ y ↔ (cutChartPos cY₁ cS₁ ψ y ↔ chartPos cS₁ cS₂ (ψ y))) := by
    rw [hc22, hc21, hc11, hcS, hcomp2', hcomp1']
  unfold cutChartSign chartSign
  by_cases a1 : chartPos cY₂ cY₁ y <;> by_cases a2 : cutChartPos cY₁ cS₁ ψ y <;> by_cases a3 : chartPos cS₁ cS₂ (ψ y) <;>
    simp [hiff, a1, a2, a3] <;> decide

/-- Pullback of `w1 AS` along a cutting `ψ : Y → S` differs from `w1 AY` by the coboundary of
`cutOrientDiff AY AS ψ` near the diagonal. -/
theorem cohRel_w1_cut_explicit (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (AY : SurfAtlas Y) (AS : SurfAtlas S) :
    ∃ N : Set (Y × Y), NearDiag N ∧ ∀ y₁ y₂ : Y, (y₁, y₂) ∈ N →
      w1 AS (ψ y₁) (ψ y₂) - w1 AY y₁ y₂ = cutOrientDiff AY AS ψ y₂ - cutOrientDiff AY AS ψ y₁ := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hloc : ∀ y : Y, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧
      ∀ y₁ ∈ W, ∀ y₂ ∈ W,
        w1 AS (ψ y₁) (ψ y₂) - w1 AY y₁ y₂ = cutOrientDiff AY AS ψ y₂ - cutOrientDiff AY AS ψ y₁ := by
    intro y
    let cY := AY.chart (AY.idx y)
    let cS := AS.chart (AS.idx (ψ y))
    obtain ⟨WY, hWYo, hyWY, hWYsub, hWY⟩ := w1_eq_chartSign_sub AY cY (AY.mem_chart y)
    obtain ⟨WS, hWSo, hψyWS, hWSsub, hWS⟩ := w1_eq_chartSign_sub AS cS (AS.mem_chart (ψ y))
    obtain ⟨r, -, -, -, hWo, hyW, hWsub, ⟨y₀, hy₀W, hy₀I⟩, hWconn⟩ :=
      cY.exists_ball_nbhd (hWYo.inter (hWSo.preimage hψ.1)) ⟨hyWY, hψyWS⟩ (fun w hw => hWYsub hw.1)
    set W := cY.U ∩ cY.j ⁻¹' ball (cY.j y) r
    obtain ⟨NY, hNY, hcocY⟩ := isCoc_w1 hY AY
    obtain ⟨NS, hNS, hcocS⟩ := isCoc_w1 hS AS
    obtain ⟨U1a, hU1a, U1b, hU1b, hU1ab⟩ := mem_nhds_prod_iff.mp (hNY y)
    obtain ⟨V1a, hV1a, V1b, hV1b, hV1ab⟩ := mem_nhds_prod_iff.mp (hNS (ψ y))
    let W' : Set Y := W ∩ (interior U1a ∩ interior U1b) ∩ ψ ⁻¹' (interior V1a ∩ interior V1b)
    have hW'o : IsOpen W' := (hWo.inter (isOpen_interior.inter isOpen_interior)).inter
      ((isOpen_interior.inter isOpen_interior).preimage hψ.1)
    have hyW' : y ∈ W' := ⟨⟨hyW, mem_interior_iff_mem_nhds.mpr hU1a, mem_interior_iff_mem_nhds.mpr hU1b⟩,
      mem_interior_iff_mem_nhds.mpr hV1a, mem_interior_iff_mem_nhds.mpr hV1b⟩
    refine ⟨W', hW'o, hyW', fun y₁ hy₁ y₂ hy₂ => ?_⟩
    have hY12 : w1 AY y₁ y₂ = w1 AY y y₂ - w1 AY y y₁ := by
      have h1 : (y, y₁) ∈ NY := hU1ab ⟨interior_subset hyW'.1.2.1, interior_subset hy₁.1.2.2⟩
      have h2 : (y₁, y₂) ∈ NY := hU1ab ⟨interior_subset hy₁.1.2.1, interior_subset hy₂.1.2.2⟩
      have h3 : (y, y₂) ∈ NY := hU1ab ⟨interior_subset hyW'.1.2.1, interior_subset hy₂.1.2.2⟩
      exact eq_sub_of_add_eq' (hcocY y y₁ y₂ h1 h2 h3)
    have hS12 : w1 AS (ψ y₁) (ψ y₂) = w1 AS (ψ y) (ψ y₂) - w1 AS (ψ y) (ψ y₁) := by
      have h1 : (ψ y, ψ y₁) ∈ NS := hV1ab ⟨interior_subset hyW'.2.1, interior_subset hy₁.2.2⟩
      have h2 : (ψ y₁, ψ y₂) ∈ NS := hV1ab ⟨interior_subset hy₁.2.1, interior_subset hy₂.2.2⟩
      have h3 : (ψ y, ψ y₂) ∈ NS := hV1ab ⟨interior_subset hyW'.2.1, interior_subset hy₂.2.2⟩
      exact eq_sub_of_add_eq' (hcocS (ψ y) (ψ y₁) (ψ y₂) h1 h2 h3)
    rw [hY12, hS12,
      hWY y₁ (hWsub hy₁.1.1).1, hWY y₂ (hWsub hy₂.1.1).1,
      hWS (ψ y₁) (hWsub hy₁.1.1).2, hWS (ψ y₂) (hWsub hy₂.1.1).2]
    have hconst : cutChartSign cY cS ψ y₁ = cutChartSign cY cS ψ y₂ := by
      have h1 := cutChartPos_iff_of_int hψ hF hWo hy₁.1.1 hy₀W hy₀I
        (fun w hw => ⟨hWYsub (hWsub hw).1, hWSsub (hWsub hw).2⟩) hWconn
      have h2 := cutChartPos_iff_of_int hψ hF hWo hy₂.1.1 hy₀W hy₀I
        (fun w hw => ⟨hWYsub (hWsub hw).1, hWSsub (hWsub hw).2⟩) hWconn
      dsimp only [cutChartSign, cS]
      by_cases hp : IsPosLocal ((AS.chart (AS.idx (ψ y))).j ∘ ψ ∘ cY.k) (cY.j y₀) <;>
        simp only [h1, h2, hp, ↓reduceIte]
    have hch1 := cutChartSign_change hψ hF (hWYsub (hWsub hy₁.1.1).1) (AY.mem_chart y₁)
      (hWSsub (hWsub hy₁.1.1).2) (AS.mem_chart (ψ y₁))
    have hch2 := cutChartSign_change hψ hF (hWYsub (hWsub hy₂.1.1).1) (AY.mem_chart y₂)
      (hWSsub (hWsub hy₂.1.1).2) (AS.mem_chart (ψ y₂))
    have hsym1 := chartSign_symm (AY.mem_chart y₁) (hWYsub (hWsub hy₁.1.1).1)
    have hsym2 := chartSign_symm (AY.mem_chart y₂) (hWYsub (hWsub hy₂.1.1).1)
    unfold cutOrientDiff
    rw [hch1, hch2, hsym1, hsym2, hconst]
    have hneg : ∀ a : ZMod 2, -a = a := fun a => by fin_cases a <;> rfl
    simp only [sub_eq_add_neg, hneg]
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]
  choose W hWo hyW hW using hloc
  refine ⟨⋃ y : Y, W y ×ˢ W y, fun y =>
    Filter.mem_of_superset ((hWo y).prod (hWo y) |>.mem_nhds ⟨hyW y, hyW y⟩)
      (subset_iUnion (fun w => W w ×ˢ W w) y), fun y₁ y₂ hpair => ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := mem_iUnion.mp hpair
  exact hW y y₁ hy₁ y₂ hy₂

/-- Pullback of `w1 AS` along a cutting `ψ : Y → S` is cohomologous to `w1 AY`. -/
theorem cohRel_w1_cut (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (AY : SurfAtlas Y) (AS : SurfAtlas S) :
    CohRel (pbk ψ (w1 AS)) (w1 AY) := by
  obtain ⟨N, hN, hdiff⟩ := cohRel_w1_cut_explicit hY hS hψ hF AY AS
  refine ⟨fun y => cutOrientDiff AY AS ψ y, N, hN, fun y₁ y₂ h => ?_⟩
  have h1 := hdiff y₁ y₂ h
  unfold pbk
  linear_combination h1

/-- Away from `ψ ⁻¹' F`, `cutOrientDiff AY AS ψ y` equals the difference between the boundary
cuff signs of locally matching parameterizations of `bd Y` and `bd S`! -/
theorem cutOrientDiff_cuff (hY : IsSurface Y) (hS : IsSurface S) {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {CY : Set Y} {CS : Set S} (hCY : CY ⊆ bd Y) (hCS : CS ⊆ bd S)
    (φY : Circle ≃ₜ CY) (φS : Circle ≃ₜ CS) {y : Y} (hyC : y ∈ CY) (hyF : ψ y ∉ F)
    {u₀ v₀ δ : ℝ} (hδ : 0 < δ) (hsgn : Bool)
    (hmatch : ∀ t ∈ Icc (-δ) δ, ψ (φY (ee (u₀ + t))).1 = (φS (ee (v₀ + if hsgn then t else -t))).1)
    (hy0 : (φY (ee u₀)).1 = y) :
    cuffSign AS φS (ψ y) - cuffSign AY φY y =
      cutOrientDiff AY AS ψ y + (if hsgn then 0 else 1) := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  have hψyC : ψ y ∈ CS := by
    have h0 := hmatch 0 ⟨by linarith, hδ.le⟩
    simp only [ite_self, neg_zero, add_zero, hy0] at h0
    rw [h0]; exact (φS _).2
  have hv0 : (φS (ee v₀)).1 = ψ y := by
    have h0 := hmatch 0 ⟨by linarith, hδ.le⟩
    simp only [ite_self, neg_zero, add_zero, hy0] at h0
    exact h0.symm
  -- Build the homeomorphism `eF : ψ ⁻¹' Fᶜ ≃ₜ Fᶜ` induced by `ψ`:
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  have hbij : Bijective (Fᶜ.restrictPreimage ψ) := by
    refine ⟨fun a b h => Subtype.ext (hψ.2.2.1 a.2 b.2 (congrArg Subtype.val h)), fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨w, rfl⟩ := hψ.2.1 x
    exact ⟨⟨w, hx⟩, rfl⟩
  let eF : (ψ ⁻¹' Fᶜ : Set Y) ≃ₜ (Fᶜ : Set S) :=
    (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨hψ.1.restrictPreimage, hcl.restrictPreimage Fᶜ, hbij⟩).homeomorph
  let ψinv : S → Y := fun x => if hx : x ∈ Fᶜ then (eF.symm ⟨x, hx⟩).1 else y
  have hψ_ψinv : ∀ x ∈ Fᶜ, ψ (ψinv x) = x := fun x hx => by
    simp only [ψinv, dite_eq_left hx]
    exact congrArg Subtype.val (eF.apply_symm_apply ⟨x, hx⟩)
  have hψinv_ψ : ∀ w ∈ ψ ⁻¹' Fᶜ, ψinv (ψ w) = w := fun w hw => by
    have hx : ψ w ∈ Fᶜ := hw
    simp only [ψinv, dite_eq_left hx]
    have : eF ⟨w, hw⟩ = ⟨ψ w, hx⟩ := rfl
    rw [← this, eF.symm_apply_apply]
  have hψinv_cont : ContinuousOn ψinv Fᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : Fᶜ.domRestrict ψinv = fun x : (Fᶜ : Set S) => (eF.symm x).1 := by
      funext x; exact dite_eq_left x.2
    rw [heq]; exact continuous_subtype_val.comp eF.symm.continuous
  -- Shrink `cS := AS.chart (AS.idx (ψ y))` to a ball neighborhood `WS ⊆ cS.U ∩ Fᶜ` around `ψ y`:
  let cS := AS.chart (AS.idx (ψ y))
  obtain ⟨r, hr, hBO, -, hWSo, hψyWS, hWSsub, -, -⟩ :=
    cS.exists_ball_nbhd (cS.hU.inter hF.isOpen_compl) ⟨AS.mem_chart (ψ y), hyF⟩ (fun _ h => h.1)
  set WS : Set S := cS.U ∩ cS.j ⁻¹' ball (cS.j (ψ y)) r
  have hWS_F : WS ⊆ Fᶜ := fun x hx => (hWSsub hx).2
  have hWS_eq : cS.k '' (ball (cS.j (ψ y)) r ∩ halfPlane) = WS := by
    ext x; constructor
    · rintro ⟨z, ⟨hzb, hzh⟩, rfl⟩
      have hzk : cS.k z ∈ cS.U := cS.hk' ⟨hBO hzb, hzh⟩
      refine ⟨hzk, ?_⟩
      show cS.j (cS.k z) ∈ ball (cS.j (ψ y)) r
      rw [cS.hr ⟨hBO hzb, hzh⟩]; exact hzb
    · rintro ⟨hxU, hxb⟩
      exact ⟨cS.j x, ⟨hxb, (cS.hm hxU).2⟩, cS.hl hxU⟩
  -- Pull back `cS|_WS` along `ψ` to a `SurfChart Y` `cY'` around `y`!
  let cY' : SurfChart Y :=
    { U := ψ ⁻¹' WS
      O := ball (cS.j (ψ y)) r
      j := cS.j ∘ ψ
      k := ψinv ∘ cS.k
      hU := hWSo.preimage hψ.1
      hO := isOpen_ball
      hj := cS.hj.comp hψ.1.continuousOn (fun w hw => hw.1)
      hk := hψinv_cont.comp (cS.hk.mono (fun z hz => ⟨hBO hz.1, hz.2⟩))
        (fun z hz => hWS_F (hWS_eq ▸ ⟨z, hz, rfl⟩))
      hm := fun w hw => ⟨hw.2, (cS.hm hw.1).2⟩
      hk' := fun z hz => by
        show ψ (ψinv (cS.k z)) ∈ WS
        have hmWS : cS.k z ∈ WS := hWS_eq ▸ ⟨z, hz, rfl⟩
        rwa [hψ_ψinv _ (hWS_F hmWS)]
      hl := fun w hw => by
        show ψinv (cS.k (cS.j (ψ w))) = w
        rw [cS.hl hw.1, hψinv_ψ w (hWS_F hw)]
      hr := fun z hz => by
        show cS.j (ψ (ψinv (cS.k z))) = z
        have hmWS : cS.k z ∈ WS := hWS_eq ▸ ⟨z, hz, rfl⟩
        rw [hψ_ψinv _ (hWS_F hmWS), cS.hr ⟨hBO hz.1, hz.2⟩] }
  have hy_cY' : y ∈ cY'.U := hψyWS
  have hcut_pos : cutChartPos cY' cS ψ y := by
    refine ⟨cY'.U, cY'.hU, hy_cY', fun w hw => ⟨hw, hw.1⟩, fun y' hy' => ?_⟩
    have hz_open : IsOpen (ball (cS.j (ψ y)) r ∩ {z : ℂ | 0 < z.re}) :=
      isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    have hz_mem : cY'.j y' ∈ ball (cS.j (ψ y)) r ∩ {z : ℂ | 0 < z.re} :=
      ⟨(cY'.hm hy'.1).1, (cY'.not_mem_bd_iff hy'.1).mp hy'.2⟩
    have hev : (cS.j ∘ ψ ∘ cY'.k) =ᶠ[𝓝 (cY'.j y')] id := by
      filter_upwards [hz_open.mem_nhds hz_mem] with z hz
      exact cY'.hr ⟨hz.1, (show 0 < z.re from hz.2).le⟩
    rw [isPosLocal_congr hev]
    exact isPosLocal_id _
  have hcut_sign0 : cutChartSign cY' cS ψ y = 0 := by simp [cutChartSign, hcut_pos]
  have hch_cut := cutChartSign_change hψ hF hy_cY' (AY.mem_chart y) (AS.mem_chart (ψ y)) (AS.mem_chart (ψ y))
  rw [hcut_sign0, chartSign_refl (AS.mem_chart (ψ y)), add_zero, add_zero] at hch_cut
  obtain ⟨u₁, δY, hδY, hδY4, hu₁, hδYU, hmoY⟩ := cuff_im_mono_or_anti hCY φY hyC hy_cY'
  obtain ⟨v₁, δS, hδS, hδS4, hv₁, hδSU, hmoS⟩ := cuff_im_mono_or_anti hCS φS hψyC (AS.mem_chart (ψ y))
  obtain ⟨kY, hkY⟩ := ee_eq_iff.mp (φY.injective (Subtype.ext (hu₁.trans hy0.symm)))
  obtain ⟨kS, hkS⟩ := ee_eq_iff.mp (φS.injective (Subtype.ext (hv₁.trans hv0.symm)))
  have hφY_sh : ∀ t, (φY (ee (u₁ + t))).1 = (φY (ee (u₀ + t))).1 := fun t => by
    have : ee (u₁ + t) = ee (u₀ + t) := ee_eq_iff.mpr ⟨kY, by linarith⟩
    rw [this]
  have hφS_sh : ∀ t, (φS (ee (v₁ + t))).1 = (φS (ee (v₀ + t))).1 := fun t => by
    have : ee (v₁ + t) = ee (v₀ + t) := ee_eq_iff.mpr ⟨kS, by linarith⟩
    rw [this]
  set η := min δ (min δY δS)
  have hη : 0 < η := lt_min hδ (lt_min hδY hδS)
  have hη_δ : η ≤ δ := min_le_left _ _
  have hη_Y : η ≤ δY := (min_le_right _ _).trans (min_le_left _ _)
  have hη_S : η ≤ δS := (min_le_right _ _).trans (min_le_right _ _)
  have hmatch_im : ∀ t ∈ Icc (-η) η,
      (cY'.j (φY (ee (u₁ + t))).1).im = (cS.j (φS (ee (v₁ + if hsgn then t else -t))).1).im := by
    intro t ht
    rw [hφY_sh, hφS_sh]
    show (cS.j (ψ (φY (ee (u₀ + t))).1)).im = _
    rw [hmatch t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  have hnot_antiY : StrictAntiOn (fun t => (cY'.j (φY (ee (u₁ + t))).1).im) (Icc (-δY) δY) →
      ¬ cuffPos cY' φY y := by
    intro ha ⟨u₂, δ₂, hδ₂, hu₂, _, hm₂⟩
    obtain ⟨m, hm⟩ := ee_eq_iff.mp (φY.injective (Subtype.ext (hu₂.trans hu₁.symm)))
    have heq : ∀ t, (φY (ee (u₂ + t))).1 = (φY (ee (u₁ + t))).1 := fun t => by
      have : ee (u₂ + t) = ee (u₁ + t) := ee_eq_iff.mpr ⟨m, by linarith⟩; rw [this]
    set ρ := min δY δ₂
    have hρ : 0 < ρ := lt_min hδY hδ₂
    have h1 := hm₂ ⟨by linarith, hδ₂.le⟩ ⟨by linarith [min_le_right δY δ₂], min_le_right _ _⟩ hρ
    have h2 := ha ⟨by linarith, hδY.le⟩ ⟨by linarith [min_le_left δY δ₂], min_le_left _ _⟩ hρ
    have h0' : (φY (ee u₂)).1 = (φY (ee u₁)).1 := by simpa using heq 0
    change (cY'.j (φY (ee (u₂ + 0))).1).im < (cY'.j (φY (ee (u₂ + ρ))).1).im at h1
    change (cY'.j (φY (ee (u₁ + ρ))).1).im < (cY'.j (φY (ee (u₁ + 0))).1).im at h2
    rw [add_zero, h0', heq ρ] at h1; rw [add_zero] at h2; linarith
  have hnot_antiS : StrictAntiOn (fun t => (cS.j (φS (ee (v₁ + t))).1).im) (Icc (-δS) δS) →
      ¬ cuffPos cS φS (ψ y) := by
    intro ha ⟨v₂, δ₂, hδ₂, hv₂, _, hm₂⟩
    obtain ⟨m, hm⟩ := ee_eq_iff.mp (φS.injective (Subtype.ext (hv₂.trans hv₁.symm)))
    have heq : ∀ t, (φS (ee (v₂ + t))).1 = (φS (ee (v₁ + t))).1 := fun t => by
      have : ee (v₂ + t) = ee (v₁ + t) := ee_eq_iff.mpr ⟨m, by linarith⟩; rw [this]
    set ρ := min δS δ₂
    have hρ : 0 < ρ := lt_min hδS hδ₂
    have h1 := hm₂ ⟨by linarith, hδ₂.le⟩ ⟨by linarith [min_le_right δS δ₂], min_le_right _ _⟩ hρ
    have h2 := ha ⟨by linarith, hδS.le⟩ ⟨by linarith [min_le_left δS δ₂], min_le_left _ _⟩ hρ
    have h0' : (φS (ee v₂)).1 = (φS (ee v₁)).1 := by simpa using heq 0
    change (cS.j (φS (ee (v₂ + 0))).1).im < (cS.j (φS (ee (v₂ + ρ))).1).im at h1
    change (cS.j (φS (ee (v₁ + ρ))).1).im < (cS.j (φS (ee (v₁ + 0))).1).im at h2
    rw [add_zero, h0', heq ρ] at h1; rw [add_zero] at h2; linarith
  have hcuff_rel : cuffPos cS φS (ψ y) ↔ (if hsgn then cuffPos cY' φY y else ¬ cuffPos cY' φY y) := by
    have h0η : (0 : ℝ) ∈ Icc (-η) η := ⟨by linarith, hη.le⟩
    have hηη : η ∈ Icc (-η) η := ⟨by linarith, le_rfl⟩
    have hm0 := hmatch_im 0 h0η
    have hmη := hmatch_im η hηη
    cases hsgn
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_zero] at hm0 hmη ⊢
      rcases hmoY with hmY | haY <;> rcases hmoS with hmS | haS
      · exfalso
        have h1 := hmY ⟨by linarith, hδY.le⟩ ⟨by linarith, hη_Y⟩ hη
        have h2 := hmS ⟨by linarith, by linarith⟩ ⟨by linarith, hδS.le⟩ (show -η < 0 by linarith)
        change (cY'.j (φY (ee (u₁ + 0))).1).im < (cY'.j (φY (ee (u₁ + η))).1).im at h1
        change (cS.j (φS (ee (v₁ + -η))).1).im < (cS.j (φS (ee (v₁ + 0))).1).im at h2
        linarith
      · have h1 : cuffPos cY' φY y := ⟨u₁, δY, hδY, hu₁, hδYU, hmY⟩
        have h2 : ¬ cuffPos cS φS (ψ y) := hnot_antiS haS
        tauto
      · have h1 : ¬ cuffPos cY' φY y := hnot_antiY haY
        have h2 : cuffPos cS φS (ψ y) := ⟨v₁, δS, hδS, hv₁, hδSU, hmS⟩
        tauto
      · exfalso
        have h1 := haY ⟨by linarith, hδY.le⟩ ⟨by linarith, hη_Y⟩ hη
        have h2 := haS ⟨by linarith, by linarith⟩ ⟨by linarith, hδS.le⟩ (show -η < 0 by linarith)
        change (cY'.j (φY (ee (u₁ + η))).1).im < (cY'.j (φY (ee (u₁ + 0))).1).im at h1
        change (cS.j (φS (ee (v₁ + 0))).1).im < (cS.j (φS (ee (v₁ + -η))).1).im at h2
        linarith
    · simp only [↓reduceIte] at hm0 hmη ⊢
      rcases hmoY with hmY | haY <;> rcases hmoS with hmS | haS
      · exact iff_of_true ⟨v₁, δS, hδS, hv₁, hδSU, hmS⟩ ⟨u₁, δY, hδY, hu₁, hδYU, hmY⟩
      · exfalso
        have h1 := hmY ⟨by linarith, hδY.le⟩ ⟨by linarith, hη_Y⟩ hη
        have h2 := haS ⟨by linarith, hδS.le⟩ ⟨by linarith, hη_S⟩ hη
        change (cY'.j (φY (ee (u₁ + 0))).1).im < (cY'.j (φY (ee (u₁ + η))).1).im at h1
        change (cS.j (φS (ee (v₁ + η))).1).im < (cS.j (φS (ee (v₁ + 0))).1).im at h2
        linarith
      · exfalso
        have h1 := haY ⟨by linarith, hδY.le⟩ ⟨by linarith, hη_Y⟩ hη
        have h2 := hmS ⟨by linarith, hδS.le⟩ ⟨by linarith, hη_S⟩ hη
        change (cY'.j (φY (ee (u₁ + η))).1).im < (cY'.j (φY (ee (u₁ + 0))).1).im at h1
        change (cS.j (φS (ee (v₁ + 0))).1).im < (cS.j (φS (ee (v₁ + η))).1).im at h2
        linarith
      · exact iff_of_false (hnot_antiS haS) (hnot_antiY haY)
  have hsign_rel : cuffSignChart cS φS (ψ y) = cuffSignChart cY' φY y + (if hsgn then 0 else 1) := by
    unfold cuffSignChart
    cases hsgn <;> by_cases h : cuffPos cY' φY y <;> simp [hcuff_rel, h]
    rfl
  have hch_Y := cuffSignChart_change hCY φY hyC hy_cY' (AY.mem_chart y)
  have hY_eq : cuffSignChart (AY.chart (AY.idx y)) φY y =
      chartSign cY' (AY.chart (AY.idx y)) y + cuffSignChart cY' φY y := eq_add_of_sub_eq hch_Y
  have hsym := chartSign_symm (AY.mem_chart y) hy_cY'
  unfold cuffSign cutOrientDiff
  rw [hsign_rel, hY_eq, hch_cut, hsym]
  have hneg : ∀ a : ZMod 2, -a = a := fun a => by fin_cases a <;> rfl
  simp only [sub_eq_add_neg, hneg]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from rfl]

end Cutting

end GraphMinor.Surface

