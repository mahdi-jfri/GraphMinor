module

public import GraphMinor.Surface.PlaneOrientation
public import GraphMinor.Surface.Collar
public import GraphMinor.Surface.LocalCoh
public import GraphMinor.Surface.CutPieces

/-!
# Local orientation sign of planar maps and path integrals of local cocycles

This file provides two core primitives for surface orientation and cohomology:

1. **Local orientation sign (`IsPosLocal`)** of a continuous injective map `g : ℂ → ℂ` at a point
   `z₀`, defined by positivity of the winding number of `w ↦ g (z₀ + r * w)` around `g z₀` for
   small `r > 0`. Using `GM19.turn_eq_of_homotopy`, `PlaneOrientation.isPosParam_or_inv`,
   `PlaneOrientation.order_of_nested`, and `Collar.exists_disc_collar`, we prove:
   - independence of radius `r`,
   - local constancy on open domains (`isPosLocal_const_of_isPreconnected`),
   - the chain rule for open local homeomorphisms (`isPosLocal_comp`),
   - explicit values on identity, complex conjugation, and non-degenerate affine maps.

2. **Path integral (`cocInt`)** of a local cocycle `IsCoc φ` along a continuous path
   `γ : [0, 1] → X`: well-definedness from fine Riemann sums, additivity, coboundary formula,
   concatenation, reversal, homotopy/reparameterization invariance, and vanishing on loops in
   closed discs (`cocInt_disc_loop`, via `LocalCoh.exists_prim`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Metric Topology Filter Function GraphMinor.GM19

universe u v

/-! ### Small helpers for `Circle` and closed balls -/

/-- Normalize a non-zero complex number to `Circle`. -/
noncomputable def unitC (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨((‖z‖ : ℝ) : ℂ)⁻¹ * z, by
    show ((‖z‖ : ℝ) : ℂ)⁻¹ * z ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.mpr hz), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩

theorem norm_mul_unitC {z : ℂ} (hz : z ≠ 0) : ((‖z‖ : ℝ) : ℂ) * (unitC z hz : ℂ) = z := by
  show ((‖z‖ : ℝ) : ℂ) * (((‖z‖ : ℝ) : ℂ)⁻¹ * z) = z
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)), one_mul]

/-- A closed ball of positive radius in `ℂ` is a closed disc with boundary the sphere. -/
theorem isClosedDisc_closedBall_of_pos (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    IsClosedDisc (closedBall z₀ r) ∧ discBd (closedBall z₀ r) = sphere z₀ r := by
  let f : ℂ → ℂ := fun z => z₀ + (r : ℂ) * z
  let f' : ℂ → ℂ := fun w => ((r : ℂ)⁻¹) * (w - z₀)
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have himg : f '' closedBall 0 1 = closedBall z₀ r := by
    ext w
    simp only [mem_image, mem_closedBall, dist_eq_norm, sub_zero, f]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    · intro hw
      refine ⟨f' w, ?_, by simp [f', hr0]⟩
      simp only [f', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      rw [inv_mul_le_iff₀ hr]
      simpa using hw
  have hsph : f '' sphere 0 1 = sphere z₀ r := by
    ext w
    simp only [mem_image, mem_sphere, dist_eq_norm, sub_zero, f]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
    · intro hw
      refine ⟨f' w, ?_, by simp [f', hr0]⟩
      simp only [f', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hw]
      exact inv_mul_cancel₀ hr.ne'
  obtain ⟨hD, hB⟩ := isClosedDisc_closedBall.1.image (f := f) (f' := f')
    (by fun_prop) (by fun_prop) (fun z _ => by simp [f, f', hr0])
  rw [himg] at hD hB
  rw [isClosedDisc_closedBall.2, hsph] at hB
  exact ⟨hD, hB⟩

/-- Image of a closed ball under a continuous injective map is a closed disc with boundary the image
of the sphere, and `g z₀` lies in `discInt`. -/
private theorem isClosedDisc_image_ball {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (closedBall z₀ r)) (hi : InjOn g (closedBall z₀ r)) :
    IsClosedDisc (g '' closedBall z₀ r) ∧
      discBd (g '' closedBall z₀ r) = g '' sphere z₀ r ∧
      g z₀ ∈ discInt (g '' closedBall z₀ r) ∧
      range (fun w : Circle => g (z₀ + (r : ℂ) * w)) = discBd (g '' closedBall z₀ r) := by
  classical
  obtain ⟨hB, hBs⟩ := isClosedDisc_closedBall_of_pos z₀ hr
  have : CompactSpace (closedBall z₀ r) := isCompact_iff_compactSpace.mp (isCompact_closedBall z₀ r)
  let f : closedBall z₀ r → ℂ := (closedBall z₀ r).domRestrict g
  have hfc : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  have hfi : Injective f := fun a b h => Subtype.ext (hi a.2 b.2 h)
  let e : closedBall z₀ r ≃ₜ range f := (hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  have hrange : range f = g '' closedBall z₀ r := by
    ext y; exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, hy⟩ => ⟨⟨a, ha⟩, hy⟩⟩
  let g' : ℂ → ℂ := fun y => if hy : y ∈ range f then (e.symm ⟨y, hy⟩).1 else 0
  have hg'c : ContinuousOn g' (g '' closedBall z₀ r) := by
    rw [← hrange, continuousOn_iff_continuous_domRestrict]
    have : (range f).domRestrict g' = fun y : range f => (e.symm y).1 := by
      funext y; show (if hy : y.1 ∈ range f then (e.symm ⟨y.1, hy⟩).1 else 0) = _
      rw [dite_eq_left y.2]
    rw [this]; exact continuous_subtype_val.comp e.symm.continuous
  have hg'l : LeftInvOn g' g (closedBall z₀ r) := fun z hz => by
    have hmem : g z ∈ range f := ⟨⟨z, hz⟩, rfl⟩
    show (if hy : g z ∈ range f then (e.symm ⟨g z, hy⟩).1 else 0) = z
    rw [dite_eq_left hmem]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  obtain ⟨hD, hDb⟩ := hB.image hc hg'c hg'l
  rw [hBs] at hDb
  have hz0_int : g z₀ ∈ discInt (g '' closedBall z₀ r) := by
    refine ⟨mem_image_of_mem g (mem_closedBall_self hr.le), fun hmem => ?_⟩
    rw [hDb] at hmem
    obtain ⟨z, hz, he⟩ := hmem
    have h1 := hi (sphere_subset_closedBall hz) (mem_closedBall_self hr.le) he
    subst h1
    rw [mem_sphere_iff_norm, sub_self, norm_zero] at hz
    linarith
  have hφr : range (fun w : Circle => g (z₀ + (r : ℂ) * w)) = discBd (g '' closedBall z₀ r) := by
    rw [hDb]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨z₀ + (r : ℂ) * w, ?_, rfl⟩
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]
    · rintro ⟨z, hz, rfl⟩
      have hzn : ‖z - z₀‖ = r := by simpa [mem_sphere, dist_eq_norm] using hz
      have hz0 : z - z₀ ≠ 0 := by intro h; simp [h] at hzn; linarith
      refine ⟨unitC (z - z₀) hz0, ?_⟩
      show g (z₀ + (r : ℂ) * (unitC (z - z₀) hz0 : ℂ)) = g z
      rw [← hzn, norm_mul_unitC hz0]; ring_nf
  exact ⟨hD, hDb, hz0_int, hφr⟩

/-! ### Winding homotopies and circle homeomorphisms -/

/-- Winding is unchanged along a continuous family of loops that avoids a moving point. -/
theorem wind_eq_of_family {F : ℝ → Circle → ℂ} (hF : Continuous fun q : ℝ × Circle => F q.1 q.2)
    {z : ℝ → ℂ} (hz : Continuous z) (hne : ∀ u w, F u w ≠ z u) (a b : ℝ) :
    wind (F a) (z a) = wind (F b) (z b) := by
  let H : ℝ → ℝ → ℂ := fun u t => F u (Circle.exp t) - z u
  have hH : Continuous fun q : ℝ × ℝ => H q.1 q.2 :=
    (hF.comp (continuous_fst.prodMk (Circle.exp.continuous.comp continuous_snd))).sub
      (hz.comp continuous_fst)
  have h0 : ∀ u t, H u t ≠ 0 := fun u t => sub_ne_zero.mpr (hne u _)
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, exp_add_two_pi']
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := by
    intro t
    obtain ⟨t', ht', n, rfl⟩ := exists_mem_period t
    exact ⟨_, ht', fun u => ((hper u).sub_zsmul_eq n).symm⟩
  have hh := turn_eq_of_homotopy hH h0 isCompact_Icc hv (s := 0) (t := 2 * Real.pi)
    (fun u => by
      have hp := hper u 0
      rw [zero_add] at hp
      exact hp.symm) a b
  simpa only [wind, H] using hh

/-- An orientation-preserving homeomorphism of the circle has a strictly increasing lift of period
`2π`. -/
theorem PreservesCircleOrientation.exists_lift_2pi {h : Circle ≃ₜ Circle}
    (hh : PreservesCircleOrientation h) :
    ∃ l : ℝ → ℝ, Continuous l ∧ StrictMono l ∧ l (2 * Real.pi) = l 0 + 2 * Real.pi ∧
      ∀ x, h (Circle.exp x) = Circle.exp (l x) := by
  obtain ⟨l, hl_c, hl_m, hl_e⟩ := hh
  have hpi := Real.pi_pos
  have heq : Circle.exp (l (2 * Real.pi)) = Circle.exp (l 0) := by
    rw [← hl_e, ← hl_e, Circle.exp_two_pi, Circle.exp_zero]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have hpos : (0 : ℝ) < m := by
    have hlt : l 0 < l (2 * Real.pi) := hl_m (by positivity)
    nlinarith
  have hm1 : 1 ≤ m := by exact_mod_cast hpos
  have hm_eq : m = 1 := by
    by_contra hne
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have hmem : l 0 + 2 * Real.pi ∈ Ioo (l 0) (l (2 * Real.pi)) := by
      rw [hm]; constructor <;> nlinarith
    obtain ⟨x, hx, hxl⟩ := intermediate_value_Ioo (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      hl_c.continuousOn hmem
    have hcx : h (Circle.exp x) = h (Circle.exp 0) := by
      rw [hl_e, hl_e, hxl, exp_add_two_pi']
    have hxx := h.injective hcx
    exact circle_exp_ne hx.1.ne' (by rw [sub_zero, abs_of_pos hx.1]; exact hx.2) hxx
  refine ⟨l, hl_c, hl_m, ?_, hl_e⟩
  rw [hm, hm_eq]; ring

/-- Precomposing with an orientation-preserving circle homeomorphism leaves `wind` unchanged. -/
theorem wind_comp_preserves {φ : Circle → ℂ} (hφ : Continuous φ) {z : ℂ} (h0 : ∀ w, φ w ≠ z)
    {h : Circle ≃ₜ Circle} (hh : PreservesCircleOrientation h) :
    wind (φ ∘ h) z = wind φ z := by
  obtain ⟨l, hl_c, -, hl_per, hl_e⟩ := hh.exists_lift_2pi
  let g : ℝ → ℂ := fun t => φ (Circle.exp t) - z
  have hg : Continuous g := (hφ.comp Circle.exp.continuous).sub continuous_const
  have hg0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.mpr (h0 _)
  have hg_per : ∀ t, g (t + 2 * Real.pi) = g t := fun t => by simp [g]
  have hcomp : (fun t => (φ ∘ h) (Circle.exp t) - z) = fun t => g (l t) := by
    funext t; simp [g, hl_e]
  unfold wind
  rw [hcomp, turn_comp hg hg0 hl_c, hl_per]
  have hp := turn_period hg hg0 hg_per (l 0) 0
  simpa using hp

/-- If `h` is a circle homeomorphism preserving `CircleCyclic`, then `PreservesCircleOrientation h`. -/
theorem preservesCircleOrientation_of_cyclic {h : Circle ≃ₜ Circle}
    (hc : ∀ a b c : Circle, CircleCyclic a b c → CircleCyclic (h a) (h b) (h c)) :
    PreservesCircleOrientation h := by
  have hpi := Real.pi_pos
  let φid : Circle ≃ₜ (univ : Set Circle) := (Homeomorph.Set.univ Circle).symm
  obtain ⟨m, hm_c, hm_e⟩ := exists_lift φid
    (h.continuous.comp continuous_ee).continuousOn (fun _ _ => mem_univ _)
  have hm_ee : ∀ u ∈ Icc (0 : ℝ) 1, ee (m u) = h (ee u) := fun u hu => by
    have := hm_e u hu
    simpa [φid] using this
  have hee01 : ee (1 : ℝ) = ee 0 := by simpa using ee_add_one 0
  have h_inj : InjOn (fun u => ee (m u)) (Ico 0 1) := by
    intro x hx y hy he
    dsimp only at he
    rw [hm_ee x (Ico_subset_Icc_self hx), hm_ee y (Ico_subset_Icc_self hy)] at he
    obtain ⟨k, hk⟩ := ee_eq_iff.mp (h.injective he)
    have h1 : (-1 : ℝ) < k := by linarith [hx.1, hy.2]
    have h2 : (k : ℝ) < 1 := by linarith [hx.2, hy.1]
    have hk0 : k = 0 := by
      have : -1 < k := by exact_mod_cast h1
      have : k < 1 := by exact_mod_cast h2
      omega
    rw [hk, hk0]; simp
  rcases lift_mono_loop hm_c h_inj with hmono | hanti
  · have hm01 : ee (m 1) = ee (m 0) := by
      rw [hm_ee 1 (by simp), hm_ee 0 (by simp), hee01]
    obtain ⟨k, hk⟩ := ee_eq_iff.mp hm01
    have hpos : (0 : ℝ) < k := by
      have := hmono (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) zero_lt_one
      linarith
    have hk1 : 1 ≤ k := by exact_mod_cast hpos
    have hk_eq : k = 1 := by
      by_contra hne
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      obtain ⟨x, hx, hxm⟩ := intermediate_value_Ioo zero_le_one hm_c
        (show m 0 + 1 ∈ Ioo (m 0) (m 1) by rw [hk]; constructor <;> linarith)
      have he : ee (m x) = ee (m 0) := by rw [hxm, ee_add_one]
      have := h_inj ⟨hx.1.le, hx.2⟩ ⟨le_rfl, zero_lt_one⟩ he
      linarith [hx.1]
    have hper : m 1 = m 0 + 1 := by rw [hk, hk_eq]; norm_num
    obtain ⟨h', hh', hh'_e⟩ := exists_circle_homeo hm_c hmono hper
    have heq : h' = h := by
      ext z
      obtain ⟨x, rfl⟩ := ee_surjective z
      have hu : Int.fract x ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
      have hfx : ee (Int.fract x) = ee x := ee_eq_iff.mpr ⟨-⌊x⌋, by rw [Int.fract]; push_cast; ring⟩
      rw [← hfx, hh'_e _ (Ico_subset_Icc_self hu), hm_ee _ (Ico_subset_Icc_self hu)]
    exact heq ▸ hh'
  · exfalso
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have h13 : (1 / 3 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h23 : (2 / 3 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have hm01 : ee (m 1) = ee (m 0) := by
      rw [hm_ee 1 h1, hm_ee 0 h0, hee01]
    obtain ⟨k, hk⟩ := ee_eq_iff.mp hm01
    have hneg : (k : ℝ) < 0 := by
      have := hanti h0 h1 zero_lt_one
      linarith
    have hk_le : k ≤ -1 := by
      have : k < 0 := by exact_mod_cast hneg
      omega
    have hk_eq : k = -1 := by
      by_contra hne
      have hk2 : (k : ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
      obtain ⟨x, hx, hxm⟩ := intermediate_value_Ioo' zero_le_one hm_c
        (show m 0 - 1 ∈ Ioo (m 1) (m 0) by rw [hk]; constructor <;> linarith)
      have he : ee (m x) = ee (m 0) := by
        rw [hxm]; exact ee_eq_iff.mpr ⟨-1, by push_cast; ring⟩
      have := h_inj ⟨hx.1.le, hx.2⟩ ⟨le_rfl, zero_lt_one⟩ he
      linarith [hx.1]
    have hper : m 1 = m 0 - 1 := by rw [hk, hk_eq]; push_cast; ring
    have hcyc0 : CircleCyclic (ee 0) (ee (1 / 3)) (ee (2 / 3)) :=
      circleCyclic_exp_of_lt (by nlinarith) (by nlinarith) (by nlinarith)
    have hcyc1 := hc _ _ _ hcyc0
    rw [← hm_ee 0 h0, ← hm_ee (1 / 3) h13, ← hm_ee (2 / 3) h23] at hcyc1
    have hlt1 : m (2 / 3) < m (1 / 3) := hanti h13 h23 (by norm_num)
    have hlt2 : m (1 / 3) < m 0 := hanti h0 h13 (by norm_num)
    have hlt3 : m 1 < m (2 / 3) := hanti h23 h1 (by norm_num)
    have hcyc_rev : CircleCyclic (ee (m 0)) (ee (m (2 / 3))) (ee (m (1 / 3))) := by
      have e0 : ee (m 0) = ee (m 0 - 1) := ee_eq_iff.mpr ⟨1, by ring⟩
      rw [e0]
      exact circleCyclic_exp_of_lt (by nlinarith) (by nlinarith) (by nlinarith)
    exact not_circleCyclic_both hcyc1 hcyc_rev

/-! ### Local orientation sign `IsPosLocal` in `ℂ` -/

/-- Winding of a positively oriented round circle `w ↦ z₀ + r * w` around `z₀` is `2π`. -/
theorem wind_circle_pos (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    wind (fun w : Circle => z₀ + (r : ℂ) * w) z₀ = 2 * Real.pi := by
  unfold wind
  have he : (fun t => z₀ + (r : ℂ) * ((Circle.exp t : Circle) : ℂ) - z₀) =
      fun t => (r : ℂ) * ((Circle.exp t : Circle) : ℂ) := by funext t; ring
  rw [he]
  have hA : IsAngle (fun t => (r : ℂ) * ((Circle.exp t : Circle) : ℂ)) (fun t => t) := by
    refine ⟨continuous_id, fun t => ?_⟩
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Circle.coe_exp]
  rw [hA.turn_eq (fun t => mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Circle.coe_ne_zero _))]
  ring

/-- `g : ℂ → ℂ` is locally orientation-preserving at `z₀` if on some small closed ball around `z₀`,
`g` is continuous and injective and the image circle winds positively around `g z₀`. -/
def IsPosLocal (g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ r > 0, ContinuousOn g (closedBall z₀ r) ∧ InjOn g (closedBall z₀ r) ∧
    0 < wind (fun w : Circle => g (z₀ + (r : ℂ) * w)) (g z₀)

/-- On any closed ball where `g` is continuous and injective, the image of the boundary circle has
non-zero winding around `g z₀`. -/
theorem wind_ne_zero_of_ball {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (closedBall z₀ r)) (hi : InjOn g (closedBall z₀ r)) :
    wind (fun w : Circle => g (z₀ + (r : ℂ) * w)) (g z₀) ≠ 0 := by
  obtain ⟨hD, -, hz0_int, hφr⟩ := isClosedDisc_image_ball hr hc hi
  let φ : Circle → ℂ := fun w => g (z₀ + (r : ℂ) * w)
  have hsub : ∀ w : Circle, z₀ + (r : ℂ) * w ∈ closedBall z₀ r := fun w => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]
  have hφc : Continuous φ := hc.comp_continuous (by fun_prop) hsub
  have hφi : Injective φ := fun a b h => by
    have h1 := hi (hsub a) (hsub b) h
    have h2 : (r : ℂ) * (a : ℂ) = (r : ℂ) * (b : ℂ) := by linear_combination h1
    exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') h2)
  have hoff : ∀ w, φ w ≠ g z₀ := fun w h =>
    hz0_int.2 (hφr ▸ (h ▸ mem_range_self w))
  rcases isPosParam_or_inv hD hφc hφi hφr with hpos | hneg
  · exact (hpos.2.2.2 _ hz0_int).ne'
  · have := hneg.2.2.2 _ hz0_int
    rw [wind_inv hφc hoff] at this
    linarith

/-- The winding number around `g z₀` is independent of the radius `r > 0`. -/
theorem wind_ball_eq_of_le {g : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂)
    (hc : ContinuousOn g (closedBall z₀ r₂)) (hi : InjOn g (closedBall z₀ r₂)) :
    wind (fun w : Circle => g (z₀ + (r₁ : ℂ) * w)) (g z₀) =
      wind (fun w : Circle => g (z₀ + (r₂ : ℂ) * w)) (g z₀) := by
  let cl : ℝ → ℝ := fun u => max r₁ (min u r₂)
  have hcl_c : Continuous cl := by fun_prop
  have hcl_mem : ∀ u, cl u ∈ Icc r₁ r₂ := fun u => ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
  have hsub : ∀ p : ℝ × Circle, z₀ + (cl p.1 : ℂ) * (p.2 : ℂ) ∈ closedBall z₀ r₂ := fun p => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hr₁.trans_le (hcl_mem p.1).1), Circle.norm_coe, mul_one]
    exact (hcl_mem p.1).2
  have hF : Continuous fun p : ℝ × Circle => g (z₀ + (cl p.1 : ℂ) * (p.2 : ℂ)) :=
    hc.comp_continuous (by fun_prop) hsub
  have hne : ∀ (u : ℝ) (w : Circle), g (z₀ + (cl u : ℂ) * (w : ℂ)) ≠ g z₀ := fun u w h => by
    have h1 := hi (hsub (u, w)) (mem_closedBall_self (hr₁.le.trans hle)) h
    have h2 : (cl u : ℂ) * (w : ℂ) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · have : cl u = 0 := Complex.ofReal_eq_zero.mp h3
      linarith [(hcl_mem u).1]
    · exact Circle.coe_ne_zero w h3
  have hh := wind_eq_of_family (F := fun u (w : Circle) => g (z₀ + (cl u : ℂ) * (w : ℂ)))
    hF continuous_const hne r₁ r₂
  simpa [cl, max_eq_left hle, min_eq_left hle, max_eq_right hle] using hh

/-- Characterization of `IsPosLocal g z₀` on any closed ball where `g` is continuous and injective. -/
theorem isPosLocal_iff_wind_pos {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (closedBall z₀ r)) (hi : InjOn g (closedBall z₀ r)) :
    IsPosLocal g z₀ ↔ 0 < wind (fun w : Circle => g (z₀ + (r : ℂ) * w)) (g z₀) := by
  constructor
  · rintro ⟨r', hr', hc', hi', hpos⟩
    set ρ := min r r'
    have hρ : 0 < ρ := lt_min hr hr'
    have e1 := wind_ball_eq_of_le hρ (min_le_left r r') hc hi
    have e2 := wind_ball_eq_of_le hρ (min_le_right r r') hc' hi'
    linarith
  · exact fun h => ⟨r, hr, hc, hi, h⟩

/-- On any closed ball where `g` is continuous and injective, `IsPosLocal g z₀` is equivalent to
`IsPosParam (g '' closedBall z₀ r) (fun w => g (z₀ + r * w))`. -/
theorem isPosLocal_iff_isPosParam {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (closedBall z₀ r)) (hi : InjOn g (closedBall z₀ r)) :
    IsPosLocal g z₀ ↔ IsPosParam (g '' closedBall z₀ r) (fun w : Circle => g (z₀ + (r : ℂ) * w)) := by
  rw [isPosLocal_iff_wind_pos hr hc hi]
  obtain ⟨hD, -, hz0_int, hφr⟩ := isClosedDisc_image_ball hr hc hi
  let φ : Circle → ℂ := fun w => g (z₀ + (r : ℂ) * w)
  have hsub : ∀ w : Circle, z₀ + (r : ℂ) * w ∈ closedBall z₀ r := fun w => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]
  have hφc : Continuous φ := hc.comp_continuous (by fun_prop) hsub
  have hφi : Injective φ := fun a b h => by
    have h1 := hi (hsub a) (hsub b) h
    have h2 : (r : ℂ) * (a : ℂ) = (r : ℂ) * (b : ℂ) := by linear_combination h1
    exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') h2)
  have hoff : ∀ w, φ w ≠ g z₀ := fun w h => hz0_int.2 (hφr ▸ (h ▸ mem_range_self w))
  constructor
  · intro hpos
    rcases isPosParam_or_inv hD hφc hφi hφr with h | h
    · exact h
    · have := h.2.2.2 _ hz0_int
      rw [wind_inv hφc hoff] at this
      linarith
  · exact fun h => h.2.2.2 _ hz0_int

/-- `IsPosLocal g` is locally constant on any open set `U` where `g` is continuous and injective. -/
theorem isPosLocal_eq_of_near {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hi : InjOn g U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ δ > 0, closedBall z₀ δ ⊆ U ∧ ∀ z ∈ ball z₀ δ, (IsPosLocal g z ↔ IsPosLocal g z₀) := by
  obtain ⟨R, hR, hBR⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  refine ⟨R / 2, by positivity, closedBall_subset_ball (by linarith) |>.trans hBR, fun z hz => ?_⟩
  set r := R / 4
  have hr : 0 < r := by positivity
  have hsub_seg : ∀ u ∈ Icc (0 : ℝ) 1, closedBall ((1 - u : ℝ) • z₀ + (u : ℝ) • z) r ⊆ ball z₀ R := by
    intro u hu x hx
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rw [mem_closedBall, dist_eq_norm] at hx
    have h1 : x - z₀ = (x - ((1 - u : ℝ) • z₀ + (u : ℝ) • z)) + (u : ℝ) • (z - z₀) := by
      rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [h1]
    have hle1 : ‖x - ((1 - u : ℝ) • z₀ + (u : ℝ) • z)‖ ≤ r := hx
    have hle2 : ‖(u : ℝ) • (z - z₀)‖ ≤ R / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
      nlinarith [norm_nonneg (z - z₀), hu.2]
    have htri := norm_add_le (x - ((1 - u : ℝ) • z₀ + (u : ℝ) • z)) ((u : ℝ) • (z - z₀))
    dsimp only [r] at hle1
    linarith
  have hsub0 : closedBall z₀ r ⊆ U := by
    have := hsub_seg 0 (by simp); simpa using this.trans hBR
  have hsubz : closedBall z r ⊆ U := by
    have := hsub_seg 1 (by simp); simpa using this.trans hBR
  rw [isPosLocal_iff_wind_pos hr (hc.mono hsubz) (hi.mono hsubz),
    isPosLocal_iff_wind_pos hr (hc.mono hsub0) (hi.mono hsub0)]
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  have hcl_mem : ∀ u, cl u ∈ Icc (0 : ℝ) 1 := fun u => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  let cen : ℝ → ℂ := fun u => (1 - cl u : ℝ) • z₀ + (cl u : ℝ) • z
  have hcen_c : Continuous cen := by unfold cen cl; fun_prop
  have hcen_mem : ∀ u, cen u ∈ U := fun u => hBR (hsub_seg (cl u) (hcl_mem u) (mem_closedBall_self hr.le))
  have hF_mem : ∀ p : ℝ × Circle, cen p.1 + (r : ℂ) * (p.2 : ℂ) ∈ U := fun p =>
    hBR (hsub_seg (cl p.1) (hcl_mem p.1) (by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]))
  have hF_c : Continuous fun p : ℝ × Circle => g (cen p.1 + (r : ℂ) * (p.2 : ℂ)) :=
    hc.comp_continuous (by fun_prop) hF_mem
  have hgz_c : Continuous fun u => g (cen u) := hc.comp_continuous hcen_c hcen_mem
  have hne : ∀ (u : ℝ) (w : Circle), g (cen u + (r : ℂ) * (w : ℂ)) ≠ g (cen u) := fun u w h => by
    have h1 := hi (hF_mem (u, w)) (hcen_mem u) h
    have h2 : (r : ℂ) * (w : ℂ) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hr.ne' (Complex.ofReal_eq_zero.mp h3)
    · exact Circle.coe_ne_zero w h3
  have hh := wind_eq_of_family (F := fun u (w : Circle) => g (cen u + (r : ℂ) * (w : ℂ)))
    hF_c hgz_c hne 0 1
  have h0 : cen 0 = z₀ := by simp [cen, cl]
  have h1 : cen 1 = z := by simp [cen, cl]
  rw [h0, h1] at hh
  rw [hh]

/-- On a connected open subset `U ⊆ ℂ` where `g` is continuous and injective, `IsPosLocal g` is
constant. -/
theorem isPosLocal_const_of_isPreconnected {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hc : ContinuousOn g U) (hi : InjOn g U) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ U) (hz₂ : z₂ ∈ U) : IsPosLocal g z₁ ↔ IsPosLocal g z₂ := by
  have hopen1 : IsOpen {z ∈ U | IsPosLocal g z} := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hpos⟩
    obtain ⟨δ, hδ, hsub, heq⟩ := isPosLocal_eq_of_near hU hc hi hzU
    exact ⟨δ, hδ, fun w hw => ⟨hsub (ball_subset_closedBall hw), (heq w hw).mpr hpos⟩⟩
  have hopen2 : IsOpen {z ∈ U | ¬ IsPosLocal g z} := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hneg⟩
    obtain ⟨δ, hδ, hsub, heq⟩ := isPosLocal_eq_of_near hU hc hi hzU
    exact ⟨δ, hδ, fun w hw => ⟨hsub (ball_subset_closedBall hw), fun h => hneg ((heq w hw).mp h)⟩⟩
  by_contra hne
  have hcov : U ⊆ {z ∈ U | IsPosLocal g z} ∪ {z ∈ U | ¬ IsPosLocal g z} := fun z hz => by
    by_cases h : IsPosLocal g z <;> [exact Or.inl ⟨hz, h⟩; exact Or.inr ⟨hz, h⟩]
  have hne1 : (U ∩ {z ∈ U | IsPosLocal g z}).Nonempty := by
    by_cases h1 : IsPosLocal g z₁
    · exact ⟨z₁, hz₁, hz₁, h1⟩
    · exact ⟨z₂, hz₂, hz₂, by tauto⟩
  have hne2 : (U ∩ {z ∈ U | ¬ IsPosLocal g z}).Nonempty := by
    by_cases h1 : IsPosLocal g z₁
    · exact ⟨z₂, hz₂, hz₂, by tauto⟩
    · exact ⟨z₁, hz₁, hz₁, h1⟩
  obtain ⟨w, -, ⟨-, hw1⟩, ⟨-, hw2⟩⟩ := hconn _ _ hopen1 hopen2 hcov hne1 hne2
  exact hw2 hw1

/-- Chain rule for `IsPosLocal` on open maps (in particular, chart transitions). -/
theorem isPosLocal_comp {g f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hgc : ContinuousOn g U) (hgi : InjOn g U) (hg_sub : g '' U ⊆ V)
    (hfc : ContinuousOn f V) (hfi : InjOn f V) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    IsPosLocal (f ∘ g) z₀ ↔ (IsPosLocal f (g z₀) ↔ IsPosLocal g z₀) := by
  obtain ⟨r, hr, hBrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set r₁ := r / 2
  have hr₁ : 0 < r₁ := by positivity
  have hB1U : closedBall z₀ r₁ ⊆ U := (closedBall_subset_ball (by dsimp only [r₁]; linarith)).trans hBrU
  obtain ⟨hD2, hD2b, hgz₀_int, hφ₂_r⟩ := isClosedDisc_image_ball hr₁ (hgc.mono hB1U) (hgi.mono hB1U)
  set D₂ := g '' closedBall z₀ r₁
  have hD2V : D₂ ⊆ V := (image_mono hB1U).trans hg_sub
  -- Pick a small closed ball `B = closedBall (g z₀) ρ ⊆ discInt D₂`.
  have hopen_int : IsOpen (discInt D₂) := by
    rw [← interior_eq_discInt_complex hD2]; exact isOpen_interior
  obtain ⟨ρ₀, hρ₀, hBρ₀⟩ := Metric.isOpen_iff.mp hopen_int (g z₀) hgz₀_int
  set ρ := ρ₀ / 2
  have hρ : 0 < ρ := by positivity
  have hB_in : closedBall (g z₀) ρ ⊆ discInt D₂ :=
    (closedBall_subset_ball (by dsimp only [ρ]; linarith)).trans hBρ₀
  obtain ⟨hB, hBb⟩ := isClosedDisc_closedBall_of_pos (g z₀) hρ
  -- Build the positive boundary parameterization `p : Circle ≃ₜ discBd B`.
  let pFun : Circle → discBd (closedBall (g z₀) ρ) := fun w =>
    ⟨g z₀ + (ρ : ℂ) * w, by
      rw [hBb, mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe, mul_one]⟩
  have hp_c : Continuous pFun := Continuous.subtype_mk (by fun_prop) _
  have hp_i : Injective pFun := fun a b h => by
    have h1 : g z₀ + (ρ : ℂ) * (a : ℂ) = g z₀ + (ρ : ℂ) * (b : ℂ) := congrArg Subtype.val h
    have h2 : (ρ : ℂ) * (a : ℂ) = (ρ : ℂ) * (b : ℂ) := by linear_combination h1
    exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne') h2)
  have hp_s : Surjective pFun := fun ⟨y, hy⟩ => by
    rw [hBb, mem_sphere, dist_eq_norm] at hy
    have hy0 : y - g z₀ ≠ 0 := by intro h; simp [h] at hy; linarith
    refine ⟨unitC (y - g z₀) hy0, Subtype.ext ?_⟩
    show g z₀ + (ρ : ℂ) * (unitC (y - g z₀) hy0 : ℂ) = y
    rw [← hy, norm_mul_unitC hy0]; ring
  let p : Circle ≃ₜ discBd (closedBall (g z₀) ρ) :=
    hp_c.homeoOfEquivCompactToT2 (f := Equiv.ofBijective pFun ⟨hp_i, hp_s⟩)
  -- Apply `exists_disc_collar` between `closedBall (g z₀) ρ` and `D₂`!
  obtain ⟨c, c', hcc, -, hcm, -, hcl, -, hcin, hcs, hcp⟩ := exists_disc_collar hB hD2 hB_in p
  have hc_inj : InjOn c (closedBall 0 2) := hcl.injOn
  have hc_ne : ∀ (t : ℝ) (w : Circle), 1 ≤ t → t ≤ 2 → c ((t : ℂ) * (w : ℂ)) ≠ g z₀ := by
    intro t w ht1 ht2 he
    have hmem2 : (t : ℂ) * (w : ℂ) ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), Circle.norm_coe, mul_one]; exact ht2
    rcases eq_or_lt_of_le ht1 with rfl | hgt
    · simp only [Complex.ofReal_one, one_mul, hcp] at he
      have : (p w).1 ∈ sphere (g z₀) ρ := hBb ▸ (p w).2
      rw [he, mem_sphere_iff_norm, sub_self, norm_zero] at this
      linarith
    · have hgz_in : g z₀ ∈ c '' closedBall 0 1 := by
        rw [hcin]; exact mem_closedBall_self hρ.le
      obtain ⟨u, hu, hue⟩ := hgz_in
      have hu2 : u ∈ closedBall (0 : ℂ) 2 := closedBall_subset_closedBall (by norm_num) hu
      have h1 := hc_inj hmem2 hu2 (he.trans hue.symm)
      have hn1 : ‖(t : ℂ) * (w : ℂ)‖ = t := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), Circle.norm_coe, mul_one]
      have hn2 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
      rw [h1] at hn1; linarith
  let cl : ℝ → ℝ := fun u => max 1 (min u 2)
  have hcl_mem : ∀ u, 1 ≤ cl u ∧ cl u ≤ 2 := fun u => ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hcl_ball : ∀ q : ℝ × Circle, (cl q.1 : ℂ) * (q.2 : ℂ) ∈ closedBall (0 : ℂ) 2 := fun q => by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [(hcl_mem q.1).1]), Circle.norm_coe, mul_one]
    exact (hcl_mem q.1).2
  have hF1 : Continuous fun q : ℝ × Circle => c ((cl q.1 : ℂ) * (q.2 : ℂ)) :=
    hcc.comp_continuous (by unfold cl; fun_prop) hcl_ball
  have hwind_c : wind (fun w : Circle => c ((2 : ℂ) * (w : ℂ))) (g z₀) = 2 * Real.pi := by
    have hh := wind_eq_of_family (F := fun u (w : Circle) => c ((cl u : ℂ) * (w : ℂ)))
      hF1 continuous_const (fun u w => hc_ne _ w (hcl_mem u).1 (hcl_mem u).2) 2 1
    have h2 : cl 2 = 2 := by simp [cl]
    have h1 : cl 1 = 1 := by simp [cl]
    simp only [h2, h1, Complex.ofReal_ofNat, Complex.ofReal_one, one_mul, hcp] at hh
    rw [hh]
    exact wind_circle_pos (g z₀) hρ
  let ψ₂ : Circle → ℂ := fun w => c ((2 : ℂ) * (w : ℂ))
  have hψ₂_sub : ∀ w : Circle, (2 : ℂ) * (w : ℂ) ∈ closedBall (0 : ℂ) 2 := fun w => by
    rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one]; norm_num
  have hψ₂_c : Continuous ψ₂ := hcc.comp_continuous (by fun_prop) hψ₂_sub
  have hψ₂_i : Injective ψ₂ := fun a b h => by
    have h1 := hc_inj (hψ₂_sub a) (hψ₂_sub b) h
    exact Circle.ext (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h1)
  have hψ₂_r : range ψ₂ = discBd D₂ := by
    rw [← hcs]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨(2 : ℂ) * (w : ℂ), ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, mul_one]; norm_num
    · rintro ⟨z, hz, rfl⟩
      have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
      have hz0 : z ≠ 0 := by intro h; simp [h] at hzn
      refine ⟨unitC z hz0, ?_⟩
      show c ((2 : ℂ) * (unitC z hz0 : ℂ)) = c z
      have h2 : (2 : ℂ) = ((‖z‖ : ℝ) : ℂ) := by rw [hzn]; norm_num
      rw [h2, norm_mul_unitC hz0]
  have hψ₂_pos : IsPosParam D₂ ψ₂ := by
    rcases isPosParam_or_inv hD2 hψ₂_c hψ₂_i hψ₂_r with h | h
    · exact h
    · exfalso
      have h1 := h.2.2.2 _ hgz₀_int
      have hoff : ∀ w, ψ₂ w ≠ g z₀ := fun w => hc_ne 2 w (by norm_num) le_rfl
      rw [wind_inv hψ₂_c hoff, hwind_c] at h1
      linarith [Real.pi_pos]
  have hF2 : Continuous fun q : ℝ × Circle => f (c ((cl q.1 : ℂ) * (q.2 : ℂ))) :=
    hfc.comp_continuous hF1 (fun q => hD2V (hcm (hcl_ball q)))
  have hF2_ne : ∀ (u : ℝ) (w : Circle), f (c ((cl u : ℂ) * (w : ℂ))) ≠ f (g z₀) := fun u w h =>
    hc_ne _ w (hcl_mem u).1 (hcl_mem u).2
      (hfi (hD2V (hcm (hcl_ball (u, w)))) (hD2V hgz₀_int.1) h)
  have hwind_fψ₂ : wind (f ∘ ψ₂) (f (g z₀)) =
      wind (fun w : Circle => f (g z₀ + (ρ : ℂ) * (w : ℂ))) (f (g z₀)) := by
    have hh := wind_eq_of_family (F := fun u (w : Circle) => f (c ((cl u : ℂ) * (w : ℂ))))
      hF2 continuous_const hF2_ne 2 1
    have h2 : cl 2 = 2 := by simp [cl]
    have h1 : cl 1 = 1 := by simp [cl]
    simp only [h2, h1, Complex.ofReal_ofNat, Complex.ofReal_one, one_mul, hcp] at hh
    exact hh
  let φ₂ : Circle → ℂ := fun w => g (z₀ + (r₁ : ℂ) * (w : ℂ))
  have hφ₂_sub : ∀ w : Circle, z₀ + (r₁ : ℂ) * (w : ℂ) ∈ closedBall z₀ r₁ := fun w => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr₁, Circle.norm_coe, mul_one]
  have hφ₂_c : Continuous φ₂ := (hgc.mono hB1U).comp_continuous (by fun_prop) hφ₂_sub
  have hφ₂_i : Injective φ₂ := fun a b h => by
    have h1 := hgi (hB1U (hφ₂_sub a)) (hB1U (hφ₂_sub b)) h
    have h2 : (r₁ : ℂ) * (a : ℂ) = (r₁ : ℂ) * (b : ℂ) := by linear_combination h1
    exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr₁.ne') h2)
  let eφ : Circle ≃ₜ discBd D₂ :=
    (hφ₂_c.subtype_mk (fun w => hφ₂_r ▸ mem_range_self w)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨fun a b h => hφ₂_i (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
        obtain ⟨w, hw⟩ := hφ₂_r.symm ▸ hy; exact ⟨w, Subtype.ext hw⟩⟩)
  let eψ : Circle ≃ₜ discBd D₂ :=
    (hψ₂_c.subtype_mk (fun w => hψ₂_r ▸ mem_range_self w)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨fun a b h => hψ₂_i (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
        obtain ⟨w, hw⟩ := hψ₂_r.symm ▸ hy; exact ⟨w, Subtype.ext hw⟩⟩)
  let H : Circle ≃ₜ Circle := eφ.trans eψ.symm
  have hH : ∀ w : Circle, ψ₂ (H w) = φ₂ w := fun w =>
    congrArg Subtype.val (eψ.apply_symm_apply (eφ w))
  have hfψ₂_c : Continuous (f ∘ ψ₂) :=
    hfc.comp_continuous hψ₂_c (fun w => hD2V (hcm (hψ₂_sub w)))
  have hfψ₂_ne : ∀ w, (f ∘ ψ₂) w ≠ f (g z₀) := fun w h =>
    hc_ne 2 w (by norm_num) le_rfl (hfi (hD2V (hcm (hψ₂_sub w))) (hD2V hgz₀_int.1) h)
  have hfg_eq : (fun w : Circle => (f ∘ g) (z₀ + (r₁ : ℂ) * (w : ℂ))) = (f ∘ ψ₂) ∘ H := by
    funext w; simp [Function.comp_apply, hH, φ₂]
  have hfg_c : ContinuousOn (f ∘ g) (closedBall z₀ r₁) :=
    hfc.comp (hgc.mono hB1U) (fun z hz => hD2V (mem_image_of_mem g hz))
  have hfg_i : InjOn (f ∘ g) (closedBall z₀ r₁) := fun a ha b hb h =>
    hgi (hB1U ha) (hB1U hb) (hfi (hD2V (mem_image_of_mem g ha)) (hD2V (mem_image_of_mem g hb)) h)
  have hBV : closedBall (g z₀) ρ ⊆ V := fun x hx => hD2V (hB_in hx).1
  rw [isPosLocal_iff_wind_pos hr₁ hfg_c hfg_i, isPosLocal_iff_wind_pos hρ (hfc.mono hBV) (hfi.mono hBV),
    isPosLocal_iff_isPosParam hr₁ (hgc.mono hB1U) (hgi.mono hB1U)]
  have hne_f : wind (fun w : Circle => f (g z₀ + (ρ : ℂ) * (w : ℂ))) (f (g z₀)) ≠ 0 :=
    wind_ne_zero_of_ball hρ (hfc.mono hBV) (hfi.mono hBV)
  by_cases hgpos : IsPosParam D₂ φ₂
  · have hH_pos : PreservesCircleOrientation H := preservesCircleOrientation_of_cyclic fun a b c habc =>
      order_of_nested hD2 hD2 Subset.rfl hgpos hψ₂_pos habc (hH a).symm (hH b).symm (hH c).symm
    change 0 < wind (fun w : Circle => (f ∘ g) (z₀ + (r₁ : ℂ) * (w : ℂ))) (f (g z₀)) ↔
      (0 < wind (fun w : Circle => f (g z₀ + (ρ : ℂ) * (w : ℂ))) (f (g z₀)) ↔ IsPosParam D₂ φ₂)
    rw [hfg_eq, wind_comp_preserves hfψ₂_c hfψ₂_ne hH_pos, hwind_fψ₂]
    exact ⟨fun h => ⟨fun _ => hgpos, fun _ => h⟩, fun h => h.mpr hgpos⟩
  · have hgneg : IsPosParam D₂ (fun w => φ₂ w⁻¹) :=
      (isPosParam_or_inv hD2 hφ₂_c hφ₂_i hφ₂_r).resolve_left hgpos
    let H' : Circle ≃ₜ Circle := (Homeomorph.inv Circle).trans H
    have hH'_pos : PreservesCircleOrientation H' := preservesCircleOrientation_of_cyclic fun a b c habc =>
      order_of_nested hD2 hD2 Subset.rfl hgneg hψ₂_pos habc (hH a⁻¹).symm (hH b⁻¹).symm (hH c⁻¹).symm
    have hrew : (f ∘ ψ₂) ∘ H = fun w => ((f ∘ ψ₂) ∘ H') w⁻¹ := by
      funext w; simp [H', Function.comp_apply]
    have hH'_c : Continuous ((f ∘ ψ₂) ∘ H') := hfψ₂_c.comp H'.continuous
    have hH'_ne : ∀ w, ((f ∘ ψ₂) ∘ H') w ≠ f (g z₀) := fun w => hfψ₂_ne (H' w)
    change 0 < wind (fun w : Circle => (f ∘ g) (z₀ + (r₁ : ℂ) * (w : ℂ))) (f (g z₀)) ↔
      (0 < wind (fun w : Circle => f (g z₀ + (ρ : ℂ) * (w : ℂ))) (f (g z₀)) ↔ IsPosParam D₂ φ₂)
    rw [hfg_eq, hrew, wind_inv hH'_c hH'_ne, wind_comp_preserves hfψ₂_c hfψ₂_ne hH'_pos, hwind_fψ₂]
    rcases hne_f.lt_or_gt with hlt | hgt
    · exact ⟨fun _ => ⟨fun h => by linarith, fun h => absurd h hgpos⟩, fun _ => by linarith⟩
    · exact ⟨fun h => by linarith, fun h => absurd (h.mp hgt) hgpos⟩

/-- Explicit values of `IsPosLocal` on standard maps. -/
theorem isPosLocal_id (z₀ : ℂ) : IsPosLocal id z₀ := by
  refine ⟨1, one_pos, continuousOn_id, Function.injective_id.injOn, ?_⟩
  change 0 < wind (fun w : Circle => z₀ + (1 : ℂ) * (w : ℂ)) z₀
  have h := wind_circle_pos z₀ one_pos
  simp only [Complex.ofReal_one] at h
  rw [h]; positivity

theorem not_isPosLocal_conj (z₀ : ℂ) : ¬ IsPosLocal (starRingEnd ℂ) z₀ := by
  rw [isPosLocal_iff_wind_pos one_pos Complex.continuous_conj.continuousOn
    (RingHom.injective (starRingEnd ℂ)).injOn]
  have h1 : (fun w : Circle => starRingEnd ℂ (z₀ + ((1 : ℝ) : ℂ) * (w : ℂ))) =
      fun w : Circle => starRingEnd ℂ (z₀ + (w : ℂ)) := by funext w; simp
  rw [h1, wind_conj (by fun_prop) (fun w h => Circle.coe_ne_zero w (by linear_combination h))]
  have h2 := wind_circle_pos z₀ one_pos
  simp only [Complex.ofReal_one, one_mul] at h2
  rw [h2]; linarith [Real.pi_pos]

theorem isPosLocal_affine {a : ℂ} (ha : a ≠ 0) (b z₀ : ℂ) :
    IsPosLocal (fun z => a * z + b) z₀ := by
  have hc : Continuous (fun z : ℂ => a * z + b) := by fun_prop
  have hi : Injective (fun z : ℂ => a * z + b) := fun x y h =>
    mul_left_cancel₀ ha (by linear_combination h)
  rw [isPosLocal_iff_wind_pos one_pos hc.continuousOn hi.injOn]
  unfold wind
  have he : (fun t => a * (z₀ + ((1 : ℝ) : ℂ) * ((Circle.exp t : Circle) : ℂ)) + b - (a * z₀ + b)) =
      fun t => a * ((Circle.exp t : Circle) : ℂ) := by funext t; simp only [Complex.ofReal_one, one_mul]; ring
  rw [he]
  obtain ⟨α, hα⟩ := isAngle_const ha
  have hA := hα.mul isAngle_exp
  rw [hA.turn_eq (fun t => mul_ne_zero ha (Circle.coe_ne_zero _))]
  linarith [Real.pi_pos]

/-- `IsPosLocal` depends only on the germ of `g` at `z₀`. -/
theorem isPosLocal_congr {g₁ g₂ : ℂ → ℂ} {z₀ : ℂ} (h : g₁ =ᶠ[𝓝 z₀] g₂) :
    IsPosLocal g₁ z₀ ↔ IsPosLocal g₂ z₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  have hcl : EqOn g₁ g₂ (closedBall z₀ (ε / 2)) := fun z hz =>
    hball (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have h1 : ∀ {f₁ f₂ : ℂ → ℂ}, EqOn f₁ f₂ (closedBall z₀ (ε / 2)) → IsPosLocal f₁ z₀ → IsPosLocal f₂ z₀ := by
    intro f₁ f₂ heq ⟨r, hr, hc, hi, hpos⟩
    set ρ := min r (ε / 2)
    have hρ : 0 < ρ := lt_min hr (by positivity)
    have hsub1 : closedBall z₀ ρ ⊆ closedBall z₀ r := closedBall_subset_closedBall (min_le_left _ _)
    have hsub2 : closedBall z₀ ρ ⊆ closedBall z₀ (ε / 2) := closedBall_subset_closedBall (min_le_right _ _)
    have heq' : EqOn f₁ f₂ (closedBall z₀ ρ) := heq.mono hsub2
    refine ⟨ρ, hρ, (hc.mono hsub1).congr (fun z hz => (heq' hz).symm),
      (hi.mono hsub1).congr heq', ?_⟩
    have e1 := wind_ball_eq_of_le hρ (min_le_left r (ε / 2)) hc hi
    have e2 : (fun w : Circle => f₂ (z₀ + (ρ : ℂ) * (w : ℂ))) = fun w : Circle => f₁ (z₀ + (ρ : ℂ) * (w : ℂ)) := by
      funext w
      exact (heq' (by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe, mul_one])).symm
    rw [e2, ← heq' (mem_closedBall_self hρ.le), e1]
    exact hpos
  exact ⟨h1 hcl, h1 hcl.symm⟩

/-! ### Path integrals of local cocycles -/

section CocInt

variable {X : Type u} [TopologicalSpace X] {A : Type} [AddCommGroup A]

/-- Riemann sum of `φ` along a curve `γ` with `N` equal steps. -/
noncomputable def cocSum (φ : X → X → A) (γ : ℝ → X) (N : ℕ) : A :=
  ∑ k ∈ Finset.range N, φ (γ ((k : ℝ) / N)) (γ (((k + 1 : ℕ) : ℝ) / N))

private theorem sum_range_mul_eq {f : ℕ → A} (a b : ℕ) :
    ∑ k ∈ Finset.range (a * b), f k = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- Compactness Lebesgue number for a curve `[0, 1] → X` and a `NearDiag` set `N`. -/
theorem exists_delta_curve {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) {N : Set (X × X)}
    (hN : NearDiag N) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < δ → (γ s, γ t) ∈ N := by
  have hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp hK
  let M : Set (Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) := (fun p => (γ p.1, γ p.2)) ⁻¹' N
  have hc : Continuous fun p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 => (γ p.1, γ p.2) := by
    have h1 : Continuous fun a : Icc (0 : ℝ) 1 => γ a :=
      hγ.comp_continuous continuous_subtype_val fun a => a.2
    exact (h1.comp continuous_fst).prodMk (h1.comp continuous_snd)
  have hM : M ∈ 𝓝ˢ (diagonal (Icc (0 : ℝ) 1)) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨a, a'⟩ h
    have h' : a = a' := h
    subst h'
    exact hc.continuousAt.preimage_mem_nhds (hN (γ a))
  rw [nhdsSet_diagonal_eq_uniformity, Metric.mem_uniformity_dist] at hM
  obtain ⟨δ, hδ, h1⟩ := hM
  exact ⟨δ, hδ, fun s hs t ht hst =>
    h1 (a := ⟨s, hs⟩) (b := ⟨t, ht⟩) (by simpa [Subtype.dist_eq, Real.dist_eq] using hst)⟩

omit [TopologicalSpace X] in
/-- For a local cocycle `φ` on `N`, subdividing an interval inside the cocycle radius telescopes. -/
theorem coc_telescoping {φ : X → X → A} {N : Set (X × X)}
    (hc : ∀ x y z, (x, y) ∈ N → (y, z) ∈ N → (x, z) ∈ N → φ x y + φ y z = φ x z)
    {p : ℕ → X} {m : ℕ} (hm : 0 < m)
    (hN : ∀ i ≤ m, ∀ j ≤ m, (p i, p j) ∈ N) :
    ∑ i ∈ Finset.range m, φ (p i) (p (i + 1)) = φ (p 0) (p m) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ, ih (by omega) (fun i hi j hj => hN i (by omega) j (by omega))]
      exact hc _ _ _ (hN 0 (by omega) (m + 1) (by omega))
        (hN (m + 1) (by omega) (m + 2) le_rfl) (hN 0 (by omega) (m + 2) le_rfl)

omit [TopologicalSpace X] in
/-- If `1 / n ≤ δ` and `1 / m ≤ δ` where `δ` is a cocycle mesh for `γ`, then
`cocSum φ γ n = cocSum φ γ m`. -/
theorem cocSum_eq_of_fine {φ : X → X → A} {N : Set (X × X)}
    (hc : ∀ x y z, (x, y) ∈ N → (y, z) ∈ N → (x, z) ∈ N → φ x y + φ y z = φ x z)
    {γ : ℝ → X} {δ : ℝ}
    (hδ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| ≤ δ → (γ s, γ t) ∈ N)
    {n m : ℕ} (hn0 : 0 < n) (hm0 : 0 < m) (hn : 1 / (n : ℝ) ≤ δ) (hm : 1 / (m : ℝ) ≤ δ) :
    cocSum φ γ n = cocSum φ γ m := by
  have href : ∀ (a b : ℕ), 0 < a → 0 < b → 1 / (a : ℝ) ≤ δ →
      cocSum φ γ (a * b) = cocSum φ γ a := by
    intro a b ha hb haδ
    unfold cocSum
    rw [sum_range_mul_eq a b]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < a := Finset.mem_range.mp hi
    have hab_pos : (0 : ℝ) < (a * b : ℕ) := by positivity
    let p : ℕ → X := fun j => γ (((i * b + j : ℕ) : ℝ) / (a * b : ℕ))
    have htel := coc_telescoping hc hb (p := p) fun j₁ hj₁ j₂ hj₂ => by
      refine hδ _ ?_ _ ?_ ?_
      · refine ⟨by positivity, (div_le_one hab_pos).mpr ?_⟩
        exact_mod_cast (show i * b + j₁ ≤ a * b by nlinarith)
      · refine ⟨by positivity, (div_le_one hab_pos).mpr ?_⟩
        exact_mod_cast (show i * b + j₂ ≤ a * b by nlinarith)
      · rw [← sub_div, abs_div, abs_of_pos hab_pos]
        have hle : |((i * b + j₁ : ℕ) : ℝ) - ((i * b + j₂ : ℕ) : ℝ)| ≤ b := by
          rw [abs_le]
          have hj1' : (j₁ : ℝ) ≤ b := by exact_mod_cast hj₁
          have hj2' : (j₂ : ℝ) ≤ b := by exact_mod_cast hj₂
          push_cast; constructor <;> linarith
        calc |((i * b + j₁ : ℕ) : ℝ) - ((i * b + j₂ : ℕ) : ℝ)| / (a * b : ℕ)
            ≤ (b : ℝ) / (a * b : ℕ) := div_le_div_of_nonneg_right hle hab_pos.le
          _ = 1 / (a : ℝ) := by
              push_cast
              have hb0 : (b : ℝ) ≠ 0 := by positivity
              field_simp
          _ ≤ δ := haδ
    have he0 : p 0 = γ ((i : ℝ) / a) := by
      simp only [p, add_zero, Nat.cast_mul]
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      congr 1; field_simp
    have heb : p b = γ (((i + 1 : ℕ) : ℝ) / a) := by
      simp only [p, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      congr 1; field_simp
    have hsum_eq : ∑ j ∈ Finset.range b,
        φ (γ (((i * b + j : ℕ) : ℝ) / ((a * b : ℕ) : ℝ)))
          (γ (((i * b + j + 1 : ℕ) : ℝ) / ((a * b : ℕ) : ℝ))) =
        ∑ j ∈ Finset.range b, φ (p j) (p (j + 1)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [p, add_assoc]
    rw [hsum_eq, htel, he0, heb]
  calc cocSum φ γ n = cocSum φ γ (n * m) := (href n m hn0 hm0 hn).symm
    _ = cocSum φ γ (m * n) := by rw [mul_comm]
    _ = cocSum φ γ m := href m n hm0 hn0 hm

/-- The path integral of a local cocycle `φ` along a curve `γ : [0, 1] → X`. -/
noncomputable def cocInt (φ : X → X → A) (γ : ℝ → X) : A :=
  open Classical in
  if h : ∃ n : ℕ, 0 < n ∧ ∀ m ≥ n, cocSum φ γ m = cocSum φ γ n then
    cocSum φ γ h.choose
  else 0

/-- For a local cocycle `φ` and continuous curve `γ`, `cocInt φ γ` equals `cocSum φ γ n` for any
sufficiently fine mesh `n`. -/
theorem cocInt_eq_sum {φ : X → X → A} {N : Set (X × X)} (hN : NearDiag N)
    (hc : ∀ x y z, (x, y) ∈ N → (y, z) ∈ N → (x, z) ∈ N → φ x y + φ y z = φ x z)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀, cocInt φ γ = cocSum φ γ n := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_curve hγ hN
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 / δ)
  have hn₀_pos : 0 < n₀ := by
    have : (0 : ℝ) < n₀ := lt_trans (by positivity) hn₀
    exact_mod_cast this
  have hn₀_le : ∀ n ≥ n₀, 1 / (n : ℝ) ≤ δ / 2 := by
    intro n hn
    have h1 : (2 / δ) < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
    have hn_pos : (0 : ℝ) < n := lt_trans (by positivity) h1
    rw [div_le_div_iff₀ hn_pos two_pos]
    have := (div_lt_iff₀ hδpos).mp h1
    linarith
  have hδ2 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| ≤ δ / 2 → (γ s, γ t) ∈ N :=
    fun s hs t ht hst => hδ s hs t ht (by linarith)
  have hconst : ∀ m ≥ n₀, cocSum φ γ m = cocSum φ γ n₀ := fun m hm =>
    cocSum_eq_of_fine hc hδ2 (lt_of_lt_of_le hn₀_pos hm) hn₀_pos (hn₀_le m hm) (hn₀_le n₀ le_rfl)
  have hex : ∃ n : ℕ, 0 < n ∧ ∀ m ≥ n, cocSum φ γ m = cocSum φ γ n := ⟨n₀, hn₀_pos, hconst⟩
  refine ⟨n₀, hn₀_pos, fun n hn => ?_⟩
  rw [cocInt, dite_eq_left hex]
  have hch := hex.choose_spec
  set M := max n hex.choose
  have h1 := hch.2 M (le_max_right _ _)
  have h2 := hconst M (hn.trans (le_max_left _ _))
  have h3 := hconst n hn
  rw [← h1, h2, h3]

theorem cocInt_add {φ₁ φ₂ : X → X → A} (h₁ : IsCoc φ₁) (h₂ : IsCoc φ₂) {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt (fun x y => φ₁ x y + φ₂ x y) γ = cocInt φ₁ γ + cocInt φ₂ γ := by
  obtain ⟨N₁, hN₁, hc₁⟩ := h₁
  obtain ⟨N₂, hN₂, hc₂⟩ := h₂
  obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN₁ hc₁ hγ
  obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN₂ hc₂ hγ
  obtain ⟨n₃, -, hn₃⟩ := cocInt_eq_sum (hN₁.inter hN₂)
    (fun x y z hxy hyz hxz => by
      have e1 := hc₁ x y z hxy.1 hyz.1 hxz.1
      have e2 := hc₂ x y z hxy.2 hyz.2 hxz.2
      calc φ₁ x y + φ₂ x y + (φ₁ y z + φ₂ y z) = (φ₁ x y + φ₁ y z) + (φ₂ x y + φ₂ y z) := by abel
        _ = φ₁ x z + φ₂ x z := by rw [e1, e2]) hγ
  set M := max n₁ (max n₂ n₃)
  rw [hn₁ M (le_max_left _ _), hn₂ M ((le_max_left _ _).trans (le_max_right _ _)),
    hn₃ M ((le_max_right _ _).trans (le_max_right _ _))]
  simp [cocSum, Finset.sum_add_distrib]

theorem cocInt_coboundary {φ : X → X → A} {h : X → A} {N : Set (X × X)} (hN : NearDiag N)
    (hφ : ∀ x y, (x, y) ∈ N → φ x y = h y - h x) {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt φ γ = h (γ 1) - h (γ 0) := by
  have hc : ∀ x y z, (x, y) ∈ N → (y, z) ∈ N → (x, z) ∈ N → φ x y + φ y z = φ x z := by
    intro x y z h1 h2 h3; rw [hφ _ _ h1, hφ _ _ h2, hφ _ _ h3]; abel
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_curve hγ hN
  obtain ⟨n₀, -, hn₀⟩ := cocInt_eq_sum hN hc hγ
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  set n := max n₀ (max m 1)
  have hn_pos : 0 < n := lt_of_lt_of_le one_pos ((le_max_right m 1).trans (le_max_right _ _))
  have hn_r : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_lt : 1 / (n : ℝ) < δ := by
    have h1 : 1 / δ < n := lt_of_lt_of_le hm (by exact_mod_cast (le_max_left m 1).trans (le_max_right _ _))
    rw [div_lt_iff₀ hn_r]; have := (div_lt_iff₀ hδpos).mp h1; linarith
  rw [hn₀ n (le_max_left _ _)]
  unfold cocSum
  have hstep : ∀ k ∈ Finset.range n,
      φ (γ ((k : ℝ) / n)) (γ (((k + 1 : ℕ) : ℝ) / n)) =
        h (γ (((k + 1 : ℕ) : ℝ) / n)) - h (γ ((k : ℝ) / n)) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    refine hφ _ _ (hδ _ ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk'.le)⟩
      _ ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk')⟩ ?_)
    have hsub : (k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n = -1 / (n : ℝ) := by
      push_cast; field_simp; ring
    rw [hsub, abs_div, abs_neg, abs_one, abs_of_pos hn_r]
    exact hn_lt
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => h (γ ((k : ℝ) / n))) n]
  have hn0 : (n : ℝ) ≠ 0 := hn_r.ne'
  simp [hn0]

theorem cocInt_of_cohRel {φ φ' : X → X → A} (_h₁ : IsCoc φ) (h₂ : IsCoc φ')
    {h : X → A} {N : Set (X × X)} (hN : NearDiag N)
    (hrel : ∀ x y, (x, y) ∈ N → φ x y - φ' x y = h y - h x)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt φ γ - cocInt φ' γ = h (γ 1) - h (γ 0) := by
  have hdiff : IsCoc (fun x y => φ x y - φ' x y) :=
    ⟨N, hN, fun x y z h1 h2 h3 => by dsimp only; rw [hrel _ _ h1, hrel _ _ h2, hrel _ _ h3]; abel⟩
  have hsum : cocInt (fun x y => (φ x y - φ' x y) + φ' x y) γ =
      cocInt (fun x y => φ x y - φ' x y) γ + cocInt φ' γ := cocInt_add hdiff h₂ hγ
  have heq : (fun x y => (φ x y - φ' x y) + φ' x y) = φ := by funext x y; abel
  rw [heq] at hsum
  rw [hsum, add_sub_cancel_right]
  exact cocInt_coboundary hN hrel hγ

theorem cocInt_pbk {X' : Type v} [TopologicalSpace X'] (e : X ≃ₜ X') {φ : X' → X' → A}
    (hφ : IsCoc φ) {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt (pbk e φ) γ = cocInt φ (e ∘ γ) := by
  obtain ⟨N, hN, hc⟩ := hφ
  obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum (φ := pbk e φ) (N := (fun p : X × X => (e p.1, e p.2)) ⁻¹' N)
    (hN.pull e) (fun x y z h1 h2 h3 => hc _ _ _ h1 h2 h3) hγ
  obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc (e.continuous.comp_continuousOn hγ)
  set M := max n₁ n₂
  rw [hn₁ M (le_max_left _ _), hn₂ M (le_max_right _ _)]
  rfl

/-- Concatenation of two curves adds their cocycle integrals. -/
theorem cocInt_conc2 {φ : X → X → A} (hφ : IsCoc φ) {γ₁ γ₂ : ℝ → X}
    (h₁ : ContinuousOn γ₁ (Icc 0 1)) (h₂ : ContinuousOn γ₂ (Icc 0 1)) (h12 : γ₁ 1 = γ₂ 0) :
    cocInt φ (conc2 γ₁ γ₂) = cocInt φ γ₁ + cocInt φ γ₂ := by
  obtain ⟨N, hN, hc⟩ := hφ
  obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN hc h₁
  obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc h₂
  obtain ⟨n₃, -, hn₃⟩ := cocInt_eq_sum hN hc (continuousOn_conc2 h₁ h₂ h12)
  set M := max n₁ (max n₂ (max n₃ 1))
  have hM1 : n₁ ≤ M := le_max_left _ _
  have hM2 : n₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : n₃ ≤ 2 * M := by
    have : n₃ ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    omega
  have hM_pos : (0 : ℝ) < M := by
    have : 1 ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    exact_mod_cast (by omega : 0 < M)
  rw [hn₃ (2 * M) hM3, hn₁ M hM1, hn₂ M hM2]
  unfold cocSum
  rw [show 2 * M = M + M by omega, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    have hle1 : (k : ℝ) / ((M + M : ℕ) : ℝ) = ((k : ℝ) / M) / 2 := by push_cast; ring
    have hle2 : (((k + 1 : ℕ) : ℝ)) / ((M + M : ℕ) : ℝ) = (((k + 1 : ℕ) : ℝ) / M) / 2 := by
      push_cast; ring
    rw [hle1, hle2, conc2_left ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk'.le)⟩,
      conc2_left ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk')⟩]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    have hM0 : (M : ℝ) ≠ 0 := hM_pos.ne'
    have hle1 : (((M + k : ℕ) : ℝ)) / ((M + M : ℕ) : ℝ) = (1 + (k : ℝ) / M) / 2 := by
      push_cast; field_simp; ring
    have hle2 : (((M + k + 1 : ℕ) : ℝ)) / ((M + M : ℕ) : ℝ) = (1 + ((k + 1 : ℕ) : ℝ) / M) / 2 := by
      push_cast; field_simp; ring
    rw [hle1, hle2, conc2_right h12 ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk'.le)⟩,
      conc2_right h12 ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk')⟩]

/-- Reversing a curve negates its cocycle integral. -/
theorem cocInt_rev {φ : X → X → A} (hφ : IsCoc φ) {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    cocInt φ (fun u => γ (1 - u)) = - cocInt φ γ := by
  obtain ⟨N, hN, hc⟩ := hφ
  have hrev_c : ContinuousOn (fun u => γ (1 - u)) (Icc 0 1) :=
    hγ.comp (continuous_const.sub continuous_id).continuousOn fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_curve hγ hN
  obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN hc hγ
  obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc hrev_c
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  set n := max n₁ (max n₂ (max m 1))
  have hn_pos : 0 < n := lt_of_lt_of_le one_pos
    ((le_max_right m 1).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hn_r : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_lt : 1 / (n : ℝ) < δ := by
    have h1 : 1 / δ < n := lt_of_lt_of_le hm
      (by exact_mod_cast (le_max_left m 1).trans ((le_max_right _ _).trans (le_max_right _ _)))
    rw [div_lt_iff₀ hn_r]; have := (div_lt_iff₀ hδpos).mp h1; linarith
  have hanti : ∀ x y, (x, y) ∈ N → (y, x) ∈ N → φ y x = - φ x y := fun x y h1 h2 => by
    have hxx := hN.mem x
    have h0 : φ x x = 0 := add_eq_left.mp (hc x x x hxx hxx hxx)
    have := hc x y x h1 h2 hxx
    rw [h0] at this
    exact eq_neg_of_add_eq_zero_right this
  rw [hn₂ n ((le_max_left _ _).trans (le_max_right _ _)), hn₁ n (le_max_left _ _)]
  unfold cocSum
  rw [← Finset.sum_neg_distrib, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < n := Finset.mem_range.mp hk
  have e1 : 1 - ((n - 1 - k : ℕ) : ℝ) / n = (((k + 1 : ℕ) : ℝ) / n) := by
    rw [Nat.cast_sub (by omega : k ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; field_simp; ring
  have e2 : 1 - (((n - 1 - k + 1 : ℕ) : ℝ) / n) = (k : ℝ) / n := by
    have : n - 1 - k + 1 = n - k := by omega
    rw [this, Nat.cast_sub hk'.le]; field_simp; ring
  dsimp only
  rw [e1, e2]
  set s := (k : ℝ) / n
  set t := (((k + 1 : ℕ) : ℝ) / n)
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk'.le)⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk')⟩
  have hst : |s - t| < δ := by
    have : s - t = -1 / (n : ℝ) := by simp only [s, t]; push_cast; field_simp; ring
    rw [this, abs_div, abs_neg, abs_one, abs_of_pos hn_r]; exact hn_lt
  have hts : |t - s| < δ := by rwa [abs_sub_comm]
  exact hanti _ _ (hδ s hs t ht hst) (hδ t ht s hs hts)

/-- Every closed loop inside a continuous image of `closedBall 0 1` has zero cocycle integral. -/
theorem cocInt_eq_zero_of_in_disc {φ : X → X → A} (hφ : IsCoc φ) {F : ℂ → X}
    (hF : ContinuousOn F (closedBall 0 1)) {α : ℝ → ℂ} (hα : ContinuousOn α (Icc 0 1))
    (hsub : ∀ u ∈ Icc (0 : ℝ) 1, α u ∈ closedBall (0 : ℂ) 1) (hloop : α 0 = α 1) :
    cocInt φ (F ∘ α) = 0 := by
  obtain ⟨g, ε, hε, hg⟩ := exists_prim hφ hF
  obtain ⟨N, hN, hc⟩ := hφ
  obtain ⟨n₀, -, hn₀⟩ := cocInt_eq_sum hN hc (hF.comp hα hsub)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hα
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  set n := max n₀ (max m 1)
  have hn_pos : 0 < n := lt_of_lt_of_le one_pos ((le_max_right m 1).trans (le_max_right _ _))
  have hn_r : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_lt : 1 / (n : ℝ) < δ := by
    have h1 : 1 / δ < n := lt_of_lt_of_le hm (by exact_mod_cast (le_max_left m 1).trans (le_max_right _ _))
    rw [div_lt_iff₀ hn_r]; have := (div_lt_iff₀ hδpos).mp h1; linarith
  rw [hn₀ n (le_max_left _ _)]
  unfold cocSum
  simp only [Function.comp_apply]
  have hstep : ∀ k ∈ Finset.range n,
      φ (F (α ((k : ℝ) / n))) (F (α (((k + 1 : ℕ) : ℝ) / n))) =
        g (α (((k + 1 : ℕ) : ℝ) / n)) - g (α ((k : ℝ) / n)) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hs : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk'.le)⟩
    have ht : (((k + 1 : ℕ) : ℝ) / n) ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hn_r).mpr (by exact_mod_cast hk')⟩
    have hdist : dist ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) < δ := by
      have hsub' : (k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n = -1 / (n : ℝ) := by
        push_cast; field_simp; ring
      rw [Real.dist_eq, hsub', abs_div, abs_neg, abs_one, abs_of_pos hn_r]
      exact hn_lt
    have hnorm : ‖α ((k : ℝ) / n) - α (((k + 1 : ℕ) : ℝ) / n)‖ < ε := by
      simpa [dist_eq_norm] using hδ _ hs _ ht hdist
    have := hg _ (hsub _ hs) _ (hsub _ ht) hnorm
    rw [this]; abel
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => g (α ((k : ℝ) / n))) n]
  have hn0 : (n : ℝ) ≠ 0 := hn_r.ne'
  simp [hn0, hloop]

/-- Every closed loop inside a closed disc `Δ ⊆ X` has zero cocycle integral. -/
theorem cocInt_disc_loop {φ : X → X → A} (hφ : IsCoc φ) {Δ : Set X} (hΔ : IsClosedDisc Δ)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) (hsub : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ Δ)
    (hloop : γ 0 = γ 1) : cocInt φ γ = 0 := by
  classical
  obtain ⟨e⟩ := hΔ
  let cToD : closedBall (0 : ℂ) 1 ≃ₜ ClosedUnitDisc :=
    { toFun := fun z => ⟨complexPlane z.1, by
        simpa [ClosedUnitDisc, mem_closedBall_zero_iff] using mem_closedBall_zero_iff.mp z.2⟩
      invFun := fun p => ⟨complexPlane.symm p.1, by
        simpa [mem_closedBall_zero_iff] using mem_closedBall_zero_iff.mp p.2⟩
      left_inv := fun z => Subtype.ext (complexPlane.symm_apply_apply z.1)
      right_inv := fun p => Subtype.ext (complexPlane.apply_symm_apply p.1)
      continuous_toFun := Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val) (fun z => by
        simpa [ClosedUnitDisc, mem_closedBall_zero_iff] using mem_closedBall_zero_iff.mp z.2)
      continuous_invFun := Continuous.subtype_mk (complexPlane.symm.continuous.comp continuous_subtype_val) (fun p => by
        simpa [mem_closedBall_zero_iff] using mem_closedBall_zero_iff.mp p.2) }
  let e' : closedBall (0 : ℂ) 1 ≃ₜ Δ := cToD.trans e
  let F : ℂ → X := fun z => if hz : z ∈ closedBall (0 : ℂ) 1 then (e' ⟨z, hz⟩).1 else γ 0
  have hFc : ContinuousOn F (closedBall 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (closedBall (0 : ℂ) 1).domRestrict F = fun z : closedBall (0 : ℂ) 1 => (e' z).1 := by
      funext z; show (if hz : z.1 ∈ closedBall (0 : ℂ) 1 then (e' ⟨z.1, hz⟩).1 else γ 0) = _
      rw [dite_eq_left z.2]
    rw [this]; exact continuous_subtype_val.comp e'.continuous
  let α : ℝ → ℂ := fun u => if hu : u ∈ Icc (0 : ℝ) 1 then (e'.symm ⟨γ u, hsub u hu⟩).1 else 0
  have hαc : ContinuousOn α (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (Icc (0 : ℝ) 1).domRestrict α = fun u : Icc (0 : ℝ) 1 => (e'.symm ⟨γ u.1, hsub u.1 u.2⟩).1 := by
      funext u; show (if hu : u.1 ∈ Icc (0 : ℝ) 1 then (e'.symm ⟨γ u.1, hsub u.1 hu⟩).1 else 0) = _
      rw [dite_eq_left u.2]
    rw [this]
    exact continuous_subtype_val.comp (e'.symm.continuous.comp
      ((continuousOn_iff_continuous_domRestrict.mp hγ).subtype_mk _))
  have hαsub : ∀ u ∈ Icc (0 : ℝ) 1, α u ∈ closedBall (0 : ℂ) 1 := fun u hu => by
    show (if hu' : u ∈ Icc (0 : ℝ) 1 then (e'.symm ⟨γ u, hsub u hu'⟩).1 else 0) ∈ closedBall (0 : ℂ) 1
    rw [dite_eq_left hu]; exact (e'.symm ⟨γ u, hsub u hu⟩).2
  have hαloop : α 0 = α 1 := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    show (if hu : (0 : ℝ) ∈ Icc (0 : ℝ) 1 then (e'.symm ⟨γ 0, hsub 0 hu⟩).1 else 0) =
      if hu : (1 : ℝ) ∈ Icc (0 : ℝ) 1 then (e'.symm ⟨γ 1, hsub 1 hu⟩).1 else 0
    rw [dite_eq_left h0, dite_eq_left h1]
    simp only [hloop]
  have hcomp : ∀ u ∈ Icc (0 : ℝ) 1, (F ∘ α) u = γ u := fun u hu => by
    show (if hz : α u ∈ closedBall (0 : ℂ) 1 then (e' ⟨α u, hz⟩).1 else γ 0) = γ u
    rw [dite_eq_left (hαsub u hu)]
    have hαu : α u = (e'.symm ⟨γ u, hsub u hu⟩).1 := by
      show (if hu' : u ∈ Icc (0 : ℝ) 1 then (e'.symm ⟨γ u, hsub u hu'⟩).1 else 0) = _
      rw [dite_eq_left hu]
    have hsub_eq : (⟨α u, hαsub u hu⟩ : closedBall (0 : ℂ) 1) = e'.symm ⟨γ u, hsub u hu⟩ :=
      Subtype.ext hαu
    rw [hsub_eq]
    exact congrArg Subtype.val (e'.apply_symm_apply ⟨γ u, hsub u hu⟩)
  have heq : cocInt φ γ = cocInt φ (F ∘ α) := by
    obtain ⟨N, hN, hc⟩ := hφ
    obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN hc hγ
    obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc (hFc.comp hαc hαsub)
    set M := max n₁ (max n₂ 1)
    have hM_pos : (0 : ℝ) < M := by
      have : 1 ≤ M := (le_max_right n₂ 1).trans (le_max_right _ _)
      exact_mod_cast (by omega : 0 < M)
    rw [hn₁ M (le_max_left _ _), hn₂ M ((le_max_left n₂ 1).trans (le_max_right _ _))]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    rw [hcomp _ ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk'.le)⟩,
      hcomp _ ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk')⟩]
  rw [heq]
  exact cocInt_eq_zero_of_in_disc hφ hFc hαc hαsub hαloop

/-- Homotopy invariance (rel endpoints) of `cocInt`. -/
theorem cocInt_homotopy {φ : X → X → A} (hφ : IsCoc φ) {H : ℝ → ℝ → X}
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, H s 0 = H 0 0) (h1 : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H 0 1) :
    cocInt φ (H 0) = cocInt φ (H 1) := by
  have hrect : IsClosedDisc (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) := (isClosedDisc_rect zero_lt_one zero_lt_one).1
  let F : ℂ → X := fun z => H (max 0 (min z.re 1)) (max 0 (min z.im 1))
  have hclamp : ∀ x : ℝ, max 0 (min x 1) ∈ Icc (0 : ℝ) 1 := fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hFc : Continuous F := by
    refine hH.comp_continuous (f := fun z : ℂ => (max 0 (min z.re 1), max 0 (min z.im 1)))
      (by fun_prop) (fun z => ⟨hclamp z.re, hclamp z.im⟩)
  have hφ' : IsCoc (fun z w => φ (F z) (F w)) := by
    obtain ⟨N, hN, hc⟩ := hφ
    refine ⟨(fun p : ℂ × ℂ => (F p.1, F p.2)) ⁻¹' N, fun z => ?_, fun x y w h1 h2 h3 => hc _ _ _ h1 h2 h3⟩
    exact (hFc.prodMap hFc).continuousAt.preimage_mem_nhds (hN (F z))
  let g₁ : ℝ → ℂ := fun u => (u : ℂ) * Complex.I
  let g₂ : ℝ → ℂ := fun u => (u : ℂ) + Complex.I
  let g₃ : ℝ → ℂ := fun u => 1 + ((1 - u : ℝ) : ℂ) * Complex.I
  let g₄ : ℝ → ℂ := fun u => ((1 - u : ℝ) : ℂ)
  have hc₁ : ContinuousOn g₁ (Icc 0 1) := by unfold g₁; fun_prop
  have hc₂ : ContinuousOn g₂ (Icc 0 1) := by unfold g₂; fun_prop
  have hc₃ : ContinuousOn g₃ (Icc 0 1) := by unfold g₃; fun_prop
  have hc₄ : ContinuousOn g₄ (Icc 0 1) := by unfold g₄; fun_prop
  have hm₁ : ∀ u ∈ Icc (0 : ℝ) 1, g₁ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := fun u hu =>
    Complex.mem_reProdIm.mpr ⟨by simp [g₁], by simpa [g₁] using hu⟩
  have hm₂ : ∀ u ∈ Icc (0 : ℝ) 1, g₂ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := fun u hu =>
    Complex.mem_reProdIm.mpr ⟨by simpa [g₂] using hu, by simp [g₂]⟩
  have hm₃ : ∀ u ∈ Icc (0 : ℝ) 1, g₃ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := fun u hu =>
    Complex.mem_reProdIm.mpr ⟨by simp [g₃], by simp [g₃]; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩
  have hm₄ : ∀ u ∈ Icc (0 : ℝ) 1, g₄ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := fun u hu =>
    Complex.mem_reProdIm.mpr ⟨by simp [g₄]; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩, by simp [g₄]⟩
  have e12 : g₁ 1 = g₂ 0 := by simp [g₁, g₂]
  have e23 : g₂ 1 = g₃ 0 := by simp [g₂, g₃]
  have e34 : g₃ 1 = g₄ 0 := by simp [g₃, g₄]
  have e41 : g₄ 1 = g₁ 0 := by simp [g₄, g₁]
  let loop := conc2 (conc2 g₁ g₂) (conc2 g₃ g₄)
  have hloop_c : ContinuousOn loop (Icc 0 1) :=
    continuousOn_conc2 (continuousOn_conc2 hc₁ hc₂ e12) (continuousOn_conc2 hc₃ hc₄ e34)
      (by rw [conc2_one e12, conc2_zero, e23])
  have hloop_mem : ∀ u ∈ Icc (0 : ℝ) 1, loop u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    intro u hu
    unfold loop conc2
    split_ifs with h1' h2' h3'
    · exact hm₁ _ ⟨by linarith [hu.1], by linarith⟩
    · exact hm₂ _ ⟨by linarith, by linarith⟩
    · exact hm₃ _ ⟨by linarith, by linarith⟩
    · exact hm₄ _ ⟨by linarith, by linarith [hu.2]⟩
  have hloop_eq : loop 0 = loop 1 := by
    show conc2 (conc2 g₁ g₂) (conc2 g₃ g₄) 0 = conc2 (conc2 g₁ g₂) (conc2 g₃ g₄) 1
    rw [conc2_zero, conc2_zero, conc2_one (by rw [conc2_one e12, conc2_zero, e23]), conc2_one e34, e41]
  have hzero := cocInt_disc_loop hφ' hrect hloop_c hloop_mem hloop_eq
  rw [cocInt_conc2 hφ' (continuousOn_conc2 hc₁ hc₂ e12) (continuousOn_conc2 hc₃ hc₄ e34)
    (by rw [conc2_one e12, conc2_zero, e23]),
    cocInt_conc2 hφ' hc₁ hc₂ e12, cocInt_conc2 hφ' hc₃ hc₄ e34] at hzero
  have hF_eval : ∀ (γ : ℝ → ℂ), ContinuousOn γ (Icc 0 1) → cocInt (fun z w => φ (F z) (F w)) γ = cocInt φ (F ∘ γ) := by
    intro γ hγc
    obtain ⟨N, hN, hc⟩ := hφ
    obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum (φ := fun z w => φ (F z) (F w))
      (N := (fun p : ℂ × ℂ => (F p.1, F p.2)) ⁻¹' N)
      (fun z => (hFc.prodMap hFc).continuousAt.preimage_mem_nhds (hN (F z)))
      (fun x y w h1 h2 h3 => hc _ _ _ h1 h2 h3) hγc
    obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc (hFc.comp_continuousOn hγc)
    set M := max n₁ n₂
    rw [hn₁ M (le_max_left _ _), hn₂ M (le_max_right _ _)]
    rfl
  rw [hF_eval g₁ hc₁, hF_eval g₂ hc₂, hF_eval g₃ hc₃, hF_eval g₄ hc₄] at hzero
  have hcongr : ∀ {α β : ℝ → X}, ContinuousOn α (Icc 0 1) → ContinuousOn β (Icc 0 1) →
      (∀ u ∈ Icc (0 : ℝ) 1, α u = β u) → cocInt φ α = cocInt φ β := by
    intro α β hα hβ heq
    obtain ⟨N, hN, hc⟩ := hφ
    obtain ⟨n₁, -, hn₁⟩ := cocInt_eq_sum hN hc hα
    obtain ⟨n₂, -, hn₂⟩ := cocInt_eq_sum hN hc hβ
    set M := max n₁ (max n₂ 1)
    have hM_pos : (0 : ℝ) < M := by
      have : 1 ≤ M := (le_max_right n₂ 1).trans (le_max_right _ _)
      exact_mod_cast (by omega : 0 < M)
    rw [hn₁ M (le_max_left _ _), hn₂ M ((le_max_left n₂ 1).trans (le_max_right _ _))]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M := Finset.mem_range.mp hk
    rw [heq _ ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk'.le)⟩,
      heq _ ⟨by positivity, (div_le_one hM_pos).mpr (by exact_mod_cast hk')⟩]
  have hconst_int : ∀ x : X, cocInt φ (fun _ => x) = 0 := fun x => by
    obtain ⟨N, hN, hc⟩ := hφ
    have h0' : φ x x = 0 := add_eq_left.mp (hc x x x (hN.mem x) (hN.mem x) (hN.mem x))
    obtain ⟨n, -, hn⟩ := cocInt_eq_sum hN hc continuousOn_const
    rw [hn n le_rfl]; simp [cocSum, h0']
  have hH0 : ContinuousOn (H 0) (Icc 0 1) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn fun u hu => ⟨by simp, hu⟩
  have hH1 : ContinuousOn (H 1) (Icc 0 1) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn fun u hu => ⟨by simp, hu⟩
  have hI1 : cocInt φ (F ∘ g₁) = cocInt φ (H 0) :=
    hcongr (hFc.comp_continuousOn hc₁) hH0 fun u hu => by
      simp [F, g₁, min_eq_left hu.2, max_eq_right hu.1]
  have hI2 : cocInt φ (F ∘ g₂) = 0 := by
    rw [hcongr (hFc.comp_continuousOn hc₂) continuousOn_const (fun u hu => by
      simp only [Function.comp_apply, F, g₂, Complex.add_re, Complex.ofReal_re, Complex.I_re,
        add_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
        min_eq_left hu.2, max_eq_right hu.1, min_self, max_eq_right zero_le_one]
      exact h1 u hu), hconst_int]
  have hI3 : cocInt φ (F ∘ g₃) = - cocInt φ (H 1) := by
    have hH1_rev : ContinuousOn (fun u => H 1 (1 - u)) (Icc 0 1) :=
      hH1.comp (f := fun u : ℝ => 1 - u) (continuous_const.sub continuous_id).continuousOn
        fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [hcongr (hFc.comp_continuousOn hc₃) hH1_rev (fun u hu => by
      simp only [Function.comp_apply, F, g₃, Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        sub_self, add_zero, Complex.add_im, Complex.one_im, Complex.mul_im, mul_one, zero_add,
        min_self, max_eq_right zero_le_one,
        min_eq_left (by linarith [hu.1] : 1 - u ≤ 1), max_eq_right (by linarith [hu.2] : 0 ≤ 1 - u)]),
      cocInt_rev hφ hH1]
  have hI4 : cocInt φ (F ∘ g₄) = 0 := by
    rw [hcongr (hFc.comp_continuousOn hc₄) continuousOn_const (fun u hu => by
      simp only [Function.comp_apply, F, g₄, Complex.ofReal_re, Complex.ofReal_im,
        min_eq_left (by linarith [hu.1] : 1 - u ≤ 1), max_eq_right (by linarith [hu.2] : 0 ≤ 1 - u),
        min_eq_left zero_le_one, max_self]
      exact h0 (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩), hconst_int]
  rw [hI1, hI2, hI3, hI4] at hzero
  have : cocInt φ (H 0) - cocInt φ (H 1) = 0 := by
    simpa [sub_eq_add_neg] using hzero
  exact sub_eq_zero.mp this

/-- Reparameterizing a curve by a continuous map `[0, 1] → [0, 1]` fixing `0` and `1` preserves
`cocInt`. -/
theorem cocInt_reparam {φ : X → X → A} (hφ : IsCoc φ) {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1))
    {τ : ℝ → ℝ} (hτ : ContinuousOn τ (Icc 0 1)) (hτm : ∀ u ∈ Icc (0 : ℝ) 1, τ u ∈ Icc (0 : ℝ) 1)
    (hτ0 : τ 0 = 0) (hτ1 : τ 1 = 1) : cocInt φ (γ ∘ τ) = cocInt φ γ := by
  let H : ℝ → ℝ → X := fun s u => γ ((1 - s) * τ u + s * u)
  have hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
    refine hγ.comp ?_ ?_
    · exact ((continuous_const.sub continuous_fst).continuousOn.mul
        (hτ.comp continuous_snd.continuousOn fun p hp => hp.2)).add
        (continuous_fst.mul continuous_snd).continuousOn
    · rintro ⟨s, u⟩ ⟨hs, hu⟩
      have ht := hτm u hu
      exact ⟨by nlinarith [hs.1, hs.2, ht.1, hu.1], by nlinarith [hs.1, hs.2, ht.2, hu.2]⟩
  have hh := cocInt_homotopy hφ hH
    (fun s _ => by simp [H, hτ0])
    (fun s _ => by simp only [H, hτ1]; congr 1; ring)
  have e0 : H 0 = γ ∘ τ := by funext u; simp [H]
  have e1 : H 1 = γ := by funext u; simp [H]
  rw [e0, e1] at hh
  exact hh

end CocInt

end GraphMinor.Surface
