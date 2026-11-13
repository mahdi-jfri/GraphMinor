module

public import GraphMinor.Surface.Jordan
public import GraphMinor.GM06.Section5PolarRimCoordinates
public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.LocalCone
import GraphMinor.Surface.Cap
import GraphMinor.GM06.Section5PolarDiscInterior
import GraphMinor.GM06.Section5PolarPathDirection
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM14.Whitney
import GraphMinor.GM11.Walks
import Mathlib.Topology.Maps.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# A disc with one radius collapsed

For the local source chart in Lemma 8 of the implementation of
VI (5.7), page 133, the incoming radius at the old target becomes
a single boundary point. The map below sends a complex point z to
(im z / 2, (norm z - re z) / 2). It collapses the positive real
radius and is one-to-one elsewhere. It takes the unit disc onto
the disc with centre i/2 and radius 1/2.

The explicit model supplies a closed-disc image for any continuous
chart collapse with precisely those fibres. This is a local fact
about the contracted star, without orientation signs for general
surface maps.
-/

public section
namespace GraphMinor.GM06
open Set Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The local quotient that collapses the positive real radius. -/
@[expose] noncomputable def section5RadiusCollapse (z : ℂ) : ℂ :=
  ⟨z.im / 2, (‖z‖ - z.re) / 2⟩

/-- The model radius collapse is continuous, including on its fibre. -/
theorem continuous_section5RadiusCollapse : Continuous section5RadiusCollapse := by
  have hrepr : section5RadiusCollapse = fun z : ℂ =>
      ((z.im / 2 : ℝ) : ℂ) + (((‖z‖ - z.re) / 2 : ℝ) : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [section5RadiusCollapse]
  rw [hrepr]
  fun_prop

/-- The collapsed fibre is exactly the nonnegative real axis. -/
theorem section5RadiusCollapse_eq_zero (z : ℂ) :
    section5RadiusCollapse z = 0 ↔ z.im = 0 ∧ 0 ≤ z.re := by
  constructor
  · intro hz
    have hy := congrArg Complex.im hz
    have hx := congrArg Complex.re hz
    change (‖z‖ - z.re) / 2 = 0 at hy
    change z.im / 2 = 0 at hx
    exact ⟨by linarith, by linarith [norm_nonneg z]⟩
  · rintro ⟨hy, hx⟩
    have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hy)
    apply Complex.ext
    · change z.im / 2 = 0
      rw [hy]; ring
    · change (‖z‖ - z.re) / 2 = 0
      rw [hz, Complex.norm_real, Real.norm_of_nonneg hx]
      simp

/-- The image lies above the real axis. -/
theorem section5RadiusCollapse_im_nonneg (z : ℂ) :
    0 ≤ (section5RadiusCollapse z).im := by
  change 0 ≤ (‖z‖ - z.re) / 2
  exact div_nonneg (sub_nonneg.mpr (Complex.re_le_norm z)) (by norm_num)

/-- Its squared norm is the old radius times its new height. -/
theorem section5RadiusCollapse_norm_sq (z : ℂ) :
    ‖section5RadiusCollapse z‖ ^ 2 = ‖z‖ * (section5RadiusCollapse z).im := by
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [Complex.sq_norm, Complex.normSq_apply]
  change (z.im / 2) * (z.im / 2) + ((‖z‖ - z.re) / 2) * ((‖z‖ - z.re) / 2) = _
  change _ = ‖z‖ * ((‖z‖ - z.re) / 2)
  nlinarith only [hz]

/-- Every fibre other than the collapsed radius is a singleton. -/
theorem section5RadiusCollapse_eq_iff (z w : ℂ) :
    section5RadiusCollapse z = section5RadiusCollapse w ↔
      z = w ∨ (section5RadiusCollapse z = 0 ∧ section5RadiusCollapse w = 0) := by
  constructor
  · intro heq
    by_cases hzero : section5RadiusCollapse z = 0
    · exact Or.inr ⟨hzero, heq.symm.trans hzero⟩
    have hheight : 0 < (section5RadiusCollapse z).im := by
      apply lt_of_le_of_ne (section5RadiusCollapse_im_nonneg z)
      intro hz
      apply hzero
      have hn := section5RadiusCollapse_norm_sq z
      have hnorm : ‖section5RadiusCollapse z‖ = 0 := by
        rw [← hz] at hn
        nlinarith only [hn, norm_nonneg (section5RadiusCollapse z)]
      exact norm_eq_zero.mp hnorm
    have hnorm : ‖z‖ = ‖w‖ := by
      have h₁ := section5RadiusCollapse_norm_sq z
      have h₂ := section5RadiusCollapse_norm_sq w
      rw [← heq] at h₂
      exact (mul_right_cancel₀ hheight.ne' (h₁.symm.trans h₂))
    have hy := congrArg Complex.im heq
    have hx := congrArg Complex.re heq
    change (‖z‖ - z.re) / 2 = (‖w‖ - w.re) / 2 at hy
    change z.im / 2 = w.im / 2 at hx
    exact Or.inl (Complex.ext (by linarith) (by linarith))
  · rintro (rfl | ⟨hz, hw⟩)
    · rfl
    · exact hz.trans hw.symm

/-- On a nonnegative radial segment the quotient is homogeneous.
In particular, the surviving rays retain their parameter order. -/
theorem section5RadiusCollapse_nonneg_smul (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    section5RadiusCollapse ((t : ℂ) * z) = (t : ℂ) * section5RadiusCollapse z := by
  apply Complex.ext <;>
    simp only [section5RadiusCollapse, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg ht] <;> ring

private theorem mem_radiusCollapse_disc (z : ℂ) :
    z ∈ closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) ↔ ‖z‖ ^ 2 ≤ z.im := by
  rw [mem_closedBall, dist_eq_norm]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  change (z.re - 0) * (z.re - 0) + (z.im - 1 / 2) * (z.im - 1 / 2) ≤
      (1 / 2 : ℝ) ^ 2 ↔ z.re * z.re + z.im * z.im ≤ z.im
  constructor <;> intro h <;> nlinarith only [h]

/-- The model quotient takes the unit disc into the tangent disc. -/
theorem section5RadiusCollapse_mem_disc {z : ℂ} (hz : ‖z‖ ≤ 1) :
    section5RadiusCollapse z ∈ closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) := by
  rw [mem_radiusCollapse_disc, section5RadiusCollapse_norm_sq]
  exact mul_le_of_le_one_left (section5RadiusCollapse_im_nonneg z) hz

/-- Every point of the tangent disc is obtained from the unit disc.
The boundary point zero is the image of the whole distinguished radius. -/
theorem section5RadiusCollapse_image_disc :
    section5RadiusCollapse '' closedBall (0 : ℂ) 1 =
      closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) := by
  apply subset_antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact section5RadiusCollapse_mem_disc (mem_closedBall_zero_iff.mp hz)
  · intro y hy
    have hybound : y.re ^ 2 + y.im ^ 2 ≤ y.im := by
      have hh := (mem_radiusCollapse_disc y).mp hy
      rw [Complex.sq_norm, Complex.normSq_apply] at hh
      nlinarith only [hh]
    by_cases hy0 : y.im = 0
    · have hyre : y.re = 0 := by nlinarith only [hybound, hy0]
      have hzero : y = 0 := Complex.ext hyre hy0
      refine ⟨0, by simp, ?_⟩
      rw [hzero]
      exact (section5RadiusCollapse_eq_zero 0).mpr (by simp)
    have hypos : 0 < y.im := by
      have hn : 0 ≤ y.im := by nlinarith only [hybound, sq_nonneg y.re, sq_nonneg y.im]
      exact lt_of_le_of_ne hn (Ne.symm hy0)
    let z : ℂ := ⟨(y.re ^ 2 - y.im ^ 2) / y.im, 2 * y.re⟩
    have hznorm : ‖z‖ = (y.re ^ 2 + y.im ^ 2) / y.im := by
      have hnonneg : 0 ≤ (y.re ^ 2 + y.im ^ 2) / y.im :=
        div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hypos.le
      apply (sq_eq_sq₀ (norm_nonneg _) hnonneg).mp
      rw [Complex.sq_norm, Complex.normSq_apply]
      change ((y.re ^ 2 - y.im ^ 2) / y.im) * ((y.re ^ 2 - y.im ^ 2) / y.im) +
        (2 * y.re) * (2 * y.re) = _
      field_simp
      ring
    refine ⟨z, mem_closedBall_zero_iff.mpr ?_, ?_⟩
    · rw [hznorm]
      exact (div_le_one hypos).mpr hybound
    · apply Complex.ext
      · change (2 * y.re) / 2 = y.re
        ring
      · change (‖z‖ - (y.re ^ 2 - y.im ^ 2) / y.im) / 2 = y.im
        rw [hznorm]
        field_simp
        ring

private theorem exists_homeomorph_ranges_of_same_fibres
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : C(X, Y)) (g : C(X, Z)) (hfib : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ h : range f ≃ₜ range g,
      ∀ x, (h ⟨f x, mem_range_self x⟩).val = g x := by
  classical
  let f' : X → range f := fun x => ⟨f x, mem_range_self x⟩
  have hfc : Continuous f' := f.continuous.rangeFactorization
  have hfs : Function.Surjective f' := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let choose : range f → X := fun y => Classical.choose y.property
  have hchoose : ∀ y : range f, f (choose y) = y.val := fun y => Classical.choose_spec y.property
  let h : range f → range g := fun y => ⟨g (choose y), mem_range_self _⟩
  have hval : ∀ x, h (f' x) = ⟨g x, mem_range_self x⟩ := by
    intro x
    apply Subtype.ext
    exact (hfib _ _).mp (hchoose (f' x))
  have hc : Continuous h := by
    apply (hfc.isClosedMap.isQuotientMap hfc hfs).continuous_iff.mpr
    exact g.continuous.rangeFactorization.congr (fun x => (hval x).symm)
  have hbij : Function.Bijective h := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      rw [← hchoose x, ← hchoose y]
      exact (hfib _ _).mpr (congrArg Subtype.val hxy)
    · rintro ⟨y, x, rfl⟩
      exact ⟨f' x, hval x⟩
  let : CompactSpace (range f) := isCompact_iff_compactSpace.mp (isCompact_range f.continuous)
  let H : range f ≃ₜ range g := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective h hbij) hc
  exact ⟨H, fun x => congrArg Subtype.val (hval x)⟩

/-- Collapsing exactly one closed polar radius gives a disc. The
homeomorphism is tied pointwise to the original collapse, so the
surviving radial germs can be read in this same chart. -/
theorem isClosedDisc_image_of_collapsing_polar_radius
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (π : C(S, S)) (Φ : C(ClosedUnitDisc, S)) (hΦ : Function.Injective Φ)
    {p : S} {A : Set S} (hfibre : π ⁻¹' {p} = A) (hi : InjOn π Aᶜ)
    (haxis : ∀ x : ClosedUnitDisc, Φ x ∈ A ↔
      (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re) :
    IsClosedDisc (range (π.comp Φ)) ∧ p ∈ discBd (range (π.comp Φ)) ∧
    ∃ H : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) ≃ₜ range (π.comp Φ),
      ∀ x : ClosedUnitDisc,
        (H ⟨section5RadiusCollapse (planeOf.symm x.val),
          section5RadiusCollapse_mem_disc (by
            rw [LinearIsometryEquiv.norm_map]
            exact mem_closedBall_zero_iff.mp x.property)⟩).val = π (Φ x) := by
  let : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  let q : C(ClosedUnitDisc, ℂ) :=
    ⟨fun x => section5RadiusCollapse (planeOf.symm x.val),
      continuous_section5RadiusCollapse.comp (planeOf.symm.continuous.comp continuous_subtype_val)⟩
  have hcoords : range (fun x : ClosedUnitDisc => planeOf.symm x.val) =
      closedBall (0 : ℂ) 1 := by
    apply subset_antisymm
    · rintro z ⟨x, rfl⟩
      rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp x.property
    · intro z hz
      refine ⟨⟨planeOf z, ?_⟩, planeOf.symm_apply_apply z⟩
      rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp hz
  have hqrange : range q = closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) := by
    change range (section5RadiusCollapse ∘ (fun x : ClosedUnitDisc => planeOf.symm x.val)) = _
    rw [range_comp, hcoords, section5RadiusCollapse_image_disc]
  have hΦaxis : ∀ x : ClosedUnitDisc, Φ x ∈ A ↔ q x = 0 := fun x =>
    (haxis x).trans (section5RadiusCollapse_eq_zero _).symm
  have hπA : ∀ x ∈ A, π x = p := fun x hx => show x ∈ π ⁻¹' {p} from hfibre.symm ▸ hx
  have hker : ∀ x y, q x = q y ↔ (π.comp Φ) x = (π.comp Φ) y := by
    intro x y
    constructor
    · intro hxy
      rcases (section5RadiusCollapse_eq_iff _ _).mp hxy with hcoord | ⟨hx, hy⟩
      · have heq : x = y := Subtype.ext (planeOf.symm.injective hcoord)
        exact congrArg (π.comp Φ) heq
      · exact (hπA _ ((hΦaxis x).mpr hx)).trans (hπA _ ((hΦaxis y).mpr hy)).symm
    · intro hxy
      by_cases hx : Φ x ∈ A
      · have hy : Φ y ∈ A := by
          rw [← hfibre]
          exact hxy.symm.trans (hπA _ hx)
        exact ((hΦaxis x).mp hx).trans ((hΦaxis y).mp hy).symm
      · have hy : Φ y ∉ A := by
          intro hy
          exact hx (hfibre ▸ hxy.trans (hπA _ hy))
        have heq : x = y := hΦ (hi hx hy hxy)
        exact congrArg q heq
  obtain ⟨h, hval⟩ := exists_homeomorph_ranges_of_same_fibres q (π.comp Φ) hker
  let H := (Homeomorph.setCongr hqrange.symm).trans h
  have hdisc : IsClosedDisc (closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) :=
    (isClosedDisc_of_convex (convex_closedBall _ _) (by
      rw [interior_closedBall _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      exact ⟨⟨0, 1 / 2⟩, mem_ball_self (by norm_num)⟩)
      isBounded_closedBall isClosed_closedBall).1
  have h0bd : (0 : ℂ) ∈ discBd (closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) := by
    rw [(isClosedDisc_of_convex (convex_closedBall _ _) (by
      rw [interior_closedBall _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      exact ⟨⟨0, 1 / 2⟩, mem_ball_self (by norm_num)⟩)
      isBounded_closedBall isClosed_closedBall).2,
      frontier_closedBall _ (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere, dist_eq_norm]
    have hc : (⟨0, 1 / 2⟩ : ℂ) = (1 / 2 : ℂ) * Complex.I := by
      apply Complex.ext <;> norm_num
    rw [zero_sub, norm_neg, hc, norm_mul, Complex.norm_I, mul_one]
    norm_num
  obtain ⟨z, hzbd, hz0⟩ := h0bd
  have hnewbd : (H z).val ∈ discBd (range (π.comp Φ)) := by
    refine ⟨H z, ?_, rfl⟩
    rw [← image_bd_homeomorph H]
    exact mem_image_of_mem H hzbd
  have hzq : z = ⟨q polarCentre, hqrange ▸ mem_range_self polarCentre⟩ := by
    apply Subtype.ext
    change z.val = section5RadiusCollapse (planeOf.symm polarCentre.val)
    rw [hz0]
    symm
    apply (section5RadiusCollapse_eq_zero _).mpr
    simp [polarCentre]
  have hpoint : (H z).val = p := by
    rw [hzq]
    exact (hval polarCentre).trans (hπA _ ((hΦaxis polarCentre).mpr (by
      apply (section5RadiusCollapse_eq_zero _).mpr
      simp [polarCentre])))
  obtain ⟨D⟩ := hdisc
  exact ⟨⟨D.trans H⟩, hpoint ▸ hnewbd, H, hval⟩

/-- Rotation of the parameter disc puts any chosen incoming ray on
the positive real axis. It changes no radial parameter. -/
@[expose] noncomputable def section5RotateDisc (w : Circle) : ClosedUnitDisc ≃ₜ ClosedUnitDisc where
  toFun x := ⟨planeOf ((w : ℂ) * planeOf.symm x.val), by
    simp only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map,
      norm_mul, Circle.norm_coe, one_mul, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.property⟩
  invFun x := ⟨planeOf (((w⁻¹ : Circle) : ℂ) * planeOf.symm x.val), by
    simp only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map,
      norm_mul, Circle.norm_coe, one_mul, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.property⟩
  left_inv x := by
    apply Subtype.ext
    change planeOf (((w⁻¹ : Circle) : ℂ) *
      planeOf.symm (planeOf ((w : ℂ) * planeOf.symm x.val))) = x.val
    simp only [planeOf.symm_apply_apply, ← mul_assoc, ← Circle.coe_mul,
      inv_mul_cancel, Circle.coe_one, one_mul, planeOf.apply_symm_apply]
  right_inv x := by
    apply Subtype.ext
    change planeOf ((w : ℂ) *
      planeOf.symm (planeOf (((w⁻¹ : Circle) : ℂ) * planeOf.symm x.val))) = x.val
    simp only [planeOf.symm_apply_apply, ← mul_assoc, ← Circle.coe_mul,
      mul_inv_cancel, Circle.coe_one, one_mul, planeOf.apply_symm_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Disc rotation preserves the order along each surviving ray. -/
theorem section5RotateDisc_polarDiscPoint (w u : Circle) (t : I) :
    section5RotateDisc w (polarDiscPoint t u) = polarDiscPoint t (w * u) := by
  apply Subtype.ext
  change planeOf ((w : ℂ) * planeOf.symm (planeOf ((t : ℂ) * u))) =
    planeOf ((t : ℂ) * (w * u : Circle))
  rw [planeOf.symm_apply_apply, Circle.coe_mul]
  congr 1
  ring

private theorem disc_axis_iff (x : ClosedUnitDisc) :
    (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re ↔
      ∃ t : I, x = polarDiscPoint t 1 := by
  constructor
  · rintro ⟨hy, hx⟩
    let t : I := ⟨(planeOf.symm x.val).re, hx,
      (Complex.re_le_norm _).trans (by
        rw [LinearIsometryEquiv.norm_map]
        exact mem_closedBall_zero_iff.mp x.property)⟩
    refine ⟨t, Subtype.ext ?_⟩
    apply planeOf.symm.injective
    change planeOf.symm x.val = planeOf.symm (planeOf ((t : ℂ) * 1))
    rw [planeOf.symm_apply_apply, mul_one]
    exact Complex.ext rfl hy
  · rintro ⟨t, rfl⟩
    change (planeOf.symm (planeOf ((t : ℂ) * 1))).im = 0 ∧
      0 ≤ (planeOf.symm (planeOf ((t : ℂ) * 1))).re
    rw [planeOf.symm_apply_apply]
    simp only [mul_one, Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact t.property.1

/-- A polar chart at a path endpoint has an interior point off
that path. Take half of the direction opposite its unique rim
contact. This supplies a retained reference point for winding. -/
theorem exists_interior_polar_point_off_path
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ P : Drawing S} (hP : P.IsSubdrawing Γ)
    {v t : S} (f : Curve S) (hf : ParametrizesSet f P.U v t)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) :
    ∃ x : ClosedUnitDisc, ‖x.val‖ < 1 ∧ Φ x ∉ P.U := by
  obtain ⟨w, _, huniq⟩ := exists_unique_polar_rim_direction_of_path hP f hf hp
  have hn : IsGammaNice Γ P.U := isGammaNice_of_frontier hP subset_rfl
    (frontier_subset_closure.trans (by rw [P.isClosed_U.closure_eq]))
  let r : I := ⟨1 / 2, by constructor <;> norm_num⟩
  have hr : 0 < r := by change (0 : ℝ) < 1 / 2; norm_num
  refine ⟨polarDiscPoint r (-w), ?_, ?_⟩
  · rw [norm_polarDiscPoint]
    change (1 / 2 : ℝ) < 1
    norm_num
  · intro hx
    apply Circle.neg_ne_self w
    apply huniq
    obtain ⟨a, ha, hbase, hscaled⟩ := hp.ray (polarDiscPoint 1 (-w))
      (polarDiscPoint_one_ne_centre _) r hr
    rw [discScale_polarDiscPoint_one] at hscaled
    exact nice_atom hn ha ⟨Φ (polarDiscPoint r (-w)), hscaled, hx⟩ hbase

/-- At a path endpoint, the entire inverse image of the path in a
polar chart is a single closed radius. Its direction is obtained
from the path, not supplied as extra chart data. -/
theorem exists_polar_path_direction_preimage
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ P : Drawing S} (hP : P.IsSubdrawing Γ)
    {v t : S} (f : Curve S) (hf : ParametrizesSet f P.U v t)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) :
    ∃ w : Circle, ∀ x : ClosedUnitDisc, Φ x ∈ P.U ↔ ∃ r : I, x = polarDiscPoint r w := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_polar_rim_direction_of_path hP f hf hp
  have hn : IsGammaNice Γ P.U := isGammaNice_of_frontier hP subset_rfl
    (frontier_subset_closure.trans (by rw [P.isClosed_U.closure_eq]))
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  have hpre : ∀ x : ClosedUnitDisc, Φ x ∈ P.U ↔ ∃ r : I, x = polarDiscPoint r w := by
    intro x
    constructor
    · intro hx
      by_cases hxv : Φ x = v
      · refine ⟨0, hp.inj ?_⟩
        have hz : polarDiscPoint 0 w = polarCentre := by
          apply Subtype.ext
          simp [polarDiscPoint, polarCentre]
        rw [hz, hp.centre]
        exact hxv
      obtain ⟨r, hr, hxr⟩ := hrepr (Φ x) ⟨mem_range_self x, hxv⟩
      have hqw : q (Φ x) = w := by
        apply huniq
        obtain ⟨a, ha, hbase, hscaled⟩ := hp.ray (polarDiscPoint 1 (q (Φ x)))
          (polarDiscPoint_one_ne_centre _) r hr
        rw [discScale_polarDiscPoint_one, hxr] at hscaled
        exact nice_atom hn ha ⟨Φ x, hscaled, hx⟩ hbase
      rw [hqw] at hxr
      exact ⟨r, (hp.inj hxr).symm⟩
    · rintro ⟨r, rfl⟩
      have hh := hp.star P.isClosed_U hn hw r
      rwa [discScale_polarDiscPoint_one] at hh
  exact ⟨w, hpre⟩

/-- Rotating the actual path direction onto the positive axis gives
the exact model fibre used in the radius collapse. -/
theorem polar_path_axis_after_rotation
    {S : Type*} [TopologicalSpace S] (Φ : C(ClosedUnitDisc, S)) {A : Set S} (w : Circle)
    (hpre : ∀ x : ClosedUnitDisc, Φ x ∈ A ↔ ∃ r : I, x = polarDiscPoint r w) :
    ∀ x : ClosedUnitDisc, Φ (section5RotateDisc w x) ∈ A ↔
      (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re := by
  intro x
  rw [disc_axis_iff, hpre]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, (section5RotateDisc w).injective ?_⟩
    rw [section5RotateDisc_polarDiscPoint, mul_one]
    exact hr
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [section5RotateDisc_polarDiscPoint, mul_one]⟩

/-- The image of an actual polar chart at the end of a path is a
disc after that path is collapsed. The single collapsed ray is
obtained from the path and the polar chart, rather than assumed.
The collapsed point lies on its boundary. This constructs the
target-star disc for the source splice. -/
theorem isClosedDisc_image_polar_of_path_endpoint_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ P : Drawing S} (hP : P.IsSubdrawing Γ)
    {v t : S} (f : Curve S) (hf : ParametrizesSet f P.U v t)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (π : C(S, S)) {p : S} (hfibre : π ⁻¹' {p} = P.U)
    (hi : InjOn π P.Uᶜ) :
    IsClosedDisc (π '' range Φ) ∧ p ∈ discBd (π '' range Φ) := by
  obtain ⟨w, hpre⟩ := exists_polar_path_direction_preimage hP f hf hp
  let R := section5RotateDisc w
  let Ψ : C(ClosedUnitDisc, S) := Φ.comp ⟨R, R.continuous⟩
  have haxis : ∀ x : ClosedUnitDisc, Ψ x ∈ P.U ↔
      (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re :=
    polar_path_axis_after_rotation Φ w hpre
  have hdisc := isClosedDisc_image_of_collapsing_polar_radius π Ψ
    (hp.inj.comp R.injective) hfibre hi haxis
  have hImage : range (π.comp Ψ) = π '' range Φ := by
    change range (π ∘ (Φ ∘ R)) = _
    rw [range_comp, range_comp, R.surjective.range_eq, image_univ]
  exact hImage ▸ ⟨hdisc.1, hdisc.2.1⟩

/-- At the target of the contracted non-loop edge, the old polar
disc has a closed-disc image. This applies directly to the
cuff-augmented drawing, whose source need not have valency one.
The collapsed source lies on the new disc boundary. -/
theorem isClosedDisc_image_polar_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ : Drawing S} {e : Set S} {s v : S}
    (hl : Γ.toGraph.IsLink e s v) (hvs : v ≠ s)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (π : C(S, S)) {p : S} (hfibre : π ⁻¹' {p} = closure e)
    (hi : InjOn π (closure e)ᶜ) :
    IsClosedDisc (π '' range Φ) ∧ p ∈ discBd (π '' range Φ) := by
  let W : GraphWalk Γ.toGraph v s := .cons hl.symm (.nil hl.left_mem)
  let P := walkDrawing Γ W
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds
    (GM14.Whitney.closure_line hl.symm hvs)
  have hvcl : v ∈ closure e := hf.2.1 ▸ (show v ∈ range f from ⟨0, hf.2.2.1⟩)
  have hscl : s ∈ closure e := hf.2.1 ▸ (show s ∈ range f from ⟨1, hf.2.2.2⟩)
  have hPU : P.U = closure e := by
    ext x
    change x ∈ (walkDrawing Γ W).U ↔ x ∈ closure e
    rw [mem_walkDrawing_U]
    simp only [W, GraphWalk.support, GraphWalk.edges, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_left]
    constructor
    · rintro ((rfl | rfl) | hx)
      · exact hvcl
      · exact hscl
      · exact hx
    · intro hx
      exact Or.inr hx
  exact isClosedDisc_image_polar_of_path_endpoint_collapse (walkDrawing_isSubdrawing Γ W)
    f (hPU.symm ▸ hf) hp π (hfibre.trans hPU.symm) (by rw [hPU]; exact hi)

end GraphMinor.GM06
