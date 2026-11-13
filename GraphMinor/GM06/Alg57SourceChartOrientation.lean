module

public import GraphMinor.GM06.Alg57SourceDiscChart
public import GraphMinor.GM06.Alg57RotationRestriction
import GraphMinor.GM06.Alg57PolarStar
import GraphMinor.GM06.Alg57ChartOrientation
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.GM11.Walks
import GraphMinor.GM14.Whitney
import GraphMinor.GM06.Section5ContractedEdgeParam
import GraphMinor.GM06.Section5PolarRay
import GraphMinor.GM06.Section4OpenSubarc

/-!
# Positive orientation of the full contracted-source chart

For Lemma 8 of the implementation of VI (5.7), page 133, the full
source chart agrees with the collapsed target star. Its tangent
model boundary is the unit circle scaled by one half, rotated by
a quarter turn, and translated to i/2. Comparing the winding of
that circle with the full chart rim proves the chart positive.
The reference point is the model image of the opposite half-radius,
which remains outside the collapsed edge throughout the homotopy.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 unitInterval

/-- The half-radius point opposite the incoming model ray. -/
@[expose] noncomputable def section5OppositeRadiusPoint : ClosedUnitDisc :=
  ⟨planeOf (-1 / 2 : ℂ), by
    simp only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    norm_num⟩

/-- The opposite half-radius lies strictly inside the old star. -/
theorem norm_section5OppositeRadiusPoint : ‖section5OppositeRadiusPoint.val‖ = 1 / 2 := by
  change ‖planeOf (-1 / 2 : ℂ)‖ = _
  rw [LinearIsometryEquiv.norm_map]
  norm_num

/-- The old target rim becomes the positively traversed tangent circle. -/
theorem section5RadiusCollapse_circle (w : Circle) :
    section5RadiusCollapse w = (⟨0, 1 / 2⟩ : ℂ) - (Complex.I / 2) * w := by
  apply Complex.ext <;> simp only [section5RadiusCollapse, Circle.norm_coe,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.I_re, Complex.I_im] <;> ring

/-- The retained opposite half-radius becomes the centre of the tangent disc. -/
theorem section5RadiusCollapse_opposite :
    section5RadiusCollapse (planeOf.symm section5OppositeRadiusPoint.val) = (⟨0, 1 / 2⟩ : ℂ) := by
  change section5RadiusCollapse (planeOf.symm (planeOf (-1 / 2 : ℂ))) = _
  rw [planeOf.symm_apply_apply]
  apply Complex.ext <;> norm_num [section5RadiusCollapse]

/-- The tangent rim and the full source rim wind equally in any
injective full chart. The quarter-turn reparametrization keeps its
orientation. -/
theorem wind_collapsed_radius_rim (χ : C(ClosedUnitDisc, ℂ)) (hi : Function.Injective χ) :
    wind (fun w => χ (section5CollapsedRadiusDiscPoint (polarDiscPoint 1 w)))
      (χ (section5CollapsedRadiusDiscPoint section5OppositeRadiusPoint)) =
    wind (fun w => χ (polarDiscPoint 1 w)) (χ polarCentre) := by
  let f : ℂ → ℂ := fun z => χ (discPt z)
  have hfc : Continuous f := χ.continuous.comp continuous_discPt
  have hfi : InjOn f (closedBall 0 1) := fun x hx y hy heq =>
    discPt_injOn hx hy (hi heq)
  let p : ℂ := ⟨0, 1 / 2⟩
  let r : ℝ := 1 / 2
  let u : Circle := ⟨-Complex.I, by
    show -Complex.I ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_I]⟩
  have hr : 0 < r := by norm_num [r]
  have hpNorm : ‖p‖ = 1 / 2 := by
    have heq : p = (1 / 2 : ℂ) * Complex.I := by apply Complex.ext <;> norm_num [p]
    rw [heq, norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hsub : closedBall p r ⊆ closedBall (0 : ℂ) 1 := by
    intro z hz
    exact mem_closedBall_zero_iff.mpr (section5_tangent_disc_norm_le hz)
  have hround (w : Circle) : p + (r : ℂ) * w ∈ closedBall p r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Circle.norm_coe,
      Complex.norm_real, Real.norm_of_nonneg hr.le, mul_one]
  have hp : p ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hpNorm]; norm_num
  have hpClosed : p ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hp
  have hne : ∀ w : Circle, f (p + (r : ℂ) * w) ≠ f p := by
    intro w heq
    have hh := hfi (hsub (hround w)) hpClosed heq
    have he : (r : ℂ) * w = 0 := add_left_cancel (hh.trans (add_zero p).symm)
    have hn := congrArg norm he
    rw [norm_mul, Circle.norm_coe, Complex.norm_real, Real.norm_of_nonneg hr.le,
      norm_zero, mul_one] at hn
    exact hr.ne' hn
  have hrotation := wind_eq_turn_rotate
    (hfc.comp (by fun_prop : Continuous fun w : Circle => p + (r : ℂ) * w)) hne u
  change wind (fun w : Circle => f (p + (r : ℂ) * w)) (f p) =
    wind (fun w : Circle => f (p + (r : ℂ) * (u * w : Circle))) (f p) at hrotation
  have hq (w : Circle) : f (p + (r : ℂ) * (u * w : Circle)) =
      χ (section5CollapsedRadiusDiscPoint (polarDiscPoint 1 w)) := by
    apply congrArg χ
    apply Subtype.ext
    change planeOf (ballClamp (p + (r : ℂ) * (u * w : Circle))) =
      planeOf (section5RadiusCollapse (planeOf.symm (planeOf (((1 : I) : ℂ) * w))))
    rw [ballClamp_of_norm_le (mem_closedBall_zero_iff.mp (hsub (hround (u * w)))),
      planeOf.symm_apply_apply, Icc.coe_one, Complex.ofReal_one, one_mul,
      section5RadiusCollapse_circle, Circle.coe_mul]
    apply congrArg planeOf
    change p + (r : ℂ) * (-Complex.I * w) = (⟨0, 1 / 2⟩ : ℂ) - Complex.I / 2 * w
    dsimp only [p, r]
    push_cast
    ring
  have hcentre : f p = χ (section5CollapsedRadiusDiscPoint section5OppositeRadiusPoint) := by
    apply congrArg χ
    apply Subtype.ext
    change planeOf (ballClamp p) = planeOf (section5RadiusCollapse (planeOf.symm section5OppositeRadiusPoint.val))
    rw [ballClamp_of_norm_le (mem_closedBall_zero_iff.mp hpClosed), section5RadiusCollapse_opposite]
  have hrim (w : Circle) : f w = χ (polarDiscPoint 1 w) := by
    simpa only [f, Icc.coe_one, Complex.ofReal_one, one_mul] using congrArg χ (discPt_mul 1 w)
  have hzero : f 0 = χ polarCentre := congrArg χ discPt_zero
  calc
    _ = wind (fun w : Circle => f (p + (r : ℂ) * (u * w : Circle))) (f p) := by
      simp only [hq, hcentre]
    _ = wind (fun w : Circle => f (p + (r : ℂ) * w)) (f p) := hrotation.symm
    _ = wind (fun w : Circle => f w) (f p) := wind_round_eq_circle hfc hfi hr hsub
    _ = wind (fun w : Circle => f w) (f 0) := wind_circle_eq_centre hfc hfi hp
    _ = _ := by simp only [hrim, hzero]

/-- The full source chart constructed from the actual radius
collapse is positive. Its sign is proved along the given rectangular
homotopy and the two explicit rims, without an assumed source order. -/
theorem positive_full_chart_of_radius_collapse
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)) (hK1 : ∀ y, K (1, y) = π y)
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hΦ : Function.Injective Φ) (hpos : GM06PositivePolar Φ)
    (haxis : ∀ x : ClosedUnitDisc,
      Φ x ∈ cylinderToSphere '' ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}) ↔
        (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re)
    (χ : C(ClosedUnitDisc, ℂ)) (hχ : ∀ x, Ψ x = (complexPlane (χ x) : OnePoint EuclideanPlane))
    (hΨ : Function.Injective Ψ)
    (hmatch : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) = π (Φ x)) : GM06PositivePolar Ψ := by
  have hx : ‖section5OppositeRadiusPoint.val‖ < 1 := by
    rw [norm_section5OppositeRadiusPoint]
    norm_num
  have hxoff : Φ section5OppositeRadiusPoint ∉ cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}) := by
    rw [haxis]
    change ¬ ((planeOf.symm (planeOf (-1 / 2 : ℂ))).im = 0 ∧
      0 ≤ (planeOf.symm (planeOf (-1 / 2 : ℂ))).re)
    rw [planeOf.symm_apply_apply]
    norm_num
  obtain ⟨F, hF, hwind⟩ := hpos.capped_rectangle_rim e H K hchart hout hK hoff hK0 hΦ
    section5OppositeRadiusPoint hx hxoff (Φ' := π.comp Φ) (fun x => (hK1 (Φ x)).symm)
  have hχi : Function.Injective χ := by
    intro x y heq
    apply hΨ
    rw [hχ x, hχ y, heq]
  have hvalue : ∀ x, χ (section5CollapsedRadiusDiscPoint x) = complexPlane.symm (F x) := by
    intro x
    have hh := (hχ (section5CollapsedRadiusDiscPoint x)).symm.trans ((hmatch x).trans (hF x))
    have hp := congrArg complexPlane.symm (OnePoint.coe_injective hh)
    exact (complexPlane.symm_apply_apply _).symm.trans hp
  refine ⟨⟨fun x => complexPlane (χ x), complexPlane.continuous.comp χ.continuous⟩, hχ, ?_⟩
  simp only [ContinuousMap.coe_mk, complexPlane.symm_apply_apply]
  rw [← wind_collapsed_radius_rim χ hχi]
  simpa only [hvalue] using hwind

/-- Rotating a positive parameter disc to the incoming ray keeps
its positive winding and fixes its centre. -/
theorem GM06PositivePolar.disc_rotate
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hpos : GM06PositivePolar Φ)
    (hi : Function.Injective Φ) (w : Circle) :
    GM06PositivePolar (Φ.comp ⟨section5RotateDisc w, (section5RotateDisc w).continuous⟩) := by
  obtain ⟨F, hF, hwind⟩ := hpos
  have hzero : section5RotateDisc w polarCentre = polarCentre := by
    apply Subtype.ext
    change planeOf ((w : ℂ) * planeOf.symm 0) = 0
    simp
  let B : Circle → ℂ := fun z => complexPlane.symm (F (polarDiscPoint 1 z))
  have hBc : Continuous B := complexPlane.symm.continuous.comp (polarRimMap F).continuous
  have hne : ∀ z, B z ≠ complexPlane.symm (F polarCentre) := by
    intro z heq
    apply polarDiscPoint_one_ne_centre z
    apply hi
    rw [hF, hF]
    exact congrArg (fun x : EuclideanPlane => (x : OnePoint EuclideanPlane))
      (complexPlane.symm.injective heq)
  have hrotation := wind_eq_turn_rotate hBc hne w
  change wind B (complexPlane.symm (F polarCentre)) =
    wind (fun z => B (w * z)) (complexPlane.symm (F polarCentre)) at hrotation
  refine ⟨F.comp ⟨section5RotateDisc w, (section5RotateDisc w).continuous⟩, fun x => hF _, ?_⟩
  change 0 < wind (fun z => complexPlane.symm (F (section5RotateDisc w (polarDiscPoint 1 z))))
    (complexPlane.symm (F (section5RotateDisc w polarCentre)))
  rw [hzero]
  simp only [section5RotateDisc_polarDiscPoint]
  exact hrotation ▸ hwind

/-- The actual rectangular radius collapse admits a positive full
source chart with its exact quotient coordinates. Finiteness in the
plane follows from the capped homotopy, rather than being assumed
as a new input to the construction. -/
theorem exists_positive_full_chart_of_radius_collapse
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)) (hK1 : ∀ y, K (1, y) = π y)
    {p : OnePoint EuclideanPlane}
    (hfibre : π ⁻¹' {p} = cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}))
    (hi : InjOn π (cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}))ᶜ)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hΦ : Function.Injective Φ) (hpos : GM06PositivePolar Φ)
    (haxis : ∀ x : ClosedUnitDisc,
      Φ x ∈ cylinderToSphere '' ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}) ↔
        (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re) :
    ∃ (Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (χ : C(ClosedUnitDisc, ℂ)),
      (∀ x, Ψ x = (complexPlane (χ x) : OnePoint EuclideanPlane)) ∧
      Function.Injective Ψ ∧ Ψ polarCentre = p ∧ Ψ polarCentre ∈ interior (range Ψ) ∧
      GM06PositivePolar Ψ ∧ ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) = π (Φ x) := by
  have hfinite : range (π.comp Φ) ⊆ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) := by
    obtain ⟨F, hF, _⟩ := hpos
    rintro y ⟨x, rfl⟩
    apply OnePoint.ne_infty_iff_exists.mp
    change π (Φ x) ≠ OnePoint.infty
    rw [← hK1 (Φ x)]
    apply capped_rectangle_homotopy_ne_infty e H K hchart hout hK hoff 1
    rw [hF]
    exact OnePoint.coe_ne_infty _
  obtain ⟨Ψ, χ, hχ, hΨi, hΨ0, hΨnhd, hmatch⟩ :=
    exists_full_chart_of_polar_radius_collapse π Φ hΦ hfibre hi haxis hfinite
  have hpositive := positive_full_chart_of_radius_collapse e H K hchart hout hK hoff hK0 π
    hK1 hΦ hpos haxis χ hχ hΨi hmatch
  exact ⟨Ψ, χ, hχ, hΨi, hΨ0, hΨnhd, hpositive, hmatch⟩

/-- An actual path-end contraction has a positive full source
chart. The incoming direction and the exact model fibre are derived
from the path and its old polar chart. The surviving germs retain
their pointwise quotient coordinates after rotating by that direction. -/
theorem exists_positive_full_chart_of_path_endpoint_collapse
    {Γ P : Surface.Drawing (OnePoint EuclideanPlane)} (hP : P.IsSubdrawing Γ)
    {v t : OnePoint EuclideanPlane} (f : Curve (OnePoint EuclideanPlane))
    (hf : ParametrizesSet f P.U v t)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ v Φ)
    (hpos : GM06PositivePolar Φ)
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)) (hK1 : ∀ y, K (1, y) = π y)
    {p : OnePoint EuclideanPlane} (hfibre : π ⁻¹' {p} = P.U) (hi : InjOn π P.Uᶜ)
    (hsegment : P.U = cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})) :
    ∃ (w : Circle) (Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (χ : C(ClosedUnitDisc, ℂ)),
      (∀ x, Φ x ∈ P.U ↔ ∃ r : I, x = polarDiscPoint r w) ∧
      (∀ x, Ψ x = (complexPlane (χ x) : OnePoint EuclideanPlane)) ∧
      Function.Injective Ψ ∧ Ψ polarCentre = p ∧ Ψ polarCentre ∈ interior (range Ψ) ∧
      GM06PositivePolar Ψ ∧ ∀ x,
        Ψ (section5CollapsedRadiusDiscPoint x) = π (Φ (section5RotateDisc w x)) := by
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) := IsClosedSurface.locallyConnectedSpace
    (GM11.IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from ⟨Homeomorph.refl _⟩)).1
  obtain ⟨w, hpre⟩ := exists_polar_path_direction_preimage hP f hf hp
  let R := section5RotateDisc w
  let F : C(ClosedUnitDisc, OnePoint EuclideanPlane) := Φ.comp ⟨R, R.continuous⟩
  have hF : Function.Injective F := hp.inj.comp R.injective
  have hFpos : GM06PositivePolar F := hpos.disc_rotate hp.inj w
  have haxis : ∀ x : ClosedUnitDisc,
      F x ∈ cylinderToSphere '' ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}) ↔
        (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re := by
    rw [← hsegment]
    exact polar_path_axis_after_rotation Φ w hpre
  obtain ⟨Ψ, χ, hχ, hΨi, hΨ0, hΨnhd, hΨpos, hmatch⟩ :=
    exists_positive_full_chart_of_radius_collapse e H K hchart hout hK hoff hK0 π hK1
      (hfibre.trans hsegment) (by rw [← hsegment]; exact hi) hF hFpos haxis
  exact ⟨w, Ψ, χ, hpre, hχ, hΨi, hΨ0, hΨnhd, hΨpos, hmatch⟩


/-- For an actual non-loop edge, the full positive quotient chart
uses exactly the incoming end's direction from the old target row.
The path through the closed edge supplies the model fibre, and its
rim contact identifies that direction uniquely. -/
theorem exists_positive_full_chart_of_closed_edge_collapse
    {Γ : Surface.Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {a : Set (OnePoint EuclideanPlane)} {s v : OnePoint EuclideanPlane}
    (hl : Γ.toGraph.IsLink a s v) (hvs : v ≠ s)
    (incoming : halfEdges Γ γ v) (hin : incoming.val.1 = a)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ v Φ)
    (hpos : GM06PositivePolar Φ) (u : Circle)
    (hu : ∀ t : I, 0 < t → Φ (polarDiscPoint t u) ∈ range (spoke γ incoming.val))
    {D : Set ClosedCylinder} (E : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (E z).val) = (E (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)) (hK1 : ∀ y, K (1, y) = π y)
    (hfibre : π ⁻¹' {s} = closure a) (hi : InjOn π (closure a)ᶜ)
    (hsegment : closure a = cylinderToSphere ''
      ((fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})) :
    ∃ (Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (χ : C(ClosedUnitDisc, ℂ)),
      (∀ x, Ψ x = (complexPlane (χ x) : OnePoint EuclideanPlane)) ∧
      Function.Injective Ψ ∧ Ψ polarCentre = s ∧ s ∈ interior (range Ψ) ∧
      GM06PositivePolar Ψ ∧ ∀ x,
        Ψ (section5CollapsedRadiusDiscPoint x) = π (Φ (section5RotateDisc u x)) := by
  let W : GraphWalk Γ.toGraph v s := .cons hl.symm (.nil hl.left_mem)
  let P := walkDrawing Γ W
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds
    (GM14.Whitney.closure_line hl.symm hvs)
  have hvcl : v ∈ closure a := hf.2.1 ▸ (show v ∈ range f from ⟨0, hf.2.2.1⟩)
  have hscl : s ∈ closure a := hf.2.1 ▸ (show s ∈ range f from ⟨1, hf.2.2.2⟩)
  have hPU : P.U = closure a := by
    ext x
    change x ∈ (walkDrawing Γ W).U ↔ x ∈ closure a
    rw [mem_walkDrawing_U]
    simp only [W, GraphWalk.support, GraphWalk.edges, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_left]
    constructor
    · rintro ((rfl | rfl) | hx)
      · exact hvcl
      · exact hscl
      · exact hx
    · exact fun hx => Or.inr hx
  obtain ⟨w, Ψ, χ, hpre, hχ, hΨi, hΨ0, hnhd, hpositive, hmatch⟩ :=
    exists_positive_full_chart_of_path_endpoint_collapse (walkDrawing_isSubdrawing Γ W)
      f (hPU.symm ▸ hf) hp hpos E H K hchart hout hK hoff hK0 π hK1
      (hfibre.trans hPU.symm) (by rw [hPU]; exact hi) (hPU.trans hsegment)
  have hmem : Φ (polarDiscPoint 1 u) ∈ P.U := by
    rw [hPU, ← range_eq_closure_of_edgePar hγ hl.edge_mem]
    obtain ⟨t, ht⟩ := hu 1 zero_lt_one
    refine ⟨halfPar incoming.val.2 t, ?_⟩
    change γ incoming.val.1 (halfPar incoming.val.2 t) = _ at ht
    simpa only [hin] using ht
  obtain ⟨r, hr⟩ := (hpre (polarDiscPoint 1 u)).mp hmem
  have huw : u = w := polarDiscPoint_direction_eq zero_lt_one hr
  subst w
  exact ⟨Ψ, χ, hχ, hΨi, hΨ0, hΨ0 ▸ hnhd, hpositive, hmatch⟩

end GraphMinor.GM06
