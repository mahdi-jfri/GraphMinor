module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.GM06.Section5CappedCollapse
import GraphMinor.GM06.Alg57ChartOrientation
import GraphMinor.GM06.Section5CollapsedRadius
import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5SmallPolar
import GraphMinor.GM06.Section5PolarShrink
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM06.Section5PolarDiscInterior
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.GM19.Winding

/-!
# Shrinking the positive rotation charts of VI (5.7)

The local contraction proof reads a rotation in a sufficiently small
neighbourhood. Positive radial restriction keeps the boundary winding
and every directed-end label of the supplied chart. Thus the same row
can be interpreted in any prescribed open neighbourhood of its vertex.

The winding calculation uses the radial annulus inside one embedded
disc. Its circles form a homotopy missing the centre. No assertion
about orientation signs of surface homeomorphisms is used.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 unitInterval

/-- All positive concentric radii of an embedded disc wind equally
around its centre. -/
theorem wind_polar_rim_eq_of_radius (Z : C(ClosedUnitDisc, ℂ))
    (hi : Function.Injective Z) (c : I) (hc : 0 < c) :
    wind (fun w => Z (polarDiscPoint c w)) (Z polarCentre) =
      wind (fun w => Z (polarDiscPoint 1 w)) (Z polarCentre) := by
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  have hcl : Continuous cl := by fun_prop
  have hclmem : ∀ u, cl u ∈ Icc (0 : ℝ) 1 := fun u =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  let r : ℝ → I := fun u => ⟨(1 - cl u) * c.val + cl u, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hclmem u).2) c.2.1) (hclmem u).1
    · calc
        (1 - cl u) * c.val + cl u ≤ (1 - cl u) * 1 + cl u :=
          add_le_add (mul_le_mul_of_nonneg_left c.2.2
            (sub_nonneg.mpr (hclmem u).2)) le_rfl
        _ = 1 := by ring⟩
  have hr : Continuous r := Continuous.subtype_mk
    (((continuous_const.sub hcl).mul continuous_const).add hcl) _
  have hrpos : ∀ u, 0 < (r u : ℝ) := by
    intro u
    change 0 < (1 - cl u) * c.val + cl u
    by_cases hu : cl u = 1
    · rw [hu]; norm_num
    · have hu' : cl u < 1 := lt_of_le_of_ne (hclmem u).2 hu
      exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hu') hc) (hclmem u).1
  have hpolar : Continuous (fun q : I × Circle => polarDiscPoint q.1 q.2) := by
    apply Continuous.subtype_mk
    change Continuous (fun q : I × Circle => planeOf ((q.1 : ℂ) * q.2))
    fun_prop
  let H : ℝ → ℝ → ℂ := fun u t => Z (polarDiscPoint (r u) (Circle.exp t)) - Z polarCentre
  have hH : Continuous (fun q : ℝ × ℝ => H q.1 q.2) :=
    (Z.continuous.comp (hpolar.comp ((hr.comp continuous_fst).prodMk
      (Circle.exp.continuous.comp continuous_snd)))).sub continuous_const
  have hne : ∀ u t, H u t ≠ 0 := by
    intro u t he
    have hp := hi (sub_eq_zero.mp he)
    have hn := congrArg (fun p : ClosedUnitDisc => ‖p.val‖) hp
    rw [norm_polarDiscPoint] at hn
    have hz : ‖(polarCentre : ClosedUnitDisc).val‖ = 0 := by simp [polarCentre]
    rw [hz] at hn
    exact (hrpos u).ne' hn
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, exp_add_two_pi]
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := by
    intro t
    obtain ⟨t', ht', n, rfl⟩ := exists_mem_period t
    exact ⟨_, ht', fun u => ((hper u).sub_zsmul_eq n).symm⟩
  have hh := turn_eq_of_homotopy hH hne isCompact_Icc hv
    (s := 0) (t := 2 * Real.pi) (fun u => by
      have hp := hper u 0
      rw [zero_add] at hp
      exact hp.symm) 0 1
  have hr0 : r 0 = c := Subtype.ext (by simp [r, cl])
  have hr1 : r 1 = 1 := Subtype.ext (by simp [r, cl])
  simpa only [wind, H, hr0, hr1] using hh

/-- Positivity in the plane survives a positive radial restriction. -/
theorem GM06PositivePolar.radial_restriction
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hi : Function.Injective Φ) (hpos : GM06PositivePolar Φ)
    (c : I) (hc : 0 < c) (hscale : ∀ x, Ψ x = Φ (discScale c x)) :
    GM06PositivePolar Ψ := by
  obtain ⟨F, hF, hwind⟩ := hpos
  let F' : C(ClosedUnitDisc, EuclideanPlane) :=
    ⟨fun x => F (discScale c x), F.continuous.comp
      (continuous_discScale.comp (continuous_const.prodMk continuous_id))⟩
  let Z : C(ClosedUnitDisc, ℂ) := ⟨fun x => complexPlane.symm (F x),
    complexPlane.symm.continuous.comp F.continuous⟩
  have hZi : Function.Injective Z := by
    intro x y hxy
    apply hi
    rw [hF, hF]
    exact congrArg (fun p : EuclideanPlane => (p : OnePoint EuclideanPlane))
      (complexPlane.symm.injective hxy)
  refine ⟨F', fun x => (hscale x).trans (hF _), ?_⟩
  have hcentre : discScale c polarCentre = polarCentre :=
    Subtype.ext (by simp [discScale, polarCentre])
  have hradial : ∀ w, discScale c (polarDiscPoint 1 w) = polarDiscPoint c w :=
    discScale_polarDiscPoint_one c
  change 0 < wind (fun w => Z (discScale c (polarDiscPoint 1 w))) (Z (discScale c polarCentre))
  simp only [hcentre, hradial]
  rw [wind_polar_rim_eq_of_radius Z hZi c hc]
  exact hwind

/-- The same positive chart, angle labels, spoke labels and rim
incidence of a supplied nontrivial row can be read in any smaller
open neighbourhood. This is the unchanged-row localization used
in the drawing-level proof of Reduction 3. -/
theorem GM06SuccessorRotationRowRep.exists_small_chart
    {Γ : GraphMinor.Surface.Drawing (OnePoint EuclideanPlane)} {m : ℕ}
    {edge : Fin m ≃ Γ.E} {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) (hlarge : 1 < xs.length)
    {O : Set (OnePoint EuclideanPlane)} (hO : IsOpen O) (hv : v ∈ O) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : ℕ → Circle),
      IsPolar Γ v Φ ∧ GM06PositivePolar Φ ∧ range Φ ⊆ O ∧
      Set.InjOn z {r | r ∈ xs} ∧
      xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
      (∀ a : halfEdges Γ γ v, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t (z (halfEdgeLabel edge a))) ∈ range (spoke γ a.1)) ∧
      ∀ (j : Fin m) (w : Circle),
        polarRimMap Φ w ∈ (edge j).val ↔ ∃ r ∈ xs,
          z r = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1) := by
  rcases hrow.2.2 with hsmall | ⟨Φ, z, hp, hpos, hi, hs, hspoke, hlabel⟩
  · exact False.elim ((not_lt_of_ge hsmall) hlarge)
  obtain ⟨c, hc, Ψ, hΨ, hΨO, hscale⟩ :=
    exists_small_polar_chart_with_factor (IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from ⟨Homeomorph.refl _⟩)).1 hp hO hv
  refine ⟨Ψ, z, hΨ, hpos.radial_restriction hp.inj c hc hscale, hΨO, hi, hs, ?_, ?_⟩
  · intro a t ht
    rw [hscale, discScale_polarDiscPoint]
    exact hspoke a (c * t) (mul_pos hc ht)
  · intro j w
    have hn : IsGammaNice Γ (edge j).val :=
      ⟨{(edge j).val}, by simpa only [singleton_subset_iff] using
        (show (edge j).val ∈ Γ.A from Or.inl (Or.inr (edge j).property)), by simp⟩
    exact (polar_rim_mem_nice_iff_of_radial_restriction hp c hc hscale hn w).symm.trans
      (hlabel j w)

/-- The rim of an embedded disc winds equally around each of its
interior points. Move the point along its radial segment, which
cannot meet the rim because its radius remains less than one. -/
theorem wind_polar_rim_eq_at_interior_point (Z : C(ClosedUnitDisc, ℂ))
    (hi : Function.Injective Z) (x₀ : ClosedUnitDisc) (hx₀ : ‖x₀.val‖ < 1) :
    wind (fun w => Z (polarDiscPoint 1 w)) (Z x₀) =
      wind (fun w => Z (polarDiscPoint 1 w)) (Z polarCentre) := by
  let u : ℝ → I := fun t => ⟨clampUnit t, clampUnit_mem t⟩
  have hu : Continuous u := continuous_clampUnit.subtype_mk _
  have hu0 : u 0 = 0 := Subtype.ext clampUnit_zero
  have hu1 : u 1 = 1 := Subtype.ext clampUnit_one
  let P : ℝ → ClosedUnitDisc := fun t => discScale (u t) x₀
  have hP : Continuous P := continuous_discScale.comp (hu.prodMk continuous_const)
  have hne : ∀ t w, Z (polarDiscPoint 1 w) ≠ Z (P t) := by
    intro t w heq
    have hnorm := congrArg (fun x : ClosedUnitDisc => ‖x.val‖) (hi heq)
    rw [norm_polarDiscPoint] at hnorm
    have hlt : ‖(P t).val‖ < 1 := by
      change ‖((u t : ℝ) • x₀.val)‖ < 1
      rw [norm_smul, Real.norm_of_nonneg (u t).property.1]
      exact (mul_le_of_le_one_left (norm_nonneg x₀.val) (u t).property.2).trans_lt hx₀
    exact (ne_of_lt hlt) hnorm.symm
  have heq := wind_eq_of_family
    (F := fun _ w => Z (polarDiscPoint 1 w))
    ((Z.continuous.comp (polarRimMap (ContinuousMap.id ClosedUnitDisc)).continuous).comp continuous_snd)
    (Z.continuous.comp hP) hne 1 0
  simpa only [Function.comp_apply, P, hu0, hu1, discScale_zero, discScale_one] using heq

/-- The old rim stays positive around any retained interior point
when moved by the capped rectangular homotopy. This also applies
when the old centre is collapsed, as in the target-star disc of
Lemma 8. Only the chosen interior point needs a singleton fibre. -/
theorem GM06PositivePolar.capped_rectangle_rim
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y)
    {Φ Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hi : Function.Injective Φ) (hpos : GM06PositivePolar Φ)
    (x₀ : ClosedUnitDisc) (hx₀ : ‖x₀.val‖ < 1)
    (hc : Φ x₀ ∉ cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}))
    (hΦ' : ∀ x, Φ' x = K (1, Φ x)) :
    ∃ F' : C(ClosedUnitDisc, EuclideanPlane),
      (∀ x, Φ' x = (F' x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w => complexPlane.symm (F' (polarDiscPoint 1 w)))
        (complexPlane.symm (F' x₀)) := by
  obtain ⟨Ψ, hΨ, hwind⟩ := hpos
  let E : EuclideanPlane ≃ₜ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph
  have hfinite : ∀ q : I × ClosedUnitDisc,
      K (q.1, Φ q.2) ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) := by
    intro q
    apply OnePoint.ne_infty_iff_exists.mp
    apply capped_rectangle_homotopy_ne_infty e H K hchart hout hK hoff q.1
    rw [hΨ]
    exact OnePoint.coe_ne_infty _
  let F : C(I × ClosedUnitDisc, EuclideanPlane) :=
    ⟨fun q => E.symm ⟨K (q.1, Φ q.2), hfinite q⟩,
      E.symm.continuous.comp ((K.continuous.comp
        (continuous_fst.prodMk (Φ.continuous.comp continuous_snd))).subtype_mk hfinite)⟩
  have hcoe : ∀ t x, (F (t, x) : OnePoint EuclideanPlane) = K (t, Φ x) := by
    intro t x
    exact congrArg Subtype.val (E.apply_symm_apply ⟨K (t, Φ x), hfinite (t, x)⟩)
  have hzero : ∀ x, F (0, x) = Ψ x := by
    intro x
    apply OnePoint.coe_injective
    rw [hcoe, hK0, hΨ]
  let F' : C(ClosedUnitDisc, EuclideanPlane) :=
    ⟨fun x => F (1, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨F', fun x => (hΦ' x).trans (hcoe 1 x).symm, ?_⟩
  let u : ℝ → I := fun t => ⟨clampUnit t, clampUnit_mem t⟩
  have hu : Continuous u := continuous_clampUnit.subtype_mk _
  have hu0 : u 0 = 0 := Subtype.ext clampUnit_zero
  have hu1 : u 1 = 1 := Subtype.ext clampUnit_one
  let B : ℝ → Circle → ℂ := fun t w => complexPlane.symm (F (u t, polarDiscPoint 1 w))
  let c : ℝ → ℂ := fun t => complexPlane.symm (F (u t, x₀))
  have hB : Continuous (fun q : ℝ × Circle => B q.1 q.2) :=
    complexPlane.symm.continuous.comp (F.continuous.comp
      ((hu.comp continuous_fst).prodMk
        ((polarRimMap (ContinuousMap.id ClosedUnitDisc)).continuous.comp continuous_snd)))
  have hcentre : Continuous c := complexPlane.symm.continuous.comp
    (F.continuous.comp (hu.prodMk continuous_const))
  have hne : ∀ t w, B t w ≠ c t := by
    intro t w heq
    have heqF : F (u t, polarDiscPoint 1 w) = F (u t, x₀) :=
      complexPlane.symm.injective heq
    have heqS := congrArg (fun p : EuclideanPlane => (p : OnePoint EuclideanPlane)) heqF
    rw [hcoe, hcoe] at heqS
    have heqΦ := (capped_rectangle_homotopy_eq_iff_off_segment e H K hchart hout hK hoff
      hc (u t) (Φ (polarDiscPoint 1 w))).mp heqS
    have hn := congrArg (fun x : ClosedUnitDisc => ‖x.val‖) (hi heqΦ)
    rw [norm_polarDiscPoint] at hn
    exact (ne_of_lt hx₀) hn.symm
  have heq := wind_eq_of_family hB hcentre hne 0 1
  have htime0 : wind (B 0) (c 0) =
      wind (fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)))
        (complexPlane.symm (Ψ x₀)) := by
    simp only [B, c, hu0, hzero]
  have htime1 : wind (B 1) (c 1) =
      wind (fun w => complexPlane.symm (F' (polarDiscPoint 1 w)))
        (complexPlane.symm (F' x₀)) := by
    simp only [B, c, hu1, F', ContinuousMap.coe_mk]
  rw [htime0, htime1] at heq
  have hwind₀ : 0 < wind (fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)))
      (complexPlane.symm (Ψ x₀)) := by
    have hZi : Function.Injective (fun x => complexPlane.symm (Ψ x)) := by
      intro a b hab
      apply hi
      rw [hΨ, hΨ]
      exact congrArg (fun x : EuclideanPlane => (x : OnePoint EuclideanPlane))
        (complexPlane.symm.injective hab)
    have hh := wind_polar_rim_eq_at_interior_point
      ⟨fun x => complexPlane.symm (Ψ x), complexPlane.symm.continuous.comp Ψ.continuous⟩ hZi x₀ hx₀
    change wind (fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)))
      (complexPlane.symm (Ψ x₀)) = wind (fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)))
        (complexPlane.symm (Ψ polarCentre)) at hh
    rw [hh]
    exact hwind
  exact heq ▸ hwind₀

/-- A retained chart stays positive when moved by the actual capped
rectangular homotopy. Its rim never meets its moving centre, by the
singleton-fibre calculation. Winding is compared along this explicit
family, without assigning orientation signs to arbitrary maps. -/
theorem GM06PositivePolar.capped_rectangle_image
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y)
    {Φ Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hi : Function.Injective Φ) (hpos : GM06PositivePolar Φ)
    (hc : Φ polarCentre ∉ cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}))
    (hΦ' : ∀ x, Φ' x = K (1, Φ x)) : GM06PositivePolar Φ' := by
  obtain ⟨F', hF', hwind⟩ := hpos.capped_rectangle_rim e H K hchart hout hK hoff hK0 hi
    polarCentre (by simp [polarCentre]) hc hΦ'
  exact ⟨F', hF', hwind⟩

/-- The target-star disc of an actual endpoint-path collapse has
positive boundary winding. Its merged source is on the boundary,
and an interior reference point off the collapsed path is supplied
by the polar chart itself. No new orientation datum is assumed. -/
theorem GM06PositivePolar.capped_rectangle_endpoint_disc
    {Γ P : Surface.Drawing (OnePoint EuclideanPlane)} (hP : P.IsSubdrawing Γ)
    {v t : OnePoint EuclideanPlane} (f : Curve (OnePoint EuclideanPlane))
    (hf : ParametrizesSet f P.U v t)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ v Φ) (hpos : GM06PositivePolar Φ)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    {p : OnePoint EuclideanPlane} (hfibre : π ⁻¹' {p} = P.U) (hi : InjOn π P.Uᶜ)
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y) (hK1 : ∀ y, K (1, y) = π y)
    (hsegment : P.U = cylinderToSphere ''
      ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})) :
    IsClosedDisc (π '' range Φ) ∧ p ∈ discBd (π '' range Φ) ∧
    ∃ (x₀ : ClosedUnitDisc) (F' : C(ClosedUnitDisc, EuclideanPlane)),
      ‖x₀.val‖ < 1 ∧ Φ x₀ ∉ P.U ∧
      (∀ x, π (Φ x) = (F' x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w => complexPlane.symm (F' (polarDiscPoint 1 w)))
        (complexPlane.symm (F' x₀)) := by
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from
        ⟨Homeomorph.refl _⟩)).1
  obtain ⟨hdisc, hboundary⟩ := isClosedDisc_image_polar_of_path_endpoint_collapse
    hP f hf hp π hfibre hi
  obtain ⟨x₀, hx₀, hx₀off⟩ := exists_interior_polar_point_off_path hP f hf hp
  obtain ⟨F', hF', hwind⟩ := hpos.capped_rectangle_rim e H K hchart hout hK hoff hK0
    hp.inj x₀ hx₀ (by rw [← hsegment]; exact hx₀off)
    (Φ' := π.comp Φ) (fun x => (hK1 (Φ x)).symm)
  exact ⟨hdisc, hboundary, x₀, F', hx₀, hx₀off, hF', hwind⟩

end GraphMinor.GM06
