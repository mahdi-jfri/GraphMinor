module

public import GraphMinor.GM06.Alg57SourceContactOrder
public import GraphMinor.GM06.Alg57PolarStar
import GraphMinor.GM06.Alg57RotationRestriction
import GraphMinor.GM06.Section5SmallPolar
import GraphMinor.GM06.Section5PolarDiscInterior

/-!
# The smaller source rim in the full collapse chart

In Lemma 8 of the implementation of VI (5.7), page 133, the full
source chart is already positive and contains the explicit images
of the target germs. A positive polar chart at the new source can
be shrunk into this neighbourhood. Reading its rim with the inverse
of the full chart gives a nonzero complex loop. Its directions have
positive winding by the chart-loop calculation, so unique germ
contacts can be compared by the contact-order lemma.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Read the rim of a smaller positive chart through the inverse of
the full source chart. Its coordinate directions wind positively,
and their radial factors and actual sphere images are retained. -/
theorem exists_positive_source_rim_directions
    {Ψ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hΨi : Function.Injective Ψ) (hΨpos : GM06PositivePolar Ψ)
    (hΦi : Function.Injective Φ) (hΦpos : GM06PositivePolar Φ)
    (hcentre : Φ polarCentre = Ψ polarCentre) (hsub : range Φ ⊆ range Ψ) :
    ∃ (f : C(Circle, ℂ)) (v : C(Circle, Circle)),
      (∀ w, ‖f w‖ ≤ 1) ∧ (∀ w, f w ≠ 0) ∧
      (∀ w, Ψ (discPt (f w)) = Φ (polarDiscPoint 1 w)) ∧
      (∀ w, f w = (‖f w‖ : ℂ) * v w) ∧
      0 < wind (fun w => (v w : ℂ)) 0 := by
  let e : ClosedUnitDisc ≃ₜ range Ψ :=
    (Ψ.continuous.isClosedEmbedding hΨi).isEmbedding.toHomeomorph
  let T : C(ClosedUnitDisc, ClosedUnitDisc) :=
    ⟨fun x => e.symm ⟨Φ x, hsub (mem_range_self x)⟩,
      e.symm.continuous.comp (Φ.continuous.subtype_mk _)⟩
  have hT (x : ClosedUnitDisc) : Ψ (T x) = Φ x :=
    congrArg Subtype.val (e.apply_symm_apply ⟨Φ x, hsub (mem_range_self x)⟩)
  have hT0 : T polarCentre = polarCentre := hΨi ((hT _).trans hcentre)
  let f : C(Circle, ℂ) :=
    ⟨fun w => planeOf.symm (T (polarDiscPoint 1 w)).val,
      planeOf.symm.continuous.comp (continuous_subtype_val.comp
        (T.continuous.comp (show Continuous (fun w : Circle => polarDiscPoint 1 w) by
          unfold polarDiscPoint; fun_prop)))⟩
  have hf : ∀ w, ‖f w‖ ≤ 1 := by
    intro w
    change ‖planeOf.symm (T (polarDiscPoint 1 w)).val‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp (T _).property
  have hdisc (w : Circle) : discPt (f w) = T (polarDiscPoint 1 w) := by
    apply Subtype.ext
    change planeOf (ballClamp (f w)) = _
    rw [ballClamp_of_norm_le (hf w)]
    exact planeOf.apply_symm_apply _
  have hf0 : ∀ w, f w ≠ 0 := by
    intro w heq
    have hTc : T (polarDiscPoint 1 w) = polarCentre := by
      rw [← hdisc, heq, discPt_zero]
    have hΦc : Φ (polarDiscPoint 1 w) = Φ polarCentre :=
      (hT _).symm.trans ((congrArg Ψ hTc).trans hcentre.symm)
    have hx := congrArg (fun x : ClosedUnitDisc => ‖x.val‖) (hΦi hΦc)
    rw [norm_polarDiscPoint] at hx
    simpa [polarCentre] using hx
  obtain ⟨F, hF, hFpos⟩ := hΨpos
  let χ : ℂ → ℂ := fun z => complexPlane.symm (F (discPt z))
  have hχc : Continuous χ := complexPlane.symm.continuous.comp
    (F.continuous.comp continuous_discPt)
  have hFi : Function.Injective F := by
    intro x y heq
    apply hΨi
    rw [hF, hF, heq]
  have hχi : InjOn χ (closedBall 0 1) := by
    intro x hx y hy heq
    exact discPt_injOn hx hy (hFi (complexPlane.symm.injective heq))
  have hχrim : ∀ w : Circle, χ w = complexPlane.symm (F (polarDiscPoint 1 w)) := by
    intro w
    dsimp only [χ]
    have hh := discPt_mul 1 w
    simpa only [Icc.coe_one, Complex.ofReal_one, one_mul] using congrArg
      (fun x => complexPlane.symm (F x)) hh
  have hχzero : χ 0 = complexPlane.symm (F polarCentre) := by
    dsimp only [χ]
    rw [discPt_zero]
  have hchart : 0 < wind (fun w : Circle => χ w) (χ 0) := by
    simpa only [hχrim, hχzero] using hFpos
  obtain ⟨F', hF', hF'pos⟩ := hΦpos
  have hFcoords (w : Circle) : F (discPt (f w)) = F' (polarDiscPoint 1 w) := by
    apply OnePoint.coe_injective
    rw [← hF, hdisc, hT, hF']
  have hFzero : F polarCentre = F' polarCentre := by
    apply OnePoint.coe_injective
    rw [← hF, ← hF', hcentre]
  have hloop : 0 < wind (fun w => χ (f w)) (χ 0) := by
    simpa only [χ, hFcoords, discPt_zero, hFzero] using hF'pos
  obtain ⟨v, hv, hvpos⟩ := exists_positive_coordinate_direction_loop χ hχc hχi f hf hf0
    hchart hloop
  exact ⟨f, v, hf, hf0, fun w => (congrArg Ψ (hdisc w)).trans (hT _), hv, hvpos⟩

/-- A positive polar chart at the source can be read as a positive
coordinate direction loop in any given positive full neighbourhood
chart. The smaller chart is constructed by radial restriction. -/
theorem exists_small_positive_source_rim_directions
    {Γ : Drawing (OnePoint EuclideanPlane)} {p : OnePoint EuclideanPlane}
    {Ψ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hΨi : Function.Injective Ψ) (hΨpos : GM06PositivePolar Ψ)
    (hΨ0 : Ψ polarCentre = p) (hnhd : p ∈ interior (range Ψ))
    (hp : IsPolar Γ p Φ) (hΦpos : GM06PositivePolar Φ) :
    ∃ (Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (f : C(Circle, ℂ)) (v : C(Circle, Circle)),
      IsPolar Γ p Φ' ∧ GM06PositivePolar Φ' ∧ range Φ' ⊆ interior (range Ψ) ∧
      (∀ w, ‖f w‖ ≤ 1) ∧ (∀ w, f w ≠ 0) ∧
      (∀ w, Ψ (discPt (f w)) = Φ' (polarDiscPoint 1 w)) ∧
      (∀ w, f w = (‖f w‖ : ℂ) * v w) ∧
      0 < wind (fun w => (v w : ℂ)) 0 := by
  have hS := (IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane)
    from ⟨Homeomorph.refl _⟩)).1
  obtain ⟨c, hc, Φ', hp', hsub, hscale⟩ :=
    exists_small_polar_chart_with_factor hS hp isOpen_interior hnhd
  have hpos' := hΦpos.radial_restriction hp.inj c hc hscale
  obtain ⟨f, v, hf, hf0, hmap, hv, hvpos⟩ := exists_positive_source_rim_directions
    hΨi hΨpos hp'.inj hpos' (hp'.centre.trans hΨ0.symm)
    (hsub.trans interior_subset)
  exact ⟨Φ', f, v, hp', hpos', hsub, hf, hf0, hmap, hv, hvpos⟩


/-- A full source chart has an open neighbourhood whose inverse
coordinates have norm below any prescribed positive bound. Remove
the compact image of the parameter points outside that bound. -/
theorem exists_source_coordinate_neighbourhood
    {Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hi : Function.Injective Ψ) {p : OnePoint EuclideanPlane}
    (hcentre : Ψ polarCentre = p) (hnhd : p ∈ interior (range Ψ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ O : Set (OnePoint EuclideanPlane), IsOpen O ∧ p ∈ O ∧
      O ⊆ interior (range Ψ) ∧ ∀ x : ClosedUnitDisc, Ψ x ∈ O → ‖x.val‖ < δ := by
  let A : Set ClosedUnitDisc := {x | δ ≤ ‖x.val‖}
  have hA : IsClosed A := isClosed_le continuous_const continuous_subtype_val.norm
  have hclosed : IsClosed (Ψ '' A) := (hA.isCompact.image Ψ.continuous).isClosed
  refine ⟨interior (range Ψ) \ (Ψ '' A), isOpen_interior.inter hclosed.isOpen_compl,
    ⟨hnhd, ?_⟩, sdiff_subset, ?_⟩
  · rintro ⟨x, hx, hxp⟩
    have hx0 : x = polarCentre := hi (hxp.trans hcentre.symm)
    subst x
    have hn : ‖(polarCentre : ClosedUnitDisc).val‖ = 0 := by simp [polarCentre]
    exact hδ.not_ge (hn ▸ hx)
  · intro x hx
    exact lt_of_not_ge (fun hle => hx.2 ⟨x, hle, rfl⟩)

/-- The smaller positive source rim may be chosen within any fixed
positive coordinate radius. This supplies a uniform radius below
the finite collection of retained half-spoke lengths. -/
theorem exists_bounded_positive_source_rim_directions
    {Γ : Drawing (OnePoint EuclideanPlane)} {p : OnePoint EuclideanPlane}
    {Ψ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hΨi : Function.Injective Ψ) (hΨpos : GM06PositivePolar Ψ)
    (hΨ0 : Ψ polarCentre = p) (hnhd : p ∈ interior (range Ψ))
    (hp : IsPolar Γ p Φ) (hΦpos : GM06PositivePolar Φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (f : C(Circle, ℂ)) (v : C(Circle, Circle)),
      IsPolar Γ p Φ' ∧ GM06PositivePolar Φ' ∧
      (∀ w, ‖f w‖ ≤ 1) ∧ (∀ w, ‖f w‖ < δ) ∧ (∀ w, f w ≠ 0) ∧
      (∀ w, Ψ (discPt (f w)) = Φ' (polarDiscPoint 1 w)) ∧
      (∀ w, f w = (‖f w‖ : ℂ) * v w) ∧
      0 < wind (fun w => (v w : ℂ)) 0 := by
  obtain ⟨O, hOo, hpO, hOsub, hOnorm⟩ :=
    exists_source_coordinate_neighbourhood hΨi hΨ0 hnhd hδ
  have hS := (IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane)
    from ⟨Homeomorph.refl _⟩)).1
  obtain ⟨c, hc, Φ', hp', hsub, hscale⟩ :=
    exists_small_polar_chart_with_factor hS hp hOo hpO
  have hpos' := hΦpos.radial_restriction hp.inj c hc hscale
  obtain ⟨f, v, hf, hf0, hmap, hv, hvpos⟩ := exists_positive_source_rim_directions
    hΨi hΨpos hp'.inj hpos' (hp'.centre.trans hΨ0.symm)
    (hsub.trans (hOsub.trans interior_subset))
  have hbound (w : Circle) : ‖f w‖ < δ := by
    have hh := hOnorm (discPt (f w)) (by rw [hmap]; exact hsub (mem_range_self _))
    change ‖planeOf (ballClamp (f w))‖ < δ at hh
    rw [LinearIsometryEquiv.norm_map, ballClamp_of_norm_le (hf w)] at hh
    exact hh
  exact ⟨Φ', f, v, hp', hpos', hf, hbound, hf0, hmap, hv, hvpos⟩

end GraphMinor.GM06
