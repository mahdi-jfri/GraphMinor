module

public import GraphMinor.GM06.Alg57SourceRimCoordinates
public import GraphMinor.GM06.Section5PolarHalfedgeEquiv
import GraphMinor.GM06.Section5HalfEdgeConnected
import GraphMinor.GM19.Winding
import GraphMinor.GM06.Section5PolarEdgeAccess
import GraphMinor.GM06.Section5SmallPolar
import GraphMinor.GM06.Alg57RotationRestriction

/-!
# Unique contacts with surviving source germs

The local splice proof for VI (5.7), page 133, reads the smaller
source rim in the full source coordinates. A straight coordinate
ray carried by a short directed half-spoke can meet that rim in
only the polar direction of that end. Positive winding ensures
that the coordinate direction is met at least once. Thus these
actual germ contacts satisfy the hypotheses of the cyclic-order
comparison, rather than being extra assumptions about the order.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A positively winding circle loop meets every direction. -/
theorem surjective_of_positive_circle_winding
    (v : C(Circle, Circle)) (hpos : 0 < wind (fun w => (v w : ℂ)) 0) :
    Function.Surjective v := by
  obtain ⟨L, hLc, hL⟩ := GraphMinor.GM19.exists_circle_lift_map
    ⟨fun t => v (Circle.exp t), v.continuous.comp Circle.exp.continuous⟩
  change ∀ t, Circle.exp (L t) = v (Circle.exp t) at hL
  have hAngle : GraphMinor.GM19.IsAngle (fun t => (v (Circle.exp t) : ℂ)) L := by
    refine ⟨hLc, fun t => ?_⟩
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul]
    exact (congrArg (fun w : Circle => (w : ℂ)) (hL t)).symm
  have hw : wind (fun w => (v w : ℂ)) 0 = L (2 * Real.pi) - L 0 := by
    change GraphMinor.GM19.turn (fun t => (v (Circle.exp t) : ℂ) - 0) 0 (2 * Real.pi) = _
    simp only [sub_zero]
    exact hAngle.turn_eq (fun t => Circle.coe_ne_zero _) 0 _
  have he : Circle.exp (L (2 * Real.pi)) = Circle.exp (L 0) := by
    rw [hL, hL, Circle.exp_two_pi, Circle.exp_zero]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp he
  have hnpos : (0 : ℝ) < n := by
    have hp := Real.two_pi_pos
    rw [hw] at hpos
    nlinarith only [hn, hpos, hp]
  have hnposZ : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hn1Z : (1 : ℤ) ≤ n := hnposZ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1Z
  have hlong : L 0 + 2 * Real.pi ≤ L (2 * Real.pi) := by
    have hp := Real.two_pi_pos
    nlinarith only [hn, hn1, hp]
  intro u
  by_cases hu : u = Circle.exp (L 0)
  · exact ⟨Circle.exp 0, (hL 0).symm.trans hu.symm⟩
  obtain ⟨t, ht0, htP, ht⟩ := exists_angle (z := (Circle.exp (L 0))⁻¹ * u)
    (fun heq => hu (inv_mul_eq_one.mp heq).symm)
  have hu' : Circle.exp (L 0 + t) = u := by
    rw [Circle.exp_add, ← ht]
    simp only [mul_inv_cancel_left]
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc Real.two_pi_pos.le hLc.continuousOn
    (show L 0 + t ∈ Icc (L 0) (L (2 * Real.pi)) from
      ⟨by linarith only [ht0], (show L 0 + t ≤ L 0 + 2 * Real.pi by linarith only [htP]).trans hlong⟩)
  exact ⟨Circle.exp r, (hL r).symm.trans ((congrArg Circle.exp hr).trans hu')⟩

/-- A rim point on the strict initial half-spoke has the direction
of that directed end in the actual polar half-edge bijection. -/
theorem polar_direction_of_rim_short_spoke
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} (hpV : p ∈ Γ.V)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.1))
    (a : halfEdges Γ γ p) {w : Circle}
    (hw : Φ (polarDiscPoint 1 w) ∈ spoke γ a.1 '' Ioo (0 : I) 1) :
    w = (d a).val := by
  obtain ⟨t, ht, heq⟩ := hw
  have hwe : polarRimMap Φ w ∈ a.1.1 := by
    change Φ (polarDiscPoint 1 w) ∈ a.1.1
    rw [← heq]
    exact spoke_mem_edge hγ a.2.1 ht.1
  let w' : {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e} :=
    ⟨w, a.1.1, a.2.1, hwe⟩
  let b := d.symm w'
  have hb : (d b).val = w := congrArg Subtype.val (d.apply_symm_apply w')
  obtain ⟨r, hr⟩ := hd b 1 zero_lt_one
  rw [hb] at hr
  have hab : a = b := halfedge_eq_of_short_spoke_point hγ hpV a b ht.1 ht.2
    (heq.trans hr.symm)
  rw [hab]
  exact hb.symm

/-- A straight coordinate ray carried by an actual short half-spoke
has exactly one contact with the smaller polar rim. The contact's
polar label is the actual surviving directed end. -/
theorem source_coordinate_ray_contact
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} (hpV : p ∈ Γ.V)
    {Ψ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.1))
    (f : C(Circle, ℂ)) (v : C(Circle, Circle))
    (hf : ∀ w, ‖f w‖ ≤ 1) (hf0 : ∀ w, f w ≠ 0)
    (hmap : ∀ w, Ψ (discPt (f w)) = Φ (polarDiscPoint 1 w))
    (hv : ∀ w, f w = (‖f w‖ : ℂ) * v w)
    (hvpos : 0 < wind (fun w => (v w : ℂ)) 0)
    {δ : ℝ} (hδ : ∀ w, ‖f w‖ ≤ δ)
    (a : halfEdges Γ γ p) (u : Circle)
    (hray : ∀ r : I, 0 < (r : ℝ) → (r : ℝ) ≤ δ →
      Ψ (polarDiscPoint r u) ∈ spoke γ a.1 '' Ioo (0 : I) 1) :
    v (d a).val = u ∧ ∀ w, v w = u ↔ w = (d a).val := by
  have hcontact : ∀ w, v w = u → w = (d a).val := by
    intro w hwu
    let r : I := ⟨‖f w‖, norm_nonneg _, hf w⟩
    have heq : f w = (r : ℂ) * u := (hv w).trans (by rw [hwu])
    have hpoint : Φ (polarDiscPoint 1 w) = Ψ (polarDiscPoint r u) := by
      rw [← hmap, heq, discPt_mul]
    apply polar_direction_of_rim_short_spoke hγ hpV hp d hd a
    rw [hpoint]
    exact hray r (norm_pos_iff.mpr (hf0 w)) (hδ w)
  obtain ⟨w, hw⟩ := surjective_of_positive_circle_winding v hvpos u
  have hdu : v (d a).val = u := by rw [← hcontact w hw]; exact hw
  exact ⟨hdu, fun w => ⟨hcontact w, fun heq => heq ▸ hdu⟩⟩


/-- Radial restriction preserves the actual end-to-direction
bijection. Its range subtype changes, but every direction stays
pointwise the same and remains carried by the same half-spoke. -/
theorem polar_halfedge_equiv_radial_restriction
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {p : OnePoint EuclideanPlane}
    {Φ Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.1))
    (c : I) (hc : 0 < c) (hscale : ∀ x, Φ' x = Φ (discScale c x)) :
    ∃ d' : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ' w ∈ e},
      (∀ a, (d' a).val = (d a).val) ∧
      ∀ a, ∀ t : I, 0 < t → Φ' (polarDiscPoint t (d' a).val) ∈ range (spoke γ a.1) := by
  have hW : {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e} =
      {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ' w ∈ e} := by
    ext w
    have heq (e : Set (OnePoint EuclideanPlane)) (he : e ∈ Γ.E) :
        polarRimMap Φ w ∈ e ↔ polarRimMap Φ' w ∈ e := by
      change Φ (polarDiscPoint 1 w) ∈ e ↔ Φ' (polarDiscPoint 1 w) ∈ e
      rw [hscale]
      exact polar_ray_mem_atom_iff hp (Or.inl (Or.inr he))
        (polarDiscPoint_one_ne_centre w) c hc
    exact exists_congr (fun e => and_congr_right (fun he => heq e he))
  let d' := d.trans (Set.equivOfEq hW)
  have hval (a : halfEdges Γ γ p) : (d' a).val = (d a).val := rfl
  refine ⟨d', hval, ?_⟩
  intro a t ht
  let r : I := ⟨(c : ℝ) * (t : ℝ), mul_nonneg c.property.1 t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 c.property.1).trans
      (by simpa only [mul_one] using c.property.2)⟩
  have hr : 0 < r := mul_pos hc ht
  have hpoint : discScale c (polarDiscPoint t (d a).val) = polarDiscPoint r (d a).val := by
    apply Subtype.ext
    change (c : ℝ) • planeOf ((t : ℂ) * (d a).val) =
      planeOf ((r : ℂ) * (d a).val)
    rw [← map_smul]
    apply congrArg planeOf
    change (c : ℂ) * ((t : ℂ) * (d a).val) =
      (((c : ℝ) * (t : ℝ) : ℝ) : ℂ) * (d a).val
    push_cast
    ring
  rw [hval, hscale, hpoint]
  exact hd a r hr


/-- Shrinking the smaller source chart retains every directed-end
direction and gives a positive coordinate loop below a prescribed
radius. All parts refer to the same actual smaller chart. -/
theorem exists_labeled_bounded_source_rim_directions
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {p : OnePoint EuclideanPlane} {Ψ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hΨi : Function.Injective Ψ) (hΨpos : GM06PositivePolar Ψ)
    (hΨ0 : Ψ polarCentre = p) (hnhd : p ∈ interior (range Ψ))
    (hp : IsPolar Γ p Φ) (hΦpos : GM06PositivePolar Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (d' : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ' w ∈ e})
      (f : C(Circle, ℂ)) (v : C(Circle, Circle)),
      IsPolar Γ p Φ' ∧ GM06PositivePolar Φ' ∧ range Φ' ⊆ range Φ ∧
      (∀ a, (d' a).val = (d a).val) ∧
      (∀ a, ∀ t : I, 0 < t → Φ' (polarDiscPoint t (d' a).val) ∈ range (spoke γ a.1)) ∧
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
  obtain ⟨d', hval, hd'⟩ := polar_halfedge_equiv_radial_restriction hp d hd c hc hscale
  obtain ⟨f, v, hf, hf0, hmap, hv, hvpos⟩ := exists_positive_source_rim_directions
    hΨi hΨpos hp'.inj hpos' (hp'.centre.trans hΨ0.symm)
    (hsub.trans (hOsub.trans interior_subset))
  have hbound (w : Circle) : ‖f w‖ < δ := by
    have hh := hOnorm (discPt (f w)) (by rw [hmap]; exact hsub (mem_range_self _))
    change ‖planeOf (ballClamp (f w))‖ < δ at hh
    rw [LinearIsometryEquiv.norm_map, ballClamp_of_norm_le (hf w)] at hh
    exact hh
  have hwithin : range Φ' ⊆ range Φ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨discScale c x, (hscale x).symm⟩
  exact ⟨Φ', d', f, v, hp', hpos', hwithin, hval, hd', hf, hbound, hf0, hmap, hv, hvpos⟩


/-- Localizing a positive polar half-edge chart in another open
neighbourhood preserves all of its directed-end directions. This
lets the same source chart lie in both the collapse coordinates
and the explicit cuff-calibration neighbourhood. -/
theorem exists_small_labeled_positive_polar_chart
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {p : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ p Φ) (hpos : GM06PositivePolar Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.val))
    {O : Set (OnePoint EuclideanPlane)} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (d' : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ' w ∈ e}),
      IsPolar Γ p Φ' ∧ GM06PositivePolar Φ' ∧ range Φ' ⊆ O ∧
      (∀ a, (d' a).val = (d a).val) ∧
      ∀ a, ∀ t : I, 0 < t → Φ' (polarDiscPoint t (d' a).val) ∈ range (spoke γ a.val) := by
  have hS := (IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane)
    from ⟨Homeomorph.refl _⟩)).1
  obtain ⟨c, hc, Φ', hp', hsub, hscale⟩ :=
    exists_small_polar_chart_with_factor hS hp hO hpO
  obtain ⟨d', hval, hd'⟩ := polar_halfedge_equiv_radial_restriction hp d hd c hc hscale
  exact ⟨Φ', d', hp', hpos.radial_restriction hp.inj c hc hscale, hsub, hval, hd'⟩

end GraphMinor.GM06
