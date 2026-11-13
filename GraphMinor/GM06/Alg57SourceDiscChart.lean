module

public import GraphMinor.GM06.Section5CollapsedRadius
import GraphMinor.Surface.OpenDisc
import GraphMinor.Surface.Cap
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.Surface.PlaneOrientation
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Extending the coordinates of the collapsed target star

For the source neighbourhood in Lemma 8 of the implementation of
VI (5.7), page 133, the old target star has already become a disc
with the merged source on its boundary. Its model is the disc
centred at i/2 with radius 1/2, tangent to the real axis at zero.

Extend its inverse coordinates across a larger plane disc by the
proved disc-extension theorem. The extended coordinates cover the
ball of radius two. Their inverse on the unit disc is consequently
a full neighbourhood chart at the source, and agrees with the
original target-star coordinates at every model point. In
particular, the surviving target germs keep their explicit rays.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11

private theorem tangent_centre_norm : ‖(⟨0, 1 / 2⟩ : ℂ)‖ = 1 / 2 := by
  have h : (⟨0, 1 / 2⟩ : ℂ) = (1 / 2 : ℂ) * Complex.I := by
    apply Complex.ext <;> norm_num
  rw [h, norm_mul, Complex.norm_I, mul_one]
  norm_num

theorem section5_tangent_disc_norm_le {z : ℂ}
    (hz : z ∈ closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) : ‖z‖ ≤ 1 := by
  have hzdist : ‖z - (⟨0, 1 / 2⟩ : ℂ)‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hn : ‖z‖ ≤ ‖z - (⟨0, 1 / 2⟩ : ℂ)‖ + ‖(⟨0, 1 / 2⟩ : ℂ)‖ := by
    calc
      ‖z‖ = ‖(z - (⟨0, 1 / 2⟩ : ℂ)) + (⟨0, 1 / 2⟩ : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [tangent_centre_norm] at hn
  linarith

theorem section5_zero_mem_tangent_disc :
    (0 : ℂ) ∈ closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) := by
  rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, tangent_centre_norm]

private theorem extend_disc_coordinates
    {D : Set ℂ} (hD : IsClosedDisc D) {ψ : ℂ → ℂ}
    (hc : ContinuousOn ψ D) (hi : InjOn ψ D) :
    ∃ (E : Set ℂ) (ψ' : ℂ → ℂ),
      IsClosedDisc E ∧ D ⊆ E ∧ ContinuousOn ψ' E ∧ InjOn ψ' E ∧
      EqOn ψ' ψ D ∧ closedBall 0 2 ⊆ ψ' '' E := by
  obtain ⟨R, hR, hbound⟩ := hD.isCompact.isBounded.exists_pos_norm_lt
  have hdisc := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) R) (by
    rw [interior_closedBall _ hR.ne']
    exact ⟨0, mem_ball_self hR⟩) isBounded_closedBall isClosed_closedBall
  have hsub : D ⊆ discInt (closedBall (0 : ℂ) R) := by
    intro z hz
    refine ⟨mem_closedBall_zero_iff.mpr (hbound z hz).le, ?_⟩
    rw [hdisc.2, frontier_closedBall _ hR.ne', mem_sphere, dist_zero_right]
    exact (hbound z hz).ne
  obtain ⟨ψ', hψ'c, hψ'i, hψ'eq, hcover⟩ := exists_extension_step hD hdisc.1
    isManifoldPoint_complex hsub hc hi 2
  exact ⟨closedBall 0 R, ψ', hdisc.1, hsub.trans (discInt_subset _),
    hψ'c, hψ'i, hψ'eq, hcover⟩

/-- The collapsed target-star coordinates extend to a full source
chart. The new chart agrees with the given disc homeomorphism at
every point of the tangent model, rather than just on its boundary.
No cyclic order or polar property is required as an extra premise. -/
theorem exists_full_chart_of_collapsed_radius_disc
    {D : Set ℂ} (hD : IsClosedDisc D)
    (H : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) ≃ₜ D) :
    ∃ Φ : C(ClosedUnitDisc, ℂ), Function.Injective Φ ∧
      Φ polarCentre = (H ⟨0, section5_zero_mem_tangent_disc⟩).val ∧
      Φ polarCentre ∈ interior (range Φ) ∧
      ∀ z : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2),
        Φ ⟨planeOf z.val, by
          rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
          exact section5_tangent_disc_norm_le z.property⟩ = (H z).val := by
  classical
  let ψ : ℂ → ℂ := fun z => if hz : z ∈ D then (H.symm ⟨z, hz⟩).val else 0
  have hψ : ∀ z : D, ψ z.val = (H.symm z).val := by
    intro z
    simp only [ψ, dite_eq_left z.property]
  have hψc : ContinuousOn ψ D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp H.symm.continuous).congr (fun z => (hψ z).symm)
  have hψi : InjOn ψ D := by
    intro x hx y hy hxy
    have hh : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hψ ⟨x, hx⟩).symm.trans (hxy.trans (hψ ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hh)
  obtain ⟨E, ψ', hE, hDE, hψ'c, hψ'i, hψ'eq, hcover⟩ := extend_disc_coordinates hD hψc hψi
  obtain ⟨g, hgc, hgl⟩ := exists_inv_of_compactOn hE.isCompact hψ'c hψ'i
  have hgr : RightInvOn g ψ' (ψ' '' E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg ψ' (hgl hx)
  have hunit : ∀ x : ClosedUnitDisc, planeOf.symm x.val ∈ ψ' '' E := by
    intro x
    apply hcover
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact (mem_closedBall_zero_iff.mp x.property).trans (by norm_num)
  let Φ : C(ClosedUnitDisc, ℂ) :=
    ⟨fun x => g (planeOf.symm x.val), hgc.comp_continuous
      (planeOf.symm.continuous.comp continuous_subtype_val) hunit⟩
  have hΦi : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply planeOf.symm.injective
    exact (hgr (hunit x)).symm.trans ((congrArg ψ' hxy).trans (hgr (hunit y)))
  have hback (z : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) : g z.val = (H z).val := by
    have heq : ψ' (H z).val = z.val := (hψ'eq (H z).property).trans
      ((hψ (H z)).trans (congrArg Subtype.val (H.symm_apply_apply z)))
    exact (congrArg g heq.symm).trans (hgl (hDE (H z).property))
  have hΦzero : Φ polarCentre = (H ⟨0, section5_zero_mem_tangent_disc⟩).val := by
    change g (planeOf.symm polarCentre.val) = _
    simpa only [polarCentre, map_zero] using hback ⟨0, section5_zero_mem_tangent_disc⟩
  let e : ClosedUnitDisc ≃ₜ range Φ := Φ.continuous.isClosedEmbedding hΦi |>.isEmbedding.toHomeomorph
  have hdisc : IsClosedDisc (range Φ) := ⟨e⟩
  have hnot : Φ polarCentre ∉ discBd (range Φ) := by
    rw [disc_boundary (range Φ) e]
    rintro ⟨x, hx, hxeq⟩
    have hx0 : x = polarCentre := hΦi hxeq
    rw [hx0] at hx
    have hn : ‖(polarCentre : ClosedUnitDisc).val‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    simp [polarCentre] at hn
  have hnhd : Φ polarCentre ∈ interior (range Φ) :=
    interior_maximal (discInt_subset _) (hdisc.isOpen_discInt isManifoldPoint_complex)
      ⟨mem_range_self _, hnot⟩
  refine ⟨Φ, hΦi, hΦzero, hnhd, ?_⟩
  intro z
  change g (planeOf.symm (planeOf z.val)) = _
  rw [planeOf.symm_apply_apply]
  exact hback z

/-- The explicit quotient point, viewed again in the unit parameter
disc of the full source chart. -/
@[expose] noncomputable def section5CollapsedRadiusDiscPoint (x : ClosedUnitDisc) : ClosedUnitDisc :=
  ⟨planeOf (section5RadiusCollapse (planeOf.symm x.val)), by
    simp only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    apply section5_tangent_disc_norm_le
    apply section5RadiusCollapse_mem_disc
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.property⟩

/-- A finite sphere disc has the same full source-neighbourhood
extension. Its complex chart is retained explicitly, so winding
can be computed using the original plane orientation. -/
theorem exists_full_chart_of_finite_sphere_disc
    {D : Set (OnePoint EuclideanPlane)}
    (H : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) ≃ₜ D)
    (hfinite : D ⊆ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane)) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (χ : C(ClosedUnitDisc, ℂ)),
      (∀ x, Φ x = (complexPlane (χ x) : OnePoint EuclideanPlane)) ∧
      Function.Injective Φ ∧ Φ polarCentre = (H ⟨0, section5_zero_mem_tangent_disc⟩).val ∧
      Φ polarCentre ∈ interior (range Φ) ∧
      ∀ z : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2),
        Φ ⟨planeOf z.val, by
          rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
          exact section5_tangent_disc_norm_le z.property⟩ = (H z).val := by
  let : CompactSpace (closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let E : EuclideanPlane ≃ₜ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph
  let F : C(closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2), ℂ) :=
    ⟨fun z => complexPlane.symm (E.symm ⟨(H z).val, hfinite (H z).property⟩),
      complexPlane.symm.continuous.comp (E.symm.continuous.comp
        ((continuous_subtype_val.comp H.continuous).subtype_mk _))⟩
  have hF : ∀ z, (complexPlane (F z) : OnePoint EuclideanPlane) = (H z).val := by
    intro z
    change ((complexPlane (complexPlane.symm (E.symm _))) : OnePoint EuclideanPlane) = _
    rw [complexPlane.apply_symm_apply]
    exact congrArg Subtype.val (E.apply_symm_apply _)
  have hFi : Function.Injective F := by
    intro z w heq
    apply H.injective
    apply Subtype.ext
    rw [← hF z, ← hF w, heq]
  let H' : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) ≃ₜ range F :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective F hFi)
      F.continuous.rangeFactorization
  have hdisc : IsClosedDisc (range F) := by
    have hA := (isClosedDisc_of_convex (convex_closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) (by
      rw [interior_closedBall _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      exact ⟨_, mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)⟩)
      isBounded_closedBall isClosed_closedBall).1
    obtain ⟨A⟩ := hA
    exact ⟨A.trans H'⟩
  obtain ⟨χ, hχi, hχ0, hχnhd, hχmodel⟩ := exists_full_chart_of_collapsed_radius_disc hdisc H'
  let c : ℂ → OnePoint EuclideanPlane := fun z => (complexPlane z : OnePoint EuclideanPlane)
  have hc : IsOpenEmbedding c := OnePoint.isOpenEmbedding_coe.comp complexPlane.toHomeomorph.isOpenEmbedding
  let Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane) := ⟨c ∘ χ, hc.continuous.comp χ.continuous⟩
  have hΦi : Function.Injective Φ := hc.injective.comp hχi
  have hΦ0 : Φ polarCentre = (H ⟨0, section5_zero_mem_tangent_disc⟩).val := by
    change c (χ polarCentre) = _
    rw [hχ0]
    exact hF _
  have hnhd : Φ polarCentre ∈ interior (range Φ) := by
    have hsub : c '' interior (range χ) ⊆ range Φ := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := interior_subset hz
      exact mem_range_self x
    exact interior_maximal hsub (hc.isOpenMap _ isOpen_interior) ⟨_, hχnhd, rfl⟩
  refine ⟨Φ, χ, fun _ => rfl, hΦi, hΦ0, hnhd, ?_⟩
  intro z
  change c (χ _) = _
  rw [hχmodel z]
  exact hF z

/-- The full source chart agrees pointwise with an actual collapse
of a polar radius. In these coordinates every surviving old ray
has precisely its explicit quotient coordinates. -/
theorem exists_full_chart_of_polar_radius_collapse
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (hΦ : Function.Injective Φ)
    {p : OnePoint EuclideanPlane} {A : Set (OnePoint EuclideanPlane)}
    (hfibre : π ⁻¹' {p} = A) (hi : InjOn π Aᶜ)
    (haxis : ∀ x : ClosedUnitDisc, Φ x ∈ A ↔
      (planeOf.symm x.val).im = 0 ∧ 0 ≤ (planeOf.symm x.val).re)
    (hfinite : range (π.comp Φ) ⊆ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane)) :
    ∃ (Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (χ : C(ClosedUnitDisc, ℂ)),
      (∀ x, Ψ x = (complexPlane (χ x) : OnePoint EuclideanPlane)) ∧
      Function.Injective Ψ ∧ Ψ polarCentre = p ∧ Ψ polarCentre ∈ interior (range Ψ) ∧
      ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) = π (Φ x) := by
  obtain ⟨_, _, H, hH⟩ := isClosedDisc_image_of_collapsing_polar_radius π Φ hΦ hfibre hi haxis
  obtain ⟨Ψ, χ, hΨ, hΨi, hΨ0, hΨnhd, hΨmodel⟩ :=
    exists_full_chart_of_finite_sphere_disc H hfinite
  have hq0 : section5RadiusCollapse (planeOf.symm polarCentre.val) = 0 := by
    apply (section5RadiusCollapse_eq_zero _).mpr
    simp [polarCentre]
  have hH0 : (H ⟨0, section5_zero_mem_tangent_disc⟩).val = p := by
    have hh := hH polarCentre
    have hpt : (⟨section5RadiusCollapse (planeOf.symm polarCentre.val),
        section5RadiusCollapse_mem_disc (by simp [polarCentre])⟩ :
        closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2)) = ⟨0, section5_zero_mem_tangent_disc⟩ :=
      Subtype.ext hq0
    have hvalue := congrArg (fun z : closedBall (⟨0, 1 / 2⟩ : ℂ) (1 / 2) => (H z).val) hpt
    exact hvalue.symm.trans (hh.trans (show Φ polarCentre ∈ π ⁻¹' {p} from hfibre.symm ▸
      (haxis polarCentre).mpr (by simp [polarCentre])))
  refine ⟨Ψ, χ, hΨ, hΨi, hΨ0.trans hH0, hΨnhd, ?_⟩
  intro x
  have hx : ‖planeOf.symm x.val‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.property
  exact (hΨmodel ⟨_, section5RadiusCollapse_mem_disc hx⟩).trans (hH x)

end GraphMinor.GM06
