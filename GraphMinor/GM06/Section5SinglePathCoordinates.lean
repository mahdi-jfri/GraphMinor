module

public import GraphMinor.GM06.Section5SingleStripFibers
import GraphMinor.GM06.Section5LiftedStripCoordinates
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripProjection
import GraphMinor.GM06.Section5SingleStrip
import GraphMinor.GM11.Cylinder
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-!
# Cylinder coordinates with a prescribed spanning path

For Reduction 3 of VI, page 129, the one-path linkage supplies a
closed lifted strip disc. Its square coordinates agree on the two
vertical sides after projection, so they descend to a continuous
map from a cylinder. The strip disc covers the original cylinder.
The projection fiber calculation proves injectivity of the descended
map, making it a homeomorphism that takes the seam to the given path.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

private theorem exists_unit_circle_parameter (z : Circle) :
    ∃ u : unitInterval, u.1 < 1 ∧ z = Circle.exp (2 * π * u.1) := by
  obtain ⟨i, hi, u, hu, hz⟩ := GM11.exists_circle_param (n := 1) (by norm_num) z
  have hi0 : i = 0 := by omega
  subst i
  exact ⟨u, hu, by simpa only [Nat.cast_zero, zero_add, Nat.cast_one, div_one] using hz⟩

/-- A one-path Section 5 linkage gives cylinder coordinates whose
seam is exactly the linkage curve. No assumption on the other edges
of the drawing is required. -/
theorem exists_cylinder_coordinates_of_single_path
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) :
    ∃ H : Circle × unitInterval ≃ₜ ClosedCylinder,
      ∀ t : unitInterval, H (1, t) = L.curve 0 t := by
  obtain ⟨D, hD, hDb, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ 1
  obtain ⟨F, hiF, hrF, hlF, hhF, _, _⟩ := exists_lifted_strip_coordinates L hG hθ 1 hD hDb
  have hleft (t) : radialCylinderProjection (F (0, t)) = L.curve 0 t := by
    rw [hlF, radialCylinderProjection_liftedLinkageCurve]
    exact congrArg (fun j : Fin 1 => L.curve j t) (Subsingleton.elim _ _)
  have hright (t) : radialCylinderProjection (F (1, t)) = L.curve 0 t := by
    rw [hhF, radialCylinderProjection_liftedLinkageCurve]
    exact congrArg (fun j : Fin 1 => L.curve j t) (Subsingleton.elim _ _)
  let η : C(unitInterval × unitInterval, ClosedCylinder) :=
    ⟨fun q => radialCylinderProjection (F q), continuous_radialCylinderProjection.comp F.continuous⟩
  obtain ⟨h, hparam⟩ := GM11.exists_cylinder (n := 1) (by norm_num)
    (G := fun _ => η) (fun _ => η.continuous)
    (fun _ t => (hright t).trans (hleft t).symm) (fun _ => rfl)
  have hv (u t : unitInterval) : h (Circle.exp (2 * π * u.1), t) = radialCylinderProjection (F (u, t)) := by
    change h (Circle.exp (2 * π * u.1), t) = η (u, t)
    simpa only [Nat.cast_zero, zero_add, Nat.cast_one, div_one] using hparam 0 (by norm_num) u t
  have hcl : closure (cylinderStrip L 0) = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ (L.pathDrawing 0).U
    · exact L.U_subset_closure_strip hG hθ 0 hp
    · apply subset_closure
      rw [cylinderStrip_eq_compl_of_one_path L hG]
      exact hp
  have hproj : radialCylinderProjection '' D = univ := by
    rw [image_stripDisc_eq_closure_strip L hG hθ 0 hD hDb hstrip, hcl]
  have hsurj : Function.Surjective h := by
    intro p
    obtain ⟨q, hq, hqp⟩ := hproj.symm ▸ mem_univ p
    obtain ⟨r, hr⟩ := hrF.symm ▸ hq
    refine ⟨(Circle.exp (2 * π * r.1.1), r.2), ?_⟩
    rw [hv, hr]
    exact hqp
  have hinj : Function.Injective h := by
    intro a b hab
    obtain ⟨u, hu, hzu⟩ := exists_unit_circle_parameter a.1
    obtain ⟨v, hv1, hzv⟩ := exists_unit_circle_parameter b.1
    have he : radialCylinderProjection (F (u, a.2)) = radialCylinderProjection (F (v, b.2)) := by
      rw [← hv, ← hv, ← hzu, ← hzv]
      exact hab
    have hFu : F (u, a.2) ∈ D := hrF ▸ mem_range_self _
    have hFv : F (v, b.2) ∈ D := hrF ▸ mem_range_self _
    rcases radialCylinderProjection_single_strip_fibers L hG hθ 1 hD hDb hstrip hFu hFv he with
      heq | ⟨t, (⟨h1, _⟩ | ⟨h1, _⟩)⟩
    · have hp := hiF heq
      have huv : u = v := congrArg Prod.fst hp
      apply Prod.ext
      · rw [hzu, hzv, huv]
      · have htEq := congrArg (fun q : unitInterval × unitInterval => q.2) hp
        exact htEq
    · have hu1 : u = 1 := congrArg Prod.fst (hiF (h1.trans (hhF t).symm))
      rw [hu1] at hu
      exact False.elim (lt_irrefl (1 : ℝ) hu)
    · have hvEq : v = 1 := congrArg Prod.fst (hiF (h1.trans (hhF t).symm))
      rw [hvEq] at hv1
      exact False.elim (lt_irrefl (1 : ℝ) hv1)
  let H : Circle × unitInterval ≃ₜ ClosedCylinder := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective h ⟨hinj, hsurj⟩) h.continuous
  refine ⟨H, ?_⟩
  intro t
  change h (1, t) = L.curve 0 t
  have hh := (hv 0 t).trans (hleft t)
  simpa only [Icc.coe_zero, mul_zero, Circle.exp_zero] using hh

end GraphMinor.GM06
