module

public import GraphMinor.GM06.Defs
import Mathlib.Tactic

/-!
# Normalizing the ends of a spanning path

For Reduction 3 of VI, page 129, a spanning path can have arbitrary
ends on the two cuffs. An angular shear keeps each radius fixed and
rotates the two cuffs independently. It therefore puts both ends in
the standard positions used for a one-path linkage, so that the
cylinder coordinates for that linkage can be applied.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Rotate each radius by the linear interpolation of two cuff angles. -/
@[expose] noncomputable def section5CylinderShear (a b : ℝ) : ClosedCylinder ≃ₜ ClosedCylinder where
  toFun p := ⟨(p.1.1, p.1.2 * Circle.exp ((2 - p.1.1) * a + (p.1.1 - 1) * b)), p.2⟩
  invFun p := ⟨(p.1.1, p.1.2 / Circle.exp ((2 - p.1.1) * a + (p.1.1 - 1) * b)), p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mul_div_cancel_right _ _
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact div_mul_cancel _ _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The shear preserves the radial coordinate. -/
theorem section5CylinderShear_fst (a b : ℝ) (p : ClosedCylinder) :
    (section5CylinderShear a b p).1.1 = p.1.1 := rfl

/-- On the inner cuff, the shear uses the first angle. -/
theorem section5CylinderShear_inner (a b : ℝ) {p : ClosedCylinder}
    (hp : p ∈ cylinderCuff1) :
    (section5CylinderShear a b p).1.2 = p.1.2 * Circle.exp a := by
  change p.1.2 * Circle.exp ((2 - p.1.1) * a + (p.1.1 - 1) * b) = _
  change p.1.1 = 1 at hp
  rw [hp]
  norm_num

/-- On the outer cuff, the shear uses the second angle. -/
theorem section5CylinderShear_outer (a b : ℝ) {p : ClosedCylinder}
    (hp : p ∈ cylinderCuff2) :
    (section5CylinderShear a b p).1.2 = p.1.2 * Circle.exp b := by
  change p.1.2 * Circle.exp ((2 - p.1.1) * a + (p.1.1 - 1) * b) = _
  change p.1.1 = 2 at hp
  rw [hp]
  norm_num

/-- A radius-preserving homeomorphism puts any chosen pair of cuff
points in the standard positions for a one-path linkage. -/
theorem exists_cylinder_shear_normalizing_ends {s t : ClosedCylinder}
    (hs : s ∈ cylinderCuff1) (ht : t ∈ cylinderCuff2) :
    ∃ α : ClosedCylinder ≃ₜ ClosedCylinder,
      (∀ p, (α p).1.1 = p.1.1) ∧
      α s = cylinderM1Point 1 0 ∧ α t = cylinderM2Point 1 0 := by
  obtain ⟨a, ha⟩ := Circle.exp_surjective (s.1.2)⁻¹
  obtain ⟨b, hb⟩ := Circle.exp_surjective (t.1.2)⁻¹
  refine ⟨section5CylinderShear a b, section5CylinderShear_fst a b, ?_, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact hs
    · rw [section5CylinderShear_inner a b hs, ha, mul_inv_cancel]
      simp [cylinderM1Point, cylinderPoint]
  · apply Subtype.ext
    apply Prod.ext
    · exact ht
    · rw [section5CylinderShear_outer a b ht, hb, mul_inv_cancel]
      simp [cylinderM2Point, cylinderPoint]

end GraphMinor.GM06
