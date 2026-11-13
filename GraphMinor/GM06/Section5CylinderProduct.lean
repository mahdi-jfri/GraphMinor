module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SpanningPathCoordinates
import Mathlib.Tactic

/-!
# Product coordinates on the concrete cylinder

For Reduction 3 of VI, page 129, replace the concrete radius interval
[1,2] by the unit interval and put the angular coordinate first.
Composing this elementary homeomorphism with spanning-path coordinates
gives a self-homeomorphism of the concrete cylinder taking its radial
seam to the prescribed path. This lets a rectangular seam chart be
carried directly to the original drawing.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Angular coordinate followed by radius minus one identifies the
concrete cylinder with the product of a circle and the unit interval. -/
@[expose] noncomputable def section5CylinderProduct : ClosedCylinder ≃ₜ Circle × unitInterval where
  toFun p := (p.1.2, ⟨p.1.1 - 1, ⟨by linarith only [p.2.1.1], by linarith only [p.2.1.2]⟩⟩)
  invFun p := ⟨(1 + p.2.1, p.1), ⟨⟨by linarith only [p.2.2.1], by linarith only [p.2.2.2]⟩, trivial⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change 1 + (p.1.1 - 1) = p.1.1
      ring
    · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change 1 + p.2.1 - 1 = p.2.1
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A prescribed spanning path is the image of the radial seam under
a self-homeomorphism of the concrete cylinder. -/
theorem exists_cylinder_self_coordinates_of_spanning_path
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hs : s ∈ cylinderCuff1) (ht : t ∈ cylinderCuff2)
    (hB : P.U ∩ bd ClosedCylinder = {s, t})
    (f : Curve ClosedCylinder) (hf : ParametrizesSet f P.U s t) :
    ∃ K : ClosedCylinder ≃ₜ ClosedCylinder,
      ∀ u : unitInterval, K (section5CylinderProduct.symm (1, u)) = f u := by
  obtain ⟨H, hH⟩ := exists_cylinder_coordinates_of_spanning_path hP hs ht hB f hf
  refine ⟨section5CylinderProduct.trans H, ?_⟩
  intro u
  change H (section5CylinderProduct (section5CylinderProduct.symm (1, u))) = f u
  rw [section5CylinderProduct.apply_symm_apply]
  exact hH u

end GraphMinor.GM06
