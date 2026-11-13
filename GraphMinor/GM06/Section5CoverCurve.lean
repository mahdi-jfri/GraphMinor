module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Winding

/-!
# Curves with a specified initial lift

To use the sides in the angular cover for VI Section 5, fix the real
angle above the initial point of a curve. Translate its angular lift
by a constant. Projection gives back the original curve, and the
endpoint displacement computes its winding, by Section4Winding.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- The chosen lift has the specified initial angle. -/
theorem cylinderCurveLiftAt_zero (f : Curve ClosedCylinder) (a : ℝ) :
    cylinderCurveLiftAt f a 0 = (⟨(f 0).1.1, (f 0).2.1⟩, a) := by
  apply Prod.ext
  · rfl
  · change cylinderAngleLift f 0 + (a - cylinderAngleLift f 0) = a
    ring

/-- With the initial sheet aligned, the lifted curve projects to the
original curve at every parameter. -/
theorem cylinderCoverProjection_curveLiftAt (f : Curve ClosedCylinder) (a : ℝ)
    (ha : Circle.exp a = (f 0).1.2) (t : unitInterval) :
    cylinderCoverProjection (cylinderCurveLiftAt f a t) = f t := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp (cylinderAngleLift f t + (a - cylinderAngleLift f 0)) = _
    rw [Circle.exp_add, Circle.exp_sub, exp_cylinderAngleLift, exp_cylinderAngleLift, ha,
      div_self', mul_one]

/-- Winding is the angular displacement of the curve lifted from a
specified initial sheet. This is the lift formula from Section4Winding. -/
theorem windingNumber_eq_curveLiftAt (f : Curve ClosedCylinder) (a : ℝ)
    (ha : Circle.exp a = (f 0).1.2) :
    windingNumber f = ((cylinderCurveLiftAt f a 1).2 - a) / (2 * π) := by
  let α : C(unitInterval, ℝ) :=
    ⟨fun t => (cylinderCurveLiftAt f a t).2,
      continuous_snd.comp (cylinderCurveLiftAt f a).continuous⟩
  have hα (t : unitInterval) : Circle.exp (α t) = (f t).1.2 :=
    congrArg (fun p : ClosedCylinder => p.1.2) (cylinderCoverProjection_curveLiftAt f a ha t)
  rw [windingNumber_eq_of_exp_lift α hα]
  change ((cylinderCurveLiftAt f a 1).2 - (cylinderCurveLiftAt f a 0).2) / (2 * π) = _
  rw [cylinderCurveLiftAt_zero]

end GraphMinor.GM06
