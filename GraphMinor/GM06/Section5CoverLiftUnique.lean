module

public import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section4

/-!
# A cover curve is the aligned lift of its projection

Normalize the angular coordinate of a given continuous cover curve
to the initial value used by the chosen exponential path lift.
Uniqueness of that lift identifies the normalized curves. Translating
back gives the cover curve itself as the lift aligned at its actual
initial angle. This retains the specified side and contact parameter
when the cut path is projected in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- A continuous cover lift agrees with the chosen lift once their
initial angles agree. -/
theorem cylinderCurveLiftAt_eq_of_cover_lift
    (f : Curve ClosedCylinder) (q : C(unitInterval, CylinderCover))
    (hproj : ∀ t, cylinderCoverProjection (q t) = f t) :
    cylinderCurveLiftAt f (q 0).2 = q := by
  let α : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  have hα (t : unitInterval) : Circle.exp (α t) = (f t).1.2 :=
    congrArg (fun p : ClosedCylinder => p.1.2) (hproj t)
  let b : C(unitInterval, ℝ) :=
    ⟨fun t => α t + (cylinderAngleLift f 0 - α 0), α.continuous.add continuous_const⟩
  have he : Circle.exp (cylinderAngleLift f 0 - α 0) = 1 := by
    simp only [Circle.exp_sub, exp_cylinderAngleLift, hα, div_self']
  have hb : b = cylinderAngleLift f := by
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩
    · funext t
      change Circle.exp (α t + (cylinderAngleLift f 0 - α 0)) = (f t).1.2
      rw [Circle.exp_add, he, mul_one, hα]
    · change α 0 + (cylinderAngleLift f 0 - α 0) = _
      rw [cylinderAngleLift_zero]
      ring
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · apply Subtype.ext
    have hr := congrArg (fun p : ClosedCylinder => p.1.1) (hproj t)
    exact hr.symm
  · have hbt := congrArg (fun c : C(unitInterval, ℝ) => c t) hb
    change α t + (cylinderAngleLift f 0 - α 0) = cylinderAngleLift f t at hbt
    change cylinderAngleLift f t + ((q 0).2 - cylinderAngleLift f 0) = (q t).2
    rw [← hbt]
    change α t + (cylinderAngleLift f 0 - α 0) + (α 0 - cylinderAngleLift f 0) = α t
    ring

end GraphMinor.GM06
