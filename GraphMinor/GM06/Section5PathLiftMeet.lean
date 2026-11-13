module

public import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section4PathTools

/-!
# Aligned lifts agree at meetings inside a path

The point set of a path is a forest. The proved forest angular-offset
lemma says that the offset of two angular lifts is the same at any
two meetings. If their initial points and initial lift angles agree,
that offset is zero. Radial coordinates agree at a meeting as well,
so the full cover points agree. This places an incident replacement
prefix on the new path's left seam in the Reduction 4 progress
argument of VI Section 5, page 129.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- Two curves inside a path with the same initial point have equal
aligned cover lifts at every meeting. -/
theorem aligned_curve_lifts_eq_at_path_meeting
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (f : Curve ClosedCylinder)
    (hf : ParametrizesSet f P.U s t) (q : Curve ClosedCylinder)
    (hqP : range q ⊆ P.U) (hq0 : q 0 = s) (a : ℝ) (ha : Circle.exp a = s.1.2)
    {u v : unitInterval} (hmeet : q u = f v) :
    cylinderCurveLiftAt q a u = cylinderCurveLiftAt f a v := by
  have hqa : Circle.exp a = (q 0).1.2 := by rw [hq0]; exact ha
  have hfa : Circle.exp a = (f 0).1.2 := by rw [hf.2.2.1]; exact ha
  let α : C(unitInterval, ℝ) :=
    ⟨fun u => (cylinderCurveLiftAt q a u).2,
      continuous_snd.comp (cylinderCurveLiftAt q a).continuous⟩
  let β : C(unitInterval, ℝ) :=
    ⟨fun u => (cylinderCurveLiftAt f a u).2,
      continuous_snd.comp (cylinderCurveLiftAt f a).continuous⟩
  have hα (u : unitInterval) : Circle.exp (α u) = (q u).1.2 :=
    congrArg (fun p : ClosedCylinder => p.1.2) (cylinderCoverProjection_curveLiftAt q a hqa u)
  have hβ (u : unitInterval) : Circle.exp (β u) = (f u).1.2 :=
    congrArg (fun p : ClosedCylinder => p.1.2) (cylinderCoverProjection_curveLiftAt f a hfa u)
  have hα0 : α 0 = a := by
    change (cylinderCurveLiftAt q a 0).2 = a
    rw [cylinderCurveLiftAt_zero]
  have hβ0 : β 0 = a := by
    change (cylinderCurveLiftAt f a 0).2 = a
    rw [cylinderCurveLiftAt_zero]
  have hstart : q 0 = f 0 := hq0.trans hf.2.2.1.symm
  have h := angular_offset_eq_of_forest (isGraphForest_of_isPathDrawing hP)
    hqP (hf.2.1 ▸ Subset.rfl) α β hα hβ hstart hmeet
  rw [hα0, hβ0, sub_self] at h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun p : ClosedCylinder => p.1.1) hmeet
  · change α u = β v
    exact sub_eq_zero.mp h.symm

end GraphMinor.GM06
