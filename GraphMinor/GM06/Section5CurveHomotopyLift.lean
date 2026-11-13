module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5CoverCurvePoint
import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifting the homotopy of a detoured curve

For the attachment count in VI (5.5), page 130, lift the angular
coordinate of the actual disc homotopy, starting from the old
curve's angular lift. Retain the radial coordinate of the homotopy.
Uniqueness of lifts shows that any parameter fixed by the homotopy
also keeps its original cover point.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Lift a curve homotopy from a specified initial angular lift.
Every parameter fixed in the cylinder is fixed in the cover too. -/
theorem exists_curve_homotopy_cover_lift
    (H : C(unitInterval × unitInterval, ClosedCylinder))
    (A : C(unitInterval, CylinderCover))
    (h0 : ∀ t, H (t, 0) = cylinderCoverProjection (A t)) :
    ∃ B : C(unitInterval × unitInterval, CylinderCover),
      (∀ t u, cylinderCoverProjection (B (t, u)) = H (t, u)) ∧
      (∀ t, B (t, 0) = A t) ∧
      ∀ t, (∀ u, H (t, u) = cylinderCoverProjection (A t)) → ∀ u, B (t, u) = A t := by
  let F : C(unitInterval × unitInterval, Circle) :=
    ⟨fun p => (H (p.2, p.1)).1.2,
      continuous_snd.comp (continuous_subtype_val.comp (H.continuous.comp continuous_swap))⟩
  let a : C(unitInterval, ℝ) := ⟨fun t => (A t).2, continuous_snd.comp A.continuous⟩
  have hF0 (t) : F (0, t) = Circle.exp (a t) := by
    change (H (t, 0)).1.2 = Circle.exp (A t).2
    rw [h0]
    rfl
  let α := Circle.isCoveringMap_exp.liftHomotopy F a hF0
  have hα (t u) : Circle.exp (α (u, t)) = (H (t, u)).1.2 :=
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts F a hF0) (u, t)
  have hα0 (t) : α (0, t) = (A t).2 := Circle.isCoveringMap_exp.liftHomotopy_zero F a hF0 t
  let B : C(unitInterval × unitInterval, CylinderCover) :=
    ⟨fun p => (⟨(H p).1.1, (H p).2.1⟩, α (p.2, p.1)),
      ((continuous_fst.comp (continuous_subtype_val.comp H.continuous)).subtype_mk _).prodMk
        (α.continuous.comp continuous_swap)⟩
  have hproj (t u) : cylinderCoverProjection (B (t, u)) = H (t, u) := by
    apply Subtype.ext
    exact Prod.ext rfl (hα t u)
  have hzero (t) : B (t, 0) = A t := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x : ClosedCylinder => x.1.1) (h0 t)
    · exact hα0 t
  refine ⟨B, hproj, hzero, ?_⟩
  intro t hfixed u
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun v => B (t, v), B.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have he : q = ContinuousMap.const _ (A t) := cover_curves_eq_of_projection_eq q
    (ContinuousMap.const _ (A t)) (fun v => (hproj t v).trans (hfixed v)) 0 (hzero t)
  exact congrArg (fun c : C(unitInterval, CylinderCover) => c u) he

end GraphMinor.GM06
