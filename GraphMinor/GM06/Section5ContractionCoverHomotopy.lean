module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5CoverCurvePoint
import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifting the contraction homotopy to the angular cover

To retain the winding class in Reduction 3 of VI (5.5), page 130,
we lift its boundary-fixed homotopy, starting with the identity of
the cover. Homotopy lifting for the circle exponential gives a
continuous angular coordinate. Uniqueness keeps every boundary
point fixed in its original sheet.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A cylinder homotopy starting at the identity lifts to the angular
cover starting at its identity, and retains each fixed boundary point. -/
theorem exists_cover_homotopy_of_boundary_fixed_homotopy
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (hH0 : ∀ p, H (0, p) = p)
    (hHbd : ∀ p ∈ bd ClosedCylinder, ∀ t, H (t, p) = p) :
    ∃ F : C(unitInterval × CylinderCover, CylinderCover),
      (∀ t p, cylinderCoverProjection (F (t, p)) = H (t, cylinderCoverProjection p)) ∧
      (∀ p, F (0, p) = p) ∧
      (∀ p, cylinderCoverProjection p ∈ bd ClosedCylinder → ∀ t, F (t, p) = p) := by
  let B : C(unitInterval × CylinderCover, ClosedCylinder) :=
    ⟨fun q => H (q.1, cylinderCoverProjection q.2),
      H.continuous.comp (continuous_fst.prodMk
        (continuous_cylinderCoverProjection.comp continuous_snd))⟩
  let A : C(unitInterval × CylinderCover, Circle) :=
    ⟨fun q => (B q).1.2, continuous_snd.comp (continuous_subtype_val.comp B.continuous)⟩
  let a : C(CylinderCover, ℝ) := ⟨Prod.snd, continuous_snd⟩
  have hA0 (p : CylinderCover) : A (0, p) = Circle.exp (a p) := by
    change (H (0, cylinderCoverProjection p)).1.2 = Circle.exp p.2
    rw [hH0]
    rfl
  let α := Circle.isCoveringMap_exp.liftHomotopy A a hA0
  have hα (t) (p) : Circle.exp (α (t, p)) = A (t, p) :=
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts A a hA0) (t, p)
  have hα0 (p) : α (0, p) = p.2 :=
    Circle.isCoveringMap_exp.liftHomotopy_zero A a hA0 p
  let F : C(unitInterval × CylinderCover, CylinderCover) :=
    ⟨fun q => (⟨(B q).1.1, (B q).2.1⟩, α q),
      ((continuous_fst.comp (continuous_subtype_val.comp B.continuous)).subtype_mk _).prodMk
        α.continuous⟩
  have hproj (t) (p) : cylinderCoverProjection (F (t, p)) = H (t, cylinderCoverProjection p) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hα t p
  have hzero (p) : F (0, p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x : ClosedCylinder => x.1.1) (hH0 (cylinderCoverProjection p))
    · exact hα0 p
  refine ⟨F, hproj, hzero, ?_⟩
  intro p hp t
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun u => F (u, p), F.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have he : q = ContinuousMap.const _ p := cover_curves_eq_of_projection_eq
    q (ContinuousMap.const _ p)
    (fun u => (hproj u p).trans (hHbd _ hp u)) 0 (hzero p)
  exact congrArg (fun c : C(unitInterval, CylinderCover) => c t) he

/-- A cover lift starting at the identity commutes with every full-turn
translation. Thus the contraction retains the relative sheet numbers. -/
theorem cover_homotopy_commutes_with_translation
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (F : C(unitInterval × CylinderCover, CylinderCover))
    (hproj : ∀ t p, cylinderCoverProjection (F (t, p)) = H (t, cylinderCoverProjection p))
    (hzero : ∀ p, F (0, p) = p) (z : ℤ) (p : CylinderCover) (t : unitInterval) :
    F (t, cylinderCoverTranslation z p) = cylinderCoverTranslation z (F (t, p)) := by
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun u => F (u, cylinderCoverTranslation z p),
      F.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let r : C(unitInterval, CylinderCover) :=
    ⟨fun u => cylinderCoverTranslation z (F (u, p)),
      (cylinderCoverTranslation z).continuous.comp
        (F.continuous.comp (continuous_id.prodMk continuous_const))⟩
  have he : q = r := cover_curves_eq_of_projection_eq q r (by
    intro u
    change cylinderCoverProjection (F (u, cylinderCoverTranslation z p)) =
      cylinderCoverProjection (cylinderCoverTranslation z (F (u, p)))
    rw [cylinderCoverProjection_translation, hproj, hproj,
      cylinderCoverProjection_translation]) 0 (by
    change F (0, cylinderCoverTranslation z p) = cylinderCoverTranslation z (F (0, p))
    rw [hzero, hzero])
  exact congrArg (fun c : C(unitInterval, CylinderCover) => c t) he

end GraphMinor.GM06
