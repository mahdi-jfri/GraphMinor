module

public import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section4

/-!
# A cover lift through a specified point

In VI (5.5), page 131, the last region segment of the helix is
lifted through a selected point of the cut sheet. Translate its
continuous angular lift by the difference at that parameter. The
translation preserves angular projection and makes the lifted curve
pass through the specified cover point. This fixes the sheet before
its endpoint contacts are chosen.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- A cylinder curve has a continuous angular-cover lift through
any specified point above any specified parameter. -/
theorem exists_cover_curve_through_point
    (f : Curve ClosedCylinder) (z : unitInterval) (p : CylinderCover)
    (hp : cylinderCoverProjection p = f z) :
    ∃ q : C(unitInterval, CylinderCover), q z = p ∧
      ∀ t, cylinderCoverProjection (q t) = f t := by
  let α := cylinderAngleLift f
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun t => (⟨(f t).1.1, (f t).2.1⟩, α t + (p.2 - α z)), by fun_prop⟩
  have hpang : Circle.exp p.2 = (f z).1.2 :=
    congrArg (fun x : ClosedCylinder => x.1.2) hp
  have hshift : Circle.exp (p.2 - α z) = 1 := by
    rw [Circle.exp_sub, exp_cylinderAngleLift, hpang, div_self']
  refine ⟨q, ?_, ?_⟩
  · apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun x : ClosedCylinder => x.1.1) hp).symm
    · change α z + (p.2 - α z) = p.2
      ring
  · intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp (α t + (p.2 - α z)) = (f t).1.2
      rw [Circle.exp_add, hshift, mul_one, exp_cylinderAngleLift]

/-- Two continuous cover curves with the same projection agree
everywhere once they agree at one parameter. This aligns the lifted
old segment and the auxiliary prefix in VI (5.5). -/
theorem cover_curves_eq_of_projection_eq
    (p q : C(unitInterval, CylinderCover))
    (hproj : ∀ t, cylinderCoverProjection (p t) = cylinderCoverProjection (q t))
    (z : unitInterval) (hz : p z = q z) : p = q := by
  let a : C(unitInterval, ℝ) := ⟨fun t => (p t).2, continuous_snd.comp p.continuous⟩
  let b : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  have he : Circle.exp ∘ a = Circle.exp ∘ b := by
    funext t
    exact congrArg (fun x : ClosedCylinder => x.1.2) (hproj t)
  have hab : (a : unitInterval → ℝ) = b := Circle.isCoveringMap_exp.eq_of_comp_eq
    a.continuous b.continuous he z (congrArg Prod.snd hz)
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x : ClosedCylinder => x.1.1) (hproj t)
  · exact congrFun hab t

end GraphMinor.GM06
