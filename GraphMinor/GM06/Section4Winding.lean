module

public import GraphMinor.Surface.Cylinder
public import GraphMinor.GM07.Section11c
public import GraphMinor.GM11.Defs
import GraphMinor.GM07.ForestFlat
import GraphMinor.GM07.Section3

/-!
# Angular lifts of paths in a forest

For the no-circuit argument in Graph Minors VI (4.2), claim (1), we compare
angular lifts at two meetings of curves in a forest. The angular displacement
of any lift computes winding. Flatness of the forest then forces the same
angular offset at both meetings.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Real

/-- Winding is the angular displacement of any continuous lift, regardless
of its initial value. -/
theorem windingNumber_eq_of_exp_lift {f : Curve ClosedCylinder}
    (a : C(unitInterval, ℝ)) (ha : ∀ t, Circle.exp (a t) = (f t).1.2) :
    windingNumber f = (a 1 - a 0) / (2 * π) := by
  let b : C(unitInterval, ℝ) :=
    a + ContinuousMap.const _ (cylinderAngleLift f 0 - a 0)
  have he : Circle.exp (cylinderAngleLift f 0 - a 0) = 1 := by
    simp only [Circle.exp_sub, exp_cylinderAngleLift, ha, div_self']
  have hb : b = cylinderAngleLift f := by
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩
    · funext t
      change Circle.exp (a t + (cylinderAngleLift f 0 - a 0)) = (f t).1.2
      rw [Circle.exp_add, he, mul_one, ha]
    · change a 0 + (cylinderAngleLift f 0 - a 0) = _
      rw [cylinderAngleLift_zero]
      ring
  unfold windingNumber
  rw [← hb]
  change (a 1 + (cylinderAngleLift f 0 - a 0) -
    (a 0 + (cylinderAngleLift f 0 - a 0))) / (2 * π) = _
  congr 1
  ring

/-- The winding of a portion of a curve is the difference of its lifted
angles at the two cut points. -/
theorem windingNumber_subPathSeg_of_exp_lift {f : Curve ClosedCylinder}
    (a : C(unitInterval, ℝ)) (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (s t : unitInterval) :
    windingNumber (GM07.subPathSeg f s t) = (a t - a s) / (2 * π) := by
  have h := windingNumber_eq_of_exp_lift (GM07.subPathSeg a s t)
    (f := GM07.subPathSeg f s t) (fun x => ha _)
  simpa only [GM07.subPathSeg_zero, GM07.subPathSeg_one] using h

/-- Two meetings of curves contained in a forest have the same angular
offset. Otherwise the two portions between the meetings would form a loop
with nonzero winding, contrary to flatness of a forest. This supplies the
no-circuit step in Graph Minors VI (4.2), claim (1), page 125. -/
theorem angular_offset_eq_of_forest
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {f g : Curve ClosedCylinder} (hf : range f ⊆ H.U) (hg : range g ⊆ H.U)
    (a b : C(unitInterval, ℝ))
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    {s₁ s₂ t₁ t₂ : unitInterval} (h₁ : f s₁ = g t₁) (h₂ : f s₂ = g t₂) :
    a s₁ - b t₁ = a s₂ - b t₂ := by
  have hh := GM07.IsFlat.curvesHomotopic (GM07.isFlat_forest hH)
    ((GM07.range_subPathSeg_subset f s₁ s₂).trans hf)
    ((GM07.range_subPathSeg_subset g t₁ t₂).trans hg)
    (by simpa only [GM07.subPathSeg_zero] using h₁)
    (by simpa only [GM07.subPathSeg_one] using h₂)
  have hw := windingNumber_eq_of_homotopic hh
  rw [windingNumber_subPathSeg_of_exp_lift a ha,
    windingNumber_subPathSeg_of_exp_lift b hb] at hw
  have he := (div_left_inj' (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    Real.pi_ne_zero)).mp hw
  linarith only [he]

end GraphMinor.GM06
