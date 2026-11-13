module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4CuffCurve
import GraphMinor.GM06.Section4Crosscut

/-!
# A crossing curve cannot start inside an enclosed cuff arc

For the minimum interval argument in Graph Minors VI (4.2), claim (2),
a path homotopic to a cuff arc blocks any disjoint curve from that arc
to the other cuff. Lift the three curves. The cuff arc's lifted angles
are monotone, so the crossing curve starts between the path's lifted
ends. Strip crossing then forces a meeting.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Real

/-- A path homotopic to an injective cuff arc meets every curve starting
on that arc and ending on the other cuff. This is the separation step
used in Graph Minors VI (4.2), claim (2), page 126. -/
theorem not_disjoint_crosscurve_of_homotopic_cuff_arc
    (outer : Bool) {f g k : Curve ClosedCylinder}
    (hk : Function.Injective k)
    (hkr : ∀ t, (k t).1.1 = (if outer then 2 else 1))
    (hfk : CurvesHomotopic f k)
    (hg0 : g 0 ∈ range k)
    (hg1 : (g 1).1.1 = (if outer then 1 else 2)) :
    ¬ Disjoint (range f) (range g) := by
  intro hdisj
  have h0 : f 0 = k 0 := by
    obtain ⟨ψ, _, _, _, hψ0, hψ0', _, _⟩ := hfk
    exact (hψ0 0).symm.trans (hψ0' 0)
  have h1 : f 1 = k 1 := by
    obtain ⟨ψ, _, _, _, _, _, hψ1, hψ1'⟩ := hfk
    exact (hψ1 0).symm.trans (hψ1' 0)
  have hstart : cylinderAngleLift f 0 = cylinderAngleLift k 0 := by
    simp only [cylinderAngleLift_zero, h0]
  have hend : cylinderAngleLift f 1 = cylinderAngleLift k 1 := by
    have hw := windingNumber_eq_of_homotopic hfk
    unfold windingNumber at hw
    rw [hstart] at hw
    have he := (div_left_inj' (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      Real.pi_ne_zero)).mp hw
    linarith only [he]
  obtain ⟨v, hv⟩ := hg0
  let b := Circle.isCoveringMap_exp.liftPath (curveCircleProj g) (cylinderAngleLift k v)
    (by rw [curveCircleProj_apply, ← hv, exp_cylinderAngleLift])
  have hb0 : b 0 = cylinderAngleLift k v :=
    Circle.isCoveringMap_exp.liftPath_zero _ _ _
  have hb : ∀ t, Circle.exp (b t) = (g t).1.2 := fun t =>
    congr_fun (Circle.isCoveringMap_exp.liftPath_lifts _ _ _) t
  have hbetween := cylinderAngleLift_mem_uIcc_of_cuff_line hk hkr v
  rw [← hstart, ← hend, ← hb0] at hbetween
  exact angle_lift_start_not_between_of_disjoint_crosscurve outer
    (cylinderAngleLift f) b (exp_cylinderAngleLift f) hb
    (by rw [h0]; exact hkr 0) (by rw [h1]; exact hkr 1)
    (by rw [← hv]; exact hkr v) hg1 hdisj hbetween

end GraphMinor.GM06
