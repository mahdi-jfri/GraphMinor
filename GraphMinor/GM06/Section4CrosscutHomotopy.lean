module

public import GraphMinor.GM06.Section4Crosscut
import Mathlib.Topology.Order.IntermediateValue

/-!
# Homotopy classes fixed by a crossing curve

A curve between the cuffs cuts the circular order at its initial point.
A cuff arc avoiding this point has an angular lift in the same interval
as any disjoint path with the same ends. Their winding numbers agree.
This proves the homotopy assertion for the initial interval in VI (4.2),
claim (2).
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Real

private theorem lift_end_between_of_avoid
    (a : C(unitInterval, ℝ)) (q : ℝ)
    (havoid : ∀ t, Circle.exp (a t) ≠ Circle.exp q)
    (hstart : a 0 ∈ Ioo q (q + 2 * π)) : a 1 ∈ Ioo q (q + 2 * π) := by
  constructor
  · by_contra hn
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc'
      (show (0 : unitInterval) ≤ 1 from zero_le_one) a.continuous.continuousOn
      (show q ∈ Icc (a 1) (a 0) from ⟨not_lt.mp hn, hstart.1.le⟩)
    exact havoid t (congrArg Circle.exp ht)
  · by_contra hn
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc
      (show (0 : unitInterval) ≤ 1 from zero_le_one) a.continuous.continuousOn
      (show q + 2 * π ∈ Icc (a 0) (a 1) from ⟨hstart.2.le, not_lt.mp hn⟩)
    exact havoid t (by rw [ht, Circle.exp_add_two_pi])

private theorem exists_angle_lift (f : Curve ClosedCylinder)
    (c : ℝ) (hc : Circle.exp c = (f 0).1.2) :
    ∃ a : C(unitInterval, ℝ), a 0 = c ∧ ∀ t, Circle.exp (a t) = (f t).1.2 := by
  let a := Circle.isCoveringMap_exp.liftPath (curveCircleProj f) c hc.symm
  exact ⟨a, Circle.isCoveringMap_exp.liftPath_zero _ _ _,
    fun t => congr_fun (Circle.isCoveringMap_exp.liftPath_lifts _ _ _) t⟩

/-- A path disjoint from a curve between cuffs is homotopic to any cuff
curve with the same ends avoiding the crossing curve's initial point.
This gives the initial homotopy assertion in Graph Minors VI (4.2),
claim (2), page 126. -/
theorem curvesHomotopic_of_disjoint_crosscurve
    (outer : Bool) {f g k : Curve ClosedCylinder}
    (hkr : ∀ t, (k t).1.1 = (if outer then 2 else 1))
    (h0 : f 0 = k 0) (h1 : f 1 = k 1)
    (hg0 : (g 0).1.1 = (if outer then 2 else 1))
    (hg1 : (g 1).1.1 = (if outer then 1 else 2))
    (hdisj : Disjoint (range f) (range g))
    (hkavoid : ∀ t, k t ≠ g 0) : CurvesHomotopic f k := by
  let b := cylinderAngleLift g
  have hangle : (g 0).1.2 ≠ (k 0).1.2 := by
    intro he
    apply hkavoid 0
    exact Subtype.ext (Prod.ext ((hkr 0).trans hg0.symm) he.symm)
  let α := Circle.angleDiff (g 0).1.2 (k 0).1.2
  have hα : 0 < α := Circle.angleDiff_pos hangle
  have hα' : α < 2 * π := Circle.angleDiff_lt_two_pi _ _
  let c := b 0 + α
  have hck : Circle.exp c = (k 0).1.2 := by
    change Circle.exp (b 0 + α) = _
    rw [Circle.exp_add, exp_cylinderAngleLift, mul_comm]
    exact Circle.exp_angleDiff_mul
  obtain ⟨a, ha0, ha⟩ := exists_angle_lift f c (by rw [h0]; exact hck)
  obtain ⟨d, hd0, hd⟩ := exists_angle_lift k c hck
  have hstart : c ∈ Ioo (b 0) (b 0 + 2 * π) := by
    dsimp [c]
    constructor <;> linarith only [hα, hα']
  have ha1 := angle_lift_end_between_of_disjoint_crosscurve outer a b ha
    (exp_cylinderAngleLift g)
    (by rw [h0]; exact hkr 0) (by rw [h1]; exact hkr 1) hg0 hg1 hdisj
    (by rw [ha0]; exact hstart)
  have hd1 := lift_end_between_of_avoid d (b 0) (fun t he => by
    apply hkavoid t
    apply Subtype.ext
    apply Prod.ext
    · exact (hkr t).trans hg0.symm
    · rw [← hd, ← exp_cylinderAngleLift g 0]
      exact he) (by rw [hd0]; exact hstart)
  have hend : a 1 = d 1 := Circle.exp_injOn_Ioc
    (a := b 0) (b := b 0 + 2 * π) (by linarith)
    ⟨ha1.1, ha1.2.le⟩ ⟨hd1.1, hd1.2.le⟩
    (by rw [ha, hd, h1])
  apply curvesHomotopic_of_windingNumber_eq h0 h1
  rw [windingNumber_eq_of_exp_lift a ha, windingNumber_eq_of_exp_lift d hd,
    ha0, hd0, hend]

end GraphMinor.GM06
