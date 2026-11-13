module

public import GraphMinor.GM06.Alg511ChosenLinkage
public import GraphMinor.GM06.Alg511WalkWinding
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Alg511CuffIndices
import Mathlib.Tactic

/-!
# The winding of a retained labelled linkage path

For VI (5.11), page 134, interpret the integer turn of a stored
path and read its prescribed endpoint index. The normalized turn
formula gives the winding of that path's actual parametrization.
All curves of the same cylinder linkage have that winding, so the
formula determines the value of the full retained linkage.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- A retained finite labelled path computes the winding of the
whole actual linkage, including its prescribed endpoint correction. -/
theorem alg511_linkage_hasTheta_of_labelled_path (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (c : Fin x.drawing.pathCount)
    (b : Fin x.drawing.vertexCount) (hb : b ∈ x.drawing.flowInput.B)
    (W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source c) b)
    (actual : GraphWalk G.toGraph (rep.graph.vertex (rep.source c)).val (rep.graph.vertex b).val)
    (hs : actual.IsSimple)
    (hturn : alg511InterpretedWalkTurn rep.graph x.edgeTurns actual =
      gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns W)
    (L : CylinderLinkage x.drawing.pathCount G)
    (hparam : ParametrizesSet (L.curve c) (walkDrawing G actual).U
      (rep.graph.vertex (rep.source c)).val (rep.graph.vertex b).val) :
    ∃ j : Fin x.drawing.pathCount, rep.target j = b ∧
      L.HasTheta ((((x.drawing.pathCount : ℤ) *
        gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns W + (j.val : ℤ) -
          (c.val : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) := by
  obtain ⟨j, hj⟩ := rep.flowB_exists_target b hb
  obtain ⟨reference, hM1, hM2, hw⟩ :=
    alg511_normalized_walk_winding rep.graph x.edgeTurns rep.turns
  have hwind := hw actual hs (L.curve c) hparam
  have hsource := rep.source_point c
  have htarget : (rep.graph.vertex b).val = cylinderM2Point x.drawing.pathCount j := by
    rw [← hj]
    exact rep.target_point j
  rw [congrArg reference hsource, congrArg reference htarget, hM1, hM2] at hwind
  have hscaled := alg511_scaled_winding_of_relative_turn hk c j (L.curve c)
    (alg511InterpretedWalkTurn rep.graph x.edgeTurns actual)
    (alg511_relative_curveTurn_iff.mpr hwind)
  rw [hturn] at hscaled
  have hcurve : windingNumber (L.curve c) =
      ((((x.drawing.pathCount : ℤ) * gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns W +
        (j.val : ℤ) - (c.val : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) := by
    apply (eq_div_iff (show (x.drawing.pathCount : ℝ) ≠ 0 from
      Nat.cast_ne_zero.mpr (ne_of_gt hk))).mpr
    simpa only [mul_comm] using hscaled
  obtain ⟨theta, htheta⟩ := L.exists_hasTheta hk
  refine ⟨j, hj, ?_⟩
  intro i
  exact (htheta i).trans ((htheta c).symm.trans hcurve)

end GraphMinor.GM06
