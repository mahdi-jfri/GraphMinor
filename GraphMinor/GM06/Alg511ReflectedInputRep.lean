module

public import GraphMinor.GM06.Alg511ReflectedTurns
public import GraphMinor.Compute.GM06Alg511Target
import GraphMinor.GM06.Section5ReflectionLinkage
import Mathlib.Tactic

/-!
# Correctness of the finite orientation-reversed input

For VI (5.11), page 134, retain the graph labels, reverse the cuff
order and use the proved corrected integer edge turns. The actual
geometric interpretation is the reflected drawing. Its target is
the negative of the original rational target, and feasibility of
those two targets is equivalent.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The computed finite orientation reversal represents the actual
reflected graph, prescribed cuffs and normalized edge turns. -/
noncomputable def alg511ReflectedInputRep {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) :
    GM06Alg511GraphTurnRep x.reflected (section5ReflectedDrawing x.drawing.pathCount G) where
  graph := alg511ReflectedGraphRep rep.graph
  source := fun i => rep.source (gm06Alg511ReflectFin i)
  target := fun i => rep.target (gm06Alg511ReflectFin i)
  inner := by
    change gm06Alg511ReflectCuffWords x.drawing.innerCuff =
      List.ofFn (fun i : Fin x.drawing.pathCount => (rep.source (gm06Alg511ReflectFin i)).val)
    rw [rep.inner, gm06Alg511ReflectCuffWords_ofFn]
  outer := by
    change gm06Alg511ReflectCuffWords x.drawing.outerCuff =
      List.ofFn (fun i : Fin x.drawing.pathCount => (rep.target (gm06Alg511ReflectFin i)).val)
    rw [rep.outer, gm06Alg511ReflectCuffWords_ofFn]
  source_point i := by
    change section5CylinderReflection x.drawing.pathCount
      (rep.graph.vertex (rep.source (gm06Alg511ReflectFin i))).val = cylinderM1Point x.drawing.pathCount i
    rw [rep.source_point, alg511_reflection_M1 hk]
    exact congrArg (cylinderM1Point x.drawing.pathCount) (gm06Alg511ReflectFin_involutive i)
  target_point i := by
    change section5CylinderReflection x.drawing.pathCount
      (rep.graph.vertex (rep.target (gm06Alg511ReflectFin i))).val = cylinderM2Point x.drawing.pathCount i
    rw [rep.target_point, alg511_reflection_M2 hk]
    exact congrArg (cylinderM2Point x.drawing.pathCount) (gm06Alg511ReflectFin_involutive i)
  turns := alg511_normalized_turns_reflected rep hk

/-- Negating the supplied numerator negates the represented target,
including when the supplied denominator is negative. -/
theorem alg511_reflected_target (x : GM06Alg511WindingInput) :
    x.reflected.drawing.target = -x.drawing.target := by
  simp only [GM06Alg511WindingInput.reflected, GM06Alg511Input.reflected,
    GM06Alg511Input.target, Int.cast_neg, neg_div]

/-- The finite reflected input has exactly the reflected target
feasibility required by the orientation step of VI (5.11). -/
theorem alg511_reflected_target_feasible_iff {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (hk : 0 < x.drawing.pathCount) :
    IsThetaFeasible x.reflected.drawing.pathCount
      (section5ReflectedDrawing x.drawing.pathCount G) x.reflected.drawing.target ↔
      IsThetaFeasible x.drawing.pathCount G x.drawing.target := by
  rw [alg511_reflected_target]
  exact isThetaFeasible_reflected_iff hk x.drawing.target

end GraphMinor.GM06
