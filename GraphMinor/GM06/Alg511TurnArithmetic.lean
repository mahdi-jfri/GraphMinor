module

public import GraphMinor.GM06.Alg511CurveTurns
import GraphMinor.GM06.Section5HelixConcatenation
import GraphMinor.GM06.Section5HelixSurgeryIdentities
import Mathlib.Tactic

/-!
# Computing turns along a cylinder path

The winding definition on page 127 of VI adds angular changes along
successive edges. Principal angles at internal vertices cancel. Thus
the integer turn of a concatenation is the sum of its edge turns,
and reversing a path negates its turn. These facts justify using
signed edge integers for the winding computation in (5.11).
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface Complex Real

/-- The turn of two joined paths is the sum of their supplied turns. -/
theorem alg511_curveTurn_trans {x y z : ClosedCylinder} (p : Path x y) (q : Path y z)
    {a b : ℤ} (hp : Alg511CurveTurn p.toContinuousMap a)
    (hq : Alg511CurveTurn q.toContinuousMap b) :
    Alg511CurveTurn (p.trans q).toContinuousMap (a + b) := by
  apply alg511_curveTurn_iff.mpr
  rw [windingNumber_path_trans, alg511_windingNumber_of_curveTurn hp,
    alg511_windingNumber_of_curveTurn hq]
  simp only [Path.coe_toContinuousMap, Path.source, Path.target, Int.cast_add]
  ring

/-- Reversing an edge or path negates its supplied integer turn. -/
theorem alg511_curveTurn_symm {x y : ClosedCylinder} (p : Path x y)
    {a : ℤ} (hp : Alg511CurveTurn p.toContinuousMap a) :
    Alg511CurveTurn p.symm.toContinuousMap (-a) := by
  apply alg511_curveTurn_iff.mpr
  rw [windingNumber_path_symm, alg511_windingNumber_of_curveTurn hp]
  simp only [Path.coe_toContinuousMap, Path.source, Path.target, Int.cast_neg]
  ring

end GraphMinor.GM06
