module

public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section5HelixConcatenation
import GraphMinor.GM06.Section5HelixSurgeryIdentities
import Mathlib.Tactic

/-!
# Whole edge turns relative to vertex reference angles

For the winding computation in VI (5.11), page 134, use reference
angles that equal the prescribed angles on the cuffs. An integer
edge label records the difference between its total angular change
and its endpoint reference-angle difference. Such a label always
exists. Labels add along a path and change sign when it is reversed.
These facts let the finite computation cancel all internal angles.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Surface Complex Real

/-- Geometric meaning of an integer edge-turn label relative to the
two vertex reference angles. It records total lifted angular change. -/
def Alg511RelativeCurveTurn (f : Curve ClosedCylinder) (startAngle endAngle : ℝ)
    (turn : ℤ) : Prop :=
  cylinderAngleLift f 1 - cylinderAngleLift f 0 =
    endAngle - startAngle + (turn : ℝ) * (2 * π)

/-- Endpoint reference angles that exponentiate to the actual
endpoints have an integer whole-turn label for every curve. -/
theorem alg511_exists_relative_curveTurn (f : Curve ClosedCylinder)
    (startAngle endAngle : ℝ)
    (hstart : Circle.exp startAngle = (f 0).val.2)
    (hend : Circle.exp endAngle = (f 1).val.2) :
    ∃ turn : ℤ, Alg511RelativeCurveTurn f startAngle endAngle turn := by
  have he : Circle.exp (cylinderAngleLift f 1 - cylinderAngleLift f 0 + startAngle) =
      Circle.exp endAngle := by
    rw [Circle.exp_add, Circle.exp_sub, exp_cylinderAngleLift, exp_cylinderAngleLift,
      hstart, hend, div_mul_cancel]
  obtain ⟨turn, ht⟩ := Circle.exp_eq_exp.mp he
  refine ⟨turn, ?_⟩
  dsimp only [Alg511RelativeCurveTurn]
  linarith

/-- Relative turn data are exactly the endpoint-angle winding formula. -/
theorem alg511_relative_curveTurn_iff {f : Curve ClosedCylinder}
    {startAngle endAngle : ℝ} {turn : ℤ} :
    Alg511RelativeCurveTurn f startAngle endAngle turn ↔
      windingNumber f = (endAngle - startAngle) / (2 * π) + (turn : ℝ) := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  constructor
  · intro ht
    unfold windingNumber
    rw [ht]
    field_simp
  · intro ht
    unfold windingNumber at ht
    field_simp at ht
    dsimp only [Alg511RelativeCurveTurn]
    linarith

/-- Relative turns add when two consecutive paths are joined. -/
theorem alg511_relative_curveTurn_trans {x y z : ClosedCylinder}
    (p : Path x y) (q : Path y z) {a b c : ℝ} {m n : ℤ}
    (hp : Alg511RelativeCurveTurn p.toContinuousMap a b m)
    (hq : Alg511RelativeCurveTurn q.toContinuousMap b c n) :
    Alg511RelativeCurveTurn (p.trans q).toContinuousMap a c (m + n) := by
  apply alg511_relative_curveTurn_iff.mpr
  rw [windingNumber_path_trans, alg511_relative_curveTurn_iff.mp hp,
    alg511_relative_curveTurn_iff.mp hq]
  push_cast
  ring

/-- Reversing a path negates its integer relative turn. -/
theorem alg511_relative_curveTurn_symm {x y : ClosedCylinder} (p : Path x y)
    {a b : ℝ} {m : ℤ} (hp : Alg511RelativeCurveTurn p.toContinuousMap a b m) :
    Alg511RelativeCurveTurn p.symm.toContinuousMap b a (-m) := by
  apply alg511_relative_curveTurn_iff.mpr
  rw [windingNumber_path_symm, alg511_relative_curveTurn_iff.mp hp]
  push_cast
  ring

end GraphMinor.GM06
