module

public import GraphMinor.Surface.Cylinder
import Mathlib.Tactic

/-!
# Integer turn data for cylinder edges

VI, Section 5, page 127, measures a curve's winding by its total
angular change. Its endpoint principal angles determine this change
up to a whole number of turns. A finite cylinder input can supply
that integer for each oriented edge, in addition to its incidence
data. This file proves existence and uniqueness of this integer for
any continuous cylinder curve and gives the resulting winding formula.
All existence choices occur in Prop, outside the executable input.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Surface Complex Real

/-- Interpret a supplied integer as the full turns in the lifted angle
beyond the principal angle of the terminal point. This is geometric
edge data relative to the fixed angular coordinates of VI, page 127. -/
def Alg511CurveTurn (f : Curve ClosedCylinder) (turn : ℤ) : Prop :=
  cylinderAngleLift f 1 = arg ((f 1).val.2 : ℂ) + (turn : ℝ) * (2 * π)

/-- Every continuous cylinder curve has an integer turn label. -/
theorem alg511_exists_curveTurn (f : Curve ClosedCylinder) :
    ∃ turn : ℤ, Alg511CurveTurn f turn := by
  have he : Circle.exp (cylinderAngleLift f 1) =
      Circle.exp (arg ((f 1).val.2 : ℂ)) := by
    rw [exp_cylinderAngleLift, Circle.exp_arg]
  obtain ⟨turn, ht⟩ := Circle.exp_eq_exp.mp he
  exact ⟨turn, ht⟩

/-- The geometric interpretation determines the integer label uniquely. -/
theorem alg511_curveTurn_unique {f : Curve ClosedCylinder} {a b : ℤ}
    (ha : Alg511CurveTurn f a) (hb : Alg511CurveTurn f b) : a = b := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have he : (a : ℝ) = (b : ℝ) := by
    dsimp only [Alg511CurveTurn] at ha hb
    nlinarith
  exact_mod_cast he

/-- Principal endpoint angles and the supplied integer turn determine
 the curve's winding. -/
theorem alg511_windingNumber_of_curveTurn {f : Curve ClosedCylinder} {turn : ℤ}
    (ht : Alg511CurveTurn f turn) :
    windingNumber f =
      (arg ((f 1).val.2 : ℂ) - arg ((f 0).val.2 : ℂ)) / (2 * π) + (turn : ℝ) := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  unfold windingNumber
  rw [ht, cylinderAngleLift_zero]
  field_simp
  ring

/-- The winding formula also suffices to interpret a supplied turn. -/
theorem alg511_curveTurn_iff {f : Curve ClosedCylinder} {turn : ℤ} :
    Alg511CurveTurn f turn ↔ windingNumber f =
      (arg ((f 1).val.2 : ℂ) - arg ((f 0).val.2 : ℂ)) / (2 * π) + (turn : ℝ) := by
  refine ⟨alg511_windingNumber_of_curveTurn, ?_⟩
  intro h
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  unfold windingNumber at h
  rw [cylinderAngleLift_zero] at h
  field_simp at h
  dsimp only [Alg511CurveTurn]
  linarith

/-- Turn labels can be supplied for every member of a finite family
of oriented curves. This is an existence statement, not an encoder
that extracts data from a drawing by choice. -/
theorem alg511_exists_curveTurn_list {m : ℕ} (curves : Fin m → Curve ClosedCylinder) :
    ∃ turns : List ℤ, ∃ hlen : turns.length = m,
      ∀ i : Fin m, Alg511CurveTurn (curves i) (turns[i.val]'(by rw [hlen]; exact i.isLt)) := by
  classical
  choose turn ht using fun i => alg511_exists_curveTurn (curves i)
  refine ⟨List.ofFn turn, List.length_ofFn, ?_⟩
  intro i
  simpa using ht i

end GraphMinor.GM06
