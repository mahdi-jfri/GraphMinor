module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Reference angles for the finite cylinder input

VI, Section 5, page 127, fixes equally spaced angular coordinates
for the prescribed cuff vertices. Choose a real angle at every point
of the cylinder that agrees with those coordinates on both cuffs.
Continuity is not required: these are reference angles at the finite
vertices, used to describe each edge's whole turns. Along a path,
the internal reference angles cancel. These witnesses occur only
in the geometric interpretation of supplied edge data, never in the
word array or an executable encoder.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface Complex Real

/-- Real reference angles can agree with every prescribed cuff angle
while exponentiating to the actual angular coordinate at every point. -/
theorem alg511_exists_reference_angles {k : ℕ} (hk : 0 < k) :
    ∃ reference : ClosedCylinder → ℝ,
      (∀ p, Circle.exp (reference p) = p.val.2) ∧
      (∀ i : Fin k, reference (cylinderM1Point k i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / k) ∧
      (∀ i : Fin k, reference (cylinderM2Point k i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / k) := by
  classical
  let angle : Fin k → Circle := fun i => (cylinderM1Point k i).val.2
  let value : Fin k → ℝ := fun i => 2 * ((i.val + 1 : ℕ) : ℝ) * π / k
  have hinj : Function.Injective angle := by
    intro i j hij
    apply cylinderM1Point_injective hk
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hij
  let phase : Circle → ℝ := Function.extend angle value (fun z => arg (z : ℂ))
  have hphase : ∀ i, phase (angle i) = value i :=
    hinj.extend_apply value (fun z => arg (z : ℂ))
  have hexp : ∀ z : Circle, Circle.exp (phase z) = z := by
    intro z
    by_cases hz : ∃ i, angle i = z
    · obtain ⟨i, rfl⟩ := hz
      rw [hphase]
      rfl
    · exact (congrArg Circle.exp (Function.extend_apply' (f := angle) value
        (fun z : Circle => arg (z : ℂ)) z hz)).trans (Circle.exp_arg z)
  refine ⟨fun p => phase p.val.2, fun p => hexp p.val.2, ?_, ?_⟩
  · intro i
    exact hphase i
  · intro i
    exact hphase i

end GraphMinor.GM06
