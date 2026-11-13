module

public import GraphMinor.Compute.GM06Alg511Input
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The rational target in VI (5.11)

The first test on page 134 checks that the path count times the target
is an integer. For a target supplied as a numerator and a nonzero
denominator, this is exactly integer divisibility. This equivalence
uses no information about the drawing and applies to either sign of
the supplied denominator.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Interpret the supplied pair of integers as a real target winding. -/
noncomputable def GM06Alg511Input.target (x : GM06Alg511Input) : ℝ :=
  (x.numerator : ℝ) / (x.denominator : ℝ)

/-- A rational target meets VI (5.10)(i) exactly when its denominator
 divides the path count times its numerator. -/
theorem gm06Alg511_integral_iff (k : ℕ) (a b : ℤ) (hb : b ≠ 0) :
    (∃ m : ℤ, (k : ℝ) * ((a : ℝ) / (b : ℝ)) = m) ↔ b ∣ (k : ℤ) * a := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have he : (k : ℝ) * (a : ℝ) = (b : ℝ) * (m : ℝ) := by
      calc
        (k : ℝ) * (a : ℝ) = ((k : ℝ) * ((a : ℝ) / (b : ℝ))) * b := by
          field_simp
        _ = (b : ℝ) * (m : ℝ) := by rw [hm]; ring
    exact_mod_cast he
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have he : (k : ℝ) * (a : ℝ) = (b : ℝ) * (m : ℝ) := by exact_mod_cast hm
    calc
      (k : ℝ) * ((a : ℝ) / (b : ℝ)) = ((k : ℝ) * (a : ℝ)) / b := by ring
      _ = m := by rw [he]; field_simp

/-- A computable arithmetic test of VI (5.10)(i) on the supplied target. -/
def gm06Alg511IntegralTest (x : GM06Alg511Input) : Bool :=
  decide (x.denominator ∣ (x.pathCount : ℤ) * x.numerator)

/-- The arithmetic test has exactly the meaning required by (5.10)(i). -/
theorem gm06Alg511IntegralTest_correct (x : GM06Alg511Input)
    (hb : x.denominator ≠ 0) :
    gm06Alg511IntegralTest x = true ↔
      ∃ m : ℤ, (x.pathCount : ℝ) * x.target = m := by
  simp only [gm06Alg511IntegralTest, decide_eq_true_eq, GM06Alg511Input.target]
  exact (gm06Alg511_integral_iff x.pathCount x.numerator x.denominator hb).symm

end GraphMinor.Compute
