module

public import GraphMinor.Thomason.ThirteenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 13-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem thirteenPotential_monotone : Monotone thirteenPotential :=
  truncatedTable_monotone thirteenPotentialValues 134 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem thirteenRequired_monotone : Monotone thirteenRequired :=
  truncatedTable_monotone thirteenRequiredValues 54 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem thirteenPotential_boundary : (10 : ℕ).choose 2 < thirteenPotential 10 := by decide

/-- Minimum degree 67 supplies the potential throughout the first reduction. -/
theorem thirteenPotential_threshold (n : ℕ) (hn : 67 < n) (hn' : n ≤ 134) :
    2 * thirteenPotential n ≤ 67 * n := by
  have h : ∀ i : Fin 135, 67 < i.val → 2 * thirteenPotential i ≤ 67 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem thirteenPotential_bounds (n : ℕ) (hn : 10 < n) (hn' : n ≤ 134)
    (he : thirteenPotential n ≤ n.choose 2) :
    2 * thirteenPotential n / n ≤ 54 ∧
      thirteenRequired (2 * thirteenPotential n / n) ≤ thirteenPotential n - thirteenPotential (n - 1) := by
  have h : ∀ i : Fin 135, 10 < i.val → thirteenPotential i ≤ i.val.choose 2 →
      2 * thirteenPotential i / i ≤ 54 ∧
      thirteenRequired (2 * thirteenPotential i / i) ≤ thirteenPotential i - thirteenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
