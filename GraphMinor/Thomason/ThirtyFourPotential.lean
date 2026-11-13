module

public import GraphMinor.Thomason.ThirtyFourTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 34-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem thirtyFourPotential_monotone : Monotone thirtyFourPotential :=
  truncatedTable_monotone thirtyFourPotentialValues 368 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem thirtyFourRequired_monotone : Monotone thirtyFourRequired :=
  truncatedTable_monotone thirtyFourRequiredValues 183 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem thirtyFourPotential_boundary : (31 : ℕ).choose 2 < thirtyFourPotential 31 := by decide

/-- Minimum degree 184 supplies the potential throughout the first reduction. -/
theorem thirtyFourPotential_threshold (n : ℕ) (hn : 184 < n) (hn' : n ≤ 368) :
    2 * thirtyFourPotential n ≤ 184 * n := by
  have h : ∀ i : Fin 369, 184 < i.val → 2 * thirtyFourPotential i ≤ 184 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem thirtyFourPotential_bounds (n : ℕ) (hn : 31 < n) (hn' : n ≤ 368)
    (he : thirtyFourPotential n ≤ n.choose 2) :
    2 * thirtyFourPotential n / n ≤ 183 ∧
      thirtyFourRequired (2 * thirtyFourPotential n / n) ≤ thirtyFourPotential n - thirtyFourPotential (n - 1) := by
  have h : ∀ i : Fin 369, 31 < i.val → thirtyFourPotential i ≤ i.val.choose 2 →
      2 * thirtyFourPotential i / i ≤ 183 ∧
      thirtyFourRequired (2 * thirtyFourPotential i / i) ≤ thirtyFourPotential i - thirtyFourPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
