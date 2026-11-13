module

public import GraphMinor.Thomason.ThirtyTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 30-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem thirtyPotential_monotone : Monotone thirtyPotential :=
  truncatedTable_monotone thirtyPotentialValues 356 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem thirtyRequired_monotone : Monotone thirtyRequired :=
  truncatedTable_monotone thirtyRequiredValues 164 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem thirtyPotential_boundary : (27 : ℕ).choose 2 < thirtyPotential 27 := by decide

/-- Minimum degree 178 supplies the potential throughout the first reduction. -/
theorem thirtyPotential_threshold (n : ℕ) (hn : 178 < n) (hn' : n ≤ 356) :
    2 * thirtyPotential n ≤ 178 * n := by
  have h : ∀ i : Fin 357, 178 < i.val → 2 * thirtyPotential i ≤ 178 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem thirtyPotential_bounds (n : ℕ) (hn : 27 < n) (hn' : n ≤ 356)
    (he : thirtyPotential n ≤ n.choose 2) :
    2 * thirtyPotential n / n ≤ 164 ∧
      thirtyRequired (2 * thirtyPotential n / n) ≤ thirtyPotential n - thirtyPotential (n - 1) := by
  have h : ∀ i : Fin 357, 27 < i.val → thirtyPotential i ≤ i.val.choose 2 →
      2 * thirtyPotential i / i ≤ 164 ∧
      thirtyRequired (2 * thirtyPotential i / i) ≤ thirtyPotential i - thirtyPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
