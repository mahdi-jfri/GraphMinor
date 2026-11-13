module

public import GraphMinor.Thomason.FortyTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 40-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem fortyPotential_monotone : Monotone fortyPotential :=
  truncatedTable_monotone fortyPotentialValues 444 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem fortyRequired_monotone : Monotone fortyRequired :=
  truncatedTable_monotone fortyRequiredValues 221 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem fortyPotential_boundary : (37 : ℕ).choose 2 < fortyPotential 37 := by decide

/-- Minimum degree 222 supplies the potential throughout the first reduction. -/
theorem fortyPotential_threshold (n : ℕ) (hn : 222 < n) (hn' : n ≤ 444) :
    2 * fortyPotential n ≤ 222 * n := by
  have h : ∀ i : Fin 445, 222 < i.val → 2 * fortyPotential i ≤ 222 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem fortyPotential_bounds (n : ℕ) (hn : 37 < n) (hn' : n ≤ 444)
    (he : fortyPotential n ≤ n.choose 2) :
    2 * fortyPotential n / n ≤ 221 ∧
      fortyRequired (2 * fortyPotential n / n) ≤ fortyPotential n - fortyPotential (n - 1) := by
  have h : ∀ i : Fin 445, 37 < i.val → fortyPotential i ≤ i.val.choose 2 →
      2 * fortyPotential i / i ≤ 221 ∧
      fortyRequired (2 * fortyPotential i / i) ≤ fortyPotential i - fortyPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
