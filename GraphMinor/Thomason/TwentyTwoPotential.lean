module

public import GraphMinor.Thomason.TwentyTwoTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 22-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyTwoPotential_monotone : Monotone twentyTwoPotential :=
  truncatedTable_monotone twentyTwoPotentialValues 248 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyTwoRequired_monotone : Monotone twentyTwoRequired :=
  truncatedTable_monotone twentyTwoRequiredValues 122 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyTwoPotential_boundary : (19 : ℕ).choose 2 < twentyTwoPotential 19 := by decide

/-- Minimum degree 124 supplies the potential throughout the first reduction. -/
theorem twentyTwoPotential_threshold (n : ℕ) (hn : 124 < n) (hn' : n ≤ 248) :
    2 * twentyTwoPotential n ≤ 124 * n := by
  have h : ∀ i : Fin 249, 124 < i.val → 2 * twentyTwoPotential i ≤ 124 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyTwoPotential_bounds (n : ℕ) (hn : 19 < n) (hn' : n ≤ 248)
    (he : twentyTwoPotential n ≤ n.choose 2) :
    2 * twentyTwoPotential n / n ≤ 122 ∧
      twentyTwoRequired (2 * twentyTwoPotential n / n) ≤ twentyTwoPotential n - twentyTwoPotential (n - 1) := by
  have h : ∀ i : Fin 249, 19 < i.val → twentyTwoPotential i ≤ i.val.choose 2 →
      2 * twentyTwoPotential i / i ≤ 122 ∧
      twentyTwoRequired (2 * twentyTwoPotential i / i) ≤ twentyTwoPotential i - twentyTwoPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
