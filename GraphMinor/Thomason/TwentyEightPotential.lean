module

public import GraphMinor.Thomason.TwentyEightTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 28-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyEightPotential_monotone : Monotone twentyEightPotential :=
  truncatedTable_monotone twentyEightPotentialValues 328 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyEightRequired_monotone : Monotone twentyEightRequired :=
  truncatedTable_monotone twentyEightRequiredValues 149 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyEightPotential_boundary : (25 : ℕ).choose 2 < twentyEightPotential 25 := by decide

/-- Minimum degree 164 supplies the potential throughout the first reduction. -/
theorem twentyEightPotential_threshold (n : ℕ) (hn : 164 < n) (hn' : n ≤ 328) :
    2 * twentyEightPotential n ≤ 164 * n := by
  have h : ∀ i : Fin 329, 164 < i.val → 2 * twentyEightPotential i ≤ 164 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyEightPotential_bounds (n : ℕ) (hn : 25 < n) (hn' : n ≤ 328)
    (he : twentyEightPotential n ≤ n.choose 2) :
    2 * twentyEightPotential n / n ≤ 149 ∧
      twentyEightRequired (2 * twentyEightPotential n / n) ≤ twentyEightPotential n - twentyEightPotential (n - 1) := by
  have h : ∀ i : Fin 329, 25 < i.val → twentyEightPotential i ≤ i.val.choose 2 →
      2 * twentyEightPotential i / i ≤ 149 ∧
      twentyEightRequired (2 * twentyEightPotential i / i) ≤ twentyEightPotential i - twentyEightPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
