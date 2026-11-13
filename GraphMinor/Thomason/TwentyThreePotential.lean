module

public import GraphMinor.Thomason.TwentyThreeTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 23-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyThreePotential_monotone : Monotone twentyThreePotential :=
  truncatedTable_monotone twentyThreePotentialValues 262 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyThreeRequired_monotone : Monotone twentyThreeRequired :=
  truncatedTable_monotone twentyThreeRequiredValues 130 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyThreePotential_boundary : (20 : ℕ).choose 2 < twentyThreePotential 20 := by decide

/-- Minimum degree 131 supplies the potential throughout the first reduction. -/
theorem twentyThreePotential_threshold (n : ℕ) (hn : 131 < n) (hn' : n ≤ 262) :
    2 * twentyThreePotential n ≤ 131 * n := by
  have h : ∀ i : Fin 263, 131 < i.val → 2 * twentyThreePotential i ≤ 131 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyThreePotential_bounds (n : ℕ) (hn : 20 < n) (hn' : n ≤ 262)
    (he : twentyThreePotential n ≤ n.choose 2) :
    2 * twentyThreePotential n / n ≤ 130 ∧
      twentyThreeRequired (2 * twentyThreePotential n / n) ≤ twentyThreePotential n - twentyThreePotential (n - 1) := by
  have h : ∀ i : Fin 263, 20 < i.val → twentyThreePotential i ≤ i.val.choose 2 →
      2 * twentyThreePotential i / i ≤ 130 ∧
      twentyThreeRequired (2 * twentyThreePotential i / i) ≤ twentyThreePotential i - twentyThreePotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
