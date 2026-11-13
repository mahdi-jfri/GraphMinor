module

public import GraphMinor.Thomason.TwentyTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 20-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyPotential_monotone : Monotone twentyPotential :=
  truncatedTable_monotone twentyPotentialValues 222 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyRequired_monotone : Monotone twentyRequired :=
  truncatedTable_monotone twentyRequiredValues 108 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyPotential_boundary : (17 : ℕ).choose 2 < twentyPotential 17 := by decide

/-- Minimum degree 111 supplies the potential throughout the first reduction. -/
theorem twentyPotential_threshold (n : ℕ) (hn : 111 < n) (hn' : n ≤ 222) :
    2 * twentyPotential n ≤ 111 * n := by
  have h : ∀ i : Fin 223, 111 < i.val → 2 * twentyPotential i ≤ 111 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyPotential_bounds (n : ℕ) (hn : 17 < n) (hn' : n ≤ 222)
    (he : twentyPotential n ≤ n.choose 2) :
    2 * twentyPotential n / n ≤ 108 ∧
      twentyRequired (2 * twentyPotential n / n) ≤ twentyPotential n - twentyPotential (n - 1) := by
  have h : ∀ i : Fin 223, 17 < i.val → twentyPotential i ≤ i.val.choose 2 →
      2 * twentyPotential i / i ≤ 108 ∧
      twentyRequired (2 * twentyPotential i / i) ≤ twentyPotential i - twentyPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
