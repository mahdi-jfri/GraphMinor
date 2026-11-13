module

public import GraphMinor.Thomason.TwentySixTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 26-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentySixPotential_monotone : Monotone twentySixPotential :=
  truncatedTable_monotone twentySixPotentialValues 302 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentySixRequired_monotone : Monotone twentySixRequired :=
  truncatedTable_monotone twentySixRequiredValues 135 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentySixPotential_boundary : (23 : ℕ).choose 2 < twentySixPotential 23 := by decide

/-- Minimum degree 151 supplies the potential throughout the first reduction. -/
theorem twentySixPotential_threshold (n : ℕ) (hn : 151 < n) (hn' : n ≤ 302) :
    2 * twentySixPotential n ≤ 151 * n := by
  have h : ∀ i : Fin 303, 151 < i.val → 2 * twentySixPotential i ≤ 151 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentySixPotential_bounds (n : ℕ) (hn : 23 < n) (hn' : n ≤ 302)
    (he : twentySixPotential n ≤ n.choose 2) :
    2 * twentySixPotential n / n ≤ 135 ∧
      twentySixRequired (2 * twentySixPotential n / n) ≤ twentySixPotential n - twentySixPotential (n - 1) := by
  have h : ∀ i : Fin 303, 23 < i.val → twentySixPotential i ≤ i.val.choose 2 →
      2 * twentySixPotential i / i ≤ 135 ∧
      twentySixRequired (2 * twentySixPotential i / i) ≤ twentySixPotential i - twentySixPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
