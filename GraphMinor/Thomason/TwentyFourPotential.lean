module

public import GraphMinor.Thomason.TwentyFourTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 24-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyFourPotential_monotone : Monotone twentyFourPotential :=
  truncatedTable_monotone twentyFourPotentialValues 274 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyFourRequired_monotone : Monotone twentyFourRequired :=
  truncatedTable_monotone twentyFourRequiredValues 135 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyFourPotential_boundary : (21 : ℕ).choose 2 < twentyFourPotential 21 := by decide

/-- Minimum degree 137 supplies the potential throughout the first reduction. -/
theorem twentyFourPotential_threshold (n : ℕ) (hn : 137 < n) (hn' : n ≤ 274) :
    2 * twentyFourPotential n ≤ 137 * n := by
  have h : ∀ i : Fin 275, 137 < i.val → 2 * twentyFourPotential i ≤ 137 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyFourPotential_bounds (n : ℕ) (hn : 21 < n) (hn' : n ≤ 274)
    (he : twentyFourPotential n ≤ n.choose 2) :
    2 * twentyFourPotential n / n ≤ 135 ∧
      twentyFourRequired (2 * twentyFourPotential n / n) ≤ twentyFourPotential n - twentyFourPotential (n - 1) := by
  have h : ∀ i : Fin 275, 21 < i.val → twentyFourPotential i ≤ i.val.choose 2 →
      2 * twentyFourPotential i / i ≤ 135 ∧
      twentyFourRequired (2 * twentyFourPotential i / i) ≤ twentyFourPotential i - twentyFourPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
