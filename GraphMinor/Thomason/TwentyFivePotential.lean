module

public import GraphMinor.Thomason.TwentyFiveTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 25-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyFivePotential_monotone : Monotone twentyFivePotential :=
  truncatedTable_monotone twentyFivePotentialValues 288 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyFiveRequired_monotone : Monotone twentyFiveRequired :=
  truncatedTable_monotone twentyFiveRequiredValues 143 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyFivePotential_boundary : (22 : ℕ).choose 2 < twentyFivePotential 22 := by decide

/-- Minimum degree 144 supplies the potential throughout the first reduction. -/
theorem twentyFivePotential_threshold (n : ℕ) (hn : 144 < n) (hn' : n ≤ 288) :
    2 * twentyFivePotential n ≤ 144 * n := by
  have h : ∀ i : Fin 289, 144 < i.val → 2 * twentyFivePotential i ≤ 144 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyFivePotential_bounds (n : ℕ) (hn : 22 < n) (hn' : n ≤ 288)
    (he : twentyFivePotential n ≤ n.choose 2) :
    2 * twentyFivePotential n / n ≤ 143 ∧
      twentyFiveRequired (2 * twentyFivePotential n / n) ≤ twentyFivePotential n - twentyFivePotential (n - 1) := by
  have h : ∀ i : Fin 289, 22 < i.val → twentyFivePotential i ≤ i.val.choose 2 →
      2 * twentyFivePotential i / i ≤ 143 ∧
      twentyFiveRequired (2 * twentyFivePotential i / i) ≤ twentyFivePotential i - twentyFivePotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
