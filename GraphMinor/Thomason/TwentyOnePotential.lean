module

public import GraphMinor.Thomason.TwentyOneTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 21-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyOnePotential_monotone : Monotone twentyOnePotential :=
  truncatedTable_monotone twentyOnePotentialValues 234 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyOneRequired_monotone : Monotone twentyOneRequired :=
  truncatedTable_monotone twentyOneRequiredValues 116 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyOnePotential_boundary : (18 : ℕ).choose 2 < twentyOnePotential 18 := by decide

/-- Minimum degree 117 supplies the potential throughout the first reduction. -/
theorem twentyOnePotential_threshold (n : ℕ) (hn : 117 < n) (hn' : n ≤ 234) :
    2 * twentyOnePotential n ≤ 117 * n := by
  have h : ∀ i : Fin 235, 117 < i.val → 2 * twentyOnePotential i ≤ 117 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyOnePotential_bounds (n : ℕ) (hn : 18 < n) (hn' : n ≤ 234)
    (he : twentyOnePotential n ≤ n.choose 2) :
    2 * twentyOnePotential n / n ≤ 116 ∧
      twentyOneRequired (2 * twentyOnePotential n / n) ≤ twentyOnePotential n - twentyOnePotential (n - 1) := by
  have h : ∀ i : Fin 235, 18 < i.val → twentyOnePotential i ≤ i.val.choose 2 →
      2 * twentyOnePotential i / i ≤ 116 ∧
      twentyOneRequired (2 * twentyOnePotential i / i) ≤ twentyOnePotential i - twentyOnePotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
