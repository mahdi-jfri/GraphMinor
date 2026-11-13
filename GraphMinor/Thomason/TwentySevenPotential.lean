module

public import GraphMinor.Thomason.TwentySevenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 27-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentySevenPotential_monotone : Monotone twentySevenPotential :=
  truncatedTable_monotone twentySevenPotentialValues 314 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentySevenRequired_monotone : Monotone twentySevenRequired :=
  truncatedTable_monotone twentySevenRequiredValues 142 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentySevenPotential_boundary : (24 : ℕ).choose 2 < twentySevenPotential 24 := by decide

/-- Minimum degree 157 supplies the potential throughout the first reduction. -/
theorem twentySevenPotential_threshold (n : ℕ) (hn : 157 < n) (hn' : n ≤ 314) :
    2 * twentySevenPotential n ≤ 157 * n := by
  have h : ∀ i : Fin 315, 157 < i.val → 2 * twentySevenPotential i ≤ 157 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentySevenPotential_bounds (n : ℕ) (hn : 24 < n) (hn' : n ≤ 314)
    (he : twentySevenPotential n ≤ n.choose 2) :
    2 * twentySevenPotential n / n ≤ 142 ∧
      twentySevenRequired (2 * twentySevenPotential n / n) ≤ twentySevenPotential n - twentySevenPotential (n - 1) := by
  have h : ∀ i : Fin 315, 24 < i.val → twentySevenPotential i ≤ i.val.choose 2 →
      2 * twentySevenPotential i / i ≤ 142 ∧
      twentySevenRequired (2 * twentySevenPotential i / i) ≤ twentySevenPotential i - twentySevenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
