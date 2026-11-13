module

public import GraphMinor.Thomason.TwentyNineTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 29-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem twentyNinePotential_monotone : Monotone twentyNinePotential :=
  truncatedTable_monotone twentyNinePotentialValues 342 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem twentyNineRequired_monotone : Monotone twentyNineRequired :=
  truncatedTable_monotone twentyNineRequiredValues 157 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem twentyNinePotential_boundary : (26 : ℕ).choose 2 < twentyNinePotential 26 := by decide

/-- Minimum degree 171 supplies the potential throughout the first reduction. -/
theorem twentyNinePotential_threshold (n : ℕ) (hn : 171 < n) (hn' : n ≤ 342) :
    2 * twentyNinePotential n ≤ 171 * n := by
  have h : ∀ i : Fin 343, 171 < i.val → 2 * twentyNinePotential i ≤ 171 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem twentyNinePotential_bounds (n : ℕ) (hn : 26 < n) (hn' : n ≤ 342)
    (he : twentyNinePotential n ≤ n.choose 2) :
    2 * twentyNinePotential n / n ≤ 157 ∧
      twentyNineRequired (2 * twentyNinePotential n / n) ≤ twentyNinePotential n - twentyNinePotential (n - 1) := by
  have h : ∀ i : Fin 343, 26 < i.val → twentyNinePotential i ≤ i.val.choose 2 →
      2 * twentyNinePotential i / i ≤ 157 ∧
      twentyNineRequired (2 * twentyNinePotential i / i) ≤ twentyNinePotential i - twentyNinePotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
