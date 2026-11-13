module

public import GraphMinor.Thomason.FortyFourTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 44-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem fortyFourPotential_monotone : Monotone fortyFourPotential :=
  truncatedTable_monotone fortyFourPotentialValues 504 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem fortyFourRequired_monotone : Monotone fortyFourRequired :=
  truncatedTable_monotone fortyFourRequiredValues 251 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem fortyFourPotential_boundary : (41 : ℕ).choose 2 < fortyFourPotential 41 := by decide

/-- Minimum degree 252 supplies the potential throughout the first reduction. -/
theorem fortyFourPotential_threshold (n : ℕ) (hn : 252 < n) (hn' : n ≤ 504) :
    2 * fortyFourPotential n ≤ 252 * n := by
  have h : ∀ i : Fin 505, 252 < i.val → 2 * fortyFourPotential i ≤ 252 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem fortyFourPotential_bounds (n : ℕ) (hn : 41 < n) (hn' : n ≤ 504)
    (he : fortyFourPotential n ≤ n.choose 2) :
    2 * fortyFourPotential n / n ≤ 251 ∧
      fortyFourRequired (2 * fortyFourPotential n / n) ≤ fortyFourPotential n - fortyFourPotential (n - 1) := by
  have h : ∀ i : Fin 505, 41 < i.val → fortyFourPotential i ≤ i.val.choose 2 →
      2 * fortyFourPotential i / i ≤ 251 ∧
      fortyFourRequired (2 * fortyFourPotential i / i) ≤ fortyFourPotential i - fortyFourPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
