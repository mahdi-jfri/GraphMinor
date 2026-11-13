module

public import GraphMinor.Thomason.FiftyTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.NumericTableChain
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 50-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem fiftyPotential_monotone : Monotone fiftyPotential :=
  truncatedTable_monotone_of_chain fiftyPotentialValues 596 (by decide) (by decide)

/-- Global monotonicity of the required degrees. -/
theorem fiftyRequired_monotone : Monotone fiftyRequired :=
  truncatedTable_monotone_of_chain fiftyRequiredValues 297 (by decide) (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem fiftyPotential_boundary : (47 : ℕ).choose 2 < fiftyPotential 47 := by decide

/-- Minimum degree 298 supplies the potential throughout the first reduction. -/
theorem fiftyPotential_threshold (n : ℕ) (hn : 298 < n) (hn' : n ≤ 596) :
    2 * fiftyPotential n ≤ 298 * n := by
  have h : ∀ i : Fin 597, 298 < i.val → 2 * fiftyPotential i ≤ 298 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem fiftyPotential_bounds (n : ℕ) (hn : 47 < n) (hn' : n ≤ 596)
    (he : fiftyPotential n ≤ n.choose 2) :
    2 * fiftyPotential n / n ≤ 297 ∧
      fiftyRequired (2 * fiftyPotential n / n) ≤ fiftyPotential n - fiftyPotential (n - 1) := by
  have h : ∀ i : Fin 597, 47 < i.val → fiftyPotential i ≤ i.val.choose 2 →
      2 * fiftyPotential i / i ≤ 297 ∧
      fiftyRequired (2 * fiftyPotential i / i) ≤ fiftyPotential i - fiftyPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
