module

public import GraphMinor.Thomason.ThirtySixTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 36-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem thirtySixPotential_monotone : Monotone thirtySixPotential :=
  truncatedTable_monotone thirtySixPotentialValues 386 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem thirtySixRequired_monotone : Monotone thirtySixRequired :=
  truncatedTable_monotone thirtySixRequiredValues 192 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem thirtySixPotential_boundary : (33 : ℕ).choose 2 < thirtySixPotential 33 := by decide

/-- Minimum degree 193 supplies the potential throughout the first reduction. -/
theorem thirtySixPotential_threshold (n : ℕ) (hn : 193 < n) (hn' : n ≤ 386) :
    2 * thirtySixPotential n ≤ 193 * n := by
  have h : ∀ i : Fin 387, 193 < i.val → 2 * thirtySixPotential i ≤ 193 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem thirtySixPotential_bounds (n : ℕ) (hn : 33 < n) (hn' : n ≤ 386)
    (he : thirtySixPotential n ≤ n.choose 2) :
    2 * thirtySixPotential n / n ≤ 192 ∧
      thirtySixRequired (2 * thirtySixPotential n / n) ≤ thirtySixPotential n - thirtySixPotential (n - 1) := by
  have h : ∀ i : Fin 387, 33 < i.val → thirtySixPotential i ≤ i.val.choose 2 →
      2 * thirtySixPotential i / i ≤ 192 ∧
      thirtySixRequired (2 * thirtySixPotential i / i) ≤ thirtySixPotential i - thirtySixPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
