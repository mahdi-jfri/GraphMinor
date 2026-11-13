module

public import GraphMinor.Thomason.FortySevenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.NumericTableChain
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 47-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem fortySevenPotential_monotone : Monotone fortySevenPotential :=
  truncatedTable_monotone_of_chain fortySevenPotentialValues 548 (by decide) (by decide)

/-- Global monotonicity of the required degrees. -/
theorem fortySevenRequired_monotone : Monotone fortySevenRequired :=
  truncatedTable_monotone_of_chain fortySevenRequiredValues 273 (by decide) (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem fortySevenPotential_boundary : (44 : ℕ).choose 2 < fortySevenPotential 44 := by decide

/-- Minimum degree 274 supplies the potential throughout the first reduction. -/
theorem fortySevenPotential_threshold (n : ℕ) (hn : 274 < n) (hn' : n ≤ 548) :
    2 * fortySevenPotential n ≤ 274 * n := by
  have h : ∀ i : Fin 549, 274 < i.val → 2 * fortySevenPotential i ≤ 274 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem fortySevenPotential_bounds (n : ℕ) (hn : 44 < n) (hn' : n ≤ 548)
    (he : fortySevenPotential n ≤ n.choose 2) :
    2 * fortySevenPotential n / n ≤ 273 ∧
      fortySevenRequired (2 * fortySevenPotential n / n) ≤ fortySevenPotential n - fortySevenPotential (n - 1) := by
  have h : ∀ i : Fin 549, 44 < i.val → fortySevenPotential i ≤ i.val.choose 2 →
      2 * fortySevenPotential i / i ≤ 273 ∧
      fortySevenRequired (2 * fortySevenPotential i / i) ≤ fortySevenPotential i - fortySevenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
