module

public import GraphMinor.Thomason.TwelveTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the twelve-vertex integer potential

Check monotonicity of the potential and the required degree table,
the complete-graph cutoff, the initial edge bound, and the degree
threshold at every possible minimal-minor order. These are finite
integer checks performed by the Lean kernel.
-/

public section
namespace GraphMinor.Thomason

/-- The twelve-vertex potential is monotone on all natural orders. -/
theorem twelvePotential_monotone : Monotone twelvePotential :=
  truncatedTable_monotone twelvePotentialValues 120 (by decide)

/-- The required-degree table is monotone on all natural orders. -/
theorem twelveRequired_monotone : Monotone twelveRequired :=
  truncatedTable_monotone twelveRequiredValues 46 (by decide)

/-- The cutoff at nine vertices excludes the complete graph. -/
theorem twelvePotential_boundary : (9 : ℕ).choose 2 < twelvePotential 9 := by decide

/-- Minimum degree sixty supplies the threshold throughout the first
reduced graph's order range. -/
theorem twelvePotential_threshold (n : ℕ) (hn : 60 < n) (hn' : n ≤ 120) :
    2 * twelvePotential n ≤ 60 * n := by
  have h : ∀ i : Fin 121, 60 < i.val → 2 * twelvePotential i ≤ 60 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- Every possible minimal-minor order gives a neighbourhood of order
at most forty-six and the required degree from the table. -/
theorem twelvePotential_bounds (n : ℕ) (hn : 9 < n) (hn' : n ≤ 120)
    (he : twelvePotential n ≤ n.choose 2) :
    2 * twelvePotential n / n ≤ 46 ∧
      twelveRequired (2 * twelvePotential n / n) ≤ twelvePotential n - twelvePotential (n - 1) := by
  have h : ∀ i : Fin 121, 9 < i.val → twelvePotential i ≤ i.val.choose 2 →
      2 * twelvePotential i / i ≤ 46 ∧
      twelveRequired (2 * twelvePotential i / i) ≤ twelvePotential i - twelvePotential (i - 1) := by
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
