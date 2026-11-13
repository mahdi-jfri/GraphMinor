module

public import GraphMinor.Thomason.FifteenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 15-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem fifteenPotential_monotone : Monotone fifteenPotential :=
  truncatedTable_monotone fifteenPotentialValues 158 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem fifteenRequired_monotone : Monotone fifteenRequired :=
  truncatedTable_monotone fifteenRequiredValues 68 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem fifteenPotential_boundary : (12 : ℕ).choose 2 < fifteenPotential 12 := by decide

/-- Minimum degree 79 supplies the potential throughout the first reduction. -/
theorem fifteenPotential_threshold (n : ℕ) (hn : 79 < n) (hn' : n ≤ 158) :
    2 * fifteenPotential n ≤ 79 * n := by
  have h : ∀ i : Fin 159, 79 < i.val → 2 * fifteenPotential i ≤ 79 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem fifteenPotential_bounds (n : ℕ) (hn : 12 < n) (hn' : n ≤ 158)
    (he : fifteenPotential n ≤ n.choose 2) :
    2 * fifteenPotential n / n ≤ 68 ∧
      fifteenRequired (2 * fifteenPotential n / n) ≤ fifteenPotential n - fifteenPotential (n - 1) := by
  have h : ∀ i : Fin 159, 12 < i.val → fifteenPotential i ≤ i.val.choose 2 →
      2 * fifteenPotential i / i ≤ 68 ∧
      fifteenRequired (2 * fifteenPotential i / i) ≤ fifteenPotential i - fifteenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
