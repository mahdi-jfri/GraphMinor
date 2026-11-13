module

public import GraphMinor.Thomason.SixteenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 16-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem sixteenPotential_monotone : Monotone sixteenPotential :=
  truncatedTable_monotone sixteenPotentialValues 170 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem sixteenRequired_monotone : Monotone sixteenRequired :=
  truncatedTable_monotone sixteenRequiredValues 76 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem sixteenPotential_boundary : (13 : ℕ).choose 2 < sixteenPotential 13 := by decide

/-- Minimum degree 85 supplies the potential throughout the first reduction. -/
theorem sixteenPotential_threshold (n : ℕ) (hn : 85 < n) (hn' : n ≤ 170) :
    2 * sixteenPotential n ≤ 85 * n := by
  have h : ∀ i : Fin 171, 85 < i.val → 2 * sixteenPotential i ≤ 85 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem sixteenPotential_bounds (n : ℕ) (hn : 13 < n) (hn' : n ≤ 170)
    (he : sixteenPotential n ≤ n.choose 2) :
    2 * sixteenPotential n / n ≤ 76 ∧
      sixteenRequired (2 * sixteenPotential n / n) ≤ sixteenPotential n - sixteenPotential (n - 1) := by
  have h : ∀ i : Fin 171, 13 < i.val → sixteenPotential i ≤ i.val.choose 2 →
      2 * sixteenPotential i / i ≤ 76 ∧
      sixteenRequired (2 * sixteenPotential i / i) ≤ sixteenPotential i - sixteenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
