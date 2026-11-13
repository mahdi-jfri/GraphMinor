module

public import GraphMinor.Thomason.FourteenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 14-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem fourteenPotential_monotone : Monotone fourteenPotential :=
  truncatedTable_monotone fourteenPotentialValues 146 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem fourteenRequired_monotone : Monotone fourteenRequired :=
  truncatedTable_monotone fourteenRequiredValues 60 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem fourteenPotential_boundary : (11 : ℕ).choose 2 < fourteenPotential 11 := by decide

/-- Minimum degree 73 supplies the potential throughout the first reduction. -/
theorem fourteenPotential_threshold (n : ℕ) (hn : 73 < n) (hn' : n ≤ 146) :
    2 * fourteenPotential n ≤ 73 * n := by
  have h : ∀ i : Fin 147, 73 < i.val → 2 * fourteenPotential i ≤ 73 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem fourteenPotential_bounds (n : ℕ) (hn : 11 < n) (hn' : n ≤ 146)
    (he : fourteenPotential n ≤ n.choose 2) :
    2 * fourteenPotential n / n ≤ 60 ∧
      fourteenRequired (2 * fourteenPotential n / n) ≤ fourteenPotential n - fourteenPotential (n - 1) := by
  have h : ∀ i : Fin 147, 11 < i.val → fourteenPotential i ≤ i.val.choose 2 →
      2 * fourteenPotential i / i ≤ 60 ∧
      fourteenRequired (2 * fourteenPotential i / i) ≤ fourteenPotential i - fourteenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
