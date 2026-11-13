module

public import GraphMinor.Thomason.SeventeenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 17-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem seventeenPotential_monotone : Monotone seventeenPotential :=
  truncatedTable_monotone seventeenPotentialValues 184 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem seventeenRequired_monotone : Monotone seventeenRequired :=
  truncatedTable_monotone seventeenRequiredValues 84 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem seventeenPotential_boundary : (14 : ℕ).choose 2 < seventeenPotential 14 := by decide

/-- Minimum degree 92 supplies the potential throughout the first reduction. -/
theorem seventeenPotential_threshold (n : ℕ) (hn : 92 < n) (hn' : n ≤ 184) :
    2 * seventeenPotential n ≤ 92 * n := by
  have h : ∀ i : Fin 185, 92 < i.val → 2 * seventeenPotential i ≤ 92 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem seventeenPotential_bounds (n : ℕ) (hn : 14 < n) (hn' : n ≤ 184)
    (he : seventeenPotential n ≤ n.choose 2) :
    2 * seventeenPotential n / n ≤ 84 ∧
      seventeenRequired (2 * seventeenPotential n / n) ≤ seventeenPotential n - seventeenPotential (n - 1) := by
  have h : ∀ i : Fin 185, 14 < i.val → seventeenPotential i ≤ i.val.choose 2 →
      2 * seventeenPotential i / i ≤ 84 ∧
      seventeenRequired (2 * seventeenPotential i / i) ≤ seventeenPotential i - seventeenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
