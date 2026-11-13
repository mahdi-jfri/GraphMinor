module

public import GraphMinor.Thomason.EighteenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 18-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem eighteenPotential_monotone : Monotone eighteenPotential :=
  truncatedTable_monotone eighteenPotentialValues 196 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem eighteenRequired_monotone : Monotone eighteenRequired :=
  truncatedTable_monotone eighteenRequiredValues 92 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem eighteenPotential_boundary : (15 : ℕ).choose 2 < eighteenPotential 15 := by decide

/-- Minimum degree 98 supplies the potential throughout the first reduction. -/
theorem eighteenPotential_threshold (n : ℕ) (hn : 98 < n) (hn' : n ≤ 196) :
    2 * eighteenPotential n ≤ 98 * n := by
  have h : ∀ i : Fin 197, 98 < i.val → 2 * eighteenPotential i ≤ 98 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem eighteenPotential_bounds (n : ℕ) (hn : 15 < n) (hn' : n ≤ 196)
    (he : eighteenPotential n ≤ n.choose 2) :
    2 * eighteenPotential n / n ≤ 92 ∧
      eighteenRequired (2 * eighteenPotential n / n) ≤ eighteenPotential n - eighteenPotential (n - 1) := by
  have h : ∀ i : Fin 197, 15 < i.val → eighteenPotential i ≤ i.val.choose 2 →
      2 * eighteenPotential i / i ≤ 92 ∧
      eighteenRequired (2 * eighteenPotential i / i) ≤ eighteenPotential i - eighteenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
