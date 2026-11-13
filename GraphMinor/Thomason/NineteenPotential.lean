module

public import GraphMinor.Thomason.NineteenTables
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 19-vertex integer potential

Monotonicity, the complete-graph cutoff, the initial edge bound, and
the required degrees are checked by finite integer computations in
the Lean kernel. No search procedure is an assumption of these results.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

/-- Global monotonicity of the potential. -/
theorem nineteenPotential_monotone : Monotone nineteenPotential :=
  truncatedTable_monotone nineteenPotentialValues 208 (by decide)

/-- Global monotonicity of the required degrees. -/
theorem nineteenRequired_monotone : Monotone nineteenRequired :=
  truncatedTable_monotone nineteenRequiredValues 99 (by decide)

/-- The complete graph at the cutoff lies below the threshold. -/
theorem nineteenPotential_boundary : (16 : ℕ).choose 2 < nineteenPotential 16 := by decide

/-- Minimum degree 104 supplies the potential throughout the first reduction. -/
theorem nineteenPotential_threshold (n : ℕ) (hn : 104 < n) (hn' : n ≤ 208) :
    2 * nineteenPotential n ≤ 104 * n := by
  have h : ∀ i : Fin 209, 104 < i.val → 2 * nineteenPotential i ≤ 104 * i := by decide
  exact h ⟨n, by omega⟩ hn

/-- The potential gives the tabulated order and degree bounds. -/
theorem nineteenPotential_bounds (n : ℕ) (hn : 16 < n) (hn' : n ≤ 208)
    (he : nineteenPotential n ≤ n.choose 2) :
    2 * nineteenPotential n / n ≤ 99 ∧
      nineteenRequired (2 * nineteenPotential n / n) ≤ nineteenPotential n - nineteenPotential (n - 1) := by
  have h : ∀ i : Fin 209, 16 < i.val → nineteenPotential i ≤ i.val.choose 2 →
      2 * nineteenPotential i / i ≤ 99 ∧
      nineteenRequired (2 * nineteenPotential i / i) ≤ nineteenPotential i - nineteenPotential (i - 1) := by
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide
  exact h ⟨n, by omega⟩ hn he

end GraphMinor.Thomason
