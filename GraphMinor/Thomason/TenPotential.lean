module

public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# An integer potential for the ten-vertex density case

The threshold `(n²+200n-2000)/12`, rounded down, is below the edge count
supplied by minimum degree forty-eight over the relevant order range.
Its successive differences give the three degree bounds needed by the
reduced-graph eight-vertex clique construction.
-/

@[expose] public section
namespace GraphMinor.Thomason

/-- The rounded integer edge threshold for the ten-vertex case. -/
def tenPotential (n : ℕ) : ℕ := (n * n + 200 * n - 2000) / 12

/-- The threshold is monotone, including below its positive range. -/
theorem tenPotential_monotone : Monotone tenPotential := by
  intro a b hab
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.add_le_add (Nat.mul_le_mul hab hab) (Nat.mul_le_mul_left 200 hab)

/-- At the cutoff the threshold is larger than a complete graph. -/
theorem tenPotential_boundary : (18 : ℕ).choose 2 < tenPotential 18 := by decide

/-- In the possible minimal-minor orders, the potential supplies all
bounds used by the reduced-graph criterion. Each inequality is a finite
integer comparison checked by the kernel. -/
theorem tenPotential_bounds (n : ℕ) (hn : 18 < n) (hn' : n ≤ 96)
    (he : tenPotential n ≤ n.choose 2) :
    let D := tenPotential n - tenPotential (n - 1)
    let N := 2 * tenPotential n / n
    21 ≤ D ∧ N ≤ 45 ∧ N + 14 ≤ 2 * D ∧ 2 * N + 3 ≤ 3 * D ∧ N ≤ D + 13 := by
  interval_cases n <;> revert he <;> decide

/-- Minimum degree forty-eight supplies at least this threshold when
the graph has at most ninety-six vertices. -/
theorem tenPotential_le_twenty_four_mul (n : ℕ) (hn : n ≤ 96) :
    tenPotential n ≤ 24 * n := by
  interval_cases n <;> decide

end GraphMinor.Thomason
