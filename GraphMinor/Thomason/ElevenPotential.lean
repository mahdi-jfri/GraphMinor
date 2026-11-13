module

public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# An integer potential for the eleven-vertex density case

The threshold `(n²+240n-2880)/12`, rounded down, is below the edge count
supplied by minimum degree fifty-four over the relevant order range.
Its successive differences give the three degree bounds needed by the
reduced-graph nine-vertex clique construction.
-/

@[expose] public section
namespace GraphMinor.Thomason

/-- The rounded integer edge threshold for the eleven-vertex case. -/
def elevenPotential (n : ℕ) : ℕ := (n * n + 240 * n - 2880) / 12

/-- The threshold is monotone, including below its positive range. -/
theorem elevenPotential_monotone : Monotone elevenPotential := by
  intro a b hab
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.add_le_add (Nat.mul_le_mul hab hab) (Nat.mul_le_mul_left 240 hab)

/-- At the cutoff the threshold is larger than a complete graph. -/
theorem elevenPotential_boundary : (24 : ℕ).choose 2 < elevenPotential 24 := by decide

/-- In the possible minimal-minor orders, the potential supplies all
bounds used by the reduced-graph criterion. Each inequality is a finite
integer comparison checked by the kernel. -/
theorem elevenPotential_bounds (n : ℕ) (hn : 24 < n) (hn' : n ≤ 108)
    (he : elevenPotential n ≤ n.choose 2) :
    let D := elevenPotential n - elevenPotential (n - 1)
    let N := 2 * elevenPotential n / n
    25 ≤ D ∧ N ≤ 53 ∧ N + 17 ≤ 2 * D ∧ 2 * N + 4 ≤ 3 * D ∧ N ≤ D + 15 := by
  interval_cases n <;> revert he <;> decide

/-- Minimum degree fifty-four supplies at least this threshold when
the graph has at most ninety-six vertices. -/
theorem elevenPotential_le_twenty_seven_mul (n : ℕ) (hn : n ≤ 108) :
    elevenPotential n ≤ 27 * n := by
  interval_cases n <;> decide

end GraphMinor.Thomason
