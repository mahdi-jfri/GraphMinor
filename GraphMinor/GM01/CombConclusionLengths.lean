module

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# The longer-comb count in the positive-height reduction

Graph Minors I, (4.14), page 59, retains the old early cells, the
middle cells of the layer subdivision, and the old late cells after
its boundary block. For a positive layer their total is exactly
`L + 2δ - 2`. At layer zero the same construction keeps more old
late cells, so its length is still greater than `L`.
-/

public section

namespace GraphMinor.GM01

/-- The retained length in GM01 (4.14), page 59, exceeds the maximal
old comb length. Natural subtraction handles the empty early piece
at the first two layers. -/
theorem comb_conclusion_length_exceeds {ν δ L m i q : ℕ}
    (hν : 3 ≤ ν) (hδ : 2 ≤ δ) (hm : m = 2 + 4 * ν + 2 * δ)
    (hq : q + 1 = ν * (i + 1)) (hbound : 2 * (q + 1) ≤ L) :
    L < 2 * (ν * (i - 1)) + (m - 4) + (L - 2 * (q + 1)) := by
  by_cases hi : i = 0
  · subst i
    simp only [Nat.zero_add, Nat.mul_one, Nat.zero_sub, Nat.mul_zero] at hq ⊢
    omega
  · have hi' : i - 1 + 2 = i + 1 := by omega
    have hmul := congrArg (fun t ↦ ν * t) hi'
    rw [Nat.mul_add, Nat.mul_two] at hmul
    omega

end GraphMinor.GM01
