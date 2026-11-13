module

public import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# The length contradiction for the last layer

Graph Minors I, (4.10), page 58, constructs a comb of length
`2ν(T-1)+4ν+2δ`. The maximal choice of `T` makes this larger than `N`:
otherwise `T+1` would also satisfy the defining bound. We prove this
arithmetic directly from that maximality condition.
-/

public section

namespace GraphMinor.GM01

/-- The strict length inequality used in GM01 (4.10), page 58, derived
from the maximal choice of `T`, with `μ = 2+4ν+2δ`. -/
theorem comb_extension_length_exceeds_maxT (ν δ L T μ : ℕ) (hT : 1 ≤ T)
    (hμ : μ = 2 + 4 * ν + 2 * δ)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T) :
    L < 2 * (ν * (T - 1)) + (μ - 2) := by
  by_contra hnot
  have hsum : 2 * (ν * (T - 1)) + (μ - 2) ≤ L := Nat.le_of_not_gt hnot
  have hEq : T - 1 + 2 = T + 1 := by omega
  have hprod := congrArg (fun t : ℕ ↦ ν * t) hEq
  simp only [Nat.mul_add, Nat.mul_two] at hprod
  have hcan : 2 * ν * (T + 1) ≤ L - 2 * δ := by
    rw [Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
    omega
  have hbad := hmaxT (T + 1) hcan
  omega

end GraphMinor.GM01
