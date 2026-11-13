module

public import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
# The Euler calculation in VIII (18.2)

After choosing one component of the cut surface, substitute the Euler
characteristic and cuff count of the other components. The resulting
balance is exactly the difference between the two connected surface
measures. The displayed inequality on page 286 prints `e' - c` where this
substitution requires `c' - c`. A nonseparating circle on the torus gives
`e = e' = 0` and `c = 0`, so the printed strict inequality would read
`0 > 0`; its new cuff count is `c' = 2`. We use the corrected cuff count.
-/

public section

namespace GraphMinor.GM08

/-- The substitution in the proof of VIII (18.2), page 286. Here the selected
component has Euler characteristic `e₁` and `c₁` cuffs. The remaining `k₂`
components have `a₂` handles, `b₂` crosscaps, and `c₂` cuffs. The correction
from `e' - c` to `c' - c` is explained in the module docstring. -/
theorem cut_euler_balance (e e' e₁ : ℤ) (c c' c₁ c₂ a₂ b₂ k₂ : ℕ)
    (hEuler : e' = e₁ + 2 * (k₂ : ℤ) - 2 * (a₂ : ℤ) - (b₂ : ℤ) - (c₂ : ℤ))
    (hCuffs : c' = c₁ + c₂) :
    2 * (e' - e) + (c' : ℤ) - (c : ℤ) + 4 * (a₂ : ℤ) +
        2 * (b₂ : ℤ) + (c₂ : ℤ) - 4 * (k₂ : ℤ) =
      (2 * e₁ + (c₁ : ℤ)) - (2 * e + (c : ℤ)) := by
  omega

/-- The corrected strict inequality in VIII (18.2) is equivalent to the
strict decrease of the selected component's measure `4 - 2e - c`. -/
theorem cut_euler_inequality_iff (e e' e₁ : ℤ) (c c' c₁ c₂ a₂ b₂ k₂ : ℕ)
    (hEuler : e' = e₁ + 2 * (k₂ : ℤ) - 2 * (a₂ : ℤ) - (b₂ : ℤ) - (c₂ : ℤ))
    (hCuffs : c' = c₁ + c₂) :
    (4 * (k₂ : ℤ) < 2 * (e' - e) + (c' : ℤ) - (c : ℤ) +
      4 * (a₂ : ℤ) + 2 * (b₂ : ℤ) + (c₂ : ℤ)) ↔
      4 - 2 * e₁ - (c₁ : ℤ) < 4 - 2 * e - (c : ℤ) := by
  have h := cut_euler_balance e e' e₁ c c' c₁ c₂ a₂ b₂ k₂ hEuler hCuffs
  omega

end GraphMinor.GM08
