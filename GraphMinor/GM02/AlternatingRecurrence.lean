module

public import GraphMinor.GM02.QuarterRecurrence
import Mathlib.Tactic.Ring

/-!
# Combining the two running-time recurrences

II, page 317, substitutes the A1 time bound into the A2 time bound.
The result has one recursive term at three quarters of the vertex bound,
with multiplier the square of the original constant. Applying the proved
three-quarter recurrence estimate gives the paper's polynomial conclusion.
-/

public section
namespace GraphMinor.GM02

/-- Substitution of the two A1/A2 inequalities in Graph Minors II, page 317. -/
theorem alternating_recurrence_step (f₁ f₂ : ℕ → ℕ) (c d n : ℕ)
    (h₁ : f₁ n ≤ c * ((n + 1) ^ d + f₂ (3 * n / 4)))
    (h₂ : f₂ n ≤ c * ((n + 1) ^ d + f₁ n)) :
    f₂ n ≤ (c + c * c) * (n + 1) ^ d + c * c * f₂ (3 * n / 4) := by
  calc
    f₂ n ≤ c * ((n + 1) ^ d + f₁ n) := h₂
    _ ≤ c * ((n + 1) ^ d + c * ((n + 1) ^ d + f₂ (3 * n / 4))) :=
      Nat.mul_le_mul_left c (Nat.add_le_add_left h₁ _)
    _ = (c + c * c) * (n + 1) ^ d + c * c * f₂ (3 * n / 4) := by ring

/-- Polynomial growth from the alternating numerical recurrences in II,
page 317. Actual program running times must first satisfy both bounds. -/
theorem alternating_recurrence_polynomial (f₁ f₂ : ℕ → ℕ) (w c d : ℕ) (hw : 1 ≤ w)
    (hsmall : ∀ n ≤ 4 * w, f₂ n ≤ c)
    (h₁ : ∀ n, 4 * w < n → f₁ n ≤ c * ((n + 1) ^ d + f₂ (3 * n / 4)))
    (h₂ : ∀ n, 4 * w < n → f₂ n ≤ c * ((n + 1) ^ d + f₁ n)) :
    ∀ n, f₂ n ≤ (c + 2 * (c + c * c) + 1) * (n + 1) ^ (8 * (c * c) + d) := by
  exact quarter_recurrence_polynomial f₂ w (c + c * c) (c * c) d c hw hsmall
    (fun n hn => alternating_recurrence_step f₁ f₂ c d n (h₁ n hn) (h₂ n hn))

end GraphMinor.GM02
