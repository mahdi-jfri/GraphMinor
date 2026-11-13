module

public import GraphMinor.GM01.QuantitativeBounds
public import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

/-!
# Parity and positivity of the separator parameters

Graph Minors I fixes an even `θ ≥ 6` in Section 2 and uses
`θ = max(6, 2^((λ+3)/2))` in Section 3. Both entries of that maximum
are even, since the exponent is positive. The power `ν = θ^(2θ)`
is at least `θ`, giving the positive block-window length used in
Part 2.
-/

public section

namespace GraphMinor.GM01

/-- The value of `θ` defined on page 53 satisfies the evenness
condition fixed on page 42 of GM01. -/
theorem gm01Theta_even (lam : ℕ) : Even (gm01Theta lam) := by
  have hp : Even (2 ^ ((lam + 3) / 2)) :=
    (show Even (2 : ℕ) from ⟨1, rfl⟩).pow_of_ne_zero (by omega)
  unfold gm01Theta
  rcases le_total 6 (2 ^ ((lam + 3) / 2)) with h | h
  · rw [max_eq_right h]
    exact hp
  · rw [max_eq_left h]
    exact ⟨3, rfl⟩

/-- The window size in Part 2, page 55, is at least three. -/
theorem theta_window_ge_three {θ : ℕ} (hθ : 6 ≤ θ) : 3 ≤ θ ^ (2 * θ) :=
  (show 3 ≤ θ by omega).trans (Nat.le_self_pow (by omega) θ)

end GraphMinor.GM01
