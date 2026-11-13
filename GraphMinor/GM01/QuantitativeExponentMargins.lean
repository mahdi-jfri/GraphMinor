module

public import GraphMinor.GM01.QuantitativeBaseEstimates
public import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

/-!
# The exponent margin in the last numerical inequality

Graph Minors I, (3.6)(iv), page 53, compares the contribution from
`α` with a preceding power of `β`. The odd height parameter and the
definition of `θ` give `2·2^γ ≤ θ²`. This bounds
`α^(δ·2^γ)` by `β^(δ−1)`. The base is at least sixteen, so its next
power absorbs both the preceding power and the larger fork input,
with the required additive margin.
-/

public section

namespace GraphMinor.GM01

/-- The parameter `θ` controls all induction heights in GM01
(3.6)(iv), page 53. Oddness makes the exponent division exact. -/
theorem gm01Theta_sq_height_margin {lam γ : ℕ} (hodd : Odd lam) (hγ : γ ≤ lam) :
    2 * 2 ^ γ ≤ (gm01Theta lam) ^ 2 := by
  have hθ : 2 ^ ((lam + 3) / 2) ≤ gm01Theta lam := le_max_right _ _
  have hp := Nat.pow_le_pow_left hθ 2
  rw [← Nat.pow_mul] at hp
  have hmod := Nat.odd_iff.mp hodd
  have heq : ((lam + 3) / 2) * 2 = lam + 3 := by omega
  rw [heq] at hp
  calc
    2 * 2 ^ γ = 2 ^ (γ + 1) := by
      rw [Nat.pow_add, Nat.pow_one]
      exact Nat.mul_comm _ _
    _ ≤ 2 ^ (lam + 3) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ (gm01Theta lam) ^ 2 := hp

/-- The `α` contribution fits in the preceding `β` power, as used in
GM01 (3.6)(iv), page 53. -/
theorem alpha_power_le_beta_previous {θ δ g : ℕ} (hδ : 2 ≤ δ) (hg : 2 * g ≤ θ ^ 2) :
    (2 ^ (θ ^ 4)) ^ (δ * g) ≤ (2 ^ (θ ^ 6)) ^ (δ - 1) := by
  have hd : δ ≤ 2 * (δ - 1) := by omega
  have hInput : δ * g ≤ θ ^ 2 * (δ - 1) := by
    calc
      δ * g ≤ (2 * (δ - 1)) * g := Nat.mul_le_mul_right g hd
      _ = (2 * g) * (δ - 1) := by ac_rfl
      _ ≤ θ ^ 2 * (δ - 1) := Nat.mul_le_mul_right (δ - 1) hg
  have hExp := Nat.mul_le_mul_left (θ ^ 4) hInput
  have hθ6 : θ ^ 6 = θ ^ 4 * θ ^ 2 := Nat.pow_add θ 4 2
  have hExp' : θ ^ 4 * (δ * g) ≤ θ ^ 6 * (δ - 1) := by
    rw [hθ6, Nat.mul_assoc]
    exact hExp
  calc
    (2 ^ (θ ^ 4)) ^ (δ * g) = 2 ^ (θ ^ 4 * (δ * g)) := (Nat.pow_mul _ _ _).symm
    _ ≤ 2 ^ (θ ^ 6 * (δ - 1)) := Nat.pow_le_pow_right (by decide) hExp'
    _ = (2 ^ (θ ^ 6)) ^ (δ - 1) := Nat.pow_mul _ _ _

/-- The two scalar margins lifted by the preceding iterate in GM01
(3.6)(iv), page 53. -/
theorem beta_power_input_margins {β δ A : ℕ} (hβ : 16 ≤ β) (hδ : 3 ≤ δ)
    (hA : A ≤ β ^ (δ - 1)) :
    A + β ^ (δ - 1) ≤ β ^ δ ∧ A + (β + 6 * A + 12) ≤ β ^ δ := by
  let B := β ^ (δ - 1)
  have hB : β ≤ B := by
    have h := Nat.pow_le_pow_right (by omega : 0 < β) (show 1 ≤ δ - 1 by omega)
    simpa only [Nat.pow_one] using h
  have hPower : β ^ δ = β * B := by
    have h := Nat.pow_succ β (δ - 1)
    change β ^ (δ - 1 + 1) = β ^ (δ - 1) * β at h
    rw [show δ - 1 + 1 = δ by omega] at h
    exact h.trans (Nat.mul_comm _ _)
  have hMul := Nat.mul_le_mul_right B (show 9 ≤ β by omega)
  change A ≤ B at hA
  constructor
  · rw [hPower]
    change A + B ≤ β * B
    omega
  · rw [hPower]
    omega

end GraphMinor.GM01
