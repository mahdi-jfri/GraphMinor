module

public import GraphMinor.GM01.QuantitativeBounds
import Lean.Elab.Tactic.Omega

/-!
# Scalar estimates for the exponential base

Graph Minors I, (3.6)(ii), page 53, needs `β` to absorb the separator
bound and the length of the larger comb. Bound `θ` by `2^θ` to bound
`θ^(2θ)` by `2^(2θ²)`. Since `θ ≥ 6`, the exponent `θ^6` exceeds
`2θ² + 3`. Thus `β` is at least eight times `θ^(2θ)`, which gives
the required additive margin.
-/

public section

namespace GraphMinor.GM01

/-- The exponential base on page 53 is at least sixteen. -/
theorem beta_pow_ge_sixteen {θ : ℕ} (hθ : 6 ≤ θ) : 16 ≤ 2 ^ (θ ^ 6) := by
  have hθ6 : θ ≤ θ ^ 6 := Nat.le_self_pow (by decide) θ
  change 2 ^ 4 ≤ 2 ^ (θ ^ 6)
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The input margin needed for GM01 (3.6)(ii), page 53. -/
theorem beta_pow_separator_margin {θ : ℕ} (hθ : 6 ≤ θ) :
    θ ^ 2 + 2 + 4 * θ ^ (2 * θ) ≤ 2 ^ (θ ^ 6) := by
  have hθpos : 0 < θ := by omega
  have hθ2 : 6 ≤ θ ^ 2 := hθ.trans (Nat.le_self_pow (by decide) θ)
  have hθ4 : 3 ≤ θ ^ 4 := (show 3 ≤ θ by omega).trans (Nat.le_self_pow (by decide) θ)
  have hprod := Nat.mul_le_mul_left (θ ^ 2) hθ4
  have hθ6 : 2 * θ ^ 2 + 3 ≤ θ ^ 6 := by
    have heq : θ ^ 6 = θ ^ 2 * θ ^ 4 := Nat.pow_add θ 2 4
    rw [heq]
    omega
  have hνExp : θ ^ (2 * θ) ≤ 2 ^ (2 * θ ^ 2) := by
    calc
      θ ^ (2 * θ) ≤ (2 ^ θ) ^ (2 * θ) :=
        Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))) _
      _ = 2 ^ (2 * θ ^ 2) := by
        rw [← Nat.pow_mul]
        congr 1
        rw [Nat.pow_two]
        ac_rfl
  have hExp : 2 ^ (2 * θ ^ 2) * 8 ≤ 2 ^ (θ ^ 6) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hθ6
    rw [Nat.pow_add] at h
    exact h
  have hν8 := (Nat.mul_le_mul_right 8 hνExp).trans hExp
  have hθ2ν : θ ^ 2 ≤ θ ^ (2 * θ) := Nat.pow_le_pow_right hθpos (by omega)
  omega

/-- The concrete base `β` has the input margin in GM01 (3.6)(ii). -/
theorem gm01Beta_separator_margin (lam : ℕ) :
    (gm01Theta lam) ^ 2 + 2 + 4 * (gm01Theta lam) ^ (2 * gm01Theta lam) ≤ gm01Beta lam :=
  beta_pow_separator_margin (gm01Theta_ge_six lam)

/-- The concrete exponential base is greater than one. -/
theorem gm01Beta_gt_one (lam : ℕ) : 1 < gm01Beta lam := by
  have h := beta_pow_ge_sixteen (gm01Theta_ge_six lam)
  change 16 ≤ gm01Beta lam at h
  omega

end GraphMinor.GM01
