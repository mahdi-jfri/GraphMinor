module

public import GraphMinor.GM01.QuantitativeBaseEstimates
import Lean.Elab.Tactic.Omega

/-!
# The first three inequalities for the rooted induction

Graph Minors I, (3.6)(i)–(iii), page 53, follow from the identity
initial iterate, the separator input margin, and the quadratic lower
bound for `β^δ` when `δ ≥ 2`. Strict monotonicity and additive growth
of the preceding iterate carry these scalar bounds to `p` and `q`.
-/

public section

namespace GraphMinor.GM01

/-- At positive height, expose the last exponential in the definition
of `p` on page 53. -/
theorem pathWidthBound_positive_eq (lam γ δ : ℕ) (hγ : 0 < γ) :
    pathWidthBound lam γ δ = widthIteration (gm01Beta lam) (γ - 1) ((gm01Beta lam) ^ δ) := by
  cases γ with
  | zero => omega
  | succ γ => rfl

/-- Graph Minors I, (3.6)(i), page 53. -/
theorem pathWidthBound_zero (lam δ : ℕ) : δ - 2 ≤ pathWidthBound lam 0 δ := Nat.sub_le _ _

/-- Graph Minors I, (3.6)(ii), page 53. The scalar separator margin
is retained by the additive growth of the preceding iterate. -/
theorem forkWidthBound_separator (lam γ δ : ℕ) :
    (gm01Theta lam) ^ 2 +
      pathWidthBound lam (γ - 1) (2 + 4 * (gm01Theta lam) ^ (2 * gm01Theta lam) + 2 * δ) ≤
      forkWidthBound lam γ δ := by
  have hβ := gm01Beta_gt_one lam
  have hmargin := gm01Beta_separator_margin lam
  have hInput : (gm01Theta lam) ^ 2 +
      (2 + 4 * (gm01Theta lam) ^ (2 * gm01Theta lam) + 2 * δ) ≤ gm01Beta lam + 2 * δ := by omega
  exact (widthIteration_add_le hβ (γ - 1) _ ((gm01Theta lam) ^ 2)).trans
    ((widthIteration_strictMono hβ (γ - 1)).monotone hInput)

private theorem beta_add_eight_le_pow {β δ : ℕ} (hβ : 16 ≤ β) (hδ : 2 ≤ δ) :
    β + 8 ≤ β ^ δ := by
  have hp := Nat.pow_le_pow_right (by omega : 0 < β) hδ
  have hm := Nat.mul_le_mul_left β (show 2 ≤ β by omega)
  rw [Nat.pow_two] at hp
  omega

/-- Graph Minors I, (3.6)(iii), page 53. -/
theorem pathWidthBound_ge_fork_four (lam : ℕ) {γ δ : ℕ} (hγ : 1 ≤ γ) (hδ : 2 ≤ δ) :
    forkWidthBound lam γ 4 ≤ pathWidthBound lam γ δ := by
  rw [pathWidthBound_positive_eq lam γ δ (by omega)]
  have hβ := beta_pow_ge_sixteen (gm01Theta_ge_six lam)
  change 16 ≤ gm01Beta lam at hβ
  have hp := beta_add_eight_le_pow hβ hδ
  exact (widthIteration_strictMono (gm01Beta_gt_one lam) (γ - 1)).monotone hp

end GraphMinor.GM01
