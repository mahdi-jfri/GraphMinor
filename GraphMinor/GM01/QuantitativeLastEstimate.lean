module

public import GraphMinor.GM01.QuantitativeFirstEstimates
public import GraphMinor.GM01.QuantitativeExponentMargins

/-!
# The last inequality for the rooted induction

For Graph Minors I, (3.6)(iv), page 53, both the preceding path input
and the larger fork input leave room for the `α` contribution before
the final exponential. The preceding iterate increases by at least
the increase in its input. Lift the two scalar margins separately,
then take their maximum. This proves the full printed inequality.
-/

public section

namespace GraphMinor.GM01

private theorem widthIteration_max_margin {β : ℕ} (hβ : 1 < β)
    (i A B C U : ℕ) (hB : A + B ≤ U) (hC : A + C ≤ U) :
    A + max (widthIteration β i B) (widthIteration β i C) ≤ widthIteration β i U := by
  have hFirst := (widthIteration_add_le hβ i B A).trans
    ((widthIteration_strictMono hβ i).monotone hB)
  have hSecond := (widthIteration_add_le hβ i C A).trans
    ((widthIteration_strictMono hβ i).monotone hC)
  by_cases h : widthIteration β i B ≤ widthIteration β i C
  · rw [max_eq_right h]
    exact hSecond
  · rw [max_eq_left (le_of_not_ge h)]
    exact hFirst

/-- Graph Minors I, (3.6)(iv), page 53. The two scalar margins are
lifted through the preceding iterate and then combined by their maximum. -/
theorem pathWidthBound_induction_margin {lam γ δ : ℕ} (hodd : Odd lam)
    (hγ : 1 ≤ γ) (hγlam : γ ≤ lam) (hδ : 3 ≤ δ) :
    (gm01Alpha lam) ^ (δ * 2 ^ γ) +
      max (pathWidthBound lam γ (δ - 1))
        (forkWidthBound lam γ (3 * (gm01Alpha lam) ^ (δ * 2 ^ γ) + 6)) ≤
      pathWidthBound lam γ δ := by
  let A := (gm01Alpha lam) ^ (δ * 2 ^ γ)
  have hA : A ≤ (gm01Beta lam) ^ (δ - 1) :=
    alpha_power_le_beta_previous (by omega : 2 ≤ δ) (gm01Theta_sq_height_margin hodd hγlam)
  have hβ := beta_pow_ge_sixteen (gm01Theta_ge_six lam)
  change 16 ≤ gm01Beta lam at hβ
  have hMargins := beta_power_input_margins hβ hδ hA
  change A + max (pathWidthBound lam γ (δ - 1)) (forkWidthBound lam γ (3 * A + 6)) ≤ _
  rw [pathWidthBound_positive_eq lam γ (δ - 1) (by omega),
    pathWidthBound_positive_eq lam γ δ (by omega)]
  change A + max (widthIteration (gm01Beta lam) (γ - 1) ((gm01Beta lam) ^ (δ - 1)))
    (widthIteration (gm01Beta lam) (γ - 1) (gm01Beta lam + 2 * (3 * A + 6))) ≤ _
  have hInput : gm01Beta lam + 2 * (3 * A + 6) = gm01Beta lam + 6 * A + 12 := by omega
  rw [hInput]
  exact widthIteration_max_margin (gm01Beta_gt_one lam) (γ - 1) A _ _ _ hMargins.1 hMargins.2

end GraphMinor.GM01
