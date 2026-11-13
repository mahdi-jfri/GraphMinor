module

public import GraphMinor.Thomason.TwentyThreeTables
public import GraphMinor.Thomason.HubAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the twenty-three-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentyThree_counts_checked : ∀ N : Fin 131,
    N.val ≤ twentyThreeRequired N ∨
      (N.val ≤ 2 * twentyThreeRequired N ∧
       (∀ j : Fin 20, 0 < twentyThreeSelection N j ∧
        chargedBudget (twentyThreeCharge N) j ≤ 2 * twentyThreeRequired N - N.val + 1 ∧
        chargedBudget (twentyThreeCharge N) j < N.val ∧
        hubSelectionCost (N.val - chargedBudget (twentyThreeCharge N) j)
          (N.val - twentyThreeRequired N - 1) (twentyThreeSelection N j) ≤ twentyThreeCharge N j ∧
        twentyThreeUncovered N j ≤ N.val - twentyThreeRequired N - 1 ∧
        (N.val * (N.val - twentyThreeRequired N - 1).choose (twentyThreeSelection N j) <
          ((N.val - chargedBudget (twentyThreeCharge N) j).choose (twentyThreeSelection N j) -
            ∑ i ∈ range j, (twentyThreeUncovered N i).choose (twentyThreeSelection N j)) *
            (twentyThreeUncovered N j + 1) ∨
          (N.val - twentyThreeRequired N - 1 ≤ twentyThreeUncovered N j ∧
            (∑ i ∈ range j, (twentyThreeUncovered N i).choose (twentyThreeSelection N j)) <
              (N.val - chargedBudget (twentyThreeCharge N) j).choose (twentyThreeSelection N j)))) ∧
       chargedBudget (twentyThreeCharge N) 20 ≤ 2 * twentyThreeRequired N - N.val + 1 ∧
       N.val - twentyThreeRequired N - 1 + chargedBudget (twentyThreeCharge N) 20 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentyThree_degree_certificate (N : ℕ) (hN : N ≤ 130) :
    N ≤ twentyThreeRequired N ∨
      (N ≤ 2 * twentyThreeRequired N ∧
       (∀ j < 20, 0 < twentyThreeSelection N j ∧
        chargedBudget (twentyThreeCharge N) j ≤ 2 * twentyThreeRequired N - N + 1 ∧
        chargedBudget (twentyThreeCharge N) j < N ∧
        hubSelectionCost (N - chargedBudget (twentyThreeCharge N) j)
          (N - twentyThreeRequired N - 1) (twentyThreeSelection N j) ≤ twentyThreeCharge N j ∧
        twentyThreeUncovered N j ≤ N - twentyThreeRequired N - 1 ∧
        (N * (N - twentyThreeRequired N - 1).choose (twentyThreeSelection N j) <
          ((N - chargedBudget (twentyThreeCharge N) j).choose (twentyThreeSelection N j) -
            ∑ i ∈ range j, (twentyThreeUncovered N i).choose (twentyThreeSelection N j)) *
            (twentyThreeUncovered N j + 1) ∨
          (N - twentyThreeRequired N - 1 ≤ twentyThreeUncovered N j ∧
            (∑ i ∈ range j, (twentyThreeUncovered N i).choose (twentyThreeSelection N j)) <
              (N - chargedBudget (twentyThreeCharge N) j).choose (twentyThreeSelection N j)))) ∧
       chargedBudget (twentyThreeCharge N) 20 ≤ 2 * twentyThreeRequired N - N + 1 ∧
       N - twentyThreeRequired N - 1 + chargedBudget (twentyThreeCharge N) 20 < N) := by
  rcases twentyThree_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
