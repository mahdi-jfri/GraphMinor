module

public import GraphMinor.Thomason.TwentyFourTables
public import GraphMinor.Thomason.HubAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 24-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentyFour_counts_checked : ∀ N : Fin 136,
    N.val ≤ twentyFourRequired N ∨
      (N.val ≤ 2 * twentyFourRequired N ∧
       (∀ j : Fin 21, 0 < twentyFourSelection N j ∧
        chargedBudget (twentyFourCharge N) j ≤ 2 * twentyFourRequired N - N.val + 1 ∧
        chargedBudget (twentyFourCharge N) j < N.val ∧
        hubSelectionCost (N.val - chargedBudget (twentyFourCharge N) j)
          (N.val - twentyFourRequired N - 1) (twentyFourSelection N j) ≤ twentyFourCharge N j ∧
        twentyFourUncovered N j ≤ N.val - twentyFourRequired N - 1 ∧
        (N.val * (N.val - twentyFourRequired N - 1).choose (twentyFourSelection N j) <
          ((N.val - chargedBudget (twentyFourCharge N) j).choose (twentyFourSelection N j) -
            ∑ i ∈ range j, (twentyFourUncovered N i).choose (twentyFourSelection N j)) *
            (twentyFourUncovered N j + 1) ∨
          (N.val - twentyFourRequired N - 1 ≤ twentyFourUncovered N j ∧
            (∑ i ∈ range j, (twentyFourUncovered N i).choose (twentyFourSelection N j)) <
              (N.val - chargedBudget (twentyFourCharge N) j).choose (twentyFourSelection N j)))) ∧
       chargedBudget (twentyFourCharge N) 21 ≤ 2 * twentyFourRequired N - N.val + 1 ∧
       N.val - twentyFourRequired N - 1 + chargedBudget (twentyFourCharge N) 21 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentyFour_degree_certificate (N : ℕ) (hN : N ≤ 135) :
    N ≤ twentyFourRequired N ∨
      (N ≤ 2 * twentyFourRequired N ∧
       (∀ j < 21, 0 < twentyFourSelection N j ∧
        chargedBudget (twentyFourCharge N) j ≤ 2 * twentyFourRequired N - N + 1 ∧
        chargedBudget (twentyFourCharge N) j < N ∧
        hubSelectionCost (N - chargedBudget (twentyFourCharge N) j)
          (N - twentyFourRequired N - 1) (twentyFourSelection N j) ≤ twentyFourCharge N j ∧
        twentyFourUncovered N j ≤ N - twentyFourRequired N - 1 ∧
        (N * (N - twentyFourRequired N - 1).choose (twentyFourSelection N j) <
          ((N - chargedBudget (twentyFourCharge N) j).choose (twentyFourSelection N j) -
            ∑ i ∈ range j, (twentyFourUncovered N i).choose (twentyFourSelection N j)) *
            (twentyFourUncovered N j + 1) ∨
          (N - twentyFourRequired N - 1 ≤ twentyFourUncovered N j ∧
            (∑ i ∈ range j, (twentyFourUncovered N i).choose (twentyFourSelection N j)) <
              (N - chargedBudget (twentyFourCharge N) j).choose (twentyFourSelection N j)))) ∧
       chargedBudget (twentyFourCharge N) 21 ≤ 2 * twentyFourRequired N - N + 1 ∧
       N - twentyFourRequired N - 1 + chargedBudget (twentyFourCharge N) 21 < N) := by
  rcases twentyFour_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
