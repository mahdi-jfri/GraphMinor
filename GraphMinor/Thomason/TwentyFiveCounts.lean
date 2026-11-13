module

public import GraphMinor.Thomason.TwentyFiveTables
public import GraphMinor.Thomason.HubAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 25-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentyFive_counts_checked : ∀ N : Fin 144,
    N.val ≤ twentyFiveRequired N ∨
      (N.val ≤ 2 * twentyFiveRequired N ∧
       (∀ j : Fin 22, 0 < twentyFiveSelection N j ∧
        chargedBudget (twentyFiveCharge N) j ≤ 2 * twentyFiveRequired N - N.val + 1 ∧
        chargedBudget (twentyFiveCharge N) j < N.val ∧
        hubSelectionCost (N.val - chargedBudget (twentyFiveCharge N) j)
          (N.val - twentyFiveRequired N - 1) (twentyFiveSelection N j) ≤ twentyFiveCharge N j ∧
        twentyFiveUncovered N j ≤ N.val - twentyFiveRequired N - 1 ∧
        (N.val * (N.val - twentyFiveRequired N - 1).choose (twentyFiveSelection N j) <
          ((N.val - chargedBudget (twentyFiveCharge N) j).choose (twentyFiveSelection N j) -
            ∑ i ∈ range j, (twentyFiveUncovered N i).choose (twentyFiveSelection N j)) *
            (twentyFiveUncovered N j + 1) ∨
          (N.val - twentyFiveRequired N - 1 ≤ twentyFiveUncovered N j ∧
            (∑ i ∈ range j, (twentyFiveUncovered N i).choose (twentyFiveSelection N j)) <
              (N.val - chargedBudget (twentyFiveCharge N) j).choose (twentyFiveSelection N j)))) ∧
       chargedBudget (twentyFiveCharge N) 22 ≤ 2 * twentyFiveRequired N - N.val + 1 ∧
       N.val - twentyFiveRequired N - 1 + chargedBudget (twentyFiveCharge N) 22 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentyFive_degree_certificate (N : ℕ) (hN : N ≤ 143) :
    N ≤ twentyFiveRequired N ∨
      (N ≤ 2 * twentyFiveRequired N ∧
       (∀ j < 22, 0 < twentyFiveSelection N j ∧
        chargedBudget (twentyFiveCharge N) j ≤ 2 * twentyFiveRequired N - N + 1 ∧
        chargedBudget (twentyFiveCharge N) j < N ∧
        hubSelectionCost (N - chargedBudget (twentyFiveCharge N) j)
          (N - twentyFiveRequired N - 1) (twentyFiveSelection N j) ≤ twentyFiveCharge N j ∧
        twentyFiveUncovered N j ≤ N - twentyFiveRequired N - 1 ∧
        (N * (N - twentyFiveRequired N - 1).choose (twentyFiveSelection N j) <
          ((N - chargedBudget (twentyFiveCharge N) j).choose (twentyFiveSelection N j) -
            ∑ i ∈ range j, (twentyFiveUncovered N i).choose (twentyFiveSelection N j)) *
            (twentyFiveUncovered N j + 1) ∨
          (N - twentyFiveRequired N - 1 ≤ twentyFiveUncovered N j ∧
            (∑ i ∈ range j, (twentyFiveUncovered N i).choose (twentyFiveSelection N j)) <
              (N - chargedBudget (twentyFiveCharge N) j).choose (twentyFiveSelection N j)))) ∧
       chargedBudget (twentyFiveCharge N) 22 ≤ 2 * twentyFiveRequired N - N + 1 ∧
       N - twentyFiveRequired N - 1 + chargedBudget (twentyFiveCharge N) 22 < N) := by
  rcases twentyFive_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
