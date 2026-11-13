module

public import GraphMinor.Thomason.TwentyTwoTables
public import GraphMinor.Thomason.HubBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the twenty-two-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

private theorem twentyTwo_counts_checked : ∀ N : Fin 123,
    N.val ≤ twentyTwoRequired N ∨
      (N.val ≤ 2 * twentyTwoRequired N ∧
       (∀ j : Fin 19, 0 < twentyTwoSelection N j ∧
        chargedBudget (twentyTwoCharge N) j ≤ 2 * twentyTwoRequired N - N.val + 1 ∧
        chargedBudget (twentyTwoCharge N) j < N.val ∧
        hubSelectionCost (N.val - chargedBudget (twentyTwoCharge N) j)
          (N.val - twentyTwoRequired N - 1) (twentyTwoSelection N j) ≤ twentyTwoCharge N j ∧
        ↑j * (N.val - twentyTwoRequired N - 1).choose (twentyTwoSelection N j) <
          (N.val - chargedBudget (twentyTwoCharge N) j).choose (twentyTwoSelection N j)) ∧
       chargedBudget (twentyTwoCharge N) 19 ≤ 2 * twentyTwoRequired N - N.val + 1 ∧
       N.val - twentyTwoRequired N - 1 + chargedBudget (twentyTwoCharge N) 19 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentyTwo_degree_certificate (N : ℕ) (hN : N ≤ 122) :
    N ≤ twentyTwoRequired N ∨
      (N ≤ 2 * twentyTwoRequired N ∧
       (∀ j < 19, 0 < twentyTwoSelection N j ∧
        chargedBudget (twentyTwoCharge N) j ≤ 2 * twentyTwoRequired N - N + 1 ∧
        chargedBudget (twentyTwoCharge N) j < N ∧
        hubSelectionCost (N - chargedBudget (twentyTwoCharge N) j)
          (N - twentyTwoRequired N - 1) (twentyTwoSelection N j) ≤ twentyTwoCharge N j ∧
        ↑j * (N - twentyTwoRequired N - 1).choose (twentyTwoSelection N j) <
          (N - chargedBudget (twentyTwoCharge N) j).choose (twentyTwoSelection N j)) ∧
       chargedBudget (twentyTwoCharge N) 19 ≤ 2 * twentyTwoRequired N - N + 1 ∧
       N - twentyTwoRequired N - 1 + chargedBudget (twentyTwoCharge N) 19 < N) := by
  rcases twentyTwo_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
