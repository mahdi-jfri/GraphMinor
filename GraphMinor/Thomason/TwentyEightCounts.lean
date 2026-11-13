module

public import GraphMinor.Thomason.TwentyEightTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 28-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentyEight_counts_checked : ∀ N : Fin 150,
    N.val ≤ twentyEightRequired N ∨
      (N.val ≤ 2 * twentyEightRequired N ∧
       (∀ j : Fin 25, (twentyEightEdge N j = true → twentyEightSelection N j = 2) ∧
        0 < twentyEightSelection N j ∧
        chargedBudget (twentyEightCharge N) j ≤ 2 * twentyEightRequired N - N.val + 1 ∧
        chargedBudget (twentyEightCharge N) j < N.val ∧
        candidateCost (N.val - chargedBudget (twentyEightCharge N) j)
          (N.val - twentyEightRequired N - 1) (twentyEightSelection N j) (twentyEightEdge N j) ≤ twentyEightCharge N j ∧
        twentyEightUncovered N j ≤ N.val - twentyEightRequired N - 1 ∧
        (N.val * (N.val - twentyEightRequired N - 1).choose (twentyEightSelection N j) <
          (candidateCount (N.val - chargedBudget (twentyEightCharge N) j) (N.val - twentyEightRequired N - 1) (twentyEightSelection N j) (twentyEightEdge N j) -
            ∑ i ∈ range j, (twentyEightUncovered N i).choose (twentyEightSelection N j)) *
            (twentyEightUncovered N j + 1) ∨
          (N.val - twentyEightRequired N - 1 ≤ twentyEightUncovered N j ∧
            (∑ i ∈ range j, (twentyEightUncovered N i).choose (twentyEightSelection N j)) <
              candidateCount (N.val - chargedBudget (twentyEightCharge N) j) (N.val - twentyEightRequired N - 1) (twentyEightSelection N j) (twentyEightEdge N j)))) ∧
       chargedBudget (twentyEightCharge N) 25 ≤ 2 * twentyEightRequired N - N.val + 1 ∧
       N.val - twentyEightRequired N - 1 + chargedBudget (twentyEightCharge N) 25 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentyEight_degree_certificate (N : ℕ) (hN : N ≤ 149) :
    N ≤ twentyEightRequired N ∨
      (N ≤ 2 * twentyEightRequired N ∧
       (∀ j < 25, (twentyEightEdge N j = true → twentyEightSelection N j = 2) ∧
        0 < twentyEightSelection N j ∧
        chargedBudget (twentyEightCharge N) j ≤ 2 * twentyEightRequired N - N + 1 ∧
        chargedBudget (twentyEightCharge N) j < N ∧
        candidateCost (N - chargedBudget (twentyEightCharge N) j)
          (N - twentyEightRequired N - 1) (twentyEightSelection N j) (twentyEightEdge N j) ≤ twentyEightCharge N j ∧
        twentyEightUncovered N j ≤ N - twentyEightRequired N - 1 ∧
        (N * (N - twentyEightRequired N - 1).choose (twentyEightSelection N j) <
          (candidateCount (N - chargedBudget (twentyEightCharge N) j) (N - twentyEightRequired N - 1) (twentyEightSelection N j) (twentyEightEdge N j) -
            ∑ i ∈ range j, (twentyEightUncovered N i).choose (twentyEightSelection N j)) *
            (twentyEightUncovered N j + 1) ∨
          (N - twentyEightRequired N - 1 ≤ twentyEightUncovered N j ∧
            (∑ i ∈ range j, (twentyEightUncovered N i).choose (twentyEightSelection N j)) <
              candidateCount (N - chargedBudget (twentyEightCharge N) j) (N - twentyEightRequired N - 1) (twentyEightSelection N j) (twentyEightEdge N j)))) ∧
       chargedBudget (twentyEightCharge N) 25 ≤ 2 * twentyEightRequired N - N + 1 ∧
       N - twentyEightRequired N - 1 + chargedBudget (twentyEightCharge N) 25 < N) := by
  rcases twentyEight_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
