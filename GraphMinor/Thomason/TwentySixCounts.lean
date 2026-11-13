module

public import GraphMinor.Thomason.TwentySixTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 26-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentySix_counts_checked : ∀ N : Fin 136,
    N.val ≤ twentySixRequired N ∨
      (N.val ≤ 2 * twentySixRequired N ∧
       (∀ j : Fin 23, (twentySixEdge N j = true → twentySixSelection N j = 2) ∧
        0 < twentySixSelection N j ∧
        chargedBudget (twentySixCharge N) j ≤ 2 * twentySixRequired N - N.val + 1 ∧
        chargedBudget (twentySixCharge N) j < N.val ∧
        candidateCost (N.val - chargedBudget (twentySixCharge N) j)
          (N.val - twentySixRequired N - 1) (twentySixSelection N j) (twentySixEdge N j) ≤ twentySixCharge N j ∧
        twentySixUncovered N j ≤ N.val - twentySixRequired N - 1 ∧
        (N.val * (N.val - twentySixRequired N - 1).choose (twentySixSelection N j) <
          (candidateCount (N.val - chargedBudget (twentySixCharge N) j) (N.val - twentySixRequired N - 1) (twentySixSelection N j) (twentySixEdge N j) -
            ∑ i ∈ range j, (twentySixUncovered N i).choose (twentySixSelection N j)) *
            (twentySixUncovered N j + 1) ∨
          (N.val - twentySixRequired N - 1 ≤ twentySixUncovered N j ∧
            (∑ i ∈ range j, (twentySixUncovered N i).choose (twentySixSelection N j)) <
              candidateCount (N.val - chargedBudget (twentySixCharge N) j) (N.val - twentySixRequired N - 1) (twentySixSelection N j) (twentySixEdge N j)))) ∧
       chargedBudget (twentySixCharge N) 23 ≤ 2 * twentySixRequired N - N.val + 1 ∧
       N.val - twentySixRequired N - 1 + chargedBudget (twentySixCharge N) 23 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentySix_degree_certificate (N : ℕ) (hN : N ≤ 135) :
    N ≤ twentySixRequired N ∨
      (N ≤ 2 * twentySixRequired N ∧
       (∀ j < 23, (twentySixEdge N j = true → twentySixSelection N j = 2) ∧
        0 < twentySixSelection N j ∧
        chargedBudget (twentySixCharge N) j ≤ 2 * twentySixRequired N - N + 1 ∧
        chargedBudget (twentySixCharge N) j < N ∧
        candidateCost (N - chargedBudget (twentySixCharge N) j)
          (N - twentySixRequired N - 1) (twentySixSelection N j) (twentySixEdge N j) ≤ twentySixCharge N j ∧
        twentySixUncovered N j ≤ N - twentySixRequired N - 1 ∧
        (N * (N - twentySixRequired N - 1).choose (twentySixSelection N j) <
          (candidateCount (N - chargedBudget (twentySixCharge N) j) (N - twentySixRequired N - 1) (twentySixSelection N j) (twentySixEdge N j) -
            ∑ i ∈ range j, (twentySixUncovered N i).choose (twentySixSelection N j)) *
            (twentySixUncovered N j + 1) ∨
          (N - twentySixRequired N - 1 ≤ twentySixUncovered N j ∧
            (∑ i ∈ range j, (twentySixUncovered N i).choose (twentySixSelection N j)) <
              candidateCount (N - chargedBudget (twentySixCharge N) j) (N - twentySixRequired N - 1) (twentySixSelection N j) (twentySixEdge N j)))) ∧
       chargedBudget (twentySixCharge N) 23 ≤ 2 * twentySixRequired N - N + 1 ∧
       N - twentySixRequired N - 1 + chargedBudget (twentySixCharge N) 23 < N) := by
  rcases twentySix_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
