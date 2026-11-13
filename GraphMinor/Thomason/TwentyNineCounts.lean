module

public import GraphMinor.Thomason.TwentyNineTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 29-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentyNine_counts_checked : ∀ N : Fin 158,
    N.val ≤ twentyNineRequired N ∨
      (N.val ≤ 2 * twentyNineRequired N ∧
       (∀ j : Fin 26, (twentyNineEdge N j = true → twentyNineSelection N j = 2) ∧
        0 < twentyNineSelection N j ∧
        chargedBudget (twentyNineCharge N) j ≤ 2 * twentyNineRequired N - N.val + 1 ∧
        chargedBudget (twentyNineCharge N) j < N.val ∧
        candidateCost (N.val - chargedBudget (twentyNineCharge N) j)
          (N.val - twentyNineRequired N - 1) (twentyNineSelection N j) (twentyNineEdge N j) ≤ twentyNineCharge N j ∧
        twentyNineUncovered N j ≤ N.val - twentyNineRequired N - 1 ∧
        (N.val * (N.val - twentyNineRequired N - 1).choose (twentyNineSelection N j) <
          (candidateCount (N.val - chargedBudget (twentyNineCharge N) j) (N.val - twentyNineRequired N - 1) (twentyNineSelection N j) (twentyNineEdge N j) -
            ∑ i ∈ range j, (twentyNineUncovered N i).choose (twentyNineSelection N j)) *
            (twentyNineUncovered N j + 1) ∨
          (N.val - twentyNineRequired N - 1 ≤ twentyNineUncovered N j ∧
            (∑ i ∈ range j, (twentyNineUncovered N i).choose (twentyNineSelection N j)) <
              candidateCount (N.val - chargedBudget (twentyNineCharge N) j) (N.val - twentyNineRequired N - 1) (twentyNineSelection N j) (twentyNineEdge N j)))) ∧
       chargedBudget (twentyNineCharge N) 26 ≤ 2 * twentyNineRequired N - N.val + 1 ∧
       N.val - twentyNineRequired N - 1 + chargedBudget (twentyNineCharge N) 26 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentyNine_degree_certificate (N : ℕ) (hN : N ≤ 157) :
    N ≤ twentyNineRequired N ∨
      (N ≤ 2 * twentyNineRequired N ∧
       (∀ j < 26, (twentyNineEdge N j = true → twentyNineSelection N j = 2) ∧
        0 < twentyNineSelection N j ∧
        chargedBudget (twentyNineCharge N) j ≤ 2 * twentyNineRequired N - N + 1 ∧
        chargedBudget (twentyNineCharge N) j < N ∧
        candidateCost (N - chargedBudget (twentyNineCharge N) j)
          (N - twentyNineRequired N - 1) (twentyNineSelection N j) (twentyNineEdge N j) ≤ twentyNineCharge N j ∧
        twentyNineUncovered N j ≤ N - twentyNineRequired N - 1 ∧
        (N * (N - twentyNineRequired N - 1).choose (twentyNineSelection N j) <
          (candidateCount (N - chargedBudget (twentyNineCharge N) j) (N - twentyNineRequired N - 1) (twentyNineSelection N j) (twentyNineEdge N j) -
            ∑ i ∈ range j, (twentyNineUncovered N i).choose (twentyNineSelection N j)) *
            (twentyNineUncovered N j + 1) ∨
          (N - twentyNineRequired N - 1 ≤ twentyNineUncovered N j ∧
            (∑ i ∈ range j, (twentyNineUncovered N i).choose (twentyNineSelection N j)) <
              candidateCount (N - chargedBudget (twentyNineCharge N) j) (N - twentyNineRequired N - 1) (twentyNineSelection N j) (twentyNineEdge N j)))) ∧
       chargedBudget (twentyNineCharge N) 26 ≤ 2 * twentyNineRequired N - N + 1 ∧
       N - twentyNineRequired N - 1 + chargedBudget (twentyNineCharge N) 26 < N) := by
  rcases twentyNine_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
