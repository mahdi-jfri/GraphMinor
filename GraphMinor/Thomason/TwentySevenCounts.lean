module

public import GraphMinor.Thomason.TwentySevenTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 27-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem twentySeven_counts_checked : ∀ N : Fin 143,
    N.val ≤ twentySevenRequired N ∨
      (N.val ≤ 2 * twentySevenRequired N ∧
       (∀ j : Fin 24, (twentySevenEdge N j = true → twentySevenSelection N j = 2) ∧
        0 < twentySevenSelection N j ∧
        chargedBudget (twentySevenCharge N) j ≤ 2 * twentySevenRequired N - N.val + 1 ∧
        chargedBudget (twentySevenCharge N) j < N.val ∧
        candidateCost (N.val - chargedBudget (twentySevenCharge N) j)
          (N.val - twentySevenRequired N - 1) (twentySevenSelection N j) (twentySevenEdge N j) ≤ twentySevenCharge N j ∧
        twentySevenUncovered N j ≤ N.val - twentySevenRequired N - 1 ∧
        (N.val * (N.val - twentySevenRequired N - 1).choose (twentySevenSelection N j) <
          (candidateCount (N.val - chargedBudget (twentySevenCharge N) j) (N.val - twentySevenRequired N - 1) (twentySevenSelection N j) (twentySevenEdge N j) -
            ∑ i ∈ range j, (twentySevenUncovered N i).choose (twentySevenSelection N j)) *
            (twentySevenUncovered N j + 1) ∨
          (N.val - twentySevenRequired N - 1 ≤ twentySevenUncovered N j ∧
            (∑ i ∈ range j, (twentySevenUncovered N i).choose (twentySevenSelection N j)) <
              candidateCount (N.val - chargedBudget (twentySevenCharge N) j) (N.val - twentySevenRequired N - 1) (twentySevenSelection N j) (twentySevenEdge N j)))) ∧
       chargedBudget (twentySevenCharge N) 24 ≤ 2 * twentySevenRequired N - N.val + 1 ∧
       N.val - twentySevenRequired N - 1 + chargedBudget (twentySevenCharge N) 24 < N.val) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The numeric degree certificate with smaller connection charges. -/
theorem twentySeven_degree_certificate (N : ℕ) (hN : N ≤ 142) :
    N ≤ twentySevenRequired N ∨
      (N ≤ 2 * twentySevenRequired N ∧
       (∀ j < 24, (twentySevenEdge N j = true → twentySevenSelection N j = 2) ∧
        0 < twentySevenSelection N j ∧
        chargedBudget (twentySevenCharge N) j ≤ 2 * twentySevenRequired N - N + 1 ∧
        chargedBudget (twentySevenCharge N) j < N ∧
        candidateCost (N - chargedBudget (twentySevenCharge N) j)
          (N - twentySevenRequired N - 1) (twentySevenSelection N j) (twentySevenEdge N j) ≤ twentySevenCharge N j ∧
        twentySevenUncovered N j ≤ N - twentySevenRequired N - 1 ∧
        (N * (N - twentySevenRequired N - 1).choose (twentySevenSelection N j) <
          (candidateCount (N - chargedBudget (twentySevenCharge N) j) (N - twentySevenRequired N - 1) (twentySevenSelection N j) (twentySevenEdge N j) -
            ∑ i ∈ range j, (twentySevenUncovered N i).choose (twentySevenSelection N j)) *
            (twentySevenUncovered N j + 1) ∨
          (N - twentySevenRequired N - 1 ≤ twentySevenUncovered N j ∧
            (∑ i ∈ range j, (twentySevenUncovered N i).choose (twentySevenSelection N j)) <
              candidateCount (N - chargedBudget (twentySevenCharge N) j) (N - twentySevenRequired N - 1) (twentySevenSelection N j) (twentySevenEdge N j)))) ∧
       chargedBudget (twentySevenCharge N) 24 ≤ 2 * twentySevenRequired N - N + 1 ∧
       N - twentySevenRequired N - 1 + chargedBudget (twentySevenCharge N) 24 < N) := by
  rcases twentySeven_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
