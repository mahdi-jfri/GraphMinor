module

public import GraphMinor.Thomason.ThirtyTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import GraphMinor.Thomason.ThirtyCounts0
import GraphMinor.Thomason.ThirtyCounts1
import GraphMinor.Thomason.ThirtyCounts2
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 30-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem thirty_counts_checked : ∀ N : Fin 165,
    N.val ≤ thirtyRequired N ∨
      (N.val ≤ 2 * thirtyRequired N ∧
       (∀ j : Fin 27, (thirtyEdge N j = true → thirtySelection N j = 2) ∧
        0 < thirtySelection N j ∧
        chargedBudget (thirtyCharge N) j ≤ 2 * thirtyRequired N - N.val + 1 ∧
        chargedBudget (thirtyCharge N) j < N.val ∧
        candidateCost (N.val - chargedBudget (thirtyCharge N) j)
          (N.val - thirtyRequired N - 1) (thirtySelection N j) (thirtyEdge N j) ≤ thirtyCharge N j ∧
        thirtyUncovered N j ≤ N.val - thirtyRequired N - 1 ∧
        (N.val * (N.val - thirtyRequired N - 1).choose (thirtySelection N j) <
          (candidateCount (N.val - chargedBudget (thirtyCharge N) j) (N.val - thirtyRequired N - 1) (thirtySelection N j) (thirtyEdge N j) -
            ∑ i ∈ range j, (thirtyUncovered N i).choose (thirtySelection N j)) *
            (thirtyUncovered N j + 1) ∨
          (N.val - thirtyRequired N - 1 ≤ thirtyUncovered N j ∧
            (∑ i ∈ range j, (thirtyUncovered N i).choose (thirtySelection N j)) <
              candidateCount (N.val - chargedBudget (thirtyCharge N) j) (N.val - thirtyRequired N - 1) (thirtySelection N j) (thirtyEdge N j)))) ∧
       chargedBudget (thirtyCharge N) 27 ≤ 2 * thirtyRequired N - N.val + 1 ∧
       N.val - thirtyRequired N - 1 + chargedBudget (thirtyCharge N) 27 < N.val) := by
  intro N
  by_cases h₀ : N.val < 55
  · exact thirty_counts_checked_0 N (Nat.zero_le _) h₀
  · by_cases h₁ : N.val < 110
    · exact thirty_counts_checked_1 N (by omega) h₁
    · exact thirty_counts_checked_2 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem thirty_degree_certificate (N : ℕ) (hN : N ≤ 164) :
    N ≤ thirtyRequired N ∨
      (N ≤ 2 * thirtyRequired N ∧
       (∀ j < 27, (thirtyEdge N j = true → thirtySelection N j = 2) ∧
        0 < thirtySelection N j ∧
        chargedBudget (thirtyCharge N) j ≤ 2 * thirtyRequired N - N + 1 ∧
        chargedBudget (thirtyCharge N) j < N ∧
        candidateCost (N - chargedBudget (thirtyCharge N) j)
          (N - thirtyRequired N - 1) (thirtySelection N j) (thirtyEdge N j) ≤ thirtyCharge N j ∧
        thirtyUncovered N j ≤ N - thirtyRequired N - 1 ∧
        (N * (N - thirtyRequired N - 1).choose (thirtySelection N j) <
          (candidateCount (N - chargedBudget (thirtyCharge N) j) (N - thirtyRequired N - 1) (thirtySelection N j) (thirtyEdge N j) -
            ∑ i ∈ range j, (thirtyUncovered N i).choose (thirtySelection N j)) *
            (thirtyUncovered N j + 1) ∨
          (N - thirtyRequired N - 1 ≤ thirtyUncovered N j ∧
            (∑ i ∈ range j, (thirtyUncovered N i).choose (thirtySelection N j)) <
              candidateCount (N - chargedBudget (thirtyCharge N) j) (N - thirtyRequired N - 1) (thirtySelection N j) (thirtyEdge N j)))) ∧
       chargedBudget (thirtyCharge N) 27 ≤ 2 * thirtyRequired N - N + 1 ∧
       N - thirtyRequired N - 1 + chargedBudget (thirtyCharge N) 27 < N) := by
  rcases thirty_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
