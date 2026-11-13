module

public import GraphMinor.Thomason.ThirtyFourTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import GraphMinor.Thomason.ThirtyFourCounts0
import GraphMinor.Thomason.ThirtyFourCounts1
import GraphMinor.Thomason.ThirtyFourCounts2
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 34-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem thirtyFour_counts_checked : ∀ N : Fin 184,
    N.val ≤ thirtyFourRequired N ∨
      (N.val ≤ 2 * thirtyFourRequired N ∧
       (∀ j : Fin 31, (thirtyFourEdge N j = true → thirtyFourSelection N j = 2) ∧
        0 < thirtyFourSelection N j ∧
        chargedBudget (thirtyFourCharge N) j ≤ 2 * thirtyFourRequired N - N.val + 1 ∧
        chargedBudget (thirtyFourCharge N) j < N.val ∧
        candidateCost (N.val - chargedBudget (thirtyFourCharge N) j)
          (N.val - thirtyFourRequired N - 1) (thirtyFourSelection N j) (thirtyFourEdge N j) ≤ thirtyFourCharge N j ∧
        thirtyFourUncovered N j ≤ N.val - thirtyFourRequired N - 1 ∧
        (N.val * (N.val - thirtyFourRequired N - 1).choose (thirtyFourSelection N j) <
          (candidateCount (N.val - chargedBudget (thirtyFourCharge N) j) (N.val - thirtyFourRequired N - 1) (thirtyFourSelection N j) (thirtyFourEdge N j) -
            ∑ i ∈ range j, (thirtyFourUncovered N i).choose (thirtyFourSelection N j)) *
            (thirtyFourUncovered N j + 1) ∨
          (N.val - thirtyFourRequired N - 1 ≤ thirtyFourUncovered N j ∧
            (∑ i ∈ range j, (thirtyFourUncovered N i).choose (thirtyFourSelection N j)) <
              candidateCount (N.val - chargedBudget (thirtyFourCharge N) j) (N.val - thirtyFourRequired N - 1) (thirtyFourSelection N j) (thirtyFourEdge N j)))) ∧
       chargedBudget (thirtyFourCharge N) 31 ≤ 2 * thirtyFourRequired N - N.val + 1 ∧
       N.val - thirtyFourRequired N - 1 + chargedBudget (thirtyFourCharge N) 31 < N.val) := by
  intro N
  by_cases h₀ : N.val < 61
  · exact thirtyFour_counts_checked_0 N (Nat.zero_le _) h₀
  · by_cases h₁ : N.val < 122
    · exact thirtyFour_counts_checked_1 N (by omega) h₁
    · exact thirtyFour_counts_checked_2 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem thirtyFour_degree_certificate (N : ℕ) (hN : N ≤ 183) :
    N ≤ thirtyFourRequired N ∨
      (N ≤ 2 * thirtyFourRequired N ∧
       (∀ j < 31, (thirtyFourEdge N j = true → thirtyFourSelection N j = 2) ∧
        0 < thirtyFourSelection N j ∧
        chargedBudget (thirtyFourCharge N) j ≤ 2 * thirtyFourRequired N - N + 1 ∧
        chargedBudget (thirtyFourCharge N) j < N ∧
        candidateCost (N - chargedBudget (thirtyFourCharge N) j)
          (N - thirtyFourRequired N - 1) (thirtyFourSelection N j) (thirtyFourEdge N j) ≤ thirtyFourCharge N j ∧
        thirtyFourUncovered N j ≤ N - thirtyFourRequired N - 1 ∧
        (N * (N - thirtyFourRequired N - 1).choose (thirtyFourSelection N j) <
          (candidateCount (N - chargedBudget (thirtyFourCharge N) j) (N - thirtyFourRequired N - 1) (thirtyFourSelection N j) (thirtyFourEdge N j) -
            ∑ i ∈ range j, (thirtyFourUncovered N i).choose (thirtyFourSelection N j)) *
            (thirtyFourUncovered N j + 1) ∨
          (N - thirtyFourRequired N - 1 ≤ thirtyFourUncovered N j ∧
            (∑ i ∈ range j, (thirtyFourUncovered N i).choose (thirtyFourSelection N j)) <
              candidateCount (N - chargedBudget (thirtyFourCharge N) j) (N - thirtyFourRequired N - 1) (thirtyFourSelection N j) (thirtyFourEdge N j)))) ∧
       chargedBudget (thirtyFourCharge N) 31 ≤ 2 * thirtyFourRequired N - N + 1 ∧
       N - thirtyFourRequired N - 1 + chargedBudget (thirtyFourCharge N) 31 < N) := by
  rcases thirtyFour_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
