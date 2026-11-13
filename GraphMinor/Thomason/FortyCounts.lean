module

public import GraphMinor.Thomason.FortyTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import GraphMinor.Thomason.FortyCounts0
import GraphMinor.Thomason.FortyCounts1
import GraphMinor.Thomason.FortyCounts2
import GraphMinor.Thomason.FortyCounts3
import GraphMinor.Thomason.FortyCounts4
import GraphMinor.Thomason.FortyCounts5
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 40-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem forty_counts_checked : ∀ N : Fin 222,
    N.val ≤ fortyRequired N ∨
      (N.val ≤ 2 * fortyRequired N ∧
       (∀ j : Fin 37, 0 < fortySelection N j ∧
        chargedBudget (fortyCharge N) j ≤ 2 * fortyRequired N - N.val + 1 ∧
        chargedBudget (fortyCharge N) j < N.val ∧
        starCandidateCost (N.val - chargedBudget (fortyCharge N) j)
          (N.val - fortyRequired N - 1) (fortySelection N j) (fortyEdge N j) ≤ fortyCharge N j ∧
        fortyUncovered N j ≤ N.val - fortyRequired N - 1 ∧
        (N.val * (N.val - fortyRequired N - 1).choose (fortySelection N j) <
          (starCandidateCount (N.val - chargedBudget (fortyCharge N) j) (N.val - fortyRequired N - 1) (fortySelection N j) (fortyEdge N j) -
            ∑ i ∈ range j, (fortyUncovered N i).choose (fortySelection N j)) *
            (fortyUncovered N j + 1) ∨
          (N.val - fortyRequired N - 1 ≤ fortyUncovered N j ∧
            (∑ i ∈ range j, (fortyUncovered N i).choose (fortySelection N j)) <
              starCandidateCount (N.val - chargedBudget (fortyCharge N) j) (N.val - fortyRequired N - 1) (fortySelection N j) (fortyEdge N j)))) ∧
       chargedBudget (fortyCharge N) 37 ≤ 2 * fortyRequired N - N.val + 1 ∧
       N.val - fortyRequired N - 1 + chargedBudget (fortyCharge N) 37 < N.val) := by
  intro N
  by_cases h0 : N.val < 40
  · exact forty_counts_checked_0 N (Nat.zero_le _) h0
  · by_cases h1 : N.val < 80
    · exact forty_counts_checked_1 N (by omega) h1
    · by_cases h2 : N.val < 120
      · exact forty_counts_checked_2 N (by omega) h2
      · by_cases h3 : N.val < 160
        · exact forty_counts_checked_3 N (by omega) h3
        · by_cases h4 : N.val < 200
          · exact forty_counts_checked_4 N (by omega) h4
          · exact forty_counts_checked_5 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem forty_degree_certificate (N : ℕ) (hN : N ≤ 221) :
    N ≤ fortyRequired N ∨
      (N ≤ 2 * fortyRequired N ∧
       (∀ j < 37, 0 < fortySelection N j ∧
        chargedBudget (fortyCharge N) j ≤ 2 * fortyRequired N - N + 1 ∧
        chargedBudget (fortyCharge N) j < N ∧
        starCandidateCost (N - chargedBudget (fortyCharge N) j)
          (N - fortyRequired N - 1) (fortySelection N j) (fortyEdge N j) ≤ fortyCharge N j ∧
        fortyUncovered N j ≤ N - fortyRequired N - 1 ∧
        (N * (N - fortyRequired N - 1).choose (fortySelection N j) <
          (starCandidateCount (N - chargedBudget (fortyCharge N) j) (N - fortyRequired N - 1) (fortySelection N j) (fortyEdge N j) -
            ∑ i ∈ range j, (fortyUncovered N i).choose (fortySelection N j)) *
            (fortyUncovered N j + 1) ∨
          (N - fortyRequired N - 1 ≤ fortyUncovered N j ∧
            (∑ i ∈ range j, (fortyUncovered N i).choose (fortySelection N j)) <
              starCandidateCount (N - chargedBudget (fortyCharge N) j) (N - fortyRequired N - 1) (fortySelection N j) (fortyEdge N j)))) ∧
       chargedBudget (fortyCharge N) 37 ≤ 2 * fortyRequired N - N + 1 ∧
       N - fortyRequired N - 1 + chargedBudget (fortyCharge N) 37 < N) := by
  rcases forty_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
