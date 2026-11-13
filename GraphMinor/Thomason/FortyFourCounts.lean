module

public import GraphMinor.Thomason.FortyFourTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import GraphMinor.Thomason.FortyFourCounts0
import GraphMinor.Thomason.FortyFourCounts1
import GraphMinor.Thomason.FortyFourCounts2
import GraphMinor.Thomason.FortyFourCounts3
import GraphMinor.Thomason.FortyFourCounts4
import GraphMinor.Thomason.FortyFourCounts5
import GraphMinor.Thomason.FortyFourCounts6
import GraphMinor.Thomason.FortyFourCounts7
import GraphMinor.Thomason.FortyFourCounts8
import GraphMinor.Thomason.FortyFourCounts9
import GraphMinor.Thomason.FortyFourCounts10
import GraphMinor.Thomason.FortyFourCounts11
import GraphMinor.Thomason.FortyFourCounts12
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 44-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem fortyFour_counts_checked : ∀ N : Fin 252,
    N.val ≤ fortyFourRequired N ∨
      (N.val ≤ 2 * fortyFourRequired N ∧
       (∀ j : Fin 41, 0 < fortyFourSelection N j ∧
        chargedBudget (fortyFourCharge N) j ≤ 2 * fortyFourRequired N - N.val + 1 ∧
        chargedBudget (fortyFourCharge N) j < N.val ∧
        starCandidateCost (N.val - chargedBudget (fortyFourCharge N) j)
          (N.val - fortyFourRequired N - 1) (fortyFourSelection N j) (fortyFourEdge N j) ≤ fortyFourCharge N j ∧
        fortyFourUncovered N j ≤ N.val - fortyFourRequired N - 1 ∧
        (N.val * (N.val - fortyFourRequired N - 1).choose (fortyFourSelection N j) <
          (starCandidateCount (N.val - chargedBudget (fortyFourCharge N) j) (N.val - fortyFourRequired N - 1) (fortyFourSelection N j) (fortyFourEdge N j) -
            ∑ i ∈ range j, (fortyFourUncovered N i).choose (fortyFourSelection N j)) *
            (fortyFourUncovered N j + 1) ∨
          (N.val - fortyFourRequired N - 1 ≤ fortyFourUncovered N j ∧
            (∑ i ∈ range j, (fortyFourUncovered N i).choose (fortyFourSelection N j)) <
              starCandidateCount (N.val - chargedBudget (fortyFourCharge N) j) (N.val - fortyFourRequired N - 1) (fortyFourSelection N j) (fortyFourEdge N j)))) ∧
       chargedBudget (fortyFourCharge N) 41 ≤ 2 * fortyFourRequired N - N.val + 1 ∧
       N.val - fortyFourRequired N - 1 + chargedBudget (fortyFourCharge N) 41 < N.val) := by
  intro N
  by_cases h0 : N.val < 20
  · exact fortyFour_counts_checked_0 N (Nat.zero_le _) h0
  · by_cases h1 : N.val < 40
    · exact fortyFour_counts_checked_1 N (by omega) h1
    · by_cases h2 : N.val < 60
      · exact fortyFour_counts_checked_2 N (by omega) h2
      · by_cases h3 : N.val < 80
        · exact fortyFour_counts_checked_3 N (by omega) h3
        · by_cases h4 : N.val < 100
          · exact fortyFour_counts_checked_4 N (by omega) h4
          · by_cases h5 : N.val < 120
            · exact fortyFour_counts_checked_5 N (by omega) h5
            · by_cases h6 : N.val < 140
              · exact fortyFour_counts_checked_6 N (by omega) h6
              · by_cases h7 : N.val < 160
                · exact fortyFour_counts_checked_7 N (by omega) h7
                · by_cases h8 : N.val < 180
                  · exact fortyFour_counts_checked_8 N (by omega) h8
                  · by_cases h9 : N.val < 200
                    · exact fortyFour_counts_checked_9 N (by omega) h9
                    · by_cases h10 : N.val < 220
                      · exact fortyFour_counts_checked_10 N (by omega) h10
                      · by_cases h11 : N.val < 240
                        · exact fortyFour_counts_checked_11 N (by omega) h11
                        · exact fortyFour_counts_checked_12 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem fortyFour_degree_certificate (N : ℕ) (hN : N ≤ 251) :
    N ≤ fortyFourRequired N ∨
      (N ≤ 2 * fortyFourRequired N ∧
       (∀ j < 41, 0 < fortyFourSelection N j ∧
        chargedBudget (fortyFourCharge N) j ≤ 2 * fortyFourRequired N - N + 1 ∧
        chargedBudget (fortyFourCharge N) j < N ∧
        starCandidateCost (N - chargedBudget (fortyFourCharge N) j)
          (N - fortyFourRequired N - 1) (fortyFourSelection N j) (fortyFourEdge N j) ≤ fortyFourCharge N j ∧
        fortyFourUncovered N j ≤ N - fortyFourRequired N - 1 ∧
        (N * (N - fortyFourRequired N - 1).choose (fortyFourSelection N j) <
          (starCandidateCount (N - chargedBudget (fortyFourCharge N) j) (N - fortyFourRequired N - 1) (fortyFourSelection N j) (fortyFourEdge N j) -
            ∑ i ∈ range j, (fortyFourUncovered N i).choose (fortyFourSelection N j)) *
            (fortyFourUncovered N j + 1) ∨
          (N - fortyFourRequired N - 1 ≤ fortyFourUncovered N j ∧
            (∑ i ∈ range j, (fortyFourUncovered N i).choose (fortyFourSelection N j)) <
              starCandidateCount (N - chargedBudget (fortyFourCharge N) j) (N - fortyFourRequired N - 1) (fortyFourSelection N j) (fortyFourEdge N j)))) ∧
       chargedBudget (fortyFourCharge N) 41 ≤ 2 * fortyFourRequired N - N + 1 ∧
       N - fortyFourRequired N - 1 + chargedBudget (fortyFourCharge N) 41 < N) := by
  rcases fortyFour_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
