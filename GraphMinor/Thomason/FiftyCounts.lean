module

public import GraphMinor.Thomason.FiftyTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import GraphMinor.Thomason.FiftyCounts0
import GraphMinor.Thomason.FiftyCounts1
import GraphMinor.Thomason.FiftyCounts2
import GraphMinor.Thomason.FiftyCounts3
import GraphMinor.Thomason.FiftyCounts4
import GraphMinor.Thomason.FiftyCounts5
import GraphMinor.Thomason.FiftyCounts6
import GraphMinor.Thomason.FiftyCounts7
import GraphMinor.Thomason.FiftyCounts8
import GraphMinor.Thomason.FiftyCounts9
import GraphMinor.Thomason.FiftyCounts10
import GraphMinor.Thomason.FiftyCounts11
import GraphMinor.Thomason.FiftyCounts12
import GraphMinor.Thomason.FiftyCounts13
import GraphMinor.Thomason.FiftyCounts14
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 50-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem fifty_counts_checked : ∀ N : Fin 298,
    N.val ≤ fiftyRequired N ∨
      (N.val ≤ 2 * fiftyRequired N ∧
       (∀ j : Fin 47, 0 < fiftySelection N j ∧
        chargedBudget (fiftyCharge N) j ≤ 2 * fiftyRequired N - N.val + 1 ∧
        chargedBudget (fiftyCharge N) j < N.val ∧
        starCandidateCost (N.val - chargedBudget (fiftyCharge N) j)
          (N.val - fiftyRequired N - 1) (fiftySelection N j) (fiftyEdge N j) ≤ fiftyCharge N j ∧
        fiftyUncovered N j ≤ N.val - fiftyRequired N - 1 ∧
        (N.val * (N.val - fiftyRequired N - 1).choose (fiftySelection N j) <
          (starCandidateCount (N.val - chargedBudget (fiftyCharge N) j) (N.val - fiftyRequired N - 1) (fiftySelection N j) (fiftyEdge N j) -
            ∑ i ∈ range j, (fiftyUncovered N i).choose (fiftySelection N j)) *
            (fiftyUncovered N j + 1) ∨
          (N.val - fiftyRequired N - 1 ≤ fiftyUncovered N j ∧
            (∑ i ∈ range j, (fiftyUncovered N i).choose (fiftySelection N j)) <
              starCandidateCount (N.val - chargedBudget (fiftyCharge N) j) (N.val - fiftyRequired N - 1) (fiftySelection N j) (fiftyEdge N j)))) ∧
       chargedBudget (fiftyCharge N) 47 ≤ 2 * fiftyRequired N - N.val + 1 ∧
       N.val - fiftyRequired N - 1 + chargedBudget (fiftyCharge N) 47 < N.val) := by
  intro N
  by_cases h0 : N.val < 20
  · exact fifty_counts_checked_0 N (Nat.zero_le _) h0
  · by_cases h1 : N.val < 40
    · exact fifty_counts_checked_1 N (by omega) h1
    · by_cases h2 : N.val < 60
      · exact fifty_counts_checked_2 N (by omega) h2
      · by_cases h3 : N.val < 80
        · exact fifty_counts_checked_3 N (by omega) h3
        · by_cases h4 : N.val < 100
          · exact fifty_counts_checked_4 N (by omega) h4
          · by_cases h5 : N.val < 120
            · exact fifty_counts_checked_5 N (by omega) h5
            · by_cases h6 : N.val < 140
              · exact fifty_counts_checked_6 N (by omega) h6
              · by_cases h7 : N.val < 160
                · exact fifty_counts_checked_7 N (by omega) h7
                · by_cases h8 : N.val < 180
                  · exact fifty_counts_checked_8 N (by omega) h8
                  · by_cases h9 : N.val < 200
                    · exact fifty_counts_checked_9 N (by omega) h9
                    · by_cases h10 : N.val < 220
                      · exact fifty_counts_checked_10 N (by omega) h10
                      · by_cases h11 : N.val < 240
                        · exact fifty_counts_checked_11 N (by omega) h11
                        · by_cases h12 : N.val < 260
                          · exact fifty_counts_checked_12 N (by omega) h12
                          · by_cases h13 : N.val < 280
                            · exact fifty_counts_checked_13 N (by omega) h13
                            · exact fifty_counts_checked_14 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem fifty_degree_certificate (N : ℕ) (hN : N ≤ 297) :
    N ≤ fiftyRequired N ∨
      (N ≤ 2 * fiftyRequired N ∧
       (∀ j < 47, 0 < fiftySelection N j ∧
        chargedBudget (fiftyCharge N) j ≤ 2 * fiftyRequired N - N + 1 ∧
        chargedBudget (fiftyCharge N) j < N ∧
        starCandidateCost (N - chargedBudget (fiftyCharge N) j)
          (N - fiftyRequired N - 1) (fiftySelection N j) (fiftyEdge N j) ≤ fiftyCharge N j ∧
        fiftyUncovered N j ≤ N - fiftyRequired N - 1 ∧
        (N * (N - fiftyRequired N - 1).choose (fiftySelection N j) <
          (starCandidateCount (N - chargedBudget (fiftyCharge N) j) (N - fiftyRequired N - 1) (fiftySelection N j) (fiftyEdge N j) -
            ∑ i ∈ range j, (fiftyUncovered N i).choose (fiftySelection N j)) *
            (fiftyUncovered N j + 1) ∨
          (N - fiftyRequired N - 1 ≤ fiftyUncovered N j ∧
            (∑ i ∈ range j, (fiftyUncovered N i).choose (fiftySelection N j)) <
              starCandidateCount (N - chargedBudget (fiftyCharge N) j) (N - fiftyRequired N - 1) (fiftySelection N j) (fiftyEdge N j)))) ∧
       chargedBudget (fiftyCharge N) 47 ≤ 2 * fiftyRequired N - N + 1 ∧
       N - fiftyRequired N - 1 + chargedBudget (fiftyCharge N) 47 < N) := by
  rcases fifty_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
