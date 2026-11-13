module

public import GraphMinor.Thomason.FortySevenTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import GraphMinor.Thomason.FortySevenCounts0
import GraphMinor.Thomason.FortySevenCounts1
import GraphMinor.Thomason.FortySevenCounts2
import GraphMinor.Thomason.FortySevenCounts3
import GraphMinor.Thomason.FortySevenCounts4
import GraphMinor.Thomason.FortySevenCounts5
import GraphMinor.Thomason.FortySevenCounts6
import GraphMinor.Thomason.FortySevenCounts7
import GraphMinor.Thomason.FortySevenCounts8
import GraphMinor.Thomason.FortySevenCounts9
import GraphMinor.Thomason.FortySevenCounts10
import GraphMinor.Thomason.FortySevenCounts11
import GraphMinor.Thomason.FortySevenCounts12
import GraphMinor.Thomason.FortySevenCounts13
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 47-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem fortySeven_counts_checked : ∀ N : Fin 274,
    N.val ≤ fortySevenRequired N ∨
      (N.val ≤ 2 * fortySevenRequired N ∧
       (∀ j : Fin 44, 0 < fortySevenSelection N j ∧
        chargedBudget (fortySevenCharge N) j ≤ 2 * fortySevenRequired N - N.val + 1 ∧
        chargedBudget (fortySevenCharge N) j < N.val ∧
        starCandidateCost (N.val - chargedBudget (fortySevenCharge N) j)
          (N.val - fortySevenRequired N - 1) (fortySevenSelection N j) (fortySevenEdge N j) ≤ fortySevenCharge N j ∧
        fortySevenUncovered N j ≤ N.val - fortySevenRequired N - 1 ∧
        (N.val * (N.val - fortySevenRequired N - 1).choose (fortySevenSelection N j) <
          (starCandidateCount (N.val - chargedBudget (fortySevenCharge N) j) (N.val - fortySevenRequired N - 1) (fortySevenSelection N j) (fortySevenEdge N j) -
            ∑ i ∈ range j, (fortySevenUncovered N i).choose (fortySevenSelection N j)) *
            (fortySevenUncovered N j + 1) ∨
          (N.val - fortySevenRequired N - 1 ≤ fortySevenUncovered N j ∧
            (∑ i ∈ range j, (fortySevenUncovered N i).choose (fortySevenSelection N j)) <
              starCandidateCount (N.val - chargedBudget (fortySevenCharge N) j) (N.val - fortySevenRequired N - 1) (fortySevenSelection N j) (fortySevenEdge N j)))) ∧
       chargedBudget (fortySevenCharge N) 44 ≤ 2 * fortySevenRequired N - N.val + 1 ∧
       N.val - fortySevenRequired N - 1 + chargedBudget (fortySevenCharge N) 44 < N.val) := by
  intro N
  by_cases h0 : N.val < 20
  · exact fortySeven_counts_checked_0 N (Nat.zero_le _) h0
  · by_cases h1 : N.val < 40
    · exact fortySeven_counts_checked_1 N (by omega) h1
    · by_cases h2 : N.val < 60
      · exact fortySeven_counts_checked_2 N (by omega) h2
      · by_cases h3 : N.val < 80
        · exact fortySeven_counts_checked_3 N (by omega) h3
        · by_cases h4 : N.val < 100
          · exact fortySeven_counts_checked_4 N (by omega) h4
          · by_cases h5 : N.val < 120
            · exact fortySeven_counts_checked_5 N (by omega) h5
            · by_cases h6 : N.val < 140
              · exact fortySeven_counts_checked_6 N (by omega) h6
              · by_cases h7 : N.val < 160
                · exact fortySeven_counts_checked_7 N (by omega) h7
                · by_cases h8 : N.val < 180
                  · exact fortySeven_counts_checked_8 N (by omega) h8
                  · by_cases h9 : N.val < 200
                    · exact fortySeven_counts_checked_9 N (by omega) h9
                    · by_cases h10 : N.val < 220
                      · exact fortySeven_counts_checked_10 N (by omega) h10
                      · by_cases h11 : N.val < 240
                        · exact fortySeven_counts_checked_11 N (by omega) h11
                        · by_cases h12 : N.val < 260
                          · exact fortySeven_counts_checked_12 N (by omega) h12
                          · exact fortySeven_counts_checked_13 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem fortySeven_degree_certificate (N : ℕ) (hN : N ≤ 273) :
    N ≤ fortySevenRequired N ∨
      (N ≤ 2 * fortySevenRequired N ∧
       (∀ j < 44, 0 < fortySevenSelection N j ∧
        chargedBudget (fortySevenCharge N) j ≤ 2 * fortySevenRequired N - N + 1 ∧
        chargedBudget (fortySevenCharge N) j < N ∧
        starCandidateCost (N - chargedBudget (fortySevenCharge N) j)
          (N - fortySevenRequired N - 1) (fortySevenSelection N j) (fortySevenEdge N j) ≤ fortySevenCharge N j ∧
        fortySevenUncovered N j ≤ N - fortySevenRequired N - 1 ∧
        (N * (N - fortySevenRequired N - 1).choose (fortySevenSelection N j) <
          (starCandidateCount (N - chargedBudget (fortySevenCharge N) j) (N - fortySevenRequired N - 1) (fortySevenSelection N j) (fortySevenEdge N j) -
            ∑ i ∈ range j, (fortySevenUncovered N i).choose (fortySevenSelection N j)) *
            (fortySevenUncovered N j + 1) ∨
          (N - fortySevenRequired N - 1 ≤ fortySevenUncovered N j ∧
            (∑ i ∈ range j, (fortySevenUncovered N i).choose (fortySevenSelection N j)) <
              starCandidateCount (N - chargedBudget (fortySevenCharge N) j) (N - fortySevenRequired N - 1) (fortySevenSelection N j) (fortySevenEdge N j)))) ∧
       chargedBudget (fortySevenCharge N) 44 ≤ 2 * fortySevenRequired N - N + 1 ∧
       N - fortySevenRequired N - 1 + chargedBudget (fortySevenCharge N) 44 < N) := by
  rcases fortySeven_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
