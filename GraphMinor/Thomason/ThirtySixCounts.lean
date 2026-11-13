module

public import GraphMinor.Thomason.ThirtySixTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import GraphMinor.Thomason.ThirtySixCounts0
import GraphMinor.Thomason.ThirtySixCounts1
import GraphMinor.Thomason.ThirtySixCounts2
import GraphMinor.Thomason.ThirtySixCounts3
import GraphMinor.Thomason.ThirtySixCounts4
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 36-vertex central-vertex charges

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

private theorem thirtySix_counts_checked : ∀ N : Fin 193,
    N.val ≤ thirtySixRequired N ∨
      (N.val ≤ 2 * thirtySixRequired N ∧
       (∀ j : Fin 33, 0 < thirtySixSelection N j ∧
        chargedBudget (thirtySixCharge N) j ≤ 2 * thirtySixRequired N - N.val + 1 ∧
        chargedBudget (thirtySixCharge N) j < N.val ∧
        starCandidateCost (N.val - chargedBudget (thirtySixCharge N) j)
          (N.val - thirtySixRequired N - 1) (thirtySixSelection N j) (thirtySixEdge N j) ≤ thirtySixCharge N j ∧
        thirtySixUncovered N j ≤ N.val - thirtySixRequired N - 1 ∧
        (N.val * (N.val - thirtySixRequired N - 1).choose (thirtySixSelection N j) <
          (starCandidateCount (N.val - chargedBudget (thirtySixCharge N) j) (N.val - thirtySixRequired N - 1) (thirtySixSelection N j) (thirtySixEdge N j) -
            ∑ i ∈ range j, (thirtySixUncovered N i).choose (thirtySixSelection N j)) *
            (thirtySixUncovered N j + 1) ∨
          (N.val - thirtySixRequired N - 1 ≤ thirtySixUncovered N j ∧
            (∑ i ∈ range j, (thirtySixUncovered N i).choose (thirtySixSelection N j)) <
              starCandidateCount (N.val - chargedBudget (thirtySixCharge N) j) (N.val - thirtySixRequired N - 1) (thirtySixSelection N j) (thirtySixEdge N j)))) ∧
       chargedBudget (thirtySixCharge N) 33 ≤ 2 * thirtySixRequired N - N.val + 1 ∧
       N.val - thirtySixRequired N - 1 + chargedBudget (thirtySixCharge N) 33 < N.val) := by
  intro N
  by_cases h0 : N.val < 40
  · exact thirtySix_counts_checked_0 N (Nat.zero_le _) h0
  · by_cases h1 : N.val < 80
    · exact thirtySix_counts_checked_1 N (by omega) h1
    · by_cases h2 : N.val < 120
      · exact thirtySix_counts_checked_2 N (by omega) h2
      · by_cases h3 : N.val < 160
        · exact thirtySix_counts_checked_3 N (by omega) h3
        · exact thirtySix_counts_checked_4 N (by omega) N.isLt

/-- The numeric degree certificate with smaller connection charges. -/
theorem thirtySix_degree_certificate (N : ℕ) (hN : N ≤ 192) :
    N ≤ thirtySixRequired N ∨
      (N ≤ 2 * thirtySixRequired N ∧
       (∀ j < 33, 0 < thirtySixSelection N j ∧
        chargedBudget (thirtySixCharge N) j ≤ 2 * thirtySixRequired N - N + 1 ∧
        chargedBudget (thirtySixCharge N) j < N ∧
        starCandidateCost (N - chargedBudget (thirtySixCharge N) j)
          (N - thirtySixRequired N - 1) (thirtySixSelection N j) (thirtySixEdge N j) ≤ thirtySixCharge N j ∧
        thirtySixUncovered N j ≤ N - thirtySixRequired N - 1 ∧
        (N * (N - thirtySixRequired N - 1).choose (thirtySixSelection N j) <
          (starCandidateCount (N - chargedBudget (thirtySixCharge N) j) (N - thirtySixRequired N - 1) (thirtySixSelection N j) (thirtySixEdge N j) -
            ∑ i ∈ range j, (thirtySixUncovered N i).choose (thirtySixSelection N j)) *
            (thirtySixUncovered N j + 1) ∨
          (N - thirtySixRequired N - 1 ≤ thirtySixUncovered N j ∧
            (∑ i ∈ range j, (thirtySixUncovered N i).choose (thirtySixSelection N j)) <
              starCandidateCount (N - chargedBudget (thirtySixCharge N) j) (N - thirtySixRequired N - 1) (thirtySixSelection N j) (thirtySixEdge N j)))) ∧
       chargedBudget (thirtySixCharge N) 33 ≤ 2 * thirtySixRequired N - N + 1 ∧
       N - thirtySixRequired N - 1 + chargedBudget (thirtySixCharge N) 33 < N) := by
  rcases thirtySix_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
