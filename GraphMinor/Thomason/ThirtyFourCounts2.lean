module

public import GraphMinor.Thomason.ThirtyFourTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 34-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem thirtyFour_counts_checked_2 : ∀ N : Fin 184, 122 ≤ N.val → N.val < 184 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
