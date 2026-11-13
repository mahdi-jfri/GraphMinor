module

public import GraphMinor.Thomason.ThirtyTables
public import GraphMinor.Thomason.MixedAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 30-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem thirty_counts_checked_0 : ∀ N : Fin 165, 0 ≤ N.val → N.val < 55 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
