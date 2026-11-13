module

public import GraphMinor.Thomason.FiftyTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 50-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem fifty_counts_checked_10 : ∀ N : Fin 298, 200 ≤ N.val → N.val < 220 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
