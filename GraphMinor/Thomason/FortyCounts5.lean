module

public import GraphMinor.Thomason.FortyTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 40-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem forty_counts_checked_5 : ∀ N : Fin 222, 200 ≤ N.val → N.val < 222 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
