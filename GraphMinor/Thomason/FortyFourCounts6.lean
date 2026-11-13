module

public import GraphMinor.Thomason.FortyFourTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 44-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem fortyFour_counts_checked_6 : ∀ N : Fin 252, 120 ≤ N.val → N.val < 140 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
