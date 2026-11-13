module

public import GraphMinor.Thomason.ThirtySixTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 36-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem thirtySix_counts_checked_0 : ∀ N : Fin 193, 0 ≤ N.val → N.val < 40 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
