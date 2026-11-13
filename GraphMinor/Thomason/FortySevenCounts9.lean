module

public import GraphMinor.Thomason.FortySevenTables
public import GraphMinor.Thomason.StarAverageBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the 47-vertex connection charges in a bounded order range

Every allowed neighbourhood order satisfies the explicit subset counts,
connection charges, intermediate degree bounds, and residual-branch
bounds. All checks are finite integer computations in Lean's kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason
open Finset

theorem fortySeven_counts_checked_9 : ∀ N : Fin 274, 180 ≤ N.val → N.val < 200 →
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
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

end GraphMinor.Thomason
