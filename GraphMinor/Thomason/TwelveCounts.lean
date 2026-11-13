module

public import GraphMinor.Thomason.TwelveTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the twelve-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

public section
namespace GraphMinor.Thomason

private theorem twelve_counts_checked : ∀ N : Fin 47,
    N.val ≤ twelveRequired N ∨
      (N.val ≤ 2 * twelveRequired N ∧
       (∀ j : Fin 9, 0 < twelveSelection N j ∧
        selectionBudget (twelveSelection N) j < 2 * twelveRequired N - N ∧
        j.val * (N.val - twelveRequired N - 1).choose (twelveSelection N j) <
          (N.val - selectionBudget (twelveSelection N) j).choose (twelveSelection N j)) ∧
       selectionBudget (twelveSelection N) 9 ≤ 2 * twelveRequired N - N + 1 ∧
       N.val - twelveRequired N - 1 + selectionBudget (twelveSelection N) 9 < N) := by
  decide

/-- The finite numeric degree certificate for the twelve-vertex bound. -/
theorem twelve_degree_certificate (N : ℕ) (hN : N ≤ 46) :
    N ≤ twelveRequired N ∨
      (N ≤ 2 * twelveRequired N ∧
       (∀ j < 9, 0 < twelveSelection N j ∧
        selectionBudget (twelveSelection N) j < 2 * twelveRequired N - N ∧
        j * (N - twelveRequired N - 1).choose (twelveSelection N j) <
          (N - selectionBudget (twelveSelection N) j).choose (twelveSelection N j)) ∧
       selectionBudget (twelveSelection N) 9 ≤ 2 * twelveRequired N - N + 1 ∧
       N - twelveRequired N - 1 + selectionBudget (twelveSelection N) 9 < N) := by
  rcases twelve_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
