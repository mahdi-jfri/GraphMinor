module

public import GraphMinor.Thomason.TwentyTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the twenty-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

private theorem twenty_counts_checked : ∀ N : Fin 109,
    N.val ≤ twentyRequired N ∨
      (N.val ≤ 2 * twentyRequired N ∧
       (∀ j : Fin 17, 0 < twentySelection N j ∧
        selectionBudget (twentySelection N) j < 2 * twentyRequired N - N ∧
        j.val * (N.val - twentyRequired N - 1).choose (twentySelection N j) <
          (N.val - selectionBudget (twentySelection N) j).choose (twentySelection N j)) ∧
       selectionBudget (twentySelection N) 17 ≤ 2 * twentyRequired N - N + 1 ∧
       N.val - twentyRequired N - 1 + selectionBudget (twentySelection N) 17 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the twenty-vertex bound. -/
theorem twenty_degree_certificate (N : ℕ) (hN : N ≤ 108) :
    N ≤ twentyRequired N ∨
      (N ≤ 2 * twentyRequired N ∧
       (∀ j < 17, 0 < twentySelection N j ∧
        selectionBudget (twentySelection N) j < 2 * twentyRequired N - N ∧
        j * (N - twentyRequired N - 1).choose (twentySelection N j) <
          (N - selectionBudget (twentySelection N) j).choose (twentySelection N j)) ∧
       selectionBudget (twentySelection N) 17 ≤ 2 * twentyRequired N - N + 1 ∧
       N - twentyRequired N - 1 + selectionBudget (twentySelection N) 17 < N) := by
  rcases twenty_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
