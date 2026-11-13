module

public import GraphMinor.Thomason.TwentyOneTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the twentyOne-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

private theorem twentyOne_counts_checked : ∀ N : Fin 117,
    N.val ≤ twentyOneRequired N ∨
      (N.val ≤ 2 * twentyOneRequired N ∧
       (∀ j : Fin 18, 0 < twentyOneSelection N j ∧
        selectionBudget (twentyOneSelection N) j < 2 * twentyOneRequired N - N ∧
        j.val * (N.val - twentyOneRequired N - 1).choose (twentyOneSelection N j) <
          (N.val - selectionBudget (twentyOneSelection N) j).choose (twentyOneSelection N j)) ∧
       selectionBudget (twentyOneSelection N) 18 ≤ 2 * twentyOneRequired N - N + 1 ∧
       N.val - twentyOneRequired N - 1 + selectionBudget (twentyOneSelection N) 18 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the twentyOne-vertex bound. -/
theorem twentyOne_degree_certificate (N : ℕ) (hN : N ≤ 116) :
    N ≤ twentyOneRequired N ∨
      (N ≤ 2 * twentyOneRequired N ∧
       (∀ j < 18, 0 < twentyOneSelection N j ∧
        selectionBudget (twentyOneSelection N) j < 2 * twentyOneRequired N - N ∧
        j * (N - twentyOneRequired N - 1).choose (twentyOneSelection N j) <
          (N - selectionBudget (twentyOneSelection N) j).choose (twentyOneSelection N j)) ∧
       selectionBudget (twentyOneSelection N) 18 ≤ 2 * twentyOneRequired N - N + 1 ∧
       N - twentyOneRequired N - 1 + selectionBudget (twentyOneSelection N) 18 < N) := by
  rcases twentyOne_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
