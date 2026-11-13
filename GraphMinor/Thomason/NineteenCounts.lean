module

public import GraphMinor.Thomason.NineteenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the nineteen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

private theorem nineteen_counts_checked : ∀ N : Fin 100,
    N.val ≤ nineteenRequired N ∨
      (N.val ≤ 2 * nineteenRequired N ∧
       (∀ j : Fin 16, 0 < nineteenSelection N j ∧
        selectionBudget (nineteenSelection N) j < 2 * nineteenRequired N - N ∧
        j.val * (N.val - nineteenRequired N - 1).choose (nineteenSelection N j) <
          (N.val - selectionBudget (nineteenSelection N) j).choose (nineteenSelection N j)) ∧
       selectionBudget (nineteenSelection N) 16 ≤ 2 * nineteenRequired N - N + 1 ∧
       N.val - nineteenRequired N - 1 + selectionBudget (nineteenSelection N) 16 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the nineteen-vertex bound. -/
theorem nineteen_degree_certificate (N : ℕ) (hN : N ≤ 99) :
    N ≤ nineteenRequired N ∨
      (N ≤ 2 * nineteenRequired N ∧
       (∀ j < 16, 0 < nineteenSelection N j ∧
        selectionBudget (nineteenSelection N) j < 2 * nineteenRequired N - N ∧
        j * (N - nineteenRequired N - 1).choose (nineteenSelection N j) <
          (N - selectionBudget (nineteenSelection N) j).choose (nineteenSelection N j)) ∧
       selectionBudget (nineteenSelection N) 16 ≤ 2 * nineteenRequired N - N + 1 ∧
       N - nineteenRequired N - 1 + selectionBudget (nineteenSelection N) 16 < N) := by
  rcases nineteen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
