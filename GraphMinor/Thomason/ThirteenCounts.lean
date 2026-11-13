module

public import GraphMinor.Thomason.ThirteenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the thirteen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

public section
namespace GraphMinor.Thomason

private theorem thirteen_counts_checked : ∀ N : Fin 55,
    N.val ≤ thirteenRequired N ∨
      (N.val ≤ 2 * thirteenRequired N ∧
       (∀ j : Fin 10, 0 < thirteenSelection N j ∧
        selectionBudget (thirteenSelection N) j < 2 * thirteenRequired N - N ∧
        j.val * (N.val - thirteenRequired N - 1).choose (thirteenSelection N j) <
          (N.val - selectionBudget (thirteenSelection N) j).choose (thirteenSelection N j)) ∧
       selectionBudget (thirteenSelection N) 10 ≤ 2 * thirteenRequired N - N + 1 ∧
       N.val - thirteenRequired N - 1 + selectionBudget (thirteenSelection N) 10 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the thirteen-vertex bound. -/
theorem thirteen_degree_certificate (N : ℕ) (hN : N ≤ 54) :
    N ≤ thirteenRequired N ∨
      (N ≤ 2 * thirteenRequired N ∧
       (∀ j < 10, 0 < thirteenSelection N j ∧
        selectionBudget (thirteenSelection N) j < 2 * thirteenRequired N - N ∧
        j * (N - thirteenRequired N - 1).choose (thirteenSelection N j) <
          (N - selectionBudget (thirteenSelection N) j).choose (thirteenSelection N j)) ∧
       selectionBudget (thirteenSelection N) 10 ≤ 2 * thirteenRequired N - N + 1 ∧
       N - thirteenRequired N - 1 + selectionBudget (thirteenSelection N) 10 < N) := by
  rcases thirteen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
