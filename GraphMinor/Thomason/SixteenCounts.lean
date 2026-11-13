module

public import GraphMinor.Thomason.SixteenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the sixteen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

public section
namespace GraphMinor.Thomason

private theorem sixteen_counts_checked : ∀ N : Fin 77,
    N.val ≤ sixteenRequired N ∨
      (N.val ≤ 2 * sixteenRequired N ∧
       (∀ j : Fin 13, 0 < sixteenSelection N j ∧
        selectionBudget (sixteenSelection N) j < 2 * sixteenRequired N - N ∧
        j.val * (N.val - sixteenRequired N - 1).choose (sixteenSelection N j) <
          (N.val - selectionBudget (sixteenSelection N) j).choose (sixteenSelection N j)) ∧
       selectionBudget (sixteenSelection N) 13 ≤ 2 * sixteenRequired N - N + 1 ∧
       N.val - sixteenRequired N - 1 + selectionBudget (sixteenSelection N) 13 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the sixteen-vertex bound. -/
theorem sixteen_degree_certificate (N : ℕ) (hN : N ≤ 76) :
    N ≤ sixteenRequired N ∨
      (N ≤ 2 * sixteenRequired N ∧
       (∀ j < 13, 0 < sixteenSelection N j ∧
        selectionBudget (sixteenSelection N) j < 2 * sixteenRequired N - N ∧
        j * (N - sixteenRequired N - 1).choose (sixteenSelection N j) <
          (N - selectionBudget (sixteenSelection N) j).choose (sixteenSelection N j)) ∧
       selectionBudget (sixteenSelection N) 13 ≤ 2 * sixteenRequired N - N + 1 ∧
       N - sixteenRequired N - 1 + selectionBudget (sixteenSelection N) 13 < N) := by
  rcases sixteen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
