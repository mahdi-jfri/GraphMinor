module

public import GraphMinor.Thomason.FourteenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the fourteen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

public section
namespace GraphMinor.Thomason

private theorem fourteen_counts_checked : ∀ N : Fin 61,
    N.val ≤ fourteenRequired N ∨
      (N.val ≤ 2 * fourteenRequired N ∧
       (∀ j : Fin 11, 0 < fourteenSelection N j ∧
        selectionBudget (fourteenSelection N) j < 2 * fourteenRequired N - N ∧
        j.val * (N.val - fourteenRequired N - 1).choose (fourteenSelection N j) <
          (N.val - selectionBudget (fourteenSelection N) j).choose (fourteenSelection N j)) ∧
       selectionBudget (fourteenSelection N) 11 ≤ 2 * fourteenRequired N - N + 1 ∧
       N.val - fourteenRequired N - 1 + selectionBudget (fourteenSelection N) 11 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the fourteen-vertex bound. -/
theorem fourteen_degree_certificate (N : ℕ) (hN : N ≤ 60) :
    N ≤ fourteenRequired N ∨
      (N ≤ 2 * fourteenRequired N ∧
       (∀ j < 11, 0 < fourteenSelection N j ∧
        selectionBudget (fourteenSelection N) j < 2 * fourteenRequired N - N ∧
        j * (N - fourteenRequired N - 1).choose (fourteenSelection N j) <
          (N - selectionBudget (fourteenSelection N) j).choose (fourteenSelection N j)) ∧
       selectionBudget (fourteenSelection N) 11 ≤ 2 * fourteenRequired N - N + 1 ∧
       N - fourteenRequired N - 1 + selectionBudget (fourteenSelection N) 11 < N) := by
  rcases fourteen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
