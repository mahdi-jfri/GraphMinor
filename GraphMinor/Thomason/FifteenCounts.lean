module

public import GraphMinor.Thomason.FifteenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the fifteen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

public section
namespace GraphMinor.Thomason

private theorem fifteen_counts_checked : ∀ N : Fin 69,
    N.val ≤ fifteenRequired N ∨
      (N.val ≤ 2 * fifteenRequired N ∧
       (∀ j : Fin 12, 0 < fifteenSelection N j ∧
        selectionBudget (fifteenSelection N) j < 2 * fifteenRequired N - N ∧
        j.val * (N.val - fifteenRequired N - 1).choose (fifteenSelection N j) <
          (N.val - selectionBudget (fifteenSelection N) j).choose (fifteenSelection N j)) ∧
       selectionBudget (fifteenSelection N) 12 ≤ 2 * fifteenRequired N - N + 1 ∧
       N.val - fifteenRequired N - 1 + selectionBudget (fifteenSelection N) 12 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the fifteen-vertex bound. -/
theorem fifteen_degree_certificate (N : ℕ) (hN : N ≤ 68) :
    N ≤ fifteenRequired N ∨
      (N ≤ 2 * fifteenRequired N ∧
       (∀ j < 12, 0 < fifteenSelection N j ∧
        selectionBudget (fifteenSelection N) j < 2 * fifteenRequired N - N ∧
        j * (N - fifteenRequired N - 1).choose (fifteenSelection N j) <
          (N - selectionBudget (fifteenSelection N) j).choose (fifteenSelection N j)) ∧
       selectionBudget (fifteenSelection N) 12 ≤ 2 * fifteenRequired N - N + 1 ∧
       N - fifteenRequired N - 1 + selectionBudget (fifteenSelection N) 12 < N) := by
  rcases fifteen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
