module

public import GraphMinor.Thomason.EighteenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the eighteen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

private theorem eighteen_counts_checked : ∀ N : Fin 93,
    N.val ≤ eighteenRequired N ∨
      (N.val ≤ 2 * eighteenRequired N ∧
       (∀ j : Fin 15, 0 < eighteenSelection N j ∧
        selectionBudget (eighteenSelection N) j < 2 * eighteenRequired N - N ∧
        j.val * (N.val - eighteenRequired N - 1).choose (eighteenSelection N j) <
          (N.val - selectionBudget (eighteenSelection N) j).choose (eighteenSelection N j)) ∧
       selectionBudget (eighteenSelection N) 15 ≤ 2 * eighteenRequired N - N + 1 ∧
       N.val - eighteenRequired N - 1 + selectionBudget (eighteenSelection N) 15 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the eighteen-vertex bound. -/
theorem eighteen_degree_certificate (N : ℕ) (hN : N ≤ 92) :
    N ≤ eighteenRequired N ∨
      (N ≤ 2 * eighteenRequired N ∧
       (∀ j < 15, 0 < eighteenSelection N j ∧
        selectionBudget (eighteenSelection N) j < 2 * eighteenRequired N - N ∧
        j * (N - eighteenRequired N - 1).choose (eighteenSelection N j) <
          (N - selectionBudget (eighteenSelection N) j).choose (eighteenSelection N j)) ∧
       selectionBudget (eighteenSelection N) 15 ≤ 2 * eighteenRequired N - N + 1 ∧
       N - eighteenRequired N - 1 + selectionBudget (eighteenSelection N) 15 < N) := by
  rcases eighteen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
