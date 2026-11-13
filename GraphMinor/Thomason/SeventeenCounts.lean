module

public import GraphMinor.Thomason.SeventeenTables
public import GraphMinor.Thomason.GeometricBranchFamily
import Lean.Elab.Tactic.Omega

/-!
# Verification of the seventeen-vertex branch counts

For each possible neighbourhood order, the required degree is either
impossible or the listed selection sizes meet every binomial inequality,
every intermediate surplus bound, and the final residual-branch bounds.
All checks are finite integer computations in the Lean kernel.
-/

set_option maxRecDepth 4096

public section
namespace GraphMinor.Thomason

private theorem seventeen_counts_checked : ∀ N : Fin 85,
    N.val ≤ seventeenRequired N ∨
      (N.val ≤ 2 * seventeenRequired N ∧
       (∀ j : Fin 14, 0 < seventeenSelection N j ∧
        selectionBudget (seventeenSelection N) j < 2 * seventeenRequired N - N ∧
        j.val * (N.val - seventeenRequired N - 1).choose (seventeenSelection N j) <
          (N.val - selectionBudget (seventeenSelection N) j).choose (seventeenSelection N j)) ∧
       selectionBudget (seventeenSelection N) 14 ≤ 2 * seventeenRequired N - N + 1 ∧
       N.val - seventeenRequired N - 1 + selectionBudget (seventeenSelection N) 14 < N) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The finite numeric degree certificate for the seventeen-vertex bound. -/
theorem seventeen_degree_certificate (N : ℕ) (hN : N ≤ 84) :
    N ≤ seventeenRequired N ∨
      (N ≤ 2 * seventeenRequired N ∧
       (∀ j < 14, 0 < seventeenSelection N j ∧
        selectionBudget (seventeenSelection N) j < 2 * seventeenRequired N - N ∧
        j * (N - seventeenRequired N - 1).choose (seventeenSelection N j) <
          (N - selectionBudget (seventeenSelection N) j).choose (seventeenSelection N j)) ∧
       selectionBudget (seventeenSelection N) 14 ≤ 2 * seventeenRequired N - N + 1 ∧
       N - seventeenRequired N - 1 + selectionBudget (seventeenSelection N) 14 < N) := by
  rcases seventeen_counts_checked ⟨N, by omega⟩ with h | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact Or.inl h
  · exact Or.inr ⟨hhalf, fun j hj => hsteps ⟨j, hj⟩, hfinal, hroom⟩

end GraphMinor.Thomason
