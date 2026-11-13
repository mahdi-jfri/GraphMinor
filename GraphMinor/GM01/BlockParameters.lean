module

import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# The number of blocks in the rooted comb

Graph Minors I, page 55, chooses the largest integer `T` with
`2νT ≤ N − 2δ` and puts `n − 1 = νT`. Integer division makes that choice
explicit. The two inequalities below give both the number of blocks and
the size of the comb left in the last block.
-/

public section

namespace GraphMinor.GM01

/-- The maximal integer choice and its consequences on page 55 of
Graph Minors I. The lower bound on `N` ensures at least two groups of
blocks. -/
theorem exists_comb_block_parameters (ν δ N : ℕ) (hν : 0 < ν)
    (hN : 2 + 4 * ν + 2 * δ ≤ N) :
    ∃ T n : ℕ, 2 ≤ T ∧ n = ν * T + 1 ∧
      2 * ν * T ≤ N - 2 * δ ∧
      (∀ t : ℕ, 2 * ν * t ≤ N - 2 * δ → t ≤ T) ∧
      N - 2 * δ - 2 * ν < 2 * n - 2 ∧
      2 * n - 2 ≤ N - 2 * δ ∧ 2 * δ ≤ N - 2 * n + 2 := by
  let T := (N - 2 * δ) / (2 * ν)
  have hpos : 0 < 2 * ν := Nat.mul_pos (by omega) hν
  have hbound : 2 * ν * T ≤ N - 2 * δ := Nat.mul_div_le _ _
  have hmax : ∀ t : ℕ, 2 * ν * t ≤ N - 2 * δ → t ≤ T := by
    intro t ht
    exact (Nat.le_div_iff_mul_le hpos).mpr (by simpa only [Nat.mul_comm] using ht)
  have htwo : 2 ≤ T := hmax 2 (by omega)
  have hnext : N - 2 * δ < 2 * ν * (T + 1) := by
    by_contra h
    have hbad := hmax (T + 1) (by omega)
    omega
  refine ⟨T, ν * T + 1, htwo, rfl, hbound, hmax, ?_, ?_, ?_⟩
  all_goals
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hbound hnext ⊢
    omega

end GraphMinor.GM01
