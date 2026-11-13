module

public import GraphMinor.Thomason.TruncatedTable
public import Mathlib.Data.List.Chain
import Mathlib.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

/-!
# Monotonicity from the consecutive entries of a table

A chain check compares each table entry only with the next entry.
Transitivity then gives all index comparisons, so a clamped table
is monotone whenever the clamp index is present.
-/

public section
namespace GraphMinor.Thomason

/-- Consecutive comparisons of the actual list entries suffice to prove
global monotonicity of a clamped numeric table. -/
theorem truncatedTable_monotone_of_chain (a : List ℕ) (L : ℕ)
    (hL : L < a.length) (ha : a.IsChain (· ≤ ·)) : Monotone (truncatedTable a L) := by
  apply truncatedTable_monotone
  intro i
  have hi : i.val + 1 ≤ L := i.isLt
  have hi₀ : i.val < a.length := i.isLt.trans hL
  have hi₁ : i.val + 1 < a.length := hi.trans_lt hL
  change a.getD (min i.val L) 0 ≤ a.getD (min (i.val + 1) L) 0
  rw [Nat.min_eq_left i.isLt.le, Nat.min_eq_left hi,
    List.getD_eq_get a 0 ⟨i.val, hi₀⟩, List.getD_eq_get a 0 ⟨i.val + 1, hi₁⟩]
  have hp : a.Pairwise (· ≤ ·) := List.isChain_iff_pairwise.mp ha
  exact hp.rel_get_of_le (show (⟨i.val, hi₀⟩ : Fin a.length) ≤ ⟨i.val + 1, hi₁⟩ from Nat.le_succ _)

end GraphMinor.Thomason
