module

public import Mathlib.Data.List.GetD
public import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
# Monotone finite numeric tables

Extend a finite numeric table constantly beyond its final index.
Checking its successive inequalities proves monotonicity on all natural
numbers. This is used for explicit integer potentials and degree bounds.
-/

@[expose] public section
namespace GraphMinor.Thomason

/-- Look up a natural number in a finite table, clamping the index to
`L`. An absent entry has value zero. -/
def truncatedTable (a : List ℕ) (L n : ℕ) : ℕ := a.getD (min n L) 0

/-- Successive comparisons up to the clamp index give global monotonicity. -/
theorem truncatedTable_monotone (a : List ℕ) (L : ℕ)
    (h : ∀ i : Fin L, truncatedTable a L i ≤ truncatedTable a L (i + 1)) :
    Monotone (truncatedTable a L) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < L
  · exact h ⟨n, hn⟩
  · have heq : min n L = L := Nat.min_eq_right (by omega)
    have heq' : min (n + 1) L = L := Nat.min_eq_right (by omega)
    simp only [truncatedTable, heq, heq', le_refl]

end GraphMinor.Thomason
