module

public import GraphMinor.GM02.CrossingSchemeCount

/-!
# A uniform branching bound for the alternating recursion

Both A1 and A2 have index at most three times the fixed width parameter.
The separator has order at most that parameter. Substituting these bounds
in (2.8) gives a constant number of crossing schemes, and there are two
induced recursive calls per scheme. The extra one in the base of the
power handles the zero parameter without a separate convention.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- A uniform bound on the number of induced calls at a recursive node. -/
def recursiveBranchBound (w : ℕ) : ℕ := 2 * max 2 ((4 * w + 1) ^ w)

/-- The constant branching estimate used in Graph Minors II, page 317. -/
theorem recursive_crossingScheme_bound {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') (A : Termination V(G)) {w : ℕ}
    (horder : (V(H) ∩ V(H')).ncard ≤ w) (hindex : A.index ≤ 3 * w) :
    Finite (CrossingScheme G H H' A) ∧
      2 * Nat.card (CrossingScheme G H H' A) ≤ recursiveBranchBound w := by
  obtain ⟨hfinite, hcount⟩ := theorem_2_8_proof hV hsep A
  have hbase : (V(H) ∩ V(H')).ncard + A.index ≤ 4 * w + 1 := by omega
  have hpow : ((V(H) ∩ V(H')).ncard + A.index) ^ (V(H) ∩ V(H')).ncard ≤ (4 * w + 1) ^ w :=
    (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by omega) horder)
  exact ⟨hfinite, Nat.mul_le_mul_left 2 (hcount.trans (max_le_max_left 2 hpow))⟩

/-- The branching constant is positive even when the width parameter is zero. -/
theorem recursiveBranchBound_pos (w : ℕ) : 0 < recursiveBranchBound w := by
  have h : 2 ≤ max 2 ((4 * w + 1) ^ w) := le_max_left _ _
  unfold recursiveBranchBound
  omega

end GraphMinor.GM02
