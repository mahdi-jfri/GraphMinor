module

public import GraphMinor.GM02.CrossingIndex

/-!
# Index bounds in the alternating recursion

Algorithm A1 of II, page 317, turns index at most five halves of the
width parameter into index at most three times that parameter. Algorithm
A2 uses a terminal-balanced separator to return to the five-halves bound.
These are direct applications of (2.10) and the support cardinality of a
termination. All bounds use natural-number multiples to avoid fractions.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The A1-to-A2 index bound in Graph Minors II, page 317. -/
theorem recursive_A1_child_index {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (hX : (V(H) ∩ V(H')).Finite) {w : ℕ}
    (horder : (V(H) ∩ V(H')).ncard ≤ w) (hindex : 2 * A.index ≤ 5 * w) :
    C.left.index ≤ 3 * w ∧ C.right.index ≤ 3 * w := by
  have hL := C.left_twice_index_le hX
  have hR := C.right_twice_index_le hX
  have hLc : ((V(H) \ V(H')) ∩ A.support).ncard ≤ 2 * A.index := by
    simpa only [A.support_ncard] using Set.ncard_le_ncard Set.inter_subset_right A.support_finite
  have hRc : ((V(H') \ V(H)) ∩ A.support).ncard ≤ 2 * A.index := by
    simpa only [A.support_ncard] using Set.ncard_le_ncard Set.inter_subset_right A.support_finite
  omega

/-- The A2-to-A1 index bound in Graph Minors II, page 317. The separator
balances the support of the current termination, as the paper requires. -/
theorem recursive_A2_child_index {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (hX : (V(H) ∩ V(H')).Finite) {w : ℕ}
    (horder : (V(H) ∩ V(H')).ncard ≤ w) (hindex : A.index ≤ 3 * w)
    (hLbal : 3 * ((V(H) \ V(H')) ∩ A.support).ncard ≤
      2 * (A.support \ (V(H) ∩ V(H'))).ncard)
    (hRbal : 3 * ((V(H') \ V(H)) ∩ A.support).ncard ≤
      2 * (A.support \ (V(H) ∩ V(H'))).ncard) :
    2 * C.left.index ≤ 5 * w ∧ 2 * C.right.index ≤ 5 * w := by
  have hL := C.left_twice_index_le hX
  have hR := C.right_twice_index_le hX
  have htotal : (A.support \ (V(H) ∩ V(H'))).ncard ≤ 2 * A.index := by
    simpa only [A.support_ncard] using Set.ncard_le_ncard Set.sdiff_subset A.support_finite
  omega

end GraphMinor.GM02
