module

public import GraphMinor.GM02.CrossingScheme
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Index bounds for induced terminated graphs

A side termination has twice as many support vertices as pairs. Its
support inside the separator has at most the separator's size. Condition
(i) identifies its remaining vertices with the original terminals on
that exclusive side. Adding these two bounds proves II (2.10).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem index_bound {α : Type u} {S X Y : Set α} (A : Termination S)
    (hX : X.Finite) (hY : Y.Finite) (h : A.support \ X = Y) :
    2 * A.index ≤ X.ncard + Y.ncard := by
  have hsub : A.support ⊆ X ∪ Y := by
    intro a ha
    by_cases hx : a ∈ X
    · exact Or.inl hx
    · exact Or.inr (h ▸ (show a ∈ A.support \ X from ⟨ha, hx⟩))
  calc
    2 * A.index = A.support.ncard := A.support_ncard.symm
    _ ≤ (X ∪ Y).ncard := Set.ncard_le_ncard hsub (hX.union hY)
    _ ≤ X.ncard + Y.ncard := Set.ncard_union_le _ _


/-- The first-side endpoint count behind II (2.10), used in the recursion
of Section 3, page 317, before replacing either exclusive count by their maximum. -/
theorem CrossingScheme.left_twice_index_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (hX : (V(H) ∩ V(H')).Finite) :
    2 * C.left.index ≤ (V(H) ∩ V(H')).ncard + ((V(H) \ V(H')) ∩ A.support).ncard := by
  have h := index_bound C.left hX (A.support_finite.inter_of_left _) C.left_support
  simpa only [Set.inter_comm A.support] using h

/-- The second-side endpoint count behind II (2.10), used in Section 3's recursion. -/
theorem CrossingScheme.right_twice_index_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (hX : (V(H) ∩ V(H')).Finite) :
    2 * C.right.index ≤ (V(H) ∩ V(H')).ncard + ((V(H') \ V(H)) ∩ A.support).ncard := by
  have h := index_bound C.right hX (A.support_finite.inter_of_left _) C.right_support
  simpa only [Set.inter_comm A.support] using h

/-- Graph Minors II, (2.10), page 315: the index of either induced
terminated graph is at most half the separator size plus half the larger
number of original terminals in an exclusive side. The induced graph's
vertex deletions do not change its termination or its index. -/
theorem theorem_2_10_proof {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') (A : Termination V(G))
    (C : CrossingScheme G H H' A) :
    (C.left.index : ℚ) ≤ (V(H) ∩ V(H')).ncard / 2 +
      (max ((V(H) \ V(H')) ∩ A.support).ncard
        ((V(H') \ V(H)) ∩ A.support).ncard : ℕ) / 2 ∧
    (C.right.index : ℚ) ≤ (V(H) ∩ V(H')).ncard / 2 +
      (max ((V(H) \ V(H')) ∩ A.support).ncard
        ((V(H') \ V(H)) ∩ A.support).ncard : ℕ) / 2 := by
  have hX : (V(H) ∩ V(H')).Finite :=
    hV.subset (Set.inter_subset_left.trans hsep.1.vertexSet_mono)
  have hL := index_bound C.left hX (A.support_finite.inter_of_left _) C.left_support
  have hR := index_bound C.right hX (A.support_finite.inter_of_left _) C.right_support
  rw [Set.inter_comm A.support] at hL hR
  have hLn : 2 * C.left.index ≤ (V(H) ∩ V(H')).ncard +
      max ((V(H) \ V(H')) ∩ A.support).ncard
        ((V(H') \ V(H)) ∩ A.support).ncard :=
    hL.trans (Nat.add_le_add_left (le_max_left _ _) _)
  have hRn : 2 * C.right.index ≤ (V(H) ∩ V(H')).ncard +
      max ((V(H) \ V(H')) ∩ A.support).ncard
        ((V(H') \ V(H)) ∩ A.support).ncard :=
    hR.trans (Nat.add_le_add_left (le_max_right _ _) _)
  have hLq := (Nat.cast_le (α := ℚ)).2 hLn
  have hRq := (Nat.cast_le (α := ℚ)).2 hRn
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hLq hRq
  constructor <;> linarith

end GraphMinor.GM02
