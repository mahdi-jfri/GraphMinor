module

public import GraphMinor.GM02.CrossingSchemeBoundary
public import GraphMinor.GM02.FeasibilityVertices

/-!
# Recovering crossing-scheme data from its boundary restriction

Every pair endpoint and reserved vertex belongs to the chosen boundary.
Forgetting the subtype therefore recovers both original terminations
and both reserved sets. In particular, boundary restriction is injective:
no two original schemes collapse to the same numbered boundary pattern.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Forgetting restricted endpoint memberships recovers the left pair set. -/
theorem CrossingScheme.induceBoundary_left_pairs_map {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    {S : Set α} (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S) :
    (C.induceBoundary hAS hXS).left.pairs.image (Sym2.map Subtype.val) = C.left.pairs := by
  have hLS : C.left.support ⊆ S := C.supports_subset.1.trans (Set.union_subset hAS hXS)
  change (C.left.rebase hLS).onVertices.pairs.image (Sym2.map Subtype.val) = C.left.pairs
  exact (C.left.rebase hLS).onVertices_map_pairs

/-- Forgetting restricted endpoint memberships recovers the right pair set. -/
theorem CrossingScheme.induceBoundary_right_pairs_map {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    {S : Set α} (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S) :
    (C.induceBoundary hAS hXS).right.pairs.image (Sym2.map Subtype.val) = C.right.pairs := by
  have hRS : C.right.support ⊆ S := C.supports_subset.2.trans (Set.union_subset hAS hXS)
  change (C.right.rebase hRS).onVertices.pairs.image (Sym2.map Subtype.val) = C.right.pairs
  exact (C.right.rebase hRS).onVertices_map_pairs

/-- The first reserved set is fully recovered after boundary restriction. -/
theorem CrossingScheme.induceBoundary_reservedLeft_image {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    {S : Set α} (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S) :
    Subtype.val '' (C.induceBoundary hAS hXS).reservedLeft = C.reservedLeft := by
  change Subtype.val '' (Subtype.val ⁻¹' C.reservedLeft : Set S) = C.reservedLeft
  apply Set.image_preimage_eq_of_subset
  intro a ha
  exact ⟨⟨a, hXS (C.reservedLeft_subset ha)⟩, rfl⟩

/-- The second reserved set is fully recovered after boundary restriction. -/
theorem CrossingScheme.induceBoundary_reservedRight_image {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    {S : Set α} (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S) :
    Subtype.val '' (C.induceBoundary hAS hXS).reservedRight = C.reservedRight := by
  change Subtype.val '' (Subtype.val ⁻¹' C.reservedRight : Set S) = C.reservedRight
  apply Set.image_preimage_eq_of_subset
  intro a ha
  exact ⟨⟨a, hXS (C.reservedRight_subset ha)⟩, rfl⟩

/-- Boundary restriction loses no crossing-scheme data. -/
theorem crossingScheme_induceBoundary_injective {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} {S : Set α}
    (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S) :
    Function.Injective (fun C : CrossingScheme G H H' A => C.induceBoundary hAS hXS) := by
  intro C D he
  apply CrossingScheme.ext_data
  · apply Termination.ext_pairs
    calc
      C.left.pairs = _ := (C.induceBoundary_left_pairs_map hAS hXS).symm
      _ = _ := congrArg (fun E => E.left.pairs.image (Sym2.map Subtype.val)) he
      _ = D.left.pairs := D.induceBoundary_left_pairs_map hAS hXS
  · apply Termination.ext_pairs
    calc
      C.right.pairs = _ := (C.induceBoundary_right_pairs_map hAS hXS).symm
      _ = _ := congrArg (fun E => E.right.pairs.image (Sym2.map Subtype.val)) he
      _ = D.right.pairs := D.induceBoundary_right_pairs_map hAS hXS
  · calc
      C.reservedLeft = _ := (C.induceBoundary_reservedLeft_image hAS hXS).symm
      _ = _ := congrArg (fun E => Subtype.val '' E.reservedLeft) he
      _ = D.reservedLeft := D.induceBoundary_reservedLeft_image hAS hXS
  · calc
      C.reservedRight = _ := (C.induceBoundary_reservedRight_image hAS hXS).symm
      _ = _ := congrArg (fun E => Subtype.val '' E.reservedRight) he
      _ = D.reservedRight := D.induceBoundary_reservedRight_image hAS hXS

end GraphMinor.GM02
