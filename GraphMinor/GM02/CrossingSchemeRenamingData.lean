module

public import GraphMinor.GM02.CrossingSchemeRenaming
import GraphMinor.GM02.CrossingSchemeFinite

/-!
# Data preserved by crossing-scheme renaming

Renaming maps both pair sets and both reserved sets by the same vertex
bijection. Injectivity of those image operations shows that distinct
boundary schemes remain distinct when numbered. This complements the
injectivity of restriction to the boundary.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u u' v

/-- The left pair set is mapped by the stated vertex bijection. -/
theorem CrossingScheme.mapEquiv_left_pairs {α : Type u} {α' : Type u'} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A) (e : α ≃ α') :
    (C.mapEquiv e).left.pairs = C.left.pairs.image (Sym2.map e) := by
  unfold CrossingScheme.mapEquiv
  rfl

/-- The right pair set is mapped by the stated vertex bijection. -/
theorem CrossingScheme.mapEquiv_right_pairs {α : Type u} {α' : Type u'} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A) (e : α ≃ α') :
    (C.mapEquiv e).right.pairs = C.right.pairs.image (Sym2.map e) := by
  unfold CrossingScheme.mapEquiv
  rfl

/-- The first reserved set is mapped by the stated vertex bijection. -/
theorem CrossingScheme.mapEquiv_reservedLeft {α : Type u} {α' : Type u'} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A) (e : α ≃ α') :
    (C.mapEquiv e).reservedLeft = e '' C.reservedLeft := by
  unfold CrossingScheme.mapEquiv
  rfl

/-- The second reserved set is mapped by the stated vertex bijection. -/
theorem CrossingScheme.mapEquiv_reservedRight {α : Type u} {α' : Type u'} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A) (e : α ≃ α') :
    (C.mapEquiv e).reservedRight = e '' C.reservedRight := by
  unfold CrossingScheme.mapEquiv
  rfl

/-- Renaming boundary vertices loses no crossing-scheme data. -/
theorem crossingScheme_mapEquiv_injective {α : Type u} {α' : Type u'} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (e : α ≃ α') :
    Function.Injective (fun C : CrossingScheme G H H' A => C.mapEquiv e) := by
  intro C D he
  apply CrossingScheme.ext_data
  · apply Termination.ext_pairs
    apply Finset.image_injective (Sym2.map.injective e.injective)
    simpa only [CrossingScheme.mapEquiv_left_pairs] using congrArg (fun E => E.left.pairs) he
  · apply Termination.ext_pairs
    apply Finset.image_injective (Sym2.map.injective e.injective)
    simpa only [CrossingScheme.mapEquiv_right_pairs] using congrArg (fun E => E.right.pairs) he
  · apply Set.image_injective.mpr e.injective
    simpa only [CrossingScheme.mapEquiv_reservedLeft] using congrArg (fun E => E.reservedLeft) he
  · apply Set.image_injective.mpr e.injective
    simpa only [CrossingScheme.mapEquiv_reservedRight] using congrArg (fun E => E.reservedRight) he

end GraphMinor.GM02
