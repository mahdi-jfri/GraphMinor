module

public import GraphMinor.GM02.CrossingSchemeFinite
public import GraphMinor.GM02.Separation

/-!
# The bounded boundary used to generate crossing schemes

In II (3.2), both internal routines have index at most three times the
fixed width parameter. Every endpoint in a crossing scheme lies in the
original support or the separator. This union therefore has at most
seven times the width parameter vertices. Numbering this boundary lets
the scheme generator use a fixed finite set of patterns.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The boundary for scheme generation is a finite set of actual vertices. -/
theorem recursive_boundary_finite_subset {α : Type u} {β : Type v}
    {G H H' : Graph α β} (hV : V(G).Finite) (hsep : IsSeparation G H H')
    (A : Termination V(G)) :
    (A.support ∪ (V(H) ∩ V(H'))).Finite ∧
      A.support ∪ (V(H) ∩ V(H')) ⊆ V(G) := by
  have hX : V(H) ∩ V(H') ⊆ V(G) :=
    Set.inter_subset_left.trans hsep.1.vertexSet_mono
  exact ⟨A.support_finite.union (hV.subset hX), Set.union_subset A.support_subset hX⟩

/-- At most seven times the fixed width parameter vertices are needed to
write every crossing-scheme pattern in either alternating routine. -/
theorem recursive_boundary_size {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A : Termination V(G)) {w : ℕ}
    (hindex : A.index ≤ 3 * w) (horder : (V(H) ∩ V(H')).ncard ≤ w) :
    (A.support ∪ (V(H) ∩ V(H'))).ncard ≤ 7 * w := by
  have hu := Set.ncard_union_le A.support (V(H) ∩ V(H'))
  rw [A.support_ncard] at hu
  omega

/-- All four pieces of a crossing scheme are supported on this boundary. -/
theorem CrossingScheme.recursive_boundary_contains {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A) :
    C.left.support ⊆ A.support ∪ (V(H) ∩ V(H')) ∧
    C.right.support ⊆ A.support ∪ (V(H) ∩ V(H')) ∧
    C.reservedLeft ⊆ A.support ∪ (V(H) ∩ V(H')) ∧
    C.reservedRight ⊆ A.support ∪ (V(H) ∩ V(H')) :=
  ⟨C.supports_subset.1, C.supports_subset.2,
    C.reservedLeft_subset.trans Set.subset_union_right,
    C.reservedRight_subset.trans Set.subset_union_right⟩

end GraphMinor.GM02
