module

public import GraphMinor.GM02.Termination
public import GraphMinor.GM02.Separation
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Crossing schemes

Graph Minors II, page 315, describes how disjoint connecting paths can
cross a separation. Two terminations record the path pieces on its two
sides. Two further sets reserve unused separator vertices for one side
or the other. The union of the two terminations must itself be precisely
a family of disjoint paths joining the original pairs.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- A graph with the given vertex set is a disjoint union of paths joining
exactly the pairs of `A`. This writes out condition (iv) in II's definition
of a crossing scheme, page 315, using walks with no repeated vertices.
The vertex and edge cover conditions exclude any further components. -/
def IsPairPathUnion {α : Type u} {vertices : Set α} (A : Termination vertices)
    (F : SimpleGraph α) (S : Set α) : Prop :=
  ∃ P : ∀ p : {p // p ∈ A.pairs}, F.Walk p.val.out.1 p.val.out.2,
    (∀ p, (P p).IsPath) ∧
    (∀ p q, p ≠ q → Disjoint {v | v ∈ (P p).support} {v | v ∈ (P q).support}) ∧
    (⋃ p, {v | v ∈ (P p).support}) = S ∧
    ∀ e ∈ F.edgeSet, ∃ p, e ∈ (P p).edges

/-- Graph Minors II, Section 2, page 315, conditions (i)–(iv): a crossing
scheme for a termination with respect to a separation. Only the data and
conditions printed in the definition are fields. -/
structure CrossingScheme {α : Type u} {β : Type v} (G H H' : Graph α β)
    (A₀ : Termination V(G)) where
  /-- Termination on the first side. -/
  left : Termination V(G)
  /-- Termination on the second side. -/
  right : Termination V(G)
  /-- Separator vertices reserved away from the first side. -/
  reservedLeft : Set α
  /-- Separator vertices reserved away from the second side. -/
  reservedRight : Set α
  /-- Both reserved sets lie in the separator. -/
  reservedLeft_subset : reservedLeft ⊆ V(H) ∩ V(H')
  /-- Both reserved sets lie in the separator. -/
  reservedRight_subset : reservedRight ⊆ V(H) ∩ V(H')
  /-- Condition (i), first side. -/
  left_support : left.support \ (V(H) ∩ V(H')) = A₀.support ∩ (V(H) \ V(H'))
  /-- Condition (i), second side. -/
  right_support : right.support \ (V(H) ∩ V(H')) = A₀.support ∩ (V(H') \ V(H))
  /-- Condition (ii): each separator vertex is in an even number of the
  three termination supports. -/
  even_support : ∀ x ∈ V(H) ∩ V(H'),
    Even ((if x ∈ A₀.support then 1 else 0) +
      (if x ∈ left.support then 1 else 0) + (if x ∈ right.support then 1 else 0) : ℕ)
  /-- Condition (iii), disjointness. -/
  reserved_disjoint : Disjoint reservedLeft reservedRight
  /-- Condition (iii), coverage. -/
  reserved_union : reservedLeft ∪ reservedRight =
    (V(H) ∩ V(H')) \ (A₀.support ∪ left.support ∪ right.support)
  /-- Condition (iv): the graph of the two terminations consists exactly
  of disjoint paths joining the original pairs. -/
  path_union : IsPairPathUnion A₀
    (SimpleGraph.fromEdgeSet (left.pairs ∪ right.pairs : Finset (Sym2 α)))
    (left.support ∪ right.support)

end GraphMinor.GM02
