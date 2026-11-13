module

public import GraphMinor.Statement
public import Mathlib.Data.Set.Card

/-!
# Expansions and the Erdős–Pósa property

These definitions follow Graph Minors V, Section 8, page 109. An expansion
is a subgraph which contracts to the specified graph. Its whole vertex set
is retained until contraction. The packing and hitting alternatives in the
Erdős–Pósa property concern these subgraphs.
-/

@[expose] public section

namespace GraphMinor.GM05

open Graph Set

universe u v u' v'

/-- Graph Minors V, Section 8, page 109: "some edges of $G'$ may be contracted to produce a graph isomorphic to $H$". -/
def IsHExpansion {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G A : Graph α β) : Prop :=
  A ≤ G ∧ ∃ F ⊆ E(A), Nonempty (Iso H (contract A F))

/-- There are `k` pairwise vertex-disjoint `H`-expansions in `G`
(Graph Minors V, Section 8, page 109). -/
def HasDisjointExpansions {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) (k : ℕ) : Prop :=
  ∃ A : Fin k → Graph α β, (∀ i, IsHExpansion H G (A i)) ∧
    Pairwise (fun i j ↦ Disjoint V(A i) V(A j))

/-- A vertex set meets every `H`-expansion in `G`
(Graph Minors V, Section 8, page 109). -/
def HitsExpansions {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) (X : Set α) : Prop :=
  ∀ A, IsHExpansion H G A → (X ∩ V(A)).Nonempty

/-- The Erdős–Pósa property of Graph Minors V, Section 8, page 109:
for every packing size there is a bound, independent of the finite host,
for a vertex set meeting every expansion when that packing does not exist. -/
def HasErdosPosaProperty {α' : Type u'} {β' : Type v'} (H : Graph α' β') : Prop :=
  ∀ k : ℕ, ∃ k' : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β),
    V(G).Finite → E(G).Finite →
    HasDisjointExpansions H G k ∨ ∃ X ⊆ V(G), X.ncard ≤ k' ∧ HitsExpansions H G X

end GraphMinor.GM05
