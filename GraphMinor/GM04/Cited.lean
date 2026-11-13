module

public import GraphMinor.GM04.TopologicalContainment

/-!
# External tree and circuit-bound theorems cited by Graph Minors IV

The introduction cites Kruskal for trees under topological containment and
Mader for graphs with a bound on their number of disjoint circuits.
-/

@[expose] public section

namespace GraphMinor.GM04

open Graph

universe u v

/-- Kruskal, *Well-quasi-ordering, the Tree Theorem, and Vazsonyi's conjecture*,
Trans. Amer. Math. Soc. 95 (1960), Section 2, pages 211–212: the collection
of all finite connected trees is well-quasi-ordered by homeomorphic embedding.
This is the unstructured-tree corollary proved there: forgetting the structure
is an onto order-preserving map, and the Tree Theorem on page 212 applies
to the one-element label order. These are the unrooted trees denoted by
`P*` in that section, rather than its labelled structured trees `T(X)`.
Source: https://www.ams.org/tran/1960-095-02/S0002-9947-1960-0111704-1/S0002-9947-1960-0111704-1.pdf -/
def KruskalTreeStatement : Prop :=
  ∀ {α : Type u} {β : Type v} (G : ℕ → Graph α β),
    (∀ n, V(G n).Finite) → (∀ n, E(G n).Finite) →
    (∀ n, IsUndirectedTree (G n)) →
    ∃ i j, i < j ∧ IsTopologicalMinor (G i) (G j)

/-- Mader, *Wohlquasigeordnete Klassen endlicher Graphen*, J. Combin. Theory
Ser. B 12 (1972), pages 105–122, abstract on page 105: finite graphs with
at most `n` disjoint circuits are well-quasi-ordered by subdivision containment,
for each fixed natural number `n`. The first order in the abstract is defined
by containment of a subdivision, rather than its separate contraction order.
Having at most `n` vertex-disjoint circuits is expressed by exclusion of a
family of `n + 1` such circuits.
Source: https://doi.org/10.1016/0095-8956(72)90015-9 -/
def MaderCircuitStatement : Prop :=
  ∀ n : ℕ, ∀ {α : Type u} {β : Type v} (G : ℕ → Graph α β),
    (∀ i, V(G i).Finite) → (∀ i, E(G i).Finite) →
    (∀ i, ¬ HasDisjointCircuits (G i) (n + 1)) →
    ∃ i j, i < j ∧ IsTopologicalMinor (G i) (G j)

end GraphMinor.GM04
