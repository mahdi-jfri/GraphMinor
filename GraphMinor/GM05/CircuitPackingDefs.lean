module

public import GraphMinor.GM09.Defs

/-!
# Circuit packing and hitting sets

These are the two alternatives in Graph Minors V, (8.1), page 109.
Circuits use the library's simple closed walks, including loops and pairs
of parallel edges.
-/

@[expose] public section

namespace GraphMinor.GM05

open Graph Set GM09

/-- The graph has `k` pairwise vertex-disjoint circuits, as in Graph Minors V,
(8.1)(i), page 109: "$G$ has $k$ disjoint circuits". -/
def HasDisjointCircuits {α β : Type*} (G : Graph α β) (k : ℕ) : Prop :=
  ∃ C : Fin k → Graph α β, (∀ i, IsGraphCircuit G (C i)) ∧
    Pairwise fun i j ↦ Disjoint V(C i) V(C j)

/-- Every circuit of `G` meets `X`. This is the hitting-set formulation of
Graph Minors V, (8.1)(ii), page 109. -/
def HitsCircuits {α β : Type*} (G : Graph α β) (X : Set α) : Prop :=
  ∀ C, IsGraphCircuit G C → (X ∩ V(C)).Nonempty

end GraphMinor.GM05
