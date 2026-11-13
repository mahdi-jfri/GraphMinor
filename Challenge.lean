module

public import GraphMinor.Statement
public import GraphMinor.GM16.Section1Statements
public import GraphMinor.Compute.DPStatement

/-!
# The three main theorems: the statements to be proved

* `GraphMinor.graph_minor_theorem`: in every infinite sequence of finite graphs, some graph is
  isomorphic to a minor of a later one. This is Wagner's conjecture, (1.1) of N. Robertson and
  P. D. Seymour, *Graph Minors. IV. Tree-width and well-quasi-ordering*, J. Combin. Theory Ser. B
  **48** (1990), 227–254, page 228, proved in *Graph Minors. XX. Wagner's conjecture*,
  J. Combin. Theory Ser. B **92** (2004), 325–357.
* `GraphMinor.structure_theorem`: Graph Minors XVI, (1.3), page 46.
* `GraphMinor.disjoint_paths_algorithm`: the main result of Graph Minors XIII, page 65, which the
  paper does not number.

Graphs may have loops and multiple edges, as in the papers. The relation `GraphMinor.IsIsoMinor`
("is isomorphic to a minor of") is defined in `GraphMinor/Statement.lean`, the notions of the
structure theorem in `GraphMinor/GM16/Section1Statements.lean`, the Word RAM model in
`GraphMinor/Compute/Basic.lean`, and the disjoint paths problem with its input and output format in
`GraphMinor/Compute/DPStatement.lean`. `Solution.lean` proves the three theorems.
-/

public section

namespace GraphMinor

open Graph

/-- **The graph minor theorem** (Robertson and Seymour, Graph Minors XX), Wagner's conjecture as
stated in Graph Minors IV, (1.1). For every sequence `G 0, G 1, …` of finite graphs, which may have
loops and multiple edges, there are `i < j` such that `G i` is isomorphic to a minor of `G j`. -/
theorem graph_minor_theorem {α β : Type*} (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite)
    (hE : ∀ n, E(G n).Finite) : ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) :=
  sorry

open Surface GM16 Compute
universe u v w u' v'

/-- **The structure theorem**, Graph Minors XVI, (1.3), page 46.
Every graph excluding a fixed nonplanar minor is built by clique-sums from bounded
vertex extensions of outgrowths by bounded rings on surfaces excluding that minor. -/
theorem structure_theorem :
  ∀ {α' : Type u'} {β' : Type v'} (L : Graph α' β'),
    V(L).Finite → E(L).Finite →
    (∀ (S : Type w) [TopologicalSpace S] [T2Space S],
      IsSphere S → ¬ CanBeDrawnIn S L) →
    ∃ r d w₀ : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β),
        V(G).Finite → E(G).Finite → ¬ IsIsoMinor L G →
        HasTreeStructureOver
          {H : Graph α (β ⊕ ℕ) | ∃ (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
            (H₀ : Graph α (β ⊕ ℕ)),
            IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
            IsVertexExtension w₀ H H₀ ∧ IsOutgrowthByRings S H₀ d r}
          (liftEdgeInl G) := by
  sorry

/-- **The disjoint paths algorithm**, the main result of Graph Minors XIII (page 65), which the
paper does not number.
For each fixed number of terminal pairs, a Word RAM program decides whether disjoint
paths join them in cubic time. -/
theorem disjoint_paths_algorithm :
  ∀ k : ℕ, ∃ P : Cmd,
    ComputesRelInTime (dpSize (k := k)) (fun x s => s.arrs inArr = encDPIn x)
      IsValidDPOutput P (fun v => (v + 1) ^ 3) := by
  sorry

end GraphMinor
