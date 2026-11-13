module

public import GraphMinor.Compute.Graph
public import GraphMinor.HP25.Web
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cited result: linear-time planarity testing

The crossing extractor of `docs/crossing/crossing_extractor.tex`, which replaces Shiloach's
algorithm in Graph Minors XIII, (8.1), uses one primitive besides graph searches and bounded flows:
a Boolean planarity test in linear time. Section 1 of the note states it as Fact P:

> On an adjacency-list representation of a graph \(K\), a deterministic procedure
> \(\operatorname{Planar}(K)\) returns whether \(K\) is planar in time \(O(|V(K)|+|E(K)|)\).

The note cites J. Hopcroft and R. Tarjan, *Efficient planarity testing*, J. ACM **21** (1974),
549–568, for the first linear-time planarity test. `PlanarityTestStatement` below is Fact P in the
Word RAM model, and it is proved, as `planarityTestStatement_proved`, from the planarity test of
`docs/planarity/planarity_test.tex`. A graph is planar when it has a plane embedding,
`HP25.PlaneEmbedding G Set.univ`: its vertices are drawn at distinct points of `ℂ`, and its edges as
arcs that meet only at common ends.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-- **Linear-time planarity testing** (J. Hopcroft and R. Tarjan, *Efficient planarity testing*,
J. ACM 21 (1974), 549–568), as used in `docs/crossing/crossing_extractor.tex`, Section 1, Fact P.

Fixed Word RAM calling convention, the same as that of `Shiloach80Statement`:
* **Input:** `s.regs 30 = N`, and the adjacency lists `IsAdjList G 30 31 32 lists s` of a simple
  graph `G : SimpleGraph (Fin N)`, with `(s.arrs 32).length < 2 ^ w`.
* **Scratch space:** the program may change only registers `≥ 30` and arrays `≥ 33`.
* **Output:** within `C * (G.edgeFinset.card + N + 1)` steps, register `35` is `1` if `G` has a
  plane embedding, and `0` if it has none. -/
def PlanarityTestStatement : Prop :=
  ∃ (prog : Cmd) (C c_w : ℕ), 0 < C ∧ 0 < c_w ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (lists : Fin N → List ℕ),
      ∀ (w : ℕ), wordSize c_w (G.edgeFinset.card + N + 1) ≤ w →
      ∀ (s : State),
        IsAdjList G 30 31 32 lists s →
        (s.arrs 32).length < 2 ^ w →
        s.regs 30 = N →
        ∃ (s' : State) (t : ℕ),
          Exec w prog s s' t ∧
          t ≤ C * (G.edgeFinset.card + N + 1) ∧
          (∀ r < 30, s'.regs r = s.regs r) ∧
          (∀ a < 33, s'.arrs a = s.arrs a) ∧
          ((s'.regs 35 = 1 ∧ Nonempty (HP25.PlaneEmbedding G Set.univ)) ∨
            (s'.regs 35 = 0 ∧ IsEmpty (HP25.PlaneEmbedding G Set.univ)))

end GraphMinor.Compute
