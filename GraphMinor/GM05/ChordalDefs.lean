module

public import GraphMinor.GM05.Defs
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Chordal graphs and subtree intersection graphs

Graph Minors V, Section 8, page 110, calls a simple graph chordal when it
has no induced circuit on four or more vertices. An induced graph
embedding of a cycle records exactly such a circuit. A subtree
intersection representation uses nonempty connected induced subgraphs of
a finite tree, with adjacency given by intersection.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Set

universe u

/-- Chordality as defined in Graph Minors V, Section 8, page 110:
"it has no induced subgraph which is a circuit of four or more vertices". -/
def IsChordal {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, 4 ≤ n → IsEmpty ((cycleGraph n) ↪g G)

/-- A subtree intersection representation, as defined in Graph Minors V,
Section 8, page 110. Connected vertex sets of a tree determine its subtrees. -/
def IsSubtreeIntersectionGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι), T.IsTree ∧
    ∃ A : V → Set ι, (∀ v, (T.induce (A v)).Connected) ∧
      ∀ v w, v ≠ w → (G.Adj v w ↔ (A v ∩ A w).Nonempty)

/-- A vertex with pairwise adjacent neighbors, as in Graph Minors V,
(8.4), page 110. -/
def IsSimplicial {V : Type u} (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

/-- Chordality is preserved by passing to an induced graph embedding. -/
theorem IsChordal.of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : IsChordal G) (f : H ↪g G) : IsChordal H := by
  intro n hn
  exact ⟨fun e ↦ (hG n hn).false (f.comp e)⟩

end GraphMinor.GM05
