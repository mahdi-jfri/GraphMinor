module

public import GraphMinor.GM05.Defs

/-!
# Reductions for series-parallel graphs

Graph Minors V, (1.2), uses series-parallel graphs without defining the term.
We use series and parallel reductions, together with deletion of isolated or
pendant vertices for graphs that are not 2-connected. On a simple graph,
suppressing a degree-two vertex adds the edge between its neighbours. Any
parallel pair produced by this operation is represented by one edge.

The reductions are described in R. J. Duffin, *Topology of Series-Parallel
Networks*, J. Math. Anal. Appl. 10 (1965), Section 4, pages 309–313.
No width condition is part of the definition.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V : Type*}

/-- Delete `v` and join its distinct neighbours. For a vertex with two
neighbours this is series reduction, with any resulting parallel edges merged.
For an isolated or pendant vertex this just deletes the vertex.
Duffin, Section 4, page 313: "Delete a node between two edges in series."
and "Delete an edge parallel to another edge." -/
def eliminateVertex (G : (⊤ : SimpleGraph V).Subgraph) (v : V) :
    (⊤ : SimpleGraph V).Subgraph where
  verts := G.verts \ {v}
  Adj x y := x ≠ y ∧ x ∈ G.verts \ {v} ∧ y ∈ G.verts \ {v} ∧
    (G.Adj x y ∨ G.Adj v x ∧ G.Adj v y)
  adj_sub h := h.1
  edge_vert h := h.2.1
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2.1, h.2.1,
    h.2.2.2.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)⟩⟩

/-- A simple graph is series-parallel when a finite sequence of isolated,
pendant, series, and parallel reductions removes all its vertices.
This is the reduction form of the term used in Graph Minors V, (1.2), page 93.
The series and parallel operations are Duffin's operations S and P
(Section 4, pages 309–313). -/
inductive IsSeriesParallelSimple : (⊤ : SimpleGraph V).Subgraph → Prop
  | empty {G} (h : G.verts = ∅) : IsSeriesParallelSimple G
  | reduce {G} (v : V) (hv : v ∈ G.verts) (hdeg : (G.neighborSet v).ncard ≤ 2)
      (h : IsSeriesParallelSimple (eliminateVertex G v)) : IsSeriesParallelSimple G

/-- The simple graph underlying a multigraph has the same vertices and joins
two distinct vertices exactly when the multigraph has an edge between them.
Loops and parallel copies impose no further conditions on vertex bags.
Graph Minors V, Section 1, pages 92–93, defines these bags by the ends of edges. -/
def simpleShadow {α β : Type*} (G : Graph α β) : (⊤ : SimpleGraph α).Subgraph where
  verts := G.vertexSet
  Adj x y := x ≠ y ∧ G.Adj x y
  adj_sub h := h.1
  edge_vert h := h.2.left_mem
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩

/-- A finite multigraph is series-parallel when its underlying simple graph
admits the series-parallel reductions. Loops and parallel copies are allowed,
as in Graph Minors V, Section 1, page 92. -/
def IsSeriesParallel {α β : Type*} (G : Graph α β) : Prop :=
  G.vertexSet.Finite ∧ G.edgeSet.Finite ∧ IsSeriesParallelSimple (simpleShadow G)

end GraphMinor.GM05
