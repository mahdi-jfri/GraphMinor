module

public import GraphMinor.GM02.TreeWidthAdjacency
public import GraphMinor.GM02.Feasibility
public import Mathlib.Combinatorics.Graph.Simple

/-!
# The underlying-simple-graph reduction

The last proof step of II (3.2), page 318, replaces the input graph by its
underlying simple graph. Keep its actual vertex set, remove loops, and
identify parallel edges. Distinct-vertex adjacency is unchanged, so both
termination feasibility and tree-width are preserved. Keeping the actual
vertex set avoids adding isolated ambient vertices.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v

/-- The underlying simple graph of II (3.2), page 318, on the same vertex
set as the original graph. Its edges are unordered adjacent distinct pairs. -/
def underlyingSimpleGraph {α : Type u} {β : Type v} (G : Graph α β) : Graph α (Sym2 α) :=
  (Graph.ofSimpleGraph (pathGraph G)).induce V(G)

/-- The reduction keeps exactly the original graph vertices. -/
theorem underlyingSimpleGraph_vertexSet {α : Type u} {β : Type v} (G : Graph α β) :
    V(underlyingSimpleGraph G) = V(G) := rfl

/-- Its adjacency is exactly original adjacency between distinct vertices. -/
theorem underlyingSimpleGraph_adj_iff {α : Type u} {β : Type v} (G : Graph α β) (a b : α) :
    (underlyingSimpleGraph G).Adj a b ↔ G.Adj a b ∧ a ≠ b := by
  constructor
  · rintro ⟨e, he⟩
    rw [underlyingSimpleGraph, Graph.induce_isLink] at he
    exact (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, he.1⟩
  · intro hab
    refine ⟨s(a, b), ?_⟩
    rw [underlyingSimpleGraph, Graph.induce_isLink]
    exact ⟨⟨rfl, (SimpleGraph.mem_edgeSet _).2 hab⟩, hab.1.left_mem, hab.1.right_mem⟩

/-- The pair-path graph is unchanged by passing to the underlying simple graph. -/
theorem pathGraph_underlyingSimpleGraph {α : Type u} {β : Type v} (G : Graph α β) :
    pathGraph (underlyingSimpleGraph G) = pathGraph G := by
  ext a b
  change ((underlyingSimpleGraph G).Adj a b ∧ a ≠ b) ↔ (G.Adj a b ∧ a ≠ b)
  rw [underlyingSimpleGraph_adj_iff]
  exact ⟨And.left, fun h => ⟨h, h.2⟩⟩

/-- Parallel edges and loops do not change termination feasibility, as
used in the final reduction of Graph Minors II (3.2), page 318. -/
theorem feasible_underlyingSimpleGraph_iff {α : Type u} {β : Type v}
    (G : Graph α β) (A : Termination V(G)) :
    A.Feasible (underlyingSimpleGraph G) ↔ A.Feasible G := by
  unfold Termination.Feasible
  rw [pathGraph_underlyingSimpleGraph]

/-- A finite vertex set gives a finite underlying simple edge set. -/
theorem underlyingSimpleGraph_edgeSet_finite {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) : E(underlyingSimpleGraph G).Finite := by
  have hfinite : (Set.image2 Sym2.mk V(G) V(G)).Finite := hV.image2 _ hV
  apply hfinite.subset
  intro e he
  obtain ⟨a, b, hab⟩ := (underlyingSimpleGraph G).exists_isLink_of_mem_edgeSet he
  rw [underlyingSimpleGraph, Graph.induce_isLink] at hab
  exact ⟨a, hab.2.1, b, hab.2.2, hab.1.1.symm⟩

/-- Tree-width is unchanged by the underlying-simple-graph reduction of
Graph Minors II (3.2), page 318, including graphs with loops or parallel edges. -/
theorem treeWidth_underlyingSimpleGraph {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    treeWidth (underlyingSimpleGraph G) (by simpa only [underlyingSimpleGraph_vertexSet] using hV)
      (underlyingSimpleGraph_edgeSet_finite G hV) = treeWidth G hV hE := by
  apply treeWidth_eq_of_distinct_adj _ _ (underlyingSimpleGraph_vertexSet G)
    (fun a b hab => by rw [underlyingSimpleGraph_adj_iff]; exact and_iff_left hab) _ _ hV hE

end GraphMinor.GM02
