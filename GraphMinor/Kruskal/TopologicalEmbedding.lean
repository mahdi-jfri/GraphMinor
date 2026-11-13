module

public import GraphMinor.Kruskal.EmbeddedChainLinks
public import GraphMinor.Kruskal.EmbeddingAddresses
public import GraphMinor.Kruskal.ChainEmbedding

/-!
# Ordered-tree embeddings give topological containment

Replace each source edge by its prefix path between the image parent and
image child. The common-ancestor property gives injective names for vertices
and edges, and consecutive prefixes preserve links. The edge-chain
construction supplies the actual finite sequence of subdivisions.
-/

public section

namespace GraphMinor.Kruskal.OrderedTree

open Graph

/-- An address embedding gives topological containment of the underlying
multigraphs, with an actual sequence of edge subdivisions. -/
theorem AddressEmbedding.isTopologicalMinor {s t : OrderedTree} (φ : AddressEmbedding s t) :
    GM04.IsTopologicalMinor (rootedGraph s.toRootedTree) (rootedGraph t.toRootedTree) := by
  have hfin := rootedGraph_finite s.toRootedTree
  exact isTopologicalMinor_of_chainEmbedding
    (rootedGraph s.toRootedTree) (rootedGraph t.toRootedTree) hfin.1 hfin.2
    s.addressParent s.addressChild
    (fun e ↦ ⟨e.property, Or.inl ⟨rfl, rfl⟩⟩)
    φ.internalCount φ.chainVertices φ.chainEdges
    φ.rawVertex_mem φ.chainLinks

/-- The recursive ordered-tree embedding relation implies topological
containment in the exact multigraph interface of Graph Minors IV. -/
theorem Embeds.isTopologicalMinor {s t : OrderedTree} (h : Embeds s t) :
    GM04.IsTopologicalMinor (rootedGraph s.toRootedTree) (rootedGraph t.toRootedTree) := by
  obtain ⟨φ⟩ := h.exists_addressEmbedding
  exact φ.isTopologicalMinor

end GraphMinor.Kruskal.OrderedTree
