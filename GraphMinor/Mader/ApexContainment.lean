module

public import GraphMinor.Mader.ApexChainLinks
import GraphMinor.Mader.ApexFinite
import GraphMinor.Mader.EndsChains

/-!
# Topological containment for forest attachment graphs

The component address maps prescribe paths for forest edges. The labels
supply enough attachment and core edges. The assembled maps are injective
and preserve links, so the edge-chain construction gives the required
finite sequence of subdivisions.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

/-- Component address embeddings and multiplicity comparisons give
an actual topological minor between the corresponding attachment graphs. -/
theorem apexForest_isTopologicalMinor {k n m : ℕ}
    {s : Fin n → OrderedTree} {t : Fin m → OrderedTree}
    (σ : Fin n ↪ Fin m) (φ : ∀ i, OrderedTree.AddressEmbedding (s i) (t (σ i)))
    (f : Fin n → List ℕ → Fin k → ℕ) (g : Fin m → List ℕ → Fin k → ℕ)
    (c d : Fin k × Fin k → ℕ)
    (hf : ∀ i (p : V(rootedGraph (s i).toRootedTree)) a,
      f i p.val a ≤ g (σ i) ((φ i).vertices p).val a)
    (hc : ∀ p, c p ≤ d p) :
    GM04.IsTopologicalMinor (apexForest s f c) (apexForest t g d) := by
  exact isTopologicalMinor_of_ends_chainEmbedding
    (apexForestLeft s f c) (apexForestRight s f c)
    (apexInternalCount s f c (fun i ↦ (φ i).internalCount)) (apexForest t g d)
    (apexChainVertices f c σ φ) (apexChainEdges σ φ f g c d hf hc)
    (fun _ ↦ Set.mem_univ _) (apexChainLinks σ φ f g c d hf hc)

end GraphMinor.Mader
