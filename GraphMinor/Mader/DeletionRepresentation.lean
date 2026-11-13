module

public import GraphMinor.Mader.DeletionEdgesInjective
import GraphMinor.Kruskal.ForestToSimple

/-!
# Representing a graph whose vertex deletion is a forest

The chosen vertices and ordered forest components give a vertex bijection.
The three edge enumerations give an edge bijection with the same ends.
Together they give an isomorphism to the forest attachment graph. This
includes empty graphs, isolated vertices, loops, and parallel edges.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal GM09 Surface

/-- A forest deletion representation gives an isomorphism including all
original vertex and edge names. -/
noncomputable def deletionGraphIso {α β : Type*} {G : Graph α β}
    {X : Set α} {k n : ℕ} (hE : E(G).Finite) (hX : X ⊆ V(G))
    (a : Fin k ≃ X) {t : Fin n → OrderedTree}
    (hforest : IsGraphForest (deleteVertices G X))
    (ψ : treeForest t ≃g (deleteVertices G X).toSimpleGraph) :
    Iso (apexForest t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a)) G :=
  graphOfEndsIso _ _ G (deletionVertexEquiv hX a ψ)
    (Equiv.ofBijective (deletionEdgeMap hE a hforest ψ)
      ⟨deletionEdgeMap_injective hE hX a hforest ψ,
        deletionEdgeMap_surjective hE a hforest ψ hX⟩)
    (deletionEdgeMap_isLink hE a hforest ψ hX)

/-- Every finite graph with an indexed vertex set whose deletion leaves
a forest is isomorphic to one of the constructed attachment graphs. -/
theorem exists_apexForest_iso {α β : Type*} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {X : Set α} {k : ℕ}
    (hX : X ⊆ V(G)) (a : Fin k ≃ X)
    (hforest : IsGraphForest (deleteVertices G X)) :
    ∃ (n : ℕ) (t : Fin n → OrderedTree)
      (f : Fin n → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ),
      Nonempty (Iso (apexForest t f c) G) := by
  let := (hV.subset (deleteVertices_le G X).vertexSet_mono).fintype
  obtain ⟨n, t, ⟨ψ⟩⟩ := exists_treeForest_iso (deleteVertices G X).toSimpleGraph
    (isAcyclic_toSimpleGraph_of_forest hforest)
  exact ⟨n, t, deletionAttachmentCounts G a ψ, deletionCoreCounts G a,
    ⟨deletionGraphIso hE hX a hforest ψ⟩⟩

end GraphMinor.Mader
