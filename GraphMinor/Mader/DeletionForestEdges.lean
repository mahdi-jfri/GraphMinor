module

public import GraphMinor.Mader.ForestEdges
public import GraphMinor.Mader.DeletionVertices
import GraphMinor.Kruskal.ForestSimple
public import GraphMinor.GM01.ForestGraphs
import GraphMinor.GM09.Basic

/-!
# Original edge names for a represented deletion forest

The forest representation gives an edge bijection on the underlying
simple graphs. A forest multigraph has neither loops nor parallel edges,
so that edge bijection recovers the actual original edge names as well.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal GM09 Surface

variable {α β : Type*} {G : Graph α β} {X : Set α} {n : ℕ}
    {t : Fin n → OrderedTree} (hforest : IsGraphForest (deleteVertices G X))
    (ψ : treeForest t ≃g (deleteVertices G X).toSimpleGraph)

/-- The edge bijection from the ordered components to the original deletion forest. -/
noncomputable def deletionForestEdgeEquiv : ForestEdge t ≃ E(deleteVertices G X) := by
  let := forest_simple hforest
  exact (forestEdgeEquiv t).trans
    (ψ.mapEdgeSet.trans (GM01.simpleGraphIso (deleteVertices G X)).edgeEquiv)

/-- The original edge corresponding to a component edge has the represented
parent and child as its ends in the deletion forest. -/
theorem deletionForestEdgeEquiv_isLink (i : Fin n)
    (e : E(rootedGraph (t i).toRootedTree)) :
    (deleteVertices G X).IsLink (deletionForestEdgeEquiv hforest ψ ⟨i, e⟩).val
      (ψ ⟨i, (t i).addressParent e⟩).val (ψ ⟨i, (t i).addressChild e⟩).val := by
  let := forest_simple hforest
  let q := ψ.mapEdgeSet (forestEdgeEquiv t ⟨i, e⟩)
  have hpair : q.val = s(ψ ⟨i, (t i).addressParent e⟩, ψ ⟨i, (t i).addressChild e⟩) := by
    rfl
  have hs : (Graph.ofSimpleGraph (deleteVertices G X).toSimpleGraph).IsLink q.val
      (ψ ⟨i, (t i).addressParent e⟩) (ψ ⟨i, (t i).addressChild e⟩) := ⟨hpair, q.property⟩
  exact ((GM01.simpleGraphIso (deleteVertices G X)).isLink_iff q
    ⟨ψ ⟨i, (t i).addressParent e⟩, Set.mem_univ _⟩
    ⟨ψ ⟨i, (t i).addressChild e⟩, Set.mem_univ _⟩).mp hs

/-- The represented forest edges remain links in the original graph. -/
theorem deletionForestEdgeEquiv_isLink_original (i : Fin n)
    (e : E(rootedGraph (t i).toRootedTree)) :
    G.IsLink (deletionForestEdgeEquiv hforest ψ ⟨i, e⟩).val
      (ψ ⟨i, (t i).addressParent e⟩).val (ψ ⟨i, (t i).addressChild e⟩).val :=
  (deletionForestEdgeEquiv_isLink hforest ψ i e).mono (deleteVertices_le G X)

end GraphMinor.Mader
