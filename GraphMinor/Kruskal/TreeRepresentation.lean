module

public import GraphMinor.Kruskal.RootedAssembly
public import GraphMinor.Kruskal.RootedSimple
public import GraphMinor.Kruskal.ForestToSimple
import GraphMinor.GM01.ForestGraphs
import GraphMinor.Minor.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Representing the multigraph trees of IV by ordered trees

First pass to the simple graph on the actual vertex set. Give those vertices
finite names and use the existing rooted-tree construction from unique tree
paths. The root-and-branch recursion then gives an ordered tree. All changes
of representation are witnessed by explicit graph isomorphisms.
-/

public section

namespace GraphMinor.Kruskal

open Graph SimpleGraph Set GraphMinor.GM04

/-- An isomorphism of simple graphs gives an isomorphism of their multigraph
representations. Vertices use the given bijection and edges use its map on
unordered pairs. -/
def simpleIsoToGraphIso {α β : Type*} {K : SimpleGraph α} {L : SimpleGraph β}
    (φ : K ≃g L) : GraphMinor.Iso (Graph.ofSimpleGraph K) (Graph.ofSimpleGraph L) where
  vertexEquiv := (Equiv.Set.univ α).trans (φ.toEquiv.trans (Equiv.Set.univ β).symm)
  edgeEquiv := φ.mapEdgeSet
  isLink_iff e x y := by
    change (e.val = s(x.val, y.val) ∧ e.val ∈ K.edgeSet) ↔
      (Sym2.map φ e.val = s(φ x.val, φ y.val) ∧ (φ.mapEdgeSet e).val ∈ L.edgeSet)
    have hpair : e.val = s(x.val, y.val) ↔
        Sym2.map φ e.val = s(φ x.val, φ y.val) := by
      rw [← Sym2.map_mk]
      exact (Sym2.map.injective φ.injective).eq_iff.symm
    exact ⟨fun h ↦ ⟨hpair.1 h.1, (φ.mapEdgeSet e).property⟩,
      fun h ↦ ⟨hpair.2 h.1, e.property⟩⟩

/-- The parent-tree multigraph is isomorphic to the multigraph of the
simple tree used in the existing rooted-tree library. -/
noncomputable def rootedGraphIsoToSimple {ι : Type*} (T : RootedTree ι) :
    GraphMinor.Iso (rootedGraph T) (Graph.ofSimpleGraph (Thomas.toSimpleGraph T)) := by
  let := rootedGraph_simple T
  exact (GM01.simpleGraphIso (rootedGraph T)).symm.trans
    (simpleIsoToGraphIso (rootedGraphToSimpleIso T))

/-- Every finite undirected multigraph tree has a parent-tree representation.
The isomorphism includes both the vertices and the actual edge names. -/
theorem exists_rootedTree_graph_iso {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hG : IsUndirectedTree G) :
    ∃ T : RootedTree ℕ, Nonempty (GraphMinor.Iso (rootedGraph T) G) := by
  classical
  let := hV.fintype
  let := forest_simple hG.2
  let e : Fin (Fintype.card V(G)) ≃ V(G) := (Fintype.equivFin V(G)).symm
  let K : SimpleGraph (Fin (Fintype.card V(G))) := G.toSimpleGraph.comap e
  let ψ : K ≃g G.toSimpleGraph := SimpleGraph.Iso.comap e G.toSimpleGraph
  have hK : K.IsTree := ψ.isTree_iff.2 (isTree_toSimpleGraph hG)
  let T := Thomas.rootedTreeOfIsTree hK
  let θ : Thomas.toSimpleGraph T ≃g K := {
    toEquiv := Thomas.equivFinOfIsTree hK
    map_rel_iff' := fun {a b} ↦ (Thomas.toSimpleGraph_rootedTreeOfIsTree_adj_iff hK a b).symm }
  exact ⟨T, ⟨(rootedGraphIsoToSimple T).trans
    ((simpleIsoToGraphIso θ).trans
      ((simpleIsoToGraphIso ψ).trans (GM01.simpleGraphIso G)))⟩⟩

/-- Every finite tree in the exact multigraph interface of IV (1.2) is
isomorphic to the underlying graph of a finite ordered rooted tree. -/
theorem exists_orderedTree_graph_iso {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hG : IsUndirectedTree G) :
    ∃ t : OrderedTree,
      Nonempty (GraphMinor.Iso (rootedGraph t.toRootedTree) G) := by
  obtain ⟨T, ⟨φ⟩⟩ := exists_rootedTree_graph_iso G hV hG
  obtain ⟨t, ⟨ψ⟩⟩ := exists_orderedTree_iso T
  exact ⟨t, ⟨ψ.toGraphIso.trans φ⟩⟩

end GraphMinor.Kruskal
