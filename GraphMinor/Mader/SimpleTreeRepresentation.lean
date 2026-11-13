module

public import GraphMinor.Kruskal.TreeRepresentation
import GraphMinor.Minor.Basic

/-!
# Ordered representations of finite simple trees

A multigraph isomorphism induces an isomorphism of the underlying simple
graphs. For a finite simple tree, give the vertices finite names, form its
parent tree, and apply the ordered-tree representation. This form can be
applied separately to each connected component of a forest.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

private theorem map_adj {α β γ δ : Type*} {H : Graph α β} {G : Graph γ δ}
    (φ : Iso H G) {x y : V(H)} (h : H.Adj x.val y.val) :
    G.Adj (φ.vertexEquiv x).val (φ.vertexEquiv y).val := by
  obtain ⟨e, he⟩ := h
  exact ⟨φ.edgeEquiv ⟨e, he.edge_mem⟩, (φ.isLink_iff ⟨e, he.edge_mem⟩ x y).mp he⟩

/-- A multigraph isomorphism gives a simple-graph isomorphism on actual
vertices when both multigraphs are loopless. -/
def simpleIsoOfGraphIso {α β γ δ : Type*} {H : Graph α β} {G : Graph γ δ}
    [H.Loopless] [G.Loopless] (φ : Iso H G) : H.toSimpleGraph ≃g G.toSimpleGraph where
  toEquiv := φ.vertexEquiv
  map_rel_iff' := by
    intro x y
    rw [G.toSimpleGraph_adj_iff, H.toSimpleGraph_adj_iff]
    constructor
    · intro h
      obtain ⟨e, he⟩ := h
      let e' := φ.edgeEquiv.symm ⟨e, he.edge_mem⟩
      refine ⟨e'.val, (φ.isLink_iff e' x y).mpr ?_⟩
      simpa only [e', Equiv.apply_symm_apply] using he
    · exact map_adj φ

/-- Every finite simple tree has an ordered representation on vertex
addresses, with an explicit adjacency-preserving vertex equivalence. -/
theorem exists_orderedTree_simple_iso {V : Type*} [Finite V]
    (K : SimpleGraph V) (hK : K.IsTree) :
    ∃ t : OrderedTree, Nonempty ((rootedGraph t.toRootedTree).toSimpleGraph ≃g K) := by
  classical
  let := Fintype.ofFinite V
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let K' := K.comap e
  let ψ : K' ≃g K := SimpleGraph.Iso.comap e K
  have hK' : K'.IsTree := ψ.isTree_iff.mpr hK
  let T := Thomas.rootedTreeOfIsTree hK'
  let θ : Thomas.toSimpleGraph T ≃g K' := {
    toEquiv := Thomas.equivFinOfIsTree hK'
    map_rel_iff' := fun {a b} ↦ (Thomas.toSimpleGraph_rootedTreeOfIsTree_adj_iff hK' a b).symm }
  obtain ⟨t, ⟨φ⟩⟩ := exists_orderedTree_iso T
  let := rootedGraph_simple t.toRootedTree
  let := rootedGraph_simple T
  exact ⟨t, ⟨(simpleIsoOfGraphIso φ.toGraphIso).trans
    ((rootedGraphToSimpleIso T).trans (θ.trans ψ))⟩⟩

end GraphMinor.Mader
