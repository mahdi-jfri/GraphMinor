module

public import GraphMinor.Mader.SimpleTreeRepresentation
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.EquivFin

/-!
# Representing a finite forest by its ordered tree components

Each connected component of an acyclic simple graph is a tree. Enumerate
the components, represent each by an ordered tree, and combine the vertex
bijections. Vertices in distinct components cannot be adjacent, so the
combined bijection is a graph isomorphism from the disjoint forest.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal SimpleGraph

/-- The simple graph of a family of disjoint ordered trees. Vertices in
different indices have no edges between them. -/
def treeForest {ι : Type*} (t : ι → OrderedTree) :
    SimpleGraph (Σ i, V(rootedGraph (t i).toRootedTree)) where
  Adj x y := ∃ h : x.1 = y.1,
    (rootedGraph (t x.1).toRootedTree).toSimpleGraph.Adj x.2 (h.symm ▸ y.2)
  symm := ⟨by
    rintro ⟨i, p⟩ ⟨j, q⟩ ⟨h, hpq⟩
    cases h
    exact ⟨rfl, hpq.symm⟩⟩
  loopless := ⟨by
    rintro ⟨i, p⟩ ⟨h, hp⟩
    exact (rootedGraph (t i).toRootedTree).toSimpleGraph.loopless.irrefl p hp⟩

/-- A finite acyclic simple graph is isomorphic to a finite indexed family
of ordered trees, including the empty family for an empty graph. -/
theorem exists_treeForest_iso {V : Type*} [Finite V] (K : SimpleGraph V)
    (hK : K.IsAcyclic) :
    ∃ (n : ℕ) (t : Fin n → OrderedTree), Nonempty (treeForest t ≃g K) := by
  classical
  let := Fintype.ofFinite K.ConnectedComponent
  let n := Fintype.card K.ConnectedComponent
  let c : Fin n ≃ K.ConnectedComponent := (Fintype.equivFin K.ConnectedComponent).symm
  have hrep : ∀ i : Fin n, ∃ t : OrderedTree,
      Nonempty ((rootedGraph t.toRootedTree).toSimpleGraph ≃g (c i).toSimpleGraph) := by
    intro i
    exact exists_orderedTree_simple_iso _ (hK.isTree_connectedComponent (c i))
  choose t ht using hrep
  let φ := fun i ↦ Classical.choice (ht i)
  let e : (Σ i, V(rootedGraph (t i).toRootedTree)) ≃ V :=
    (Equiv.sigmaCongr c (fun i ↦ (φ i).toEquiv)).trans
      (Equiv.sigmaFiberEquiv K.connectedComponentMk)
  refine ⟨n, t, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  rintro ⟨i, p⟩ ⟨j, q⟩
  change K.Adj (φ i p).val (φ j q).val ↔ _
  constructor
  · intro hadj
    have hi : K.connectedComponentMk (φ i p).val = c i := (φ i p).property
    have hj : K.connectedComponentMk (φ j q).val = c j := (φ j q).property
    have hij : i = j := c.injective
      (hi.symm.trans ((ConnectedComponent.sound hadj.reachable).trans hj))
    subst j
    refine ⟨rfl, ?_⟩
    exact (φ i).map_adj_iff.mp hadj
  · rintro ⟨hij, hadj⟩
    cases hij
    exact (φ i).map_adj_iff.mpr hadj

end GraphMinor.Mader
