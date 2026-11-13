module

public import GraphMinor.Mader.ForestRepresentation
public import GraphMinor.Mader.ApexForest
import GraphMinor.Kruskal.RootedSimple

/-!
# Edges of the disjoint ordered forest

An ordered-tree edge is named by its child address. Sending it to the
unordered pair consisting of its parent and child gives precisely the
edge set of the simple disjoint forest. Simplicity of each parent tree
ensures injectivity even when the unordered pair is reversed.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

/-- The parent and child of a tree edge are adjacent in the disjoint forest. -/
theorem treeForest_adj_edge {n : ℕ} (t : Fin n → OrderedTree) (i : Fin n)
    (e : E(rootedGraph (t i).toRootedTree)) :
    (treeForest t).Adj ⟨i, (t i).addressParent e⟩ ⟨i, (t i).addressChild e⟩ := by
  let := rootedGraph_simple (t i).toRootedTree
  exact ⟨rfl, ((rootedGraph (t i).toRootedTree).toSimpleGraph_adj_iff _ _).mpr
    ⟨e.val, e.property, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Send a forest edge to the unordered pair of its two ends. -/
def forestEdgePair {n : ℕ} (t : Fin n → OrderedTree) :
    ForestEdge t → (treeForest t).edgeSet
  | ⟨i, e⟩ => ⟨s(⟨i, (t i).addressParent e⟩, ⟨i, (t i).addressChild e⟩),
      treeForest_adj_edge t i e⟩

/-- The pair of ends uniquely determines an edge in the disjoint forest. -/
theorem forestEdgePair_injective {n : ℕ} (t : Fin n → OrderedTree) :
    Function.Injective (forestEdgePair t) := by
  rintro ⟨i, e⟩ ⟨j, f⟩ hef
  rcases Sym2.eq_iff.mp (congrArg Subtype.val hef) with h | h
  · have hij : i = j := congrArg Sigma.fst h.1
    subst j
    have hchild : (t i).addressChild e = (t i).addressChild f := eq_of_heq (Sigma.mk.inj h.2).2
    exact congrArg (Sigma.mk i) (Subtype.ext (congrArg (fun v : V(rootedGraph (t i).toRootedTree) ↦ v.val) hchild))
  · have hij : i = j := congrArg Sigma.fst h.1
    subst j
    have hparent : (t i).addressParent e = (t i).addressChild f := eq_of_heq (Sigma.mk.inj h.1).2
    have hchild : (t i).addressChild e = (t i).addressParent f := eq_of_heq (Sigma.mk.inj h.2).2
    let := rootedGraph_simple (t i).toRootedTree
    have he : (rootedGraph (t i).toRootedTree).IsLink e.val
        ((t i).addressParent e).val ((t i).addressChild e).val := ⟨e.property, Or.inl ⟨rfl, rfl⟩⟩
    have hf : (rootedGraph (t i).toRootedTree).IsLink f.val
        ((t i).addressParent e).val ((t i).addressChild e).val := by
      rw [hparent, hchild]
      exact ⟨f.property, Or.inr ⟨rfl, rfl⟩⟩
    exact congrArg (Sigma.mk i) (Subtype.ext (he.eq hf))

/-- Every edge of the simple disjoint forest is the parent-child pair
of an edge in one ordered component. -/
theorem forestEdgePair_surjective {n : ℕ} (t : Fin n → OrderedTree) :
    Function.Surjective (forestEdgePair t) := by
  rintro ⟨d, hd⟩
  induction d using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨i, p⟩ := x
    obtain ⟨j, q⟩ := y
    obtain ⟨hij, hpq⟩ := hd
    cases hij
    obtain ⟨e, he⟩ := hpq.2
    let e' : E(rootedGraph (t i).toRootedTree) := ⟨e, he.edge_mem⟩
    rcases he.2 with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hp' : p = (t i).addressParent e' := Subtype.ext hp
      have hq' : q = (t i).addressChild e' := Subtype.ext hq
      exact ⟨⟨i, e'⟩, Subtype.ext (Sym2.eq_iff.mpr
        (Or.inl ⟨congrArg (Sigma.mk i) hp'.symm, congrArg (Sigma.mk i) hq'.symm⟩))⟩
    · have hp' : p = (t i).addressChild e' := Subtype.ext hp
      have hq' : q = (t i).addressParent e' := Subtype.ext hq
      exact ⟨⟨i, e'⟩, Subtype.ext (Sym2.eq_iff.mpr
        (Or.inr ⟨congrArg (Sigma.mk i) hq'.symm, congrArg (Sigma.mk i) hp'.symm⟩))⟩

/-- The edge names of the ordered components enumerate exactly the
edges of their simple disjoint forest. -/
noncomputable def forestEdgeEquiv {n : ℕ} (t : Fin n → OrderedTree) :
    ForestEdge t ≃ (treeForest t).edgeSet :=
  Equiv.ofBijective (forestEdgePair t)
    ⟨forestEdgePair_injective t, forestEdgePair_surjective t⟩

end GraphMinor.Mader
