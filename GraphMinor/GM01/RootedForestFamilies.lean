module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.ForestTrees
import GraphMinor.GM01.MinorNonempty
import Mathlib.Data.Set.Card

/-!
# The disjoint families in Part 3

Graph Minors I, Section 5, page 60, chooses disjoint subsets
`X_0, …, X_N` of the target vertex set satisfying (X1) and (X2).
The root set contains the ambient root and has the rooted `H_γ`
minor. Each other set has a `Y_(γ−1)` minor. The structure below
contains precisely these data and conditions. Nonemptiness of the
tree minors bounds the number of other sets by the target vertex count.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The disjoint sets with conditions (X1) and (X2) in GM01,
Section 5, page 60. The other sets are indexed from zero, corresponding
to the paper's `X_1, …, X_N`. No maximality or derived fact is a field. -/
structure RootedForestFamily {α β : Type*} (G : RootedGraph α β) (γ N : ℕ) where
  rootSet : Set α
  otherSet : Fin N → Set α
  root_subset : rootSet ⊆ V(G.graph)
  other_subset : ∀ i, otherSet i ⊆ V(G.graph)
  other_disjoint : Pairwise fun i j ↦ Disjoint (otherSet i) (otherSet j)
  root_disjoint : ∀ i, Disjoint rootSet (otherSet i)
  root_mem : G.root.val ∈ rootSet
  root_minor : HasRootedMinor (binaryRootedTree γ)
    (⟨G.graph.induce rootSet, ⟨G.root.val, root_mem⟩⟩ : RootedGraph α β)
  other_minor : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce (otherSet i))

/-- A rooted `H_γ` model gives a family with no other sets. This
establishes the nonempty choice at the start of GM01 Section 5, page 60. -/
def RootedForestFamily.root_only {α β : Type*} (G : RootedGraph α β) (γ : ℕ)
    (h : HasRootedMinor (binaryRootedTree γ) G) : RootedForestFamily G γ 0 where
  rootSet := V(G.graph)
  otherSet := Fin.elim0
  root_subset := Subset.rfl
  other_subset i := Fin.elim0 i
  other_disjoint i := Fin.elim0 i
  root_disjoint i := Fin.elim0 i
  root_mem := G.root.property
  root_minor := by
    obtain ⟨M⟩ := h
    exact ⟨M.mono (le_of_eq G.graph.induce_vertexSet.symm) rfl⟩
  other_minor i := Fin.elim0 i

/-- Each other set contains a vertex, since its `Y_(γ−1)` minor
contains its centre. -/
theorem RootedForestFamily.other_nonempty {α β : Type*} {G : RootedGraph α β} {γ N : ℕ}
    (F : RootedForestFamily G γ N) (i : Fin N) : (F.otherSet i).Nonempty :=
  minor_vertexSet_nonempty (F.other_minor i) ⟨none, forestTree_centre_mem (γ - 1)⟩

/-- The disjoint family size is bounded by the finite target vertex
count, justifying the maximum choice on page 60 of GM01. -/
theorem RootedForestFamily.card_le {α β : Type*} {G : RootedGraph α β} {γ N : ℕ}
    (F : RootedForestFamily G γ N) (hfin : V(G.graph).Finite) : N ≤ V(G.graph).ncard := by
  classical
  choose f hf using F.other_nonempty
  let e : Fin N ↪ V(G.graph) :=
    { toFun := fun i ↦ ⟨f i, F.other_subset i (hf i)⟩
      inj' := by
        intro i j hij
        by_contra hne
        have heq : f i = f j := congrArg Subtype.val hij
        exact Set.disjoint_left.mp (F.other_disjoint hne) (hf i) (heq.symm ▸ hf j) }
  let : Finite V(G.graph) := hfin.to_subtype
  have h := Nat.card_le_card_of_injective e e.injective
  rwa [Nat.card_fin] at h

end GraphMinor.GM01
