module

public import GraphMinor.GM02.TreeDecomposition
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Branches of a tree-decomposition in Graph Minors II

For II (2.1), the bags containing a vertex outside one fixed bag are joined
by tree paths that avoid that fixed node, by (W3). They therefore lie in
one branch. For (2.2), the edge-coverage condition supplies a common bag
for adjacent vertices. For (2.3), apply (2.2) along a walk avoiding the bag.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v w

/-- Graph Minors II, Section 2, page 311: the branches at `i` are the
connected components of the tree after deleting `i`. -/
abbrev BranchAt {ι : Type w} (T : SimpleGraph ι) (i : ι) :=
  (T.induce ({i}ᶜ : Set ι)).ConnectedComponent

/-- The original tree vertices of a branch after deleting its center. -/
def branchVertices {ι : Type w} {T : SimpleGraph ι} {i : ι} (B : BranchAt T i) : Set ι :=
  Subtype.val '' B.supp

/-- Two branches containing the same original vertex are equal. -/
theorem branch_eq_of_common_vertex {ι : Type w} {T : SimpleGraph ι} {i j : ι}
    {B C : BranchAt T i} (hB : j ∈ branchVertices B) (hC : j ∈ branchVertices C) : B = C := by
  obtain ⟨a, ha, haj⟩ := hB
  obtain ⟨b, hb, hbj⟩ := hC
  have hab : a = b := Subtype.ext (haj.trans hbj.symm)
  change (T.induce ({i}ᶜ : Set ι)).connectedComponentMk a = B at ha
  change (T.induce ({i}ᶜ : Set ι)).connectedComponentMk b = C at hb
  exact ha.symm.trans ((congrArg (T.induce ({i}ᶜ : Set ι)).connectedComponentMk hab).trans hb)

/-- A branch at `i` contains no copy of `i`. -/
theorem ne_center_of_mem_branch {ι : Type w} {T : SimpleGraph ι} {i j : ι}
    {B : BranchAt T i} (h : j ∈ branchVertices B) : j ≠ i := by
  obtain ⟨a, _, rfl⟩ := h
  exact a.property

/-- Graph Minors II, (2.1), page 311:
"For $i \in I$ and $v \in V(G)$, either $v \in X_i$, or there is a branch
of $T$ at $i$ which contains all $j \in I$ with $v \in X_j$."

Choose one bag containing `v` by (W1). Every tree path to another such bag
stays in bags containing `v`, by (W3), and hence avoids `i`. -/
theorem theorem_2_1_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) (v : α) (hv : v ∈ V(G)) :
    v ∈ X i ∨ ∃ B : BranchAt T i, ∀ j, v ∈ X j → j ∈ branchVertices B := by
  by_cases hvi : v ∈ X i
  · exact Or.inl hvi
  · right
    have hcover : v ∈ ⋃ j, X j := hD.iUnion_eq ▸ hv
    obtain ⟨j₀, hvj₀⟩ := Set.mem_iUnion.1 hcover
    have hj₀ : j₀ ≠ i := fun h => hvi (h ▸ hvj₀)
    let B : BranchAt T i := (T.induce ({i}ᶜ : Set ι)).connectedComponentMk ⟨j₀, hj₀⟩
    refine ⟨B, ?_⟩
    intro j hvj
    have hj : j ≠ i := fun h => hvi (h ▸ hvj)
    obtain ⟨p, hp⟩ := hD.isTree.connected.exists_isPath j₀ j
    have havoid : ∀ k ∈ p.support, k ∈ ({i}ᶜ : Set ι) := by
      intro k hk hki
      have hvk := hD.inter_subset
        ((GM10.onTreePath_iff_of_isPath hD.isTree hp).2 hk) ⟨hvj₀, hvj⟩
      exact hvi (hki ▸ hvk)
    have hreach : (T.induce ({i}ᶜ : Set ι)).Reachable ⟨j₀, hj₀⟩ ⟨j, hj⟩ :=
      ⟨p.induce ({i}ᶜ : Set ι) havoid⟩
    exact ⟨⟨j, hj⟩, (ConnectedComponent.sound hreach).symm, rfl⟩

/-- The unique branch `T_i(v)` defined after II (2.1), page 311, for a
vertex outside the bag at `i`. -/
noncomputable def vertexBranch {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) (v : (V(G) \ X i : Set α)) : BranchAt T i :=
  ((theorem_2_1_proof hD i v.val v.property.1).resolve_left v.property.2).choose

/-- Every bag containing `v` belongs to `T_i(v)`. -/
theorem mem_vertexBranch_of_mem_bag {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) (v : (V(G) \ X i : Set α))
    {j : ι} (hvj : v.val ∈ X j) : j ∈ branchVertices (vertexBranch hD i v) :=
  ((theorem_2_1_proof hD i v.val v.property.1).resolve_left v.property.2).choose_spec j hvj

/-- Graph Minors II, (2.2), page 311:
"If $v, v' \notin X_i$ and $v, v'$ are adjacent in $G$ then $T_i(v) = T_i(v')$."

By (W2), both ends lie in one bag. Both branches contain its tree node,
so the branches are equal. -/
theorem theorem_2_2_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι)
    (v v' : (V(G) \ X i : Set α)) (hadj : G.Adj v.val v'.val) :
    vertexBranch hD i v = vertexBranch hD i v' := by
  obtain ⟨e, he⟩ := hadj
  obtain ⟨j, hvj, hvj'⟩ := hD.edge_mem he
  exact branch_eq_of_common_vertex (mem_vertexBranch_of_mem_bag hD i v hvj)
    (mem_vertexBranch_of_mem_bag hD i v' hvj')

/-- Graph Minors II, (2.3), pages 311–312:
"If $v, v \notin X_i$ and are not separated in $G$ by $X_i$, then
$T_i(v) = T_i(v')$."
The print has "$v, v \notin X_i$", a misprint for $v, v' \notin X_i$, which the Lean uses. See
the correction to (2.3) in `corrections/GM02.md`.

Apply (2.2) successively along a walk in the graph after deleting the bag. -/
theorem theorem_2_3_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) (v v' : (V(G) \ X i : Set α))
    (hreach : Relation.ReflTransGen (G.induce (V(G) \ X i)).Adj v.val v'.val) :
    vertexBranch hD i v = vertexBranch hD i v' := by
  have aux : ∀ {a b}, Relation.ReflTransGen (G.induce (V(G) \ X i)).Adj a b →
      ∀ (ha : a ∈ V(G) \ X i) (hb : b ∈ V(G) \ X i),
        vertexBranch hD i ⟨a, ha⟩ = vertexBranch hD i ⟨b, hb⟩ := by
    intro a b h
    induction h with
    | refl => intro _ _; rfl
    | @tail b c _ hbc ih =>
      intro ha hc
      obtain ⟨e, he⟩ := hbc
      have hb : b ∈ V(G) \ X i := he.left_mem
      exact (ih ha hb).trans (theorem_2_2_proof hD i ⟨b, hb⟩ ⟨c, hc⟩ ⟨e, he.1⟩)
  exact aux hreach v.property v'.property

end GraphMinor.GM02
