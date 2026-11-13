module

public import GraphMinor.GM10.Defs
public import GraphMinor.Minor.Model
import GraphMinor.GM10.Section7TreeWidth
import GraphMinor.GM10.TreeWidthBasic

/-!
# Vertex bags and tree-width in Graph Minors II

The bags in II satisfy vertex coverage, edge coverage, and the tree-path
condition. To compare with X, assign each edge to one bag containing its ends.
Conversely, forget the edge assignments of a decomposition in X. These two
constructions preserve the vertex bags and their size bounds. Taking the
natural predecessor of X's width plus one gives II's nonnegative tree-width,
including zero for a graph with no vertices.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Hypergraph SimpleGraph

universe u v w

/-- Graph Minors II, Section 1, page 309, (W1)–(W3): a tree-decomposition
is a tree with vertex bags covering the vertices and both ends of every edge,
whose bags containing any given vertex form a subtree. -/
structure IsTreeDecomposition {α : Type u} {β : Type v} {ι : Type w}
    (G : Graph α β) (T : SimpleGraph ι) (X : ι → Set α) : Prop where
  /-- The indexing graph is a tree. -/
  isTree : T.IsTree
  /-- (W1). -/
  iUnion_eq : (⋃ i, X i) = V(G)
  /-- (W2), including loops and parallel edges. -/
  edge_mem : ∀ ⦃e a b⦄, G.IsLink e a b → ∃ i, a ∈ X i ∧ b ∈ X i
  /-- (W3). -/
  inter_subset : ∀ ⦃i j k⦄, GM10.OnTreePath T i k j → X i ∩ X k ⊆ X j

/-- Graph Minors II, Section 1, pages 309–310: tree-width at most `w`
means that a tree-decomposition has every bag of size at most `w + 1`.
All graphs in the paper, including the indexing tree, are finite. -/
def TreeWidthLE {α : Type u} {β : Type v} (G : Graph α β) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (X : ι → Set α),
    IsTreeDecomposition G T X ∧ ∀ i, (X i).ncard ≤ w + 1

/-- II's vertex bags give the same width bounds as X's hypergraph bags.
The forward construction assigns each edge to one bag. The reverse
construction forgets these assignments. No graph edge is removed. -/
theorem treeWidthLE_iff {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (w : ℕ) :
    TreeWidthLE G w ↔ GM10.treeWidthPlusOne (Hypergraph.ofGraph G hV hE) ≤ w + 1 := by
  constructor
  · rintro ⟨ι, _, T, X, hD, hw⟩
    have hedge : ∀ e ∈ E(G), ∃ i, (Hypergraph.ofGraph G hV hE).ends e ⊆ X i := by
      intro e he
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
      obtain ⟨i, ha, hb⟩ := hD.edge_mem hab
      refine ⟨i, fun z hz => ?_⟩
      rcases Graph.Inc.eq_or_eq_of_isLink hz hab with rfl | rfl
      · exact ha
      · exact hb
    obtain ⟨τ, hτ, hτX⟩ := GM10.exists_treeDecomposition_of_vertex_bags
      (Hypergraph.ofGraph G hV hE) T X hD.isTree hD.iUnion_eq hedge (fun {_ _ _} hp => hD.inter_subset hp)
    apply (GM10.treeWidthPlusOne_le_of_isTreeDecomposition hτ).trans
    let : Nonempty ι := hD.isTree.connected.nonempty
    apply GM10.treeDecompWidthPlusOne_le_iff.2
    intro i
    rw [hτX i]
    exact hw i
  · intro hw
    obtain ⟨ι, _, T, τ, hτ, hwidth⟩ :=
      GM10.exists_treeDecomposition_eq_treeWidthPlusOne (Hypergraph.ofGraph G hV hE)
    refine ⟨ι, inferInstance, T, fun i => (τ i).vertexSet, ?_, ?_⟩
    · refine ⟨hτ.isTree, ?_, ?_, ?_⟩
      · ext a
        exact Set.mem_iUnion.trans hτ.vertex_mem_iff.symm
      · intro e a b hab
        obtain ⟨i, hi⟩ := hτ.edge_mem_iff.1 hab.edge_mem
        have hends := hτ.ends_subset_vertexSet_of_edge_mem hi
        exact ⟨i, hends hab.inc_left, hends hab.inc_right⟩
      · intro i j k hp
        exact (hτ.inter_le hp).vertexSet_subset
    · intro i
      exact (GM10.ncard_vertexSet_le_treeDecompWidthPlusOne τ i).trans (hwidth ▸ hw)

/-- The nonnegative tree-width of II, Section 1, pages 309–310.
X gives the empty graph width `-1`, so use its width plus one and take the
natural predecessor to give II's value zero. -/
noncomputable def treeWidth {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) : ℕ :=
  GM10.treeWidthPlusOne (Hypergraph.ofGraph G hV hE) - 1

/-- The nonnegative width defined using X is exactly the least bound admitted
by the vertex bags of II. This also covers the empty graph. -/
theorem treeWidth_le_iff {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (w : ℕ) :
    treeWidth G hV hE ≤ w ↔ TreeWidthLE G w := by
  rw [treeWidthLE_iff G hV hE w]
  unfold treeWidth
  omega

end GraphMinor.GM02
