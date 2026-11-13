module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Cited
public import GraphMinor.GM04.Main
public import GraphMinor.GM09.Basic
public import GraphMinor.GM13.Section4
public import GraphMinor.Planar.Grid
public import GraphMinor.Thomas.Separator
public import GraphMinor.Thomas.Translate

/-!
# Graph Minors III, Section 1: Introduction

This file formalizes the numbered statements of Section 1 (pages 49–51) of N. Robertson and
P. D. Seymour, *Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984),
49–64:

- Equivalence between the vertex-bag formulation `(T, X)` (`IsTreeDecomposition`,
  `TreeDecompHasWidthLE`) of Section 1 (page 49) and the subgraph-bag formulation `TreeWidthLE`
  (`treeWidthLE_iff_exists_isTreeDecomposition`), and translation to Graph Minors IV
  (`treeWidthLE_gm04_of_treeWidthLE`).
- **(1.1)** (`theorem_1_1`, page 50): if $\mathcal{F}$ is an infinite set of graphs all with
  tree-width $\le w$, then there exist distinct $G, G' \in \mathcal{F}$ such that $G$ is isomorphic
  to a minor of $G'$.

(1.3), (1.4) and (1.5) are proved in `GraphMinor/GM03/Section5.lean`, after (5.3), since the paper
proves (1.4) in Section 5 ("Now we prove (1.4)", page 62).
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM13 GraphMinor.GM21
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂

/-! ## 1. Equivalence of tree-decomposition formulations -/

/-- Every subgraph-bag tree-decomposition `(T, W)` (`IsGraphTreeDecomposition G T W`) induces a
vertex-bag tree-decomposition `(T, fun t => V(W t))` (`IsTreeDecomposition G T (fun t => V(W t))`)
satisfying (W1), (W2), (W3) of Graph Minors III, Section 1 (page 49). -/
lemma isTreeDecomposition_of_isGraphTreeDecomposition {α : Type u} {β : Type v} {ι : Type*}
    [Fintype ι] {G : Graph α β} {T : SimpleGraph ι} {W : ι → Graph α β}
    (hW : IsGraphTreeDecomposition G T W) :
    IsTreeDecomposition G T (fun t => V(W t)) where
  isTree := hW.isTree
  bag_subset t := (hW.le t).vertexSet_mono
  iUnion_bags := by
    have hV := congrArg Graph.vertexSet hW.sUnion_eq
    rw [vertexSet_subgraphSUnion] at hV
    ext v
    rw [← hV, mem_iUnion, mem_iUnion₂]
    exact ⟨fun ⟨t, hv⟩ => ⟨W t, ⟨t, rfl⟩, hv⟩, fun ⟨_, ⟨t, rfl⟩, hv⟩ => ⟨t, hv⟩⟩
  edge_in_bag e u v hl := by
    have hW_mem : ∀ P ∈ Set.range W, P ≤ G := by
      rintro _ ⟨t, rfl⟩
      exact hW.le t
    have hE := congrArg Graph.edgeSet hW.sUnion_eq
    rw [edgeSet_subgraphSUnion hW_mem] at hE
    have he_mem : e ∈ ⋃ P ∈ Set.range W, E(P) := by
      rw [hE]
      exact hl.edge_mem
    rw [mem_iUnion₂] at he_mem
    obtain ⟨_, ⟨t, rfl⟩, het⟩ := he_mem
    obtain ⟨u', v', hlt⟩ := exists_isLink_of_mem_edgeSet het
    have hlG : G.IsLink e u' v' := (hW.le t).2 hlt
    rcases hl.left_eq_or_eq hlG with rfl | rfl
    · have hv_eq : v = v' := hl.right_unique hlG
      subst hv_eq
      exact ⟨t, hlt.left_mem, hlt.right_mem⟩
    · have hv_eq : v = u' := hl.right_unique hlG.symm
      subst hv_eq
      exact ⟨t, hlt.right_mem, hlt.left_mem⟩
  inter_subset_on_path t t' t'' hp := by
    have hle := (hW.inter_le hp).vertexSet_mono
    rwa [vertexSet_subgraphInter] at hle

/-- Every vertex-bag tree-decomposition `(T, X)` (`IsTreeDecomposition G T X`) induces a
subgraph-bag tree-decomposition `(T, fun t => G.induce (X t))` (`IsGraphTreeDecomposition`). -/
lemma isGraphTreeDecomposition_induce_of_isTreeDecomposition {α : Type u} {β : Type v} {ι : Type*}
    [Fintype ι] {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hX : IsTreeDecomposition G T X) :
    IsGraphTreeDecomposition G T (fun t => G.induce (X t)) where
  isTree := hX.isTree
  le t := G.induce_le (hX.bag_subset t)
  sUnion_eq := by
    let W : ι → Graph α β := fun t => G.induce (X t)
    have hW_le : ∀ t : ι, W t ≤ G := fun t => G.induce_le (hX.bag_subset t)
    have hW_mem : ∀ P ∈ Set.range W, P ≤ G := by
      rintro _ ⟨t, rfl⟩
      exact hW_le t
    refine (Compatible.of_le_le (subgraphSUnion_le hW_mem) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion]
      ext v
      rw [mem_iUnion₂, ← hX.iUnion_bags, mem_iUnion]
      exact ⟨fun ⟨_, ⟨t, rfl⟩, hv⟩ => ⟨t, hv⟩, fun ⟨t, hv⟩ => ⟨W t, ⟨t, rfl⟩, hv⟩⟩
    · rw [edgeSet_subgraphSUnion hW_mem]
      ext e
      rw [mem_iUnion₂]
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨t, rfl⟩, he⟩
        exact (hW_le t).edgeSet_mono he
      · intro he
        obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet he
        obtain ⟨t, hu, hv⟩ := hX.edge_in_bag hl
        exact ⟨W t, ⟨t, rfl⟩, ⟨u, v, hl, hu, hv⟩⟩
  inter_le t t' t'' hp := by
    let W : ι → Graph α β := fun s => G.induce (X s)
    have hW_le : ∀ s : ι, W s ≤ G := fun s => G.induce_le (hX.bag_subset s)
    refine (Compatible.of_le_le (subgraphInter_le (hW_le t)) (hW_le t')).le_iff.mpr ⟨?_, ?_⟩
    · rw [vertexSet_subgraphInter]
      exact hX.inter_subset_on_path hp
    · rw [edgeSet_subgraphInter (hW_le t) (hW_le t'')]
      rintro e ⟨⟨u, v, hl, hu_t, hv_t⟩, ⟨u', v', hl', hu'_t'', hv'_t''⟩⟩
      rcases hl.left_eq_or_eq hl' with rfl | rfl
      · have hv_eq : v = v' := hl.right_unique hl'
        subst hv_eq
        exact ⟨u, v, hl, hX.inter_subset_on_path hp ⟨hu_t, hu'_t''⟩,
          hX.inter_subset_on_path hp ⟨hv_t, hv'_t''⟩⟩
      · have hv_eq : v = u' := hl.right_unique hl'.symm
        subst hv_eq
        exact ⟨u, v, hl, hX.inter_subset_on_path hp ⟨hu_t, hv'_t''⟩,
          hX.inter_subset_on_path hp ⟨hv_t, hu'_t''⟩⟩

/-- `TreeWidthLE G w` holds if and only if `G` admits a finite vertex-bag tree-decomposition
`(T, X)` of width at most `w` (`IsTreeDecomposition G T X ∧ TreeDecompHasWidthLE X w`). -/
theorem treeWidthLE_iff_exists_isTreeDecomposition {α : Type u} {β : Type v}
    (G : Graph α β) (w : ℕ) :
    TreeWidthLE G w ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (X : ι → Set α),
        IsTreeDecomposition G T X ∧ TreeDecompHasWidthLE X w := by
  constructor
  · rintro ⟨ι, hfin, T, W, hW, hw⟩
    exact ⟨ι, hfin, T, fun t => V(W t),
      isTreeDecomposition_of_isGraphTreeDecomposition hW, hw⟩
  · rintro ⟨ι, hfin, T, X, hX, hw⟩
    exact ⟨ι, hfin, T, fun t => G.induce (X t),
      isGraphTreeDecomposition_induce_of_isTreeDecomposition hX, hw⟩

/-- Convert a `GM21.Final.TreeWidthLE G w` witness into `GM03.TreeWidthLE G w`. -/
lemma treeWidthLE_of_gm21 {α : Type u} {β : Type v} {G : Graph α β} {w : ℕ}
    (h : GM21.Final.TreeWidthLE G w) : TreeWidthLE G w := by
  rcases h with ⟨ι, hfin, T, W, ⟨h1, h2, h3, h4⟩, hw⟩
  exact ⟨ι, hfin, T, W, ⟨h1, h2, h3, h4⟩, hw⟩

/-- Any finite graph `G` with `TreeWidthLE G w` satisfies
`GM04.TreeWidthLE (Hypergraph.ofGraph G hVG hEG).toRooted w`. -/
lemma treeWidthLE_gm04_of_treeWidthLE {α : Type u} {β : Type v} {G : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) {w : ℕ} (htw : TreeWidthLE G w) :
    GM04.TreeWidthLE (Hypergraph.ofGraph G hVG hEG).toRooted w := by
  rw [treeWidthLE_iff_exists_isTreeDecomposition] at htw
  obtain ⟨ι, hfin, T, X, hX, hw⟩ := htw
  let _ : Fintype ι := hfin
  let H := Hypergraph.ofGraph G hVG hEG
  let D₀ : Thomas.TreeDecomp H.skeleton H.vertexSet ι :=
    { T := T
      isTree := hX.isTree
      bag := X
      iUnion_bag := hX.iUnion_bags
      adj_mem_bag := by
        rintro u v _ _ ⟨hne, e, ⟨u', hlu⟩, ⟨v', hlv⟩⟩
        have hl_uv : G.IsLink e u v := by
          rcases hlv.left_eq_or_eq hlu with h_eq | rfl
          · exact (hne h_eq.symm).elim
          · exact hlu
        exact hX.edge_in_bag hl_uv
      inter_subset_bag := fun t₁ t₂ t₃ hp => hX.inter_subset_on_path hp }
  have hw₀ : D₀.WidthLE w := hw
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let D := D₀.reindex e
  have hw_D : D.WidthLE w := (D₀.reindex_widthLE e).mpr hw₀
  have hG_graph : H.IsGraph := GM13.graphToHypergraph_isGraph G hVG hEG
  exact ⟨Thomas.rootedTreeOfIsTree D.isTree, Thomas.gm04Bags D hG_graph,
    Thomas.isTreeDecomposition_gm04Bags D hG_graph,
    Thomas.widthLE_gm04Bags D hG_graph hw_D⟩

/-! ## 2. Numbered statements of Section 1 (pages 50–51) -/

/-- **Graph Minors III, (1.1)** (Section 1, page 50):
"(1.1) [3]. *If $\mathcal{F}$ is an infinite set of graphs all with tree-width $\le w$, where $w$
is some integer, then there exist $G, G' \in \mathcal{F}$ such that $G$ is isomorphic to a minor
of $G'$.*" -/
theorem theorem_1_1_proof {α : Type u} {β : Type v} (w : ℕ) (ℱ : Set (Graph α β))
    (hℱ : ℱ.Infinite)
    (hV : ∀ G ∈ ℱ, V(G).Finite) (hE : ∀ G ∈ ℱ, E(G).Finite)
    (htw : ∀ G ∈ ℱ, TreeWidthLE G w) :
    ∃ G ∈ ℱ, ∃ G' ∈ ℱ, G ≠ G' ∧ IsIsoMinor G G' := by
  let f : ℕ ↪ ℱ := hℱ.natEmbedding
  have htw_gm04 : ∀ n : ℕ,
      GM04.TreeWidthLE (Hypergraph.ofGraph (f n).1 (hV _ (f n).2) (hE _ (f n).2)).toRooted w :=
    fun n => treeWidthLE_gm04_of_treeWidthLE (hV _ (f n).2) (hE _ (f n).2) (htw _ (f n).2)
  obtain ⟨i, j, hij, hminor⟩ :=
    GM04.theorem_1_5_proved w (fun n => (f n).1)
      (fun n => hV _ (f n).2) (fun n => hE _ (f n).2) htw_gm04
  have hne : (f i).1 ≠ (f j).1 := by
    intro heq
    exact hij.ne (f.injective (Subtype.ext heq))
  exact ⟨(f i).1, (f i).2, (f j).1, (f j).2, hne, hminor⟩

end GraphMinor.GM03
