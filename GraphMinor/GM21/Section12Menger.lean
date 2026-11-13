module

public import GraphMinor.GM21.Section11Tree
public import GraphMinor.GM21.Section6Separation
public import GraphMinor.GM21.Section11Three
import GraphMinor.GM10.Section9
import GraphMinor.Menger.Basic
import GraphMinor.GM10.BranchWidth
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, Section 12: disjoint paths through separations

Tools for the proof of (12.2), all from Menger's theorem (`GraphMinor.menger`).

* `hasDisjointPaths_trans`: `k` disjoint paths from `X` to `Y = V(G₁ ∩ G₂)` and from `Y` to `Z`,
  for a separation `(G₁, G₂)` of order `≤ k` with `X ⊆ V(G₁)` and `Z ⊆ V(G₂)`, give `k` disjoint
  paths from `X` to `Z`. This is the paper's "we can pair these paths".
* `exists_separation_of_treeDecomp`: an edge of a tree-decomposition gives a separation whose
  middle is `W(e)`.
* `le_ncard_of_hasDisjointPaths`: `k` disjoint paths between two bags give `|W(e)| ≥ k` for every
  edge `e` of the path of `T` between them.
* `hasDisjointPaths_insert`: from `X ∪ {v}` to `X ∪ {v'}` along an edge `vv'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

theorem hasDisjointPaths_zero (K : SimpleGraph α) (X Y : Set α) : HasDisjointPaths K X Y 0 :=
  ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩

/-- **Pairing paths through a separation.** -/
theorem hasDisjointPaths_trans {G G₁ G₂ : Hypergraph α β} (hs : G.IsSeparation G₁ G₂)
    {X Z : Set α} {k : ℕ} (hX : X ⊆ G₁.vertexSet) (hZ : Z ⊆ G₂.vertexSet)
    (hord : separationOrder G₁ G₂ ≤ k)
    (h₁ : HasDisjointPaths G.skeleton X (G₁ ∩ G₂).vertexSet k)
    (h₂ : HasDisjointPaths G.skeleton (G₁ ∩ G₂).vertexSet Z k) :
    HasDisjointPaths G.skeleton X Z k := by
  have hXG : X ⊆ G.vertexSet := hX.trans hs.left_le.vertexSet_subset
  have hZG : Z ⊆ G.vertexSet := hZ.trans hs.right_le.vertexSet_subset
  have hYG : (G₁ ∩ G₂).vertexSet ⊆ G.vertexSet :=
    fun y hy ↦ hs.left_le.vertexSet_subset hy.1
  refine (menger G X Z hXG hZG k).1 fun H₁ H₂ hH hX₁ hZ₂ ↦ ?_
  have hS₁ : G.IsSeparation (H₁ ∩ G₁) (H₂ ∪ G₂) := (hH.symm.union_inter hs.symm).symm
  have hS₂ : G.IsSeparation (H₁ ∪ G₁) (H₂ ∩ G₂) := hH.union_inter hs
  have k₁ := (menger G X _ hXG hYG k).2 h₁ _ _ hS₁ (fun x hx ↦ ⟨hX₁ hx, hX hx⟩)
    (fun y hy ↦ Or.inr hy.2)
  have k₂ := (menger G _ Z hYG hZG k).2 h₂ _ _ hS₂ (fun y hy ↦ Or.inr hy.1)
    (fun z hz ↦ ⟨hZ₂ hz, hZ hz⟩)
  have hsum := GM10.separationOrder_inter_union_add_union_inter hH hs.symm
  have hcomm : separationOrder G₂ G₁ = separationOrder G₁ G₂ := by
    unfold separationOrder
    exact congrArg Set.ncard (Set.inter_comm _ _)
  omega

/-- Two subgraphs of `G` that together cover `G` give a separation of `G` with the same middle:
remove from the second the edges of the first. -/
theorem exists_separation_of_cover {G H₁ H₂ : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G)
    (hV : H₁.vertexSet ∪ H₂.vertexSet = G.vertexSet) (hE : H₁.edgeSet ∪ H₂.edgeSet = G.edgeSet) :
    ∃ H₂' : Hypergraph α β, G.IsSeparation H₁ H₂' ∧ H₂'.vertexSet = H₂.vertexSet := by
  have hle : subOn G H₂.vertexSet (H₂.edgeSet \ H₁.edgeSet) ≤ G := by
    refine subOn_le fun e he _ x hx ↦ ?_
    rw [h₂.ends_eq e he.1] at hx
    exact H₂.vertex_mem_of_inc hx
  have hV₂ : (subOn G H₂.vertexSet (H₂.edgeSet \ H₁.edgeSet)).vertexSet = H₂.vertexSet :=
    inter_eq_left.2 h₂.vertexSet_subset
  refine ⟨_, ⟨h₁, hle, ?_, ?_⟩, hV₂⟩
  · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (GM10.union_le h₁ hle) le_rfl ?_ ?_
    · change H₁.vertexSet ∪ _ = _
      rw [hV₂, hV]
    · change H₁.edgeSet ∪ (H₂.edgeSet \ H₁.edgeSet) ∩ G.edgeSet = _
      rw [← hE]
      ext e
      constructor
      · rintro (he | ⟨⟨he, -⟩, -⟩)
        exacts [Or.inl he, Or.inr he]
      · rintro (he | he)
        · exact Or.inl he
        · by_cases he1 : e ∈ H₁.edgeSet
          · exact Or.inl he1
          · exact Or.inr ⟨⟨he, he1⟩, Or.inr he⟩
  · ext e
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨he1, ⟨-, he1'⟩, -⟩
    exact he1' he1

section Tree

variable {ι : Type*} [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι} {W : ι → Hypergraph α β}

/-- An edge `uv` of a tree-decomposition gives a separation `(G₁, G₂)` of `G` with
`V(G₁ ∩ G₂) = W(uv)`, where `G₁` contains the bags on the side of `u` and `G₂` those on the side of
`v`. -/
theorem exists_separation_of_treeDecomp (h : IsTreeDecomp21 G T W) {u v : ι} (huv : T.Adj u v) :
    ∃ G₁ G₂ : Hypergraph α β, G.IsSeparation G₁ G₂ ∧
      (G₁ ∩ G₂).vertexSet = treeEdgeSet T W u v ∧
      (∀ t, (T.deleteEdges {s(u, v)}).Reachable u t → (W t).vertexSet ⊆ G₁.vertexSet) ∧
      (∀ t, (T.deleteEdges {s(u, v)}).Reachable v t → (W t).vertexSet ⊆ G₂.vertexSet) := by
  classical
  set H₁ := GM10.treeDecompSide T W s(u, v) u
  set H₂ := GM10.treeDecompSide T W s(u, v) v
  have hle : ∀ x, GM10.treeDecompSide T W s(u, v) x ≤ G := fun x ↦
    GM10.biUnion_le_of_le fun t _ ↦ h.le t
  -- Every vertex of `T` is on one of the two sides.
  have hside : ∀ t, (T.deleteEdges {s(u, v)}).Reachable u t ∨
      (T.deleteEdges {s(u, v)}).Reachable v t := by
    intro t
    by_cases ht : Thomas.OnTreePath T t v u
    · have ht' : ¬ Thomas.OnTreePath T t u v := fun h' ↦
        huv.ne (Thomas.onTreePath_antisymm h.isTree ht h')
      have := reachable_deleteEdges_of_not_onTreePath h.isTree ht'
      rw [Sym2.eq_swap] at this
      exact Or.inl this.symm
    · exact Or.inr (reachable_deleteEdges_of_not_onTreePath h.isTree ht).symm
  have hmemV : ∀ x y, y ∈ (GM10.treeDecompSide T W s(u, v) x).vertexSet ↔
      ∃ t, (T.deleteEdges {s(u, v)}).Reachable x t ∧ y ∈ (W t).vertexSet :=
    fun _ _ ↦ mem_treeDecompSide_vertexSet
  have hmemE : ∀ x e, e ∈ (GM10.treeDecompSide T W s(u, v) x).edgeSet ↔
      ∃ t, (T.deleteEdges {s(u, v)}).Reachable x t ∧ e ∈ (W t).edgeSet := by
    intro x e
    simp [GM10.treeDecompSide, Hypergraph.biUnion]
  have hGV : ∀ y, y ∈ G.vertexSet ↔ ∃ t, y ∈ (W t).vertexSet := by
    intro y
    rw [← h.biUnion_eq]
    simp [Hypergraph.biUnion]
  have hGE : ∀ e, e ∈ G.edgeSet ↔ ∃ t, e ∈ (W t).edgeSet := by
    intro e
    rw [← h.biUnion_eq]
    simp [Hypergraph.biUnion]
  have hcovV : H₁.vertexSet ∪ H₂.vertexSet = G.vertexSet := by
    apply Subset.antisymm (union_subset (hle u).vertexSet_subset (hle v).vertexSet_subset)
    intro y hy
    obtain ⟨t, ht⟩ := (hGV y).1 hy
    rcases hside t with h' | h'
    · exact Or.inl ((hmemV u y).2 ⟨t, h', ht⟩)
    · exact Or.inr ((hmemV v y).2 ⟨t, h', ht⟩)
  have hcovE : H₁.edgeSet ∪ H₂.edgeSet = G.edgeSet := by
    apply Subset.antisymm (union_subset (hle u).edgeSet_subset (hle v).edgeSet_subset)
    intro e he
    obtain ⟨t, ht⟩ := (hGE e).1 he
    rcases hside t with h' | h'
    · exact Or.inl ((hmemE u e).2 ⟨t, h', ht⟩)
    · exact Or.inr ((hmemE v e).2 ⟨t, h', ht⟩)
  obtain ⟨H₂', hs, hV⟩ := exists_separation_of_cover (hle u) (hle v) hcovV hcovE
  refine ⟨H₁, H₂', hs, ?_, ?_, ?_⟩
  · change H₁.vertexSet ∩ H₂'.vertexSet = (H₁ ∩ H₂).vertexSet
    rw [hV]
    rfl
  · exact fun t ht y hy ↦ (hmemV u y).2 ⟨t, ht, hy⟩
  · intro t ht y hy
    rw [hV]
    exact (hmemV v y).2 ⟨t, ht, hy⟩

theorem treeEdgeSet_comm (h : IsTreeDecomp21 G T W) {u v : ι} (huv : T.Adj u v) :
    treeEdgeSet T W u v = treeEdgeSet T W v u := by
  rw [h.treeEdgeSet_eq huv, h.treeEdgeSet_eq huv.symm, inter_comm]

/-- `k` disjoint paths between two bags give `|W(e)| ≥ k` for every edge `e` on the path of `T`
between them. -/
theorem le_ncard_of_hasDisjointPaths (h : IsTreeDecomp21 G T W) {X Y : Set α} {k : ℕ}
    (hk : HasDisjointPaths G.skeleton X Y k) {x y s s' : ι} (hX : X ⊆ (W x).vertexSet)
    (hY : Y ⊆ (W y).vertexSet) (hss : Thomas.OnTreePathEdge T x y s s') :
    k ≤ (treeEdgeSet T W s s').ncard := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges] at hss
  obtain ⟨hadj, hnr⟩ := hss
  obtain ⟨G₁, G₂, hs, hmid, h₁, h₂⟩ := exists_separation_of_treeDecomp h hadj
  have hside : ∀ t, (T.deleteEdges {s(s, s')}).Reachable s t ∨
      (T.deleteEdges {s(s, s')}).Reachable s' t := by
    intro t
    by_cases ht : Thomas.OnTreePath T t s' s
    · have ht' : ¬ Thomas.OnTreePath T t s s' := fun h' ↦
        hadj.ne (Thomas.onTreePath_antisymm h.isTree ht h')
      have := reachable_deleteEdges_of_not_onTreePath h.isTree ht'
      rw [Sym2.eq_swap] at this
      exact Or.inl this.symm
    · exact Or.inr (reachable_deleteEdges_of_not_onTreePath h.isTree ht).symm
  have hord : separationOrder G₁ G₂ = (treeEdgeSet T W s s').ncard := by
    rw [separationOrder, hmid]
  rcases hside x with hx | hx
  · have hy : (T.deleteEdges {s(s, s')}).Reachable s' y := by
      rcases hside y with hy | hy
      · exact absurd (hx.symm.trans hy) hnr
      · exact hy
    rw [← hord]
    exact (menger G X Y (hX.trans ((h₁ x hx).trans hs.left_le.vertexSet_subset))
      (hY.trans ((h₂ y hy).trans hs.right_le.vertexSet_subset)) k).2 hk _ _ hs
      (hX.trans (h₁ x hx)) (hY.trans (h₂ y hy))
  · have hy : (T.deleteEdges {s(s, s')}).Reachable s y := by
      rcases hside y with hy | hy
      · exact hy
      · exact absurd (hx.symm.trans hy) hnr
    rw [← hord]
    exact (menger G Y X (hY.trans ((h₁ y hy).trans hs.left_le.vertexSet_subset))
      (hX.trans ((h₂ x hx).trans hs.right_le.vertexSet_subset)) k).2 (HasDisjointPaths.symm hk) _ _ hs
      (hY.trans (h₁ y hy)) (hX.trans (h₂ x hx))

end Tree

/-- **One step along `P`.** If `G` has an edge with ends `v, v'`, then there are `k` disjoint paths
from `X ∪ {v}` to `X ∪ {v'}`, where `|X| = k - 1` and `v, v' ∉ X`. -/
theorem hasDisjointPaths_insert {G : Hypergraph α β} {X : Set α} {v v' : α} {g : β} {k : ℕ}
    (hX : X ⊆ G.vertexSet) (hXf : X.Finite) (hXk : X.ncard + 1 = k) (hv : v ∉ X) (hv' : v' ∉ X)
    (hg : G.ends g = {v, v'}) :
    HasDisjointPaths G.skeleton (insert v X) (insert v' X) k := by
  have hvG : v ∈ G.vertexSet := G.vertex_mem_of_inc (show v ∈ G.ends g by rw [hg]; simp)
  have hv'G : v' ∈ G.vertexSet := G.vertex_mem_of_inc (show v' ∈ G.ends g by rw [hg]; simp)
  refine (menger G _ _ (insert_subset hvG hX) (insert_subset hv'G hX) k).1
    fun H₁ H₂ hH h₁ h₂ ↦ ?_
  have hXm : X ⊆ (H₁ ∩ H₂).vertexSet := fun x hx ↦
    ⟨h₁ (mem_insert_of_mem _ hx), h₂ (mem_insert_of_mem _ hx)⟩
  have hfin : (H₁ ∩ H₂).vertexSet.Finite := (H₁ ∩ H₂).vertexSet_finite
  by_contra hlt
  push Not at hlt
  have hle : (H₁ ∩ H₂).vertexSet.ncard ≤ X.ncard := by
    change separationOrder H₁ H₂ < k at hlt
    rw [separationOrder] at hlt
    omega
  have heq : (H₁ ∩ H₂).vertexSet = X := (Set.eq_of_subset_of_ncard_le hXm hle hfin).symm
  -- `v` is only on the first side and `v'` only on the second.
  have hv₂ : v ∉ H₂.vertexSet := fun hv₂ ↦ hv (heq ▸ ⟨h₁ (mem_insert v X), hv₂⟩)
  have hv'₁ : v' ∉ H₁.vertexSet := fun hv'₁ ↦ hv' (heq ▸ ⟨hv'₁, h₂ (mem_insert v' X)⟩)
  have hgG : g ∈ G.edgeSet := G.edge_mem_of_inc (show v ∈ G.ends g by rw [hg]; simp)
  rw [← hH.union_eq] at hgG
  rcases hgG with hg₁ | hg₂
  · have := hH.left_le.ends_eq g hg₁
    have hv'g : v' ∈ H₁.ends g := by rw [← this, hg]; simp
    exact hv'₁ (H₁.vertex_mem_of_inc hv'g)
  · have := hH.right_le.ends_eq g hg₂
    have hvg : v ∈ H₂.ends g := by rw [← this, hg]; simp
    exact hv₂ (H₂.vertex_mem_of_inc hvg)

end GM21
end GraphMinor
