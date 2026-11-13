module

public import GraphMinor.GM21.Section11Defs
public import GraphMinor.GM10.Defs
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM10.TreeWidthBasic
import GraphMinor.GM10.Section9
import GraphMinor.Thomas.Translate
import GraphMinor.Thomas.LeanDecomp

/-!
# Graph Minors XXI, Section 11: tree-decompositions and Thomas's theorem

Basic facts about the tree-decompositions of Graph Minors XXI (page 1 of the preprint) and the sets
`W(e)` of page 43, and the start of the proof of (11.2): "By the main result of [14], there is a
linked tree-decomposition $(T, W)$ of $G$, with width $\le w$."

The main result of [14] is Thomas's theorem. We use it in the form of Bellenbaum and Diestel: a
graph with a tree-decomposition of width `≤ w` has a *lean* one of width `≤ w`
(`Thomas.theorem_3`), and in a lean tree-decomposition there are `k` disjoint paths between any
two sets of size `k` in two bags `V_{t₁}, V_{t₂}`, unless some edge of the path of `T` between `t₁`
and `t₂` has a smaller adhesion (`Thomas.TreeDecomp.IsLean`). Graph Minors IV, (5.1)
(`GM04.thomas_5_1`) is derived from the same two facts. Applied to the sets `W(e₁)` and `W(e₂)`,
leanness says that the decomposition is linked.

The bags of a lean decomposition are vertex sets. We put each edge of `G` into one bag that holds
its ends, so the tree-decomposition we get has no edge in two bags
(`exists_linked_treeDecomposition`).
-/

public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10

universe u v w

variable {α : Type u} {β : Type v}

section Basic

variable {ι : Type w} [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
  {W : ι → Hypergraph α β}

/-- A tree-decomposition of Graph Minors X (whose bags share no edges) is a tree-decomposition of
Graph Minors XXI. -/
theorem _root_.GraphMinor.GM10.IsTreeDecomposition.isTreeDecomp21
    (h : IsTreeDecomposition G T W) : IsTreeDecomp21 G T W :=
  ⟨h.isTree, h.le, h.biUnion_eq, h.inter_le⟩

theorem mem_treeDecompSide_vertexSet {e : Sym2 ι} {u : ι} {x : α} :
    x ∈ (treeDecompSide T W e u).vertexSet ↔
      ∃ t, (T.deleteEdges {e}).Reachable u t ∧ x ∈ (W t).vertexSet := by
  classical
  simp [treeDecompSide, Hypergraph.biUnion]

/-- Graph Minors XXI, page 43: "$W(T_1) \cap W(T_2) = W(t_1) \cap W(t_2)$". So
`W(uv) = V(W u) ∩ V(W v)`. -/
theorem IsTreeDecomp21.treeEdgeSet_eq (h : IsTreeDecomp21 G T W) {u v : ι} (hadj : T.Adj u v) :
    treeEdgeSet T W u v = (W u).vertexSet ∩ (W v).vertexSet := by
  ext x
  change x ∈ (treeDecompSide T W s(u, v) u).vertexSet ∩ (treeDecompSide T W s(u, v) v).vertexSet ↔
    _
  rw [mem_inter_iff, mem_treeDecompSide_vertexSet, mem_treeDecompSide_vertexSet]
  constructor
  · rintro ⟨⟨t, ht, hxt⟩, ⟨t', ht', hxt'⟩⟩
    have h1 : OnTreePath T t t' u := onTreePath_of_reachable_deleteEdges h.isTree hadj ht ht'
    rw [Sym2.eq_swap] at ht ht'
    have h2 : OnTreePath T t' t v :=
      onTreePath_of_reachable_deleteEdges h.isTree hadj.symm ht' ht
    exact ⟨(h.inter_le h1).vertexSet_subset ⟨hxt, hxt'⟩,
      (h.inter_le h2).vertexSet_subset ⟨hxt', hxt⟩⟩
  · rintro ⟨hu, hv⟩
    exact ⟨⟨u, SimpleGraph.Reachable.refl _, hu⟩, ⟨v, SimpleGraph.Reachable.refl _, hv⟩⟩

end Basic

/-! ## Disjoint paths -/

/-- Reversing `k` disjoint paths from `X` to `Y` gives `k` disjoint paths from `Y` to `X`. -/
theorem HasDisjointPaths.symm {K : SimpleGraph α} {X Y : Set α} {k : ℕ}
    (h : HasDisjointPaths K X Y k) : HasDisjointPaths K Y X k := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun i ↦
    { first := (P i).last
      last := (P i).first
      walk := (P i).walk.reverse
      isPath := (P i).isPath.reverse
      first_mem := (P i).last_mem
      last_mem := (P i).first_mem }, fun i j hij ↦ ?_⟩
  simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact hP hij

/-- A set `X` with `k` elements has `k` disjoint one-vertex paths from `X` to itself. -/
theorem hasDisjointPaths_self (K : SimpleGraph α) {X : Set α} (hX : X.Finite) {k : ℕ}
    (hk : X.ncard = k) : HasDisjointPaths K X X k := by
  classical
  have hcard : hX.toFinset.card = k := by rw [← ncard_eq_toFinset_card X hX, hk]
  let e : Fin k ≃ hX.toFinset := (hX.toFinset.equivFinOfCardEq hcard).symm
  refine ⟨fun i ↦
    { first := (e i).1
      last := (e i).1
      walk := SimpleGraph.Walk.nil
      isPath := SimpleGraph.Walk.IsPath.nil
      first_mem := hX.mem_toFinset.1 (e i).2
      last_mem := hX.mem_toFinset.1 (e i).2 }, fun i j hij ↦ ?_⟩
  simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, Set.disjoint_iff]
  rintro x ⟨hxi, hxj⟩
  simp only [Set.mem_ofPred_eq] at hxi hxj
  exact hij (e.injective (Subtype.ext (hxi.symm.trans hxj)))

/-! ## A linked tree-decomposition from Thomas's theorem -/

section Thomas

variable {G : Hypergraph α β}

/-- The tree-decomposition of Bellenbaum and Diestel given by the vertex sets of the bags of a
tree-decomposition of Graph Minors XXI. -/
noncomputable def IsTreeDecomp21.toThomas {κ : Type w} [Fintype κ] {T : SimpleGraph κ}
    {W : κ → Hypergraph α β} (h : IsTreeDecomp21 G T W) :
    Thomas.TreeDecomp G.skeleton G.vertexSet κ where
  T := T
  isTree := h.isTree
  bag t := (W t).vertexSet
  iUnion_bag := by
    have := congrArg Hypergraph.vertexSet h.biUnion_eq
    simpa [Hypergraph.biUnion] using this
  adj_mem_bag := by
    rintro x y - - ⟨-, e, hx, hy⟩
    have he : e ∈ G.edgeSet := G.edge_mem_of_inc hx
    rw [← h.biUnion_eq] at he
    simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at he
    obtain ⟨t, het⟩ := he
    refine ⟨t, (W t).vertex_mem_of_inc ((inc_iff_of_le (h.le t) het).2 hx),
      (W t).vertex_mem_of_inc ((inc_iff_of_le (h.le t) het).2 hy)⟩
  inter_subset_bag := by
    intro t₁ t₂ t₃ hp
    exact (h.inter_le hp).vertexSet_subset

/-- The bag at `t` of the tree-decomposition built from a Bellenbaum–Diestel decomposition `D`:
the vertices of the bag `D.bag t`, and the edges `e` of `G` that `Thomas.edgeBag` puts at `t`. -/
noncomputable def thomasBag (hG : G.IsGraph) {m : ℕ}
    (D : Thomas.TreeDecomp G.skeleton G.vertexSet (Fin m)) (t : Fin m) : Hypergraph α β where
  vertexSet := D.bag t
  edgeSet := {e ∈ G.edgeSet | Thomas.edgeBag D hG e = t}
  Inc e x := G.Inc e x ∧ Thomas.edgeBag D hG e = t
  vertex_mem_of_inc := by
    rintro e x ⟨hx, rfl⟩
    exact Thomas.ends_subset_bag_edgeBag D hG (G.edge_mem_of_inc hx) hx
  edge_mem_of_inc := by
    rintro e x ⟨hx, rfl⟩
    exact ⟨G.edge_mem_of_inc hx, rfl⟩
  vertexSet_finite := G.vertexSet_finite.subset (D.bag_subset t)
  edgeSet_finite := G.edgeSet_finite.subset fun _ he ↦ he.1

theorem thomasBag_le (hG : G.IsGraph) {m : ℕ}
    (D : Thomas.TreeDecomp G.skeleton G.vertexSet (Fin m)) (t : Fin m) :
    thomasBag hG D t ≤ G where
  vertexSet_subset := D.bag_subset t
  edgeSet_subset := fun _ he ↦ he.1
  ends_eq e he := by
    ext x
    simp only [ends, mem_ofPred_eq, thomasBag]
    exact ⟨fun hx ↦ ⟨hx, he.2⟩, fun hx ↦ hx.1⟩

/-- The bags `thomasBag` form a tree-decomposition of Graph Minors X (no edge in two bags). -/
theorem isTreeDecomposition_thomasBag (hG : G.IsGraph) {m : ℕ}
    (D : Thomas.TreeDecomp G.skeleton G.vertexSet (Fin m)) :
    IsTreeDecomposition G D.T (thomasBag hG D) where
  isTree := D.isTree
  le := thomasBag_le hG D
  biUnion_eq := by
    refine Hypergraph.ext ?_ ?_ ?_
    · simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, thomasBag]
      exact D.iUnion_bag
    · ext e
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion, thomasBag,
        mem_ofPred_eq]
      exact ⟨fun ⟨_, he, _⟩ ↦ he, fun he ↦ ⟨_, he, rfl⟩⟩
    · funext e x
      simp only [Hypergraph.biUnion, Finset.mem_univ, true_and, thomasBag, eq_iff_iff]
      exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨_, hx, rfl⟩⟩
  edgeSet_inter_eq := by
    intro t t' hne
    ext e
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    exact hne (h₁.symm.trans h₂)
  inter_le := by
    intro t t' t'' hp
    rw [le_iff_of_le (inter_le (thomasBag_le hG D t) (thomasBag_le hG D t''))
      (thomasBag_le hG D t')]
    refine ⟨D.inter_subset_bag hp, ?_⟩
    rintro e ⟨⟨he, h₁⟩, ⟨-, h₂⟩⟩
    have htt : t = t'' := h₁.symm.trans h₂
    subst htt
    have : t' ∈ (SimpleGraph.Walk.nil : D.T.Walk t t).support :=
      hp _ SimpleGraph.Walk.IsPath.nil
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at this
    exact ⟨he, this ▸ h₁⟩

/-- **The main result of [14]**, as (11.2) uses it: a graph of tree-width `≤ w` has a linked
tree-decomposition of width `≤ w`, in which moreover no edge is in two bags. -/
theorem exists_linked_treeDecomposition (hG : G.IsGraph) {w : ℕ} (hw : TreeWidthLE21 G w) :
    ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      IsTreeDecomposition G T W ∧ IsLinkedTreeDecomp G T W ∧
        ∀ t, (W t).vertexSet.ncard ≤ w + 1 := by
  obtain ⟨κ₀, _, T₀, W₀, hTD, hwid⟩ := hw
  obtain ⟨m, D, hlean, hDw⟩ := Thomas.theorem_3 G hTD.toThomas (w := w) hwid
  have hTD' := isTreeDecomposition_thomasBag hG D
  refine ⟨Fin m, inferInstance, D.T, thomasBag hG D, hTD', ?_, hDw⟩
  intro a₁ b₁ a₂ b₂ h₁ h₂ _ _ k hk₁ hk₂ hpath
  have hE : ∀ {s s' : Fin m}, D.T.Adj s s' →
      treeEdgeSet D.T (thomasBag hG D) s s' = D.bag s ∩ D.bag s' :=
    fun hss ↦ hTD'.isTreeDecomp21.treeEdgeSet_eq hss
  rw [hE h₁] at hk₁ ⊢
  rw [hE h₂] at hk₂ ⊢
  rcases hlean a₁ b₂ _ _ k inter_subset_left inter_subset_right hk₁ hk₂ with hP | ⟨s, s', hss, hlt⟩
  · exact hP
  · have := hpath hss
    rw [hE hss.1] at this
    omega

end Thomas

end GM21
end GraphMinor
