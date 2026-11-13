module

public import GraphMinor.GM10.Defs
public import GraphMinor.GM05.Defs
public import GraphMinor.Minor.Model
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM10.TreeWidthBasic

/-!
# Converting vertex bags to a hypergraph tree-decomposition

The definition in Graph Minors X, Section 5, page 168, asks that each
edge belong to exactly one bag. Starting from vertex bags, choose one
bag containing all ends of each edge and assign that edge to it.
This changes no vertex bag and preserves the tree-path condition.
-/

public section

namespace GraphMinor.GM10

open Graph Hypergraph SimpleGraph

universe u v w

/-- Vertex bags covering every vertex and the ends of every edge give a
tree-decomposition as defined in Graph Minors X, Section 5, page 168.
Each edge is assigned to one bag containing all its ends. -/
theorem exists_treeDecomposition_of_vertex_bags
    {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (G : Hypergraph α β) (T : SimpleGraph ι) (χ : ι → Set α)
    (hT : T.IsTree) (hcover : (⋃ t, χ t) = G.vertexSet)
    (hedge : ∀ e ∈ G.edgeSet, ∃ t, G.ends e ⊆ χ t)
    (hpath : ∀ ⦃a b c⦄, OnTreePath T a b c → χ a ∩ χ b ⊆ χ c) :
    ∃ τ : ι → Hypergraph α β,
      IsTreeDecomposition G T τ ∧ ∀ t, (τ t).vertexSet = χ t := by
  classical
  let : Nonempty ι := hT.connected.nonempty
  let f : β → ι := fun e ↦ if he : e ∈ G.edgeSet then (hedge e he).choose
    else Classical.choice inferInstance
  have hf : ∀ e ∈ G.edgeSet, G.ends e ⊆ χ (f e) := by
    intro e he
    simpa only [f, he, ↓reduceDIte] using (hedge e he).choose_spec
  have hχ : ∀ t, χ t ⊆ G.vertexSet := by
    intro t x hx
    rw [← hcover]
    exact Set.mem_iUnion.2 ⟨t, hx⟩
  let τ : ι → Hypergraph α β := fun t ↦ {
    vertexSet := χ t
    edgeSet := {e ∈ G.edgeSet | f e = t}
    Inc := fun e x ↦ G.Inc e x ∧ f e = t
    vertex_mem_of_inc := by
      intro e x hx
      exact hx.2 ▸ hf e (G.edge_mem_of_inc hx.1) hx.1
    edge_mem_of_inc := fun _ _ hx ↦ ⟨G.edge_mem_of_inc hx.1, hx.2⟩
    vertexSet_finite := G.vertexSet_finite.subset (hχ t)
    edgeSet_finite := G.edgeSet_finite.subset (fun _ h ↦ h.1) }
  have hle : ∀ t, τ t ≤ G := by
    intro t
    refine ⟨hχ t, fun _ he ↦ he.1, ?_⟩
    intro e he
    ext x
    change G.Inc e x ↔ (G.Inc e x ∧ f e = t)
    exact ⟨fun hx ↦ ⟨hx, he.2⟩, And.left⟩
  refine ⟨τ, ⟨hT, hle, ?_, ?_, ?_⟩, fun _ ↦ rfl⟩
  · apply Hypergraph.ext
    · simpa only [Hypergraph.biUnion, τ, Finset.mem_univ, Set.iUnion_true] using hcover
    · ext e
      simp only [Hypergraph.biUnion, τ, Finset.mem_univ, Set.iUnion_true,
        Set.mem_iUnion, Set.mem_sep_iff]
      exact ⟨fun ⟨_, he, _⟩ ↦ he, fun he ↦ ⟨f e, he, rfl⟩⟩
    · funext e x
      apply propext
      change (∃ t ∈ Finset.univ, G.Inc e x ∧ f e = t) ↔ G.Inc e x
      exact ⟨fun ⟨_, _, hx, _⟩ ↦ hx, fun hx ↦ ⟨f e, Finset.mem_univ _, hx, rfl⟩⟩
  · intro a b hab
    apply Set.eq_empty_iff_forall_notMem.2
    intro e he
    exact hab (he.1.2.symm.trans he.2.2)
  · intro a c b hp
    refine (le_iff_of_le (GM10.inter_le (hle a) (hle b)) (hle c)).2 ⟨?_, ?_⟩
    · exact hpath hp
    · intro e he
      have hab : a = b := he.1.2.symm.trans he.2.2
      subst b
      -- Edge sets of two distinct bags are disjoint, so only the case a = b remains.
      -- A point on the path from a vertex to itself is that vertex.
      have hc : c = a := by
        have hc_mem := hp (SimpleGraph.Walk.nil : T.Walk a a) (by simp)
        simpa using hc_mem
      exact hc.symm ▸ he.1

/-- A vertex-bag decomposition of the simple graph on the vertices of a
finite graph bounds its GM10 tree-width as well. Loops use any bag
containing their vertex, and parallel edges may be assigned independently. -/
theorem treeWidthPlusOne_le_of_toSimpleGraph_decomposition
    {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    {T : SimpleGraph ι} {χ : ι → Set V(G)} {k : ℕ}
    (hD : GM05.IsTreeDecomposition (SimpleGraph.toSubgraph G.toSimpleGraph le_top) T χ)
    (hk : GM05.WidthLE χ k) :
    treeWidthPlusOne (Hypergraph.ofGraph G hV hE) ≤ k + 1 := by
  classical
  let ψ : ι → Set α := fun t ↦ Subtype.val '' χ t
  have hcover : (⋃ t, ψ t) = V(G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, y, _, rfl⟩ := Set.mem_iUnion.1 hx
      exact y.property
    · intro hx
      have hy : (⟨x, hx⟩ : V(G)) ∈ ⋃ t, χ t := by
        rw [hD.iUnion_eq]
        trivial
      obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hy
      exact Set.mem_iUnion.2 ⟨t, ⟨⟨x, hx⟩, ht, rfl⟩⟩
  have hedge : ∀ e ∈ E(G), ∃ t, (Hypergraph.ofGraph G hV hE).ends e ⊆ ψ t := by
    intro e he
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
    let x' : V(G) := ⟨x, hxy.left_mem⟩
    let y' : V(G) := ⟨y, hxy.right_mem⟩
    have hbag : ∃ t, x' ∈ χ t ∧ y' ∈ χ t := by
      by_cases hsame : x = y
      · have hyx : y' = x' := Subtype.ext hsame.symm
        have hx : x' ∈ ⋃ t, χ t := by rw [hD.iUnion_eq]; trivial
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hx
        exact ⟨t, ht, hyx.symm ▸ ht⟩
      · apply hD.adj_mem
        exact ⟨fun hh ↦ hsame (congrArg Subtype.val hh), ⟨e, hxy⟩⟩
    obtain ⟨t, hxt, hyt⟩ := hbag
    refine ⟨t, fun z hz ↦ ?_⟩
    rcases Graph.Inc.eq_or_eq_of_isLink hz hxy with rfl | rfl
    · exact ⟨x', hxt, rfl⟩
    · exact ⟨y', hyt, rfl⟩
  have hpath : ∀ ⦃a b c⦄, OnTreePath T a b c → ψ a ∩ ψ b ⊆ ψ c := by
    intro a b c hp z hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    obtain ⟨y, hy, heq⟩ := hz.2
    have hyx : y = x := Subtype.ext heq
    exact ⟨x, hD.inter_subset hp ⟨hx, hyx ▸ hy⟩, rfl⟩
  obtain ⟨τ, hτ, hτV⟩ := exists_treeDecomposition_of_vertex_bags
    (Hypergraph.ofGraph G hV hE) T ψ hD.isTree hcover hedge hpath
  apply (treeWidthPlusOne_le_of_isTreeDecomposition hτ).trans
  let : Nonempty ι := hD.isTree.connected.nonempty
  apply treeDecompWidthPlusOne_le_iff.2
  intro t
  rw [hτV t]
  change (Subtype.val '' χ t).ncard ≤ k + 1
  rw [Set.ncard_image_of_injective _ Subtype.val_injective]
  exact hk t

/-- A GM05 width bound for the simple graph of a finite graph also bounds
the GM10 tree-width of the original graph. -/
theorem treeWidthPlusOne_le_of_toSimpleGraph_treeWidthLE
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) {k : ℕ}
    (h : GM05.TreeWidthLE (SimpleGraph.toSubgraph G.toSimpleGraph le_top) k) :
    treeWidthPlusOne (Hypergraph.ofGraph G hV hE) ≤ k + 1 := by
  obtain ⟨ι, _, T, χ, hD, hk⟩ := h
  exact treeWidthPlusOne_le_of_toSimpleGraph_decomposition G hV hE hD hk

end GraphMinor.GM10
