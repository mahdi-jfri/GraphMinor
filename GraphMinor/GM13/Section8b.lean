module

public import GraphMinor.GM13.Section8a

/-!
# Graph Minors XIII, Section 8 (Part 2): Construction of the Division in (8.6)

This file formalizes the construction of the families `𝒜'` (`coreRawDivision`) and `𝒜`
(`coreDivision`) from a 4-linked core `C` of a society `S = (G, Ω)` in Algorithm (8.6) (pages 96–97),
and proves Claims (1), (2), and (3) of (8.6), establishing that `coreDivision S C` is a division of
`S` (`IsSocietyDivision S (coreDivision S C)`) whose boundaries are cliques of size `≤ 3` in `C`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v} {β' : Type*}

/-! ## Subgraphs in `𝒜'` (`coreRawDivision`) and `𝒜` (`coreDivision`) (page 96) -/

/-- The subgraph of `G` consisting of a single vertex `v` and no edges
(Graph Minors XIII, Section 8, (8.6)(iii), page 96). -/
def singleVertexSubgraph (G : Graph α β) (v : α) : Graph α β :=
  (G.induce {v}).restrict ∅

theorem singleVertexSubgraph_le {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    singleVertexSubgraph G v ≤ G :=
  restrict_le.trans (G.induce_le (singleton_subset_iff.mpr hv))

@[simp]
theorem vertexSet_singleVertexSubgraph (G : Graph α β) (v : α) :
    V(singleVertexSubgraph G v) = {v} := rfl

@[simp]
theorem edgeSet_singleVertexSubgraph (G : Graph α β) (v : α) :
    E(singleVertexSubgraph G v) = ∅ := by
  change E((G.induce {v}).restrict ∅) = ∅
  rw [edgeSet_restrict, inter_empty]

/-- The vertex set of the bridge subgraph associated with a component `K` of `G \ Z`:
`V(K) ∪ {z ∈ Z | ∃ u ∈ V(K), G.Adj u z}` (Graph Minors XIII, Section 8, (8.6)(ii), page 96). -/
def coreBridgeVerts (G : Graph α β) (Z : Set α) (K : Graph α β) : Set α :=
  V(K) ∪ {z ∈ Z | ∃ u ∈ V(K), G.Adj u z}

/-- The edge set of the bridge subgraph associated with a component `K` of `G \ Z`:
all edges of `G` incident with at least one vertex of `V(K)`
(Graph Minors XIII, Section 8, (8.6)(ii), page 96). -/
def coreBridgeEdges (G : Graph α β) (K : Graph α β) : Set β :=
  {e ∈ E(G) | ∃ u ∈ V(K), G.Inc e u}

/-- The bridge subgraph of `G` consisting of a component `K` of `G \ Z`, together with all edges of
`G` between `K` and `Z`, and their ends (Graph Minors XIII, Section 8, (8.6)(ii), page 96). -/
def coreBridgeSubgraph (G : Graph α β) (Z : Set α) (K : Graph α β) : Graph α β :=
  (G.induce (coreBridgeVerts G Z K)).restrict (coreBridgeEdges G K)

@[simp]
theorem vertexSet_coreBridgeSubgraph (G : Graph α β) (Z : Set α) (K : Graph α β) :
    V(coreBridgeSubgraph G Z K) = coreBridgeVerts G Z K := rfl

theorem coreBridgeSubgraph_le {G : Graph α β} {Z : Set α} {K : Graph α β}
    (hZ : Z ⊆ V(G)) (hK : K ∈ graphComponents (deleteVertices G Z)) :
    coreBridgeSubgraph G Z K ≤ G := by
  refine restrict_le.trans (G.induce_le ?_)
  rintro x (hxK | ⟨hxZ, _⟩)
  · exact (hK.1.trans (deleteVertices_le G Z)).vertexSet_mono hxK
  · exact hZ hxZ

theorem edgeSet_coreBridgeSubgraph {G : Graph α β} {Z : Set α} {K : Graph α β}
    (hK : K ∈ graphComponents (deleteVertices G Z)) :
    E(coreBridgeSubgraph G Z K) = coreBridgeEdges G K := by
  change E((G.induce (coreBridgeVerts G Z K)).restrict (coreBridgeEdges G K)) = _
  rw [edgeSet_restrict, inter_eq_right]
  rintro e ⟨heG, u, huK, w, hlink⟩
  refine ⟨u, w, hlink, Or.inl huK, ?_⟩
  by_cases hwZ : w ∈ Z
  · exact Or.inr ⟨hwZ, u, huK, e, hlink⟩
  · left
    have hu_del : u ∈ V(deleteVertices G Z) := hK.1.vertexSet_mono huK
    have hw_del : w ∈ V(deleteVertices G Z) := ⟨hlink.right_mem, hwZ⟩
    have hl_del : (deleteVertices G Z).IsLink e u w := by
      change (G.induce (V(G) \ Z)).IsLink e u w
      rw [induce_isLink]
      exact ⟨hlink, hu_del, hw_del⟩
    exact (mem_graphComponent_iff_of_isLink hK hl_del).mp huK

theorem coreBridgeSubgraph_isLink_iff {G : Graph α β} {Z : Set α} {K : Graph α β}
    (hZ : Z ⊆ V(G)) (hK : K ∈ graphComponents (deleteVertices G Z)) {e : β} {x y : α} :
    (coreBridgeSubgraph G Z K).IsLink e x y ↔ G.IsLink e x y ∧ (x ∈ V(K) ∨ y ∈ V(K)) := by
  constructor
  · intro hl
    have hlG : G.IsLink e x y := hl.mono (coreBridgeSubgraph_le hZ hK)
    have he : e ∈ coreBridgeEdges G K := by
      rw [← edgeSet_coreBridgeSubgraph hK]
      exact hl.edge_mem
    obtain ⟨_, u, huK, w, hluw⟩ := he
    refine ⟨hlG, ?_⟩
    rcases hlG.eq_and_eq_or_eq_and_eq hluw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl huK
    · exact Or.inr huK
  · rintro ⟨hlG, hxK | hyK⟩
    · have he : e ∈ E(coreBridgeSubgraph G Z K) := by
        rw [edgeSet_coreBridgeSubgraph hK]
        exact ⟨hlG.edge_mem, x, hxK, y, hlG⟩
      exact ((coreBridgeSubgraph_le hZ hK).isLink_iff he).mpr hlG
    · have he : e ∈ E(coreBridgeSubgraph G Z K) := by
        rw [edgeSet_coreBridgeSubgraph hK]
        exact ⟨hlG.edge_mem, y, hyK, x, hlG.symm⟩
      exact ((coreBridgeSubgraph_le hZ hK).isLink_iff he).mpr hlG

/-- The raw family `𝒜'` of subgraphs of `S.G` defined from a core `C` in Algorithm (8.6)
(Graph Minors XIII, Section 8, (8.6), page 96):
“Let $\mathcal{A}'$ be the set of all subgraphs $A$ of $G$ such that either
(i) $A$ consists of an edge of $G$ with both ends in $V(C)$, and its ends, or
(ii) $A$ consists of a component of $G \setminus V(C)$, together with all edges of $G$ between this
component and $V(C)$, and their ends, or
(iii) $A$ consists of a vertex $v \in \tilde{\Omega}$ incident with no edges of $G$.” -/
def coreRawDivision (S : Society α β) (C : Graph α β') : Set (Graph α β) :=
  {A : Graph α β |
    (∃ e ∈ E(S.G), (∀ v, S.G.Inc e v → v ∈ V(C)) ∧ A = singleEdgeSubgraph S.G e) ∨
    (∃ K ∈ graphComponents (deleteVertices S.G V(C)), A = coreBridgeSubgraph S.G V(C) K) ∨
    (∃ v ∈ S.Ω.bar, (∀ e ∈ E(S.G), ¬ S.G.Inc e v) ∧ A = singleVertexSubgraph S.G v)}

/-- The division `𝒜` obtained from `𝒜' = coreRawDivision S C` by taking the union of each
equivalence class under `divBoundary S A₁ = divBoundary S A₂`
(Graph Minors XIII, Section 8, (8.6), page 96):
“Finally, say $A_1, A_2 \in \mathcal{A}'$ are *equivalent* if $\partial A_1 = \partial A_2$, let
$\mathcal{A}_1, \dots, \mathcal{A}_k$ be the equivalence classes into which $\mathcal{A}'$ is
partitioned by this relation, and let
$$\mathcal{A} = \left\{ \bigcup(A : A \in \mathcal{A}_i) : 1 \le i \le k \right\}.$$” -/
def coreDivision (S : Society α β) (C : Graph α β') : Set (Graph α β) :=
  {B : Graph α β | ∃ X ∈ (divBoundary S) '' (coreRawDivision S C),
    B = subgraphSUnion S.G {A ∈ coreRawDivision S C | divBoundary S A = X}}

/-! ## Basic Properties of `coreRawDivision S C` -/

theorem sub_of_mem_coreRawDivision {S : Society α β} {C : Graph α β'} (hC : IsCoreOf S C)
    {A : Graph α β} (hA : A ∈ coreRawDivision S C) : A ≤ S.G := by
  rcases hA with ⟨e, _, _, rfl⟩ | ⟨K, hK, rfl⟩ | ⟨v, hv, _, rfl⟩
  · exact singleEdgeSubgraph_le S.G e
  · exact coreBridgeSubgraph_le hC.isTrisecting.subset_V hK
  · exact singleVertexSubgraph_le (S.bar_subset hv)

/-- Every vertex `v ∈ V(C) \ S.Ω.bar` in a 4-linked core `C` is incident with at least one edge of
`S.G`. -/
theorem exists_inc_of_mem_fourLinkedCore_diff_bar {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v : α} (hv : v ∈ V(C) \ S.Ω.bar) :
    ∃ e ∈ E(S.G), S.G.Inc e v := by
  by_contra hno
  push Not at hno
  have hv_iso_C : ∀ e ∈ E(C), ¬ C.Inc e v := by
    rintro e he ⟨w, hl⟩
    have hvw : v ≠ w := IsSimpleGraph.ne_of_isLink hC.isCore.isSimple hl
    obtain ⟨P, hP, _⟩ := (hC.isCore.adj_iff v hv.1 w hl.right_mem hvw).mp ⟨e, hl⟩
    rcases hP with ⟨hPG, W, _, _, _⟩
    cases W with
    | nil _ => exact hvw rfl
    | @cons _ z _ f hlf _ =>
      have hfG : f ∈ E(S.G) := hPG.edgeSet_mono hlf.edge_mem
      exact hno f hfG ⟨z, hlf.mono hPG⟩
  let A : Graph α β' := (C.induce {v}).restrict ∅
  let B : Graph α β' := deleteVertices C {v}
  have hA_le : A ≤ C := restrict_le.trans (C.induce_le (singleton_subset_iff.mpr hv.1))
  have hB_le : B ≤ C := deleteVertices_le C {v}
  have hE_A : E(A) = ∅ := by
    change E((C.induce {v}).restrict ∅) = ∅
    rw [edgeSet_restrict, inter_empty]
  have hE_B : E(B) = E(C) := by
    refine subset_antisymm hB_le.edgeSet_mono fun e he => ?_
    obtain ⟨x, y, hl⟩ := C.exists_isLink_of_mem_edgeSet he
    have hxv : x ≠ v := fun h => hv_iso_C e he ⟨y, h ▸ hl⟩
    have hyv : y ≠ v := fun h => hv_iso_C e he ⟨x, h ▸ hl.symm⟩
    exact ⟨x, y, hl, ⟨hl.left_mem, hxv⟩, ⟨hl.right_mem, hyv⟩⟩
  have hsep : IsGraphSeparation C A B := by
    refine ⟨hA_le, hB_le, ?_, ?_, ?_⟩
    · refine subset_antisymm (union_subset hA_le.vertexSet_mono hB_le.vertexSet_mono) fun z hz => ?_
      by_cases hzv : z = v
      · exact Or.inl hzv
      · exact Or.inr ⟨hz, hzv⟩
    · rw [hE_A, hE_B, empty_union]
    · rw [hE_A]
      exact disjoint_bot_left
  have hinter : V(A) ∩ V(B) = ∅ := by
    ext z
    simp [A, B, deleteVertices]
  have hord : (V(A) ∩ V(B)).ncard ≤ 3 := by rw [hinter, ncard_empty]; omega
  have hbar : S.Ω.bar ⊆ V(B) := fun z hz => ⟨hC.isCore.isTrisecting.bar_subset hz,
    fun hzv => hv.2 (hzv ▸ hz)⟩
  exact (hC.fourLinked v hv.1).2 A B hsep hord hbar ⟨rfl, fun h => h.2 rfl⟩

/-- `⋃ (A : A ∈ coreRawDivision S C) = S.G`. -/
theorem subgraphSUnion_coreRawDivision_eq {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) :
    subgraphSUnion S.G (coreRawDivision S C) = S.G := by
  have hsub : ∀ A ∈ coreRawDivision S C, A ≤ S.G :=
    fun A hA => sub_of_mem_coreRawDivision hC.isCore hA
  refine (Compatible.of_le_le (subgraphSUnion_le hsub) le_rfl).ext ?_ ?_
  · refine subset_antisymm (subgraphSUnion_le hsub).vertexSet_mono fun v hvG => ?_
    rw [vertexSet_subgraphSUnion]
    by_cases hvC : v ∈ V(C)
    · by_cases hinc : ∃ e ∈ E(S.G), S.G.Inc e v
      · obtain ⟨e, heG, w, hlink⟩ := hinc
        by_cases hwC : w ∈ V(C)
        · refine mem_iUnion₂.mpr ⟨singleEdgeSubgraph S.G e,
            Or.inl ⟨e, heG, ?_, rfl⟩, ?_⟩
          · intro z ⟨u, hlz⟩
            rcases hlz.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
          · rw [vertexSet_singleEdgeSubgraph_eq_pair hlink]
            exact Or.inl rfl
        · have hw_del : w ∈ V(deleteVertices S.G V(C)) := ⟨hlink.right_mem, hwC⟩
          obtain ⟨K, hK, hwK⟩ := exists_graphComponent_of_mem hw_del
          refine mem_iUnion₂.mpr ⟨coreBridgeSubgraph S.G V(C) K,
            Or.inr (Or.inl ⟨K, hK, rfl⟩), ?_⟩
          exact Or.inr ⟨hvC, w, hwK, e, hlink.symm⟩
      · push Not at hinc
        have hv_bar : v ∈ S.Ω.bar := by
          by_contra hv_not_bar
          obtain ⟨e, he, hinc_e⟩ := exists_inc_of_mem_fourLinkedCore_diff_bar hC ⟨hvC, hv_not_bar⟩
          exact hinc e he hinc_e
        exact mem_iUnion₂.mpr ⟨singleVertexSubgraph S.G v,
          Or.inr (Or.inr ⟨v, hv_bar, hinc, rfl⟩), rfl⟩
    · have hv_del : v ∈ V(deleteVertices S.G V(C)) := ⟨hvG, hvC⟩
      obtain ⟨K, hK, hvK⟩ := exists_graphComponent_of_mem hv_del
      exact mem_iUnion₂.mpr ⟨coreBridgeSubgraph S.G V(C) K,
        Or.inr (Or.inl ⟨K, hK, rfl⟩), Or.inl hvK⟩
  · refine subset_antisymm (subgraphSUnion_le hsub).edgeSet_mono fun e heG => ?_
    rw [edgeSet_subgraphSUnion hsub]
    obtain ⟨u, w, hlink⟩ := S.G.exists_isLink_of_mem_edgeSet heG
    by_cases huC : u ∈ V(C)
    · by_cases hwC : w ∈ V(C)
      · refine mem_iUnion₂.mpr ⟨singleEdgeSubgraph S.G e, Or.inl ⟨e, heG, ?_, rfl⟩, ?_⟩
        · intro z ⟨x, hlz⟩
          rcases hlz.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        · rw [edgeSet_singleEdgeSubgraph heG]
          rfl
      · have hw_del : w ∈ V(deleteVertices S.G V(C)) := ⟨hlink.right_mem, hwC⟩
        obtain ⟨K, hK, hwK⟩ := exists_graphComponent_of_mem hw_del
        refine mem_iUnion₂.mpr ⟨coreBridgeSubgraph S.G V(C) K,
          Or.inr (Or.inl ⟨K, hK, rfl⟩), ?_⟩
        rw [edgeSet_coreBridgeSubgraph hK]
        exact ⟨heG, w, hwK, u, hlink.symm⟩
    · have hu_del : u ∈ V(deleteVertices S.G V(C)) := ⟨hlink.left_mem, huC⟩
      obtain ⟨K, hK, huK⟩ := exists_graphComponent_of_mem hu_del
      refine mem_iUnion₂.mpr ⟨coreBridgeSubgraph S.G V(C) K,
        Or.inr (Or.inl ⟨K, hK, rfl⟩), ?_⟩
      rw [edgeSet_coreBridgeSubgraph hK]
      exact ⟨heG, u, huK, w, hlink⟩

/-- Every `A ∈ coreRawDivision S C` has a private edge or a private vertex that belongs to no other
member of `coreRawDivision S C`. -/
theorem exists_private_of_mem_coreRawDivision {S : Society α β} {C : Graph α β'}
    (hC : IsCoreOf S C) {A : Graph α β} (hA : A ∈ coreRawDivision S C) :
    (∃ v ∈ V(A), ∀ A' ∈ coreRawDivision S C, A' ≠ A → v ∉ V(A')) ∨
    (∃ e ∈ E(A), ∀ A' ∈ coreRawDivision S C, A' ≠ A → e ∉ E(A')) := by
  rcases hA with ⟨e, heG, hends, rfl⟩ | ⟨K, hK, rfl⟩ | ⟨v, hv_bar, hno_inc, rfl⟩
  · right
    refine ⟨e, by rw [edgeSet_singleEdgeSubgraph heG]; rfl, fun A' hA' hne heA' => ?_⟩
    rcases hA' with ⟨e', _, _, rfl⟩ | ⟨K', hK', rfl⟩ | ⟨v', _, _, rfl⟩
    · have hee' : e = e' := heA'.2
      exact hne (hee' ▸ rfl)
    · rw [edgeSet_coreBridgeSubgraph hK'] at heA'
      obtain ⟨_, u, huK', hinc⟩ := heA'
      exact (hK'.1.vertexSet_mono huK').2 (hends u hinc)
    · rw [edgeSet_singleVertexSubgraph] at heA'
      exact heA'
  · left
    obtain ⟨u, huK⟩ := hK.2.1.1
    refine ⟨u, Or.inl huK, fun A' hA' hne huA' => ?_⟩
    have hu_not_C : u ∉ V(C) := (hK.1.vertexSet_mono huK).2
    rcases hA' with ⟨e', he'G, hends', rfl⟩ | ⟨K', hK', rfl⟩ | ⟨v', hv'_bar, _, rfl⟩
    · obtain ⟨x, y, hl⟩ := S.G.exists_isLink_of_mem_edgeSet he'G
      rw [vertexSet_singleEdgeSubgraph_eq_pair hl] at huA'
      rcases huA' with rfl | rfl
      · exact hu_not_C (hends' u ⟨y, hl⟩)
      · exact hu_not_C (hends' u ⟨x, hl.symm⟩)
    · rcases huA' with huK' | ⟨huC, _⟩
      · have hKK' : K = K' := isGraphComponent_eq_of_mem_inter hK hK' ⟨u, huK, huK'⟩
        exact hne (hKK' ▸ rfl)
      · exact hu_not_C huC
    · rw [vertexSet_singleVertexSubgraph, mem_singleton_iff] at huA'
      exact hu_not_C (huA' ▸ hC.isTrisecting.bar_subset hv'_bar)
  · left
    refine ⟨v, rfl, fun A' hA' hne hvA' => ?_⟩
    rcases hA' with ⟨e', he'G, _, rfl⟩ | ⟨K', hK', rfl⟩ | ⟨v', _, _, rfl⟩
    · obtain ⟨x, y, hl⟩ := S.G.exists_isLink_of_mem_edgeSet he'G
      rw [vertexSet_singleEdgeSubgraph_eq_pair hl] at hvA'
      rcases hvA' with rfl | rfl
      · exact hno_inc e' he'G ⟨y, hl⟩
      · exact hno_inc e' he'G ⟨x, hl.symm⟩
    · rcases hvA' with hvK' | ⟨_, u, _, e', hl⟩
      · exact (hK'.1.vertexSet_mono hvK').2 (hC.isTrisecting.bar_subset hv_bar)
      · exact hno_inc e' hl.edge_mem ⟨u, hl.symm⟩
    · rw [vertexSet_singleVertexSubgraph, mem_singleton_iff] at hvA'
      exact hne (hvA' ▸ rfl)

/-- Distinct members `A₁ ≠ A₂` of `coreRawDivision S C` are edge-disjoint and satisfy
`V(A₁) ∩ V(A₂) ⊆ V(C)`. -/
theorem disjoint_edges_and_inter_subset_core_of_mem_coreRawDivision
    {S : Society α β} {C : Graph α β'} (hC : IsCoreOf S C)
    {A₁ A₂ : Graph α β} (hA₁ : A₁ ∈ coreRawDivision S C) (hA₂ : A₂ ∈ coreRawDivision S C)
    (hne : A₁ ≠ A₂) :
    Disjoint E(A₁) E(A₂) ∧ V(A₁) ∩ V(A₂) ⊆ V(C) := by
  refine ⟨disjoint_left.mpr fun e he₁ he₂ => ?_, fun v ⟨hv₁, hv₂⟩ => ?_⟩
  · rcases hA₁ with ⟨e₁, _, hends₁, rfl⟩ | ⟨K₁, hK₁, rfl⟩ | ⟨v₁, _, _, rfl⟩
    · have hee₁ : e = e₁ := he₁.2
      subst hee₁
      rcases hA₂ with ⟨e₂, _, _, rfl⟩ | ⟨K₂, hK₂, rfl⟩ | ⟨v₂, _, _, rfl⟩
      · have hee₂ : e = e₂ := he₂.2
        exact hne (hee₂ ▸ rfl)
      · rw [edgeSet_coreBridgeSubgraph hK₂] at he₂
        obtain ⟨_, u, huK₂, hinc⟩ := he₂
        exact (hK₂.1.vertexSet_mono huK₂).2 (hends₁ u hinc)
      · rw [edgeSet_singleVertexSubgraph] at he₂
        exact he₂
    · rw [edgeSet_coreBridgeSubgraph hK₁] at he₁
      obtain ⟨heG, u₁, huK₁, w₁, hl₁⟩ := he₁
      rcases hA₂ with ⟨e₂, _, hends₂, rfl⟩ | ⟨K₂, hK₂, rfl⟩ | ⟨v₂, _, _, rfl⟩
      · have hee₂ : e = e₂ := he₂.2
        subst hee₂
        exact (hK₁.1.vertexSet_mono huK₁).2 (hends₂ u₁ ⟨w₁, hl₁⟩)
      · rw [edgeSet_coreBridgeSubgraph hK₂] at he₂
        obtain ⟨_, u₂, huK₂, w₂, hl₂⟩ := he₂
        rcases hl₁.eq_and_eq_or_eq_and_eq hl₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hKK : K₁ = K₂ := isGraphComponent_eq_of_mem_inter hK₁ hK₂ ⟨u₁, huK₁, huK₂⟩
          exact hne (hKK ▸ rfl)
        · have hl_del : (deleteVertices S.G V(C)).IsLink e u₁ w₁ := by
            change (S.G.induce (V(S.G) \ V(C))).IsLink e u₁ w₁
            rw [induce_isLink]
            exact ⟨hl₁, hK₁.1.vertexSet_mono huK₁, hK₂.1.vertexSet_mono huK₂⟩
          have hw₁_K₁ : w₁ ∈ V(K₁) := (mem_graphComponent_iff_of_isLink hK₁ hl_del).mp huK₁
          have hKK : K₁ = K₂ := isGraphComponent_eq_of_mem_inter hK₁ hK₂ ⟨w₁, hw₁_K₁, huK₂⟩
          exact hne (hKK ▸ rfl)
      · rw [edgeSet_singleVertexSubgraph] at he₂
        exact he₂
    · rw [edgeSet_singleVertexSubgraph] at he₁
      exact he₁.elim
  · by_contra hv_not_C
    rcases hA₁ with ⟨e₁, he₁G, hends₁, rfl⟩ | ⟨K₁, hK₁, rfl⟩ | ⟨v₁, hv₁_bar, _, rfl⟩
    · obtain ⟨x, y, hl⟩ := S.G.exists_isLink_of_mem_edgeSet he₁G
      rw [vertexSet_singleEdgeSubgraph_eq_pair hl] at hv₁
      rcases hv₁ with rfl | rfl
      · exact hv_not_C (hends₁ v ⟨y, hl⟩)
      · exact hv_not_C (hends₁ v ⟨x, hl.symm⟩)
    · have hvK₁ : v ∈ V(K₁) := by
        rcases hv₁ with hvK₁ | ⟨hvC, _⟩
        · exact hvK₁
        · exact (hv_not_C hvC).elim
      rcases hA₂ with ⟨e₂, he₂G, hends₂, rfl⟩ | ⟨K₂, hK₂, rfl⟩ | ⟨v₂, hv₂_bar, _, rfl⟩
      · obtain ⟨x, y, hl⟩ := S.G.exists_isLink_of_mem_edgeSet he₂G
        rw [vertexSet_singleEdgeSubgraph_eq_pair hl] at hv₂
        rcases hv₂ with rfl | rfl
        · exact hv_not_C (hends₂ v ⟨y, hl⟩)
        · exact hv_not_C (hends₂ v ⟨x, hl.symm⟩)
      · have hvK₂ : v ∈ V(K₂) := by
          rcases hv₂ with hvK₂ | ⟨hvC, _⟩
          · exact hvK₂
          · exact (hv_not_C hvC).elim
        have hKK : K₁ = K₂ := isGraphComponent_eq_of_mem_inter hK₁ hK₂ ⟨v, hvK₁, hvK₂⟩
        exact hne (hKK ▸ rfl)
      · rw [vertexSet_singleVertexSubgraph, mem_singleton_iff] at hv₂
        exact hv_not_C (hv₂ ▸ hC.isTrisecting.bar_subset hv₂_bar)
    · rw [vertexSet_singleVertexSubgraph, mem_singleton_iff] at hv₁
      exact hv_not_C (hv₁ ▸ hC.isTrisecting.bar_subset hv₁_bar)

/-! ## Claims (1), (2), and (3) of Algorithm (8.6) (pages 96–97) -/

/-- **Graph Minors XIII, (8.6), Claim (1)** (Section 8, page 96):
“(1) *For each $A \in \mathcal{A}'$, $|V(A) \cap V(C)| \le 3$ and there are $|V(A) \cap V(C)|$
mutually vertex-disjoint paths of $G$ between $V(A) \cap V(C)$ and $\tilde{\Omega}$.*” -/
theorem lemma_8_6_claim_1 {S : Society α β} {C : Graph α β'} (hC : IsFourLinkedCore S C)
    {A : Graph α β} (hA : A ∈ coreRawDivision S C) :
    (V(A) ∩ V(C)).ncard ≤ 3 ∧
      ∃ P : Fin (V(A) ∩ V(C)).ncard → Graph α β,
        Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
        ∀ i : Fin (V(A) ∩ V(C)).ncard,
          ∃ s ∈ V(A) ∩ V(C), ∃ t ∈ S.Ω.bar, IsGraphPathWithEnds S.G (P i) s t ∧
            V(P i) ∩ (V(A) ∩ V(C)) = {s} ∧ V(P i) ∩ S.Ω.bar = {t} := by
  classical
  have hcard : (V(A) ∩ V(C)).ncard ≤ 3 := by
    rcases hA with ⟨e, heG, _, rfl⟩ | ⟨K, hK, rfl⟩ | ⟨v, _, _, rfl⟩
    · obtain ⟨u, w, hl⟩ := S.G.exists_isLink_of_mem_edgeSet heG
      have hsub : V(singleEdgeSubgraph S.G e) ∩ V(C) ⊆ {u, w} := by
        rw [vertexSet_singleEdgeSubgraph_eq_pair hl]
        exact inter_subset_left
      have hle : (V(singleEdgeSubgraph S.G e) ∩ V(C)).ncard ≤ ({u, w} : Set α).ncard :=
        ncard_le_ncard hsub ((finite_singleton w).insert u)
      have hpair : ({u, w} : Set α).ncard ≤ 2 := (ncard_insert_le u {w}).trans (by simp)
      omega
    · obtain ⟨v₀, hv₀K⟩ := hK.2.1.1
      have hv₀_del : v₀ ∈ V(deleteVertices S.G V(C)) := hK.1.vertexSet_mono hv₀K
      have hsub_att : V(coreBridgeSubgraph S.G V(C) K) ∩ V(C) ⊆
          {z ∈ V(C) | ∃ P : Graph α β, IsGraphPathWithEnds S.G P v₀ z ∧ V(P) ∩ V(C) = {z}} := by
        rintro z ⟨hz_bridge, hzC⟩
        rcases hz_bridge with hzK | ⟨_, u, huK, e, hlink⟩
        · exact ((hK.1.vertexSet_mono hzK).2 hzC).elim
        · refine ⟨hzC, ?_⟩
          obtain ⟨W_K⟩ := hK.2.1.2 v₀ hv₀K u huK
          obtain ⟨P_K, hP_K, hVP_K, _⟩ := exists_isGraphPathWithEnds_of_walk W_K
          have hP_K_G : IsGraphPathWithEnds S.G P_K v₀ u :=
            hP_K.mono (hK.1.trans (deleteVertices_le S.G V(C)))
          have hP_K_disj_C : Disjoint V(P_K) V(C) := by
            rw [disjoint_left]
            intro x hxP hxC
            exact (hK.1.vertexSet_mono (hP_K.le.vertexSet_mono hxP)).2 hxC
          have huz : u ≠ z := fun h =>
            (hK.1.vertexSet_mono huK).2 (h ▸ hzC)
          let P_e := singleEdgeSubgraph S.G e
          have hP_e : IsGraphPathWithEnds S.G P_e u z :=
            (isGraphPathWithEnds_singleEdgeSubgraph huz hlink).mono (singleEdgeSubgraph_le S.G e)
          have hinter_uz : V(P_K) ∩ V(P_e) = {u} := by
            rw [vertexSet_singleEdgeSubgraph_eq_pair hlink]
            ext x
            simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
            refine ⟨fun ⟨hxP, hx_uz⟩ => ?_, fun h => h.symm ▸ ⟨hP_K.right_mem, Or.inl rfl⟩⟩
            rcases hx_uz with rfl | rfl
            · rfl
            · exact (disjoint_left.mp hP_K_disj_C hxP hzC).elim
          let P := subgraphUnion S.G P_K P_e
          have hP : IsGraphPathWithEnds S.G P v₀ z := hP_K_G.subgraphUnion hP_e hinter_uz
          refine ⟨P, hP, ?_⟩
          ext x
          simp only [P, P_e, vertexSet_subgraphUnion, vertexSet_singleEdgeSubgraph_eq_pair hlink,
            mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
          refine ⟨fun ⟨hx, hxC⟩ => ?_, fun h => h.symm ▸ ⟨Or.inr (Or.inr rfl), hzC⟩⟩
          rcases hx with hxP | rfl | rfl
          · exact (disjoint_left.mp hP_K_disj_C hxP hxC).elim
          · exact (disjoint_left.mp hP_K_disj_C hP_K.right_mem hxC).elim
          · rfl
      have hfin_att :
          {z ∈ V(C) | ∃ P : Graph α β, IsGraphPathWithEnds S.G P v₀ z ∧ V(P) ∩ V(C) = {z}}.Finite :=
        S.finite_V.subset (fun z hz => hC.isCore.isTrisecting.subset_V hz.1)
      exact (ncard_le_ncard hsub_att hfin_att).trans
        (hC.isCore.isTrisecting.attach_ncard_le_three v₀ hv₀_del)
    · have hsub : V(singleVertexSubgraph S.G v) ∩ V(C) ⊆ {v} := inter_subset_left
      exact (ncard_le_ncard hsub (finite_singleton v)).trans (by simp)
  refine ⟨hcard, ?_⟩
  let X := V(A) ∩ V(C)
  let CS := coreSociety S C hC.isCore
  have hX_sub : X ⊆ V(C) := inter_subset_right
  have hfin_V : V(C).Finite := CS.finite_V
  have : Finite V(C) := hfin_V.to_subtype
  rcases exists_fromToPaths_or_graphSeparation hX_sub CS.bar_subset X.ncard with
    ⟨Q_C, hQ_disj, hQ_paths⟩ | ⟨A_C, B_C, hsep_C, _, hX_AC, hbar_BC, hlt_ord⟩
  · have hQ_simple : ∀ i : Fin X.ncard, ∃ s ∈ X, ∃ t ∈ S.Ω.bar,
        IsGraphPathWithEnds C (Q_C i) s t ∧ V(Q_C i) ∩ X = {s} ∧ V(Q_C i) ∩ S.Ω.bar = {t} := by
      intro i
      obtain ⟨s, t, hpath, hX_eq, hY_eq⟩ := hQ_paths i
      have hs : s ∈ X := (hX_eq ▸ rfl : s ∈ V(Q_C i) ∩ X).2
      have ht : t ∈ S.Ω.bar := (hY_eq ▸ rfl : t ∈ V(Q_C i) ∩ S.Ω.bar).2
      exact ⟨s, hs, t, ht, hpath, hX_eq, hY_eq⟩
    choose s hs t ht hQ_path hQ_X hQ_bar using hQ_simple
    have hstep : ∀ i : Fin X.ncard,
        ∃ P_i : Graph α β, IsGraphPathWithEnds S.G P_i (s i) (t i) ∧
          V(P_i) ∩ V(C) ⊆ V(Q_C i) ∧
          ∀ z ∈ V(P_i) \ V(C), ∃ u ∈ V(Q_C i), ∃ v ∈ V(Q_C i), u ≠ v ∧ (Q_C i).Adj u v ∧
            ∃ R : Graph α β, IsGraphPathWithEnds S.G R u v ∧ V(R) ∩ V(C) = {u, v} ∧ z ∈ V(R) := by
      intro i
      rcases hQ_path i with ⟨hQi_le, W_i, _, hV_Qi, hE_Qi⟩
      have hwalk_lift : ∀ {u v : α} (W : GraphWalk C u v),
          (∀ x ∈ W.support, x ∈ V(Q_C i)) →
          (∀ e ∈ W.edges, e ∈ E(Q_C i)) →
          ∃ W_G : GraphWalk S.G u v,
            (∀ z ∈ W_G.support, z ∈ V(C) → z ∈ W.support) ∧
            (∀ z ∈ W_G.support, z ∉ V(C) →
              ∃ a ∈ V(Q_C i), ∃ b ∈ V(Q_C i), a ≠ b ∧ (Q_C i).Adj a b ∧
                ∃ R : Graph α β, IsGraphPathWithEnds S.G R a b ∧
                  V(R) ∩ V(C) = {a, b} ∧ z ∈ V(R)) := by
        intro u v W
        induction W with
        | @nil x hx =>
          intro _ _
          refine ⟨.nil (hC.isCore.isTrisecting.subset_V hx), ?_, ?_⟩
          · intro z hz _
            simpa using hz
          · intro z hz hz_not_C
            simp only [GraphWalk.support_nil, List.mem_singleton] at hz
            exact (hz_not_C (hz ▸ hx)).elim
        | @cons x y w e hl rest ih =>
          intro hsupp hedges
          have hxy : x ≠ y := IsSimpleGraph.ne_of_isLink hC.isCore.isSimple hl
          obtain ⟨R, hR, hR_C⟩ :=
            (hC.isCore.adj_iff x hl.left_mem y hl.right_mem hxy).mp ⟨e, hl⟩
          obtain ⟨W_R, hW_R⟩ := hR.exists_walk_in Subset.rfl
          obtain ⟨W_rest, hW_rest_C, hW_rest_out⟩ := ih
            (fun z hz => hsupp z (List.mem_cons_of_mem _ hz))
            (fun f hf => hedges f (List.mem_cons_of_mem _ hf))
          refine ⟨W_R.append W_rest, ?_, ?_⟩
          · intro z hz hzC
            rcases (GraphWalk.mem_support_append W_R W_rest).mp hz with hz1 | hz2
            · have hz_xy : z ∈ ({x, y} : Set α) := hR_C ▸ ⟨hW_R hz1, hzC⟩
              rcases hz_xy with rfl | rfl
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ rest.start_mem_support
            · exact List.mem_cons_of_mem _ (hW_rest_C z hz2 hzC)
          · intro z hz hz_not_C
            rcases (GraphWalk.mem_support_append W_R W_rest).mp hz with hz1 | hz2
            · have he_Qi : e ∈ E(Q_C i) := hedges e List.mem_cons_self
              have hl_Qi : (Q_C i).IsLink e x y := (hQi_le.isLink_iff he_Qi).mpr hl
              exact ⟨x, hl_Qi.left_mem, y, hl_Qi.right_mem, hxy, ⟨e, hl_Qi⟩,
                R, hR, hR_C, hW_R hz1⟩
            · exact hW_rest_out z hz2 hz_not_C
      obtain ⟨W_C, hs_WC, he_WC⟩ := exists_walk_up_of_le hQi_le W_i
      obtain ⟨W_G, hWG_C, hWG_out⟩ := hwalk_lift W_C
        (fun x hx => by rw [hV_Qi, mem_ofPred_eq, ← hs_WC]; exact hx)
        (fun e he => by rw [hE_Qi, mem_ofPred_eq, ← he_WC]; exact he)
      obtain ⟨P_i, hP_i, hVP_i, _⟩ := exists_isGraphPathWithEnds_of_walk W_G
      refine ⟨P_i, hP_i, fun z ⟨hzP, hzC⟩ => ?_, fun z ⟨hzP, hz_not_C⟩ =>
        hWG_out z (hVP_i hzP) hz_not_C⟩
      rw [hV_Qi, mem_ofPred_eq, ← hs_WC]
      exact hWG_C z (hVP_i hzP) hzC
    choose P hP_path hP_sub_Q hP_out using hstep
    refine ⟨P, fun i j hij => disjoint_left.mpr fun z hz_i hz_j => ?_, fun i => ?_⟩
    · by_cases hzC : z ∈ V(C)
      · exact disjoint_left.mp (hQ_disj hij) (hP_sub_Q i ⟨hz_i, hzC⟩) (hP_sub_Q j ⟨hz_j, hzC⟩)
      · obtain ⟨u₁, hu₁, v₁, hv₁, hne₁, _, R₁, hR₁, hR₁_C, hzR₁⟩ := hP_out i z ⟨hz_i, hzC⟩
        obtain ⟨u₂, hu₂, v₂, hv₂, hne₂, _, R₂, hR₂, hR₂_C, hzR₂⟩ := hP_out j z ⟨hz_j, hzC⟩
        have hdisj_ends : Disjoint ({u₁, v₁} : Set α) {u₂, v₂} := by
          refine (hQ_disj hij).mono ?_ ?_
          · rintro x (rfl | rfl) <;> assumption
          · rintro x (rfl | rfl) <;> assumption
        have hdisj_R := disjoint_core_jumps hC.isCore hR₁ hR₁_C hne₁ hR₂ hR₂_C hne₂ hdisj_ends
        exact disjoint_left.mp hdisj_R hzR₁ hzR₂
    · refine ⟨s i, hs i, t i, ht i, hP_path i, ?_, ?_⟩
      · refine subset_antisymm (fun z ⟨hzP, hzX⟩ => ?_)
          (singleton_subset_iff.mpr ⟨(hP_path i).left_mem, hs i⟩)
        have hzQ : z ∈ V(Q_C i) := hP_sub_Q i ⟨hzP, hX_sub hzX⟩
        rw [← hQ_X i]
        exact ⟨hzQ, hzX⟩
      · refine subset_antisymm (fun z ⟨hzP, hz_bar⟩ => ?_)
          (singleton_subset_iff.mpr ⟨(hP_path i).right_mem, ht i⟩)
        have hzQ : z ∈ V(Q_C i) := hP_sub_Q i ⟨hzP, CS.bar_subset hz_bar⟩
        rw [← hQ_bar i]
        exact ⟨hzQ, hz_bar⟩
  · exfalso
    have hord_le : (V(A_C) ∩ V(B_C)).ncard ≤ 3 := (Nat.le_of_lt hlt_ord).trans hcard
    have hVA_sub_VB : V(A_C) ⊆ V(B_C) := by
      intro v hvA
      by_contra hv_not_B
      exact (hC.fourLinked v (hsep_C.1.vertexSet_mono hvA)).2 A_C B_C hsep_C hord_le hbar_BC
        ⟨hvA, hv_not_B⟩
    have hX_sub_inter : X ⊆ V(A_C) ∩ V(B_C) := fun x hx => ⟨hX_AC hx, hVA_sub_VB (hX_AC hx)⟩
    have hle : X.ncard ≤ (V(A_C) ∩ V(B_C)).ncard :=
      ncard_le_ncard hX_sub_inter (hfin_V.subset (inter_subset_left.trans hsep_C.1.vertexSet_mono))
    omega

/-- Any walk in `S.G` from `u ∈ V(B)` to `v ∈ S.Ω.bar` meets `divBoundary S B`. -/
theorem exists_mem_divBoundary_of_walk_to_bar {S : Society α β} {B : Graph α β} (hB : B ≤ S.G)
    {u v : α} (hu : u ∈ V(B)) (hv : v ∈ S.Ω.bar) (W : GraphWalk S.G u v) :
    ∃ z ∈ W.support, z ∈ divBoundary S B := by
  induction W with
  | @nil x _ =>
    exact ⟨x, List.mem_singleton_self x, hu, Or.inl hv⟩
  | @cons x y w e hl rest ih =>
    by_cases hyB : y ∈ V(B)
    · obtain ⟨z, hz_supp, hz_bd⟩ := ih hyB hv
      exact ⟨z, List.mem_cons_of_mem _ hz_supp, hz_bd⟩
    · refine ⟨x, List.mem_cons_self, hu, Or.inr ⟨e, ⟨hl.edge_mem, fun heB => ?_⟩, y, hl⟩⟩
      exact hyB (((hB.isLink_iff heB).mpr hl).right_mem)

/-- General boundary equality lemma used in Claims (2) and (3) of (8.6): if `B ≤ S.G`,
`X ⊆ V(B)`, `divBoundary S B ⊆ X`, and there are `|X|` mutually vertex-disjoint paths in `S.G`
between `X` and `S.Ω.bar`, then `divBoundary S B = X`. -/
theorem eq_divBoundary_of_subset_of_disjoint_paths {S : Society α β} {B : Graph α β}
    {X : Set α} (hB : B ≤ S.G) (hX_sub_B : X ⊆ V(B)) (hbd_sub_X : divBoundary S B ⊆ X)
    {P : Fin X.ncard → Graph α β} (hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hP_paths : ∀ i : Fin X.ncard,
      ∃ s ∈ X, ∃ t ∈ S.Ω.bar, IsGraphPathWithEnds S.G (P i) s t) :
    divBoundary S B = X := by
  classical
  have hhit : ∀ i : Fin X.ncard, ∃ z ∈ V(P i), z ∈ divBoundary S B := by
    intro i
    obtain ⟨s, hsX, t, ht_bar, hPi⟩ := hP_paths i
    obtain ⟨W_Pi, hW_Pi⟩ := hPi.exists_walk_in Subset.rfl
    obtain ⟨z, hz_supp, hz_bd⟩ :=
      exists_mem_divBoundary_of_walk_to_bar hB (hX_sub_B hsX) ht_bar W_Pi
    exact ⟨z, hW_Pi hz_supp, hz_bd⟩
  choose z hz_P hz_bd using hhit
  have hz_inj : Function.Injective z := by
    intro i j hij
    by_contra hne
    exact disjoint_left.mp (hP_disj hne) (hz_P i) (hij ▸ hz_P j)
  have hfin_X : X.Finite := S.finite_V.subset (hX_sub_B.trans hB.vertexSet_mono)
  have hfin_bd : (divBoundary S B).Finite := hfin_X.subset hbd_sub_X
  have hcard_le : X.ncard ≤ (divBoundary S B).ncard := by
    have hsub_range : range z ⊆ divBoundary S B := by rintro _ ⟨i, rfl⟩; exact hz_bd i
    have hcard_range : (range z).ncard = X.ncard := by
      rw [ncard_range_of_injective hz_inj, Nat.card_fin]
    rw [← hcard_range]
    exact ncard_le_ncard hsub_range hfin_bd
  exact eq_of_subset_of_ncard_le hbd_sub_X hcard_le hfin_X

/-- **Graph Minors XIII, (8.6), Claim (2)** (Section 8, page 97):
“(2) *For each $A \in \mathcal{A}'$, $V(A) \cap V(C) = \partial A$.*” -/
theorem lemma_8_6_claim_2 {S : Society α β} {C : Graph α β'} (hC : IsFourLinkedCore S C)
    {A : Graph α β} (hA : A ∈ coreRawDivision S C) :
    V(A) ∩ V(C) = divBoundary S A := by
  have hA_le : A ≤ S.G := sub_of_mem_coreRawDivision hC.isCore hA
  have hbd_sub : divBoundary S A ⊆ V(A) ∩ V(C) := by
    rintro v ⟨hvA, hv_bar | ⟨e, ⟨heG, he_not_A⟩, w, hlink⟩⟩
    · exact ⟨hvA, hC.isCore.isTrisecting.bar_subset hv_bar⟩
    · refine ⟨hvA, ?_⟩
      rcases hA with ⟨e₀, he₀G, hends₀, rfl⟩ | ⟨K, hK, rfl⟩ | ⟨v₀, hv₀_bar, _, rfl⟩
      · obtain ⟨x, y, hl₀⟩ := S.G.exists_isLink_of_mem_edgeSet he₀G
        rw [vertexSet_singleEdgeSubgraph_eq_pair hl₀] at hvA
        rcases hvA with rfl | rfl
        · exact hends₀ v ⟨y, hl₀⟩
        · exact hends₀ v ⟨x, hl₀.symm⟩
      · rcases hvA with hvK | ⟨hvC, _⟩
        · exfalso
          apply he_not_A
          rw [edgeSet_coreBridgeSubgraph hK]
          exact ⟨heG, v, hvK, w, hlink⟩
        · exact hvC
      · rw [vertexSet_singleVertexSubgraph, mem_singleton_iff] at hvA
        exact hvA ▸ hC.isCore.isTrisecting.bar_subset hv₀_bar
  obtain ⟨_, P, hP_disj, hP_paths⟩ := lemma_8_6_claim_1 hC hA
  exact (eq_divBoundary_of_subset_of_disjoint_paths hA_le inter_subset_left hbd_sub hP_disj
    (fun i => by
      obtain ⟨s, hs, t, ht, hPi, _, _⟩ := hP_paths i
      exact ⟨s, hs, t, ht, hPi⟩)).symm

/-- **Graph Minors XIII, (8.6), Claim (3)** (Section 8, page 97):
“(3) *Let $X \subseteq V(G)$, let $\mathcal{B} = \{A \in \mathcal{A}' : \partial A = X\}$, and let
$B = \bigcup(A : A \in \mathcal{B})$. Then $\partial B = X$, if $\mathcal{B} \ne \emptyset$.*” -/
theorem lemma_8_6_claim_3 {S : Society α β} {C : Graph α β'} (hC : IsFourLinkedCore S C)
    {X : Set α} (hℬ : {A ∈ coreRawDivision S C | divBoundary S A = X}.Nonempty) :
    divBoundary S (subgraphSUnion S.G {A ∈ coreRawDivision S C | divBoundary S A = X}) = X := by
  let ℬ := {A ∈ coreRawDivision S C | divBoundary S A = X}
  let B := subgraphSUnion S.G ℬ
  have hsub_ℬ : ∀ A ∈ ℬ, A ≤ S.G := fun A hA => sub_of_mem_coreRawDivision hC.isCore hA.1
  have hB_le : B ≤ S.G := subgraphSUnion_le hsub_ℬ
  obtain ⟨A₀, hA₀_raw, hA₀_bd⟩ := hℬ
  have hX_sub_B : X ⊆ V(B) := by
    rw [← hA₀_bd]
    intro v hv
    rw [vertexSet_subgraphSUnion]
    exact mem_iUnion₂.mpr ⟨A₀, ⟨hA₀_raw, hA₀_bd⟩, hv.1⟩
  have hbd_sub_X : divBoundary S B ⊆ X := by
    rintro v ⟨hvB, hv_bar | ⟨e, ⟨heG, he_not_B⟩, hinc⟩⟩
    · rw [vertexSet_subgraphSUnion] at hvB
      obtain ⟨A, ⟨_, hA_bd⟩, hvA⟩ := mem_iUnion₂.mp hvB
      rw [← hA_bd]
      exact ⟨hvA, Or.inl hv_bar⟩
    · rw [vertexSet_subgraphSUnion] at hvB
      obtain ⟨A, ⟨hA_raw, hA_bd⟩, hvA⟩ := mem_iUnion₂.mp hvB
      rw [← hA_bd]
      refine ⟨hvA, Or.inr ⟨e, ⟨heG, fun heA => he_not_B ?_⟩, hinc⟩⟩
      rw [edgeSet_subgraphSUnion hsub_ℬ]
      exact mem_iUnion₂.mpr ⟨A, ⟨hA_raw, hA_bd⟩, heA⟩
  have hX_eq_AC : V(A₀) ∩ V(C) = X := (lemma_8_6_claim_2 hC hA₀_raw).trans hA₀_bd
  obtain ⟨_, hex_P⟩ := lemma_8_6_claim_1 hC hA₀_raw
  rw [hX_eq_AC] at hex_P
  obtain ⟨P, hP_disj, hP_paths⟩ := hex_P
  exact eq_divBoundary_of_subset_of_disjoint_paths hB_le hX_sub_B hbd_sub_X hP_disj
    (fun i => by
      obtain ⟨s, hs, t, ht, hPi, _, _⟩ := hP_paths i
      exact ⟨s, hs, t, ht, hPi⟩)

/-! ## Internal Paths and Clique Property of Boundaries -/

/-- For each `A ∈ coreRawDivision S C` and all `u, v ∈ divBoundary S A`, there is a path of `A`
between `u` and `v` with no internal vertex in `divBoundary S A`. -/
theorem internal_path_of_mem_coreRawDivision {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {A : Graph α β} (hA : A ∈ coreRawDivision S C)
    {u v : α} (hu : u ∈ divBoundary S A) (hv : v ∈ divBoundary S A) :
    ∃ P : Graph α β, IsGraphPathWithEnds A P u v ∧ V(P) ∩ divBoundary S A ⊆ {u, v} := by
  have hbd_eq : divBoundary S A = V(A) ∩ V(C) := (lemma_8_6_claim_2 hC hA).symm
  by_cases huv : u = v
  · subst huv
    let P := singleVertexSubgraph A u
    have hP_le : P ≤ A := singleVertexSubgraph_le hu.1
    have huP : u ∈ V(P) := rfl
    have hP_path : IsGraphPathWithEnds A P u u := by
      refine ⟨hP_le, .nil huP, by simp [GraphWalk.IsSimple], ?_, ?_⟩
      · simp [P]
      · simp [P]
    refine ⟨P, hP_path, ?_⟩
    rw [vertexSet_singleVertexSubgraph, pair_eq_singleton]
    exact inter_subset_left
  · rcases hA with ⟨e, heG, _, rfl⟩ | ⟨K, hK, rfl⟩ | ⟨w, _, _, rfl⟩
    · obtain ⟨x, y, hl⟩ := S.G.exists_isLink_of_mem_edgeSet heG
      have hu_xy : u ∈ ({x, y} : Set α) := by
        rw [← vertexSet_singleEdgeSubgraph_eq_pair hl]; exact hu.1
      have hv_xy : v ∈ ({x, y} : Set α) := by
        rw [← vertexSet_singleEdgeSubgraph_eq_pair hl]; exact hv.1
      have hlink_uv : S.G.IsLink e u v := by
        rcases hu_xy with rfl | rfl <;> rcases hv_xy with rfl | rfl
        · exact (huv rfl).elim
        · exact hl
        · exact hl.symm
        · exact (huv rfl).elim
      refine ⟨singleEdgeSubgraph S.G e,
        isGraphPathWithEnds_singleEdgeSubgraph huv hlink_uv, ?_⟩
      rw [vertexSet_singleEdgeSubgraph_eq_pair hlink_uv]
      exact inter_subset_left
    · have hu_AC : u ∈ V(coreBridgeSubgraph S.G V(C) K) ∩ V(C) := hbd_eq ▸ hu
      have hv_AC : v ∈ V(coreBridgeSubgraph S.G V(C) K) ∩ V(C) := hbd_eq ▸ hv
      have hu_adj : ∃ x ∈ V(K), S.G.Adj x u := by
        rcases hu_AC.1 with huK | ⟨_, x, hxK, h⟩
        · exact ((hK.1.vertexSet_mono huK).2 hu_AC.2).elim
        · exact ⟨x, hxK, h⟩
      have hv_adj : ∃ y ∈ V(K), S.G.Adj y v := by
        rcases hv_AC.1 with hvK | ⟨_, y, hyK, h⟩
        · exact ((hK.1.vertexSet_mono hvK).2 hv_AC.2).elim
        · exact ⟨y, hyK, h⟩
      obtain ⟨x, hxK, e₁, hl₁⟩ := hu_adj
      obtain ⟨y, hyK, e₂, hl₂⟩ := hv_adj
      obtain ⟨W_K⟩ := hK.2.1.2 x hxK y hyK
      obtain ⟨P_K, hP_K, _, _⟩ := exists_isGraphPathWithEnds_of_walk W_K
      have hK_le_A : K ≤ coreBridgeSubgraph S.G V(C) K := by
        rw [(Compatible.of_le_le (hK.1.trans (deleteVertices_le S.G V(C)))
          (coreBridgeSubgraph_le hC.isCore.isTrisecting.subset_V hK)).le_iff]
        refine ⟨subset_union_left, fun f hf => ?_⟩
        rw [edgeSet_coreBridgeSubgraph hK]
        obtain ⟨a, b, hlab⟩ := K.exists_isLink_of_mem_edgeSet hf
        exact ⟨(hK.1.trans (deleteVertices_le S.G V(C))).edgeSet_mono hf,
          a, hlab.left_mem, b, hlab.mono (hK.1.trans (deleteVertices_le S.G V(C)))⟩
      have hP_K_A : IsGraphPathWithEnds (coreBridgeSubgraph S.G V(C) K) P_K x y :=
        hP_K.mono hK_le_A
      have hP_K_disj_C : Disjoint V(P_K) V(C) := by
        rw [disjoint_left]
        intro z hzP hzC
        exact (hK.1.vertexSet_mono (hP_K.le.vertexSet_mono hzP)).2 hzC
      have hl₁_A : (coreBridgeSubgraph S.G V(C) K).IsLink e₁ u x :=
        (coreBridgeSubgraph_isLink_iff hC.isCore.isTrisecting.subset_V hK).mpr
          ⟨hl₁.symm, Or.inr hxK⟩
      have hl₂_A : (coreBridgeSubgraph S.G V(C) K).IsLink e₂ y v :=
        (coreBridgeSubgraph_isLink_iff hC.isCore.isTrisecting.subset_V hK).mpr
          ⟨hl₂, Or.inl hyK⟩
      have hux : u ≠ x := fun h => (hK.1.vertexSet_mono hxK).2 (h ▸ hu_AC.2)
      have hyv : y ≠ v := fun h => (hK.1.vertexSet_mono hyK).2 (h.symm ▸ hv_AC.2)
      let P₁ := singleEdgeSubgraph (coreBridgeSubgraph S.G V(C) K) e₁
      let P₂ := singleEdgeSubgraph (coreBridgeSubgraph S.G V(C) K) e₂
      have hP₁ : IsGraphPathWithEnds (coreBridgeSubgraph S.G V(C) K) P₁ u x :=
        (isGraphPathWithEnds_singleEdgeSubgraph hux hl₁_A).mono (singleEdgeSubgraph_le _ e₁)
      have hP₂ : IsGraphPathWithEnds (coreBridgeSubgraph S.G V(C) K) P₂ y v :=
        (isGraphPathWithEnds_singleEdgeSubgraph hyv hl₂_A).mono (singleEdgeSubgraph_le _ e₂)
      have hinter₁ : V(P₁) ∩ V(P_K) = {x} := by
        rw [vertexSet_singleEdgeSubgraph_eq_pair hl₁_A]
        ext z
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        refine ⟨fun ⟨hz₁, hzK⟩ => ?_, fun h => h.symm ▸ ⟨Or.inr rfl, hP_K.left_mem⟩⟩
        rcases hz₁ with rfl | rfl
        · exact (disjoint_left.mp hP_K_disj_C hzK hu_AC.2).elim
        · rfl
      have hP₁K : IsGraphPathWithEnds (coreBridgeSubgraph S.G V(C) K)
          (subgraphUnion (coreBridgeSubgraph S.G V(C) K) P₁ P_K) u y :=
        hP₁.subgraphUnion hP_K_A hinter₁
      have hinter₂ : V(subgraphUnion (coreBridgeSubgraph S.G V(C) K) P₁ P_K) ∩ V(P₂) = {y} := by
        rw [vertexSet_subgraphUnion, vertexSet_singleEdgeSubgraph_eq_pair hl₁_A,
          vertexSet_singleEdgeSubgraph_eq_pair hl₂_A]
        ext z
        simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
        refine ⟨fun ⟨hz₁, hz₂⟩ => ?_, fun h => h.symm ▸ ⟨Or.inr hP_K.right_mem, Or.inl rfl⟩⟩
        rcases hz₂ with rfl | rfl
        · rfl
        · rcases hz₁ with (rfl | rfl) | hzK
          · exact (huv rfl).elim
          · exact ((hK.1.vertexSet_mono hxK).2 hv_AC.2).elim
          · exact (disjoint_left.mp hP_K_disj_C hzK hv_AC.2).elim
      let P := subgraphUnion (coreBridgeSubgraph S.G V(C) K)
        (subgraphUnion (coreBridgeSubgraph S.G V(C) K) P₁ P_K) P₂
      have hP : IsGraphPathWithEnds (coreBridgeSubgraph S.G V(C) K) P u v :=
        hP₁K.subgraphUnion hP₂ hinter₂
      refine ⟨P, hP, ?_⟩
      rw [hbd_eq]
      rintro z ⟨hzP, _, hzC⟩
      simp only [P, P₁, P₂, vertexSet_subgraphUnion, vertexSet_singleEdgeSubgraph_eq_pair hl₁_A,
        vertexSet_singleEdgeSubgraph_eq_pair hl₂_A, mem_union, mem_insert_iff,
        mem_singleton_iff] at hzP
      rcases hzP with ((rfl | rfl) | hzK) | (rfl | rfl)
      · exact Or.inl rfl
      · exact ((hK.1.vertexSet_mono hxK).2 hzC).elim
      · exact (disjoint_left.mp hP_K_disj_C hzK hzC).elim
      · exact ((hK.1.vertexSet_mono hyK).2 hzC).elim
      · exact Or.inr rfl
    · have hu_w : u = w := hu.1
      have hv_w : v = w := hv.1
      exact (huv (hu_w.trans hv_w.symm)).elim

/-- Theorem: `coreDivision S C` is a division of `S` (`IsSocietyDivision S (coreDivision S C)`)
whenever `C` is a 4-linked core of `S` (Graph Minors XIII, Section 8, (8.6), pages 96–97). -/
theorem isSocietyDivision_coreDivision {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) :
    IsSocietyDivision S (coreDivision S C) := by
  have hsub_raw : ∀ A ∈ coreRawDivision S C, A ≤ S.G :=
    fun A hA => sub_of_mem_coreRawDivision hC.isCore hA
  have hB_le : ∀ ⦃B : Graph α β⦄, B ∈ coreDivision S C → B ≤ S.G := by
    rintro B ⟨X, _, rfl⟩
    exact subgraphSUnion_le (fun A hA => hsub_raw A hA.1)
  have hB_bd : ∀ ⦃B : Graph α β⦄, B ∈ coreDivision S C →
      ∃ A₀ ∈ coreRawDivision S C,
        B = subgraphSUnion S.G {A ∈ coreRawDivision S C | divBoundary S A = divBoundary S A₀} ∧
        divBoundary S B = divBoundary S A₀ := by
    rintro B ⟨X, ⟨A₀, hA₀_raw, rfl⟩, rfl⟩
    refine ⟨A₀, hA₀_raw, rfl, ?_⟩
    exact lemma_8_6_claim_3 hC ⟨A₀, hA₀_raw, rfl⟩
  have hB_inter_C : ∀ ⦃B : Graph α β⦄, B ∈ coreDivision S C → V(B) ∩ V(C) = divBoundary S B := by
    intro B hB
    obtain ⟨A₀, hA₀_raw, hB_eq, hB_bd_eq⟩ := hB_bd hB
    rw [hB_bd_eq, hB_eq]
    ext v
    simp only [vertexSet_subgraphSUnion, mem_inter_iff, mem_iUnion, exists_prop]
    refine ⟨fun ⟨⟨A, ⟨hA_raw, hA_bd⟩, hvA⟩, hvC⟩ => ?_,
      fun hv => ⟨⟨A₀, ⟨hA₀_raw, rfl⟩, hv.1⟩, ((lemma_8_6_claim_2 hC hA₀_raw).symm ▸ hv).2⟩⟩
    rw [← hA_bd, ← lemma_8_6_claim_2 hC hA_raw]
    exact ⟨hvA, hvC⟩
  refine
    { sub_of_mem := hB_le
      sUnion_eq := ?_
      edge_disjoint := ?_
      vertex_inter_eq := ?_
      boundary_ncard_le_three := ?_
      disjoint_paths_to_bar := ?_
      internal_path := ?_
      boundary_injOn := ?_
      has_private_element := ?_ }
  · refine (Compatible.of_le_le (subgraphSUnion_le hB_le) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion, ← subgraphSUnion_coreRawDivision_eq hC, vertexSet_subgraphSUnion]
      ext v
      simp only [mem_iUnion, exists_prop]
      refine ⟨fun ⟨B, ⟨_, ⟨A₀, hA₀, rfl⟩, hB_eq⟩, hvB⟩ => ?_, fun ⟨A, hA, hvA⟩ => ?_⟩
      · rw [hB_eq, vertexSet_subgraphSUnion] at hvB
        obtain ⟨A, ⟨hA, _⟩, hvA⟩ := mem_iUnion₂.mp hvB
        exact ⟨A, hA, hvA⟩
      · refine ⟨subgraphSUnion S.G {A' ∈ coreRawDivision S C | divBoundary S A' = divBoundary S A},
          ⟨divBoundary S A, ⟨A, hA, rfl⟩, rfl⟩, ?_⟩
        rw [vertexSet_subgraphSUnion]
        exact mem_iUnion₂.mpr ⟨A, ⟨hA, rfl⟩, hvA⟩
    · rw [edgeSet_subgraphSUnion hB_le, ← subgraphSUnion_coreRawDivision_eq hC,
        edgeSet_subgraphSUnion hsub_raw]
      ext e
      simp only [mem_iUnion, exists_prop]
      refine ⟨fun ⟨B, ⟨_, ⟨A₀, hA₀, rfl⟩, hB_eq⟩, heB⟩ => ?_, fun ⟨A, hA, heA⟩ => ?_⟩
      · rw [hB_eq, edgeSet_subgraphSUnion (fun A' hA' => hsub_raw A' hA'.1)] at heB
        obtain ⟨A, ⟨hA, _⟩, heA⟩ := mem_iUnion₂.mp heB
        exact ⟨A, hA, heA⟩
      · refine ⟨subgraphSUnion S.G {A' ∈ coreRawDivision S C | divBoundary S A' = divBoundary S A},
          ⟨divBoundary S A, ⟨A, hA, rfl⟩, rfl⟩, ?_⟩
        rw [edgeSet_subgraphSUnion (fun A' hA' => hsub_raw A' hA'.1)]
        exact mem_iUnion₂.mpr ⟨A, ⟨hA, rfl⟩, heA⟩
  · intro B₁ B₂ hB₁ hB₂ hne
    obtain ⟨A₁, hA₁_raw, hB₁_eq, _⟩ := hB_bd hB₁
    obtain ⟨A₂, hA₂_raw, hB₂_eq, _⟩ := hB_bd hB₂
    rw [hB₁_eq, hB₂_eq,
      edgeSet_subgraphSUnion (fun A hA => hsub_raw A hA.1),
      edgeSet_subgraphSUnion (fun A hA => hsub_raw A hA.1),
      disjoint_left]
    intro e he₁ he₂
    obtain ⟨A₁', ⟨hA₁'_raw, hA₁'_bd⟩, heA₁'⟩ := mem_iUnion₂.mp he₁
    obtain ⟨A₂', ⟨hA₂'_raw, hA₂'_bd⟩, heA₂'⟩ := mem_iUnion₂.mp he₂
    have hne_A' : A₁' ≠ A₂' := fun heq => by
      subst heq
      have hbd_eq : divBoundary S A₁ = divBoundary S A₂ := hA₁'_bd.symm.trans hA₂'_bd
      exact hne (by rw [hB₁_eq, hB₂_eq, hbd_eq])
    exact disjoint_left.mp
      (disjoint_edges_and_inter_subset_core_of_mem_coreRawDivision hC.isCore hA₁'_raw hA₂'_raw hne_A').1
      heA₁' heA₂'
  · intro B₁ B₂ hB₁ hB₂ hne
    obtain ⟨A₁, hA₁_raw, hB₁_eq, hB₁_bd⟩ := hB_bd hB₁
    obtain ⟨A₂, hA₂_raw, hB₂_eq, hB₂_bd⟩ := hB_bd hB₂
    refine subset_antisymm (fun v ⟨hv₁, hv₂⟩ => ?_)
      (inter_subset_inter (fun v hv => hv.1) (fun v hv => hv.1))
    have hv₁' : v ∈ V(B₁) := hv₁
    have hv₂' : v ∈ V(B₂) := hv₂
    rw [hB₁_eq, vertexSet_subgraphSUnion] at hv₁
    rw [hB₂_eq, vertexSet_subgraphSUnion] at hv₂
    obtain ⟨A₁', ⟨hA₁'_raw, hA₁'_bd⟩, hvA₁'⟩ := mem_iUnion₂.mp hv₁
    obtain ⟨A₂', ⟨hA₂'_raw, hA₂'_bd⟩, hvA₂'⟩ := mem_iUnion₂.mp hv₂
    have hne_A' : A₁' ≠ A₂' := fun heq => by
      subst heq
      have hbd_eq : divBoundary S A₁ = divBoundary S A₂ := hA₁'_bd.symm.trans hA₂'_bd
      exact hne (by rw [hB₁_eq, hB₂_eq, hbd_eq])
    have hvC : v ∈ V(C) :=
      (disjoint_edges_and_inter_subset_core_of_mem_coreRawDivision hC.isCore hA₁'_raw hA₂'_raw hne_A').2
        ⟨hvA₁', hvA₂'⟩
    exact ⟨hB_inter_C hB₁ ▸ ⟨hv₁', hvC⟩, hB_inter_C hB₂ ▸ ⟨hv₂', hvC⟩⟩
  · intro B hB
    obtain ⟨A₀, hA₀_raw, _, hB_bd_eq⟩ := hB_bd hB
    rw [hB_bd_eq, ← lemma_8_6_claim_2 hC hA₀_raw]
    exact (lemma_8_6_claim_1 hC hA₀_raw).1
  · intro B hB
    obtain ⟨A₀, hA₀_raw, _, hB_bd_eq⟩ := hB_bd hB
    have h_eq : V(A₀) ∩ V(C) = divBoundary S B :=
      (lemma_8_6_claim_2 hC hA₀_raw).trans hB_bd_eq.symm
    obtain ⟨_, hex_P⟩ := lemma_8_6_claim_1 hC hA₀_raw
    rw [h_eq] at hex_P
    obtain ⟨P, hP_disj, hP_paths⟩ := hex_P
    exact ⟨P, hP_disj, fun i => by
      obtain ⟨s, hs, t, ht, hPi, _, _⟩ := hP_paths i
      exact ⟨s, hs, t, ht, hPi⟩⟩
  · intro B hB u hu v hv
    obtain ⟨A₀, hA₀_raw, hB_eq, hB_bd_eq⟩ := hB_bd hB
    have hu_A₀ : u ∈ divBoundary S A₀ := hB_bd_eq ▸ hu
    have hv_A₀ : v ∈ divBoundary S A₀ := hB_bd_eq ▸ hv
    obtain ⟨P, hP_A₀, hP_inter⟩ := internal_path_of_mem_coreRawDivision hC hA₀_raw hu_A₀ hv_A₀
    have hA₀_le_B : A₀ ≤ B := by
      rw [hB_eq]
      exact le_subgraphSUnion (fun A hA => hsub_raw A hA.1) ⟨hA₀_raw, rfl⟩
    refine ⟨P, hP_A₀.mono hA₀_le_B, ?_⟩
    rwa [hB_bd_eq]
  · intro B₁ hB₁ B₂ hB₂ hbd_eq
    obtain ⟨A₁, _, hB₁_eq, hB₁_bd⟩ := hB_bd hB₁
    obtain ⟨A₂, _, hB₂_eq, hB₂_bd⟩ := hB_bd hB₂
    have hA_bd_eq : divBoundary S A₁ = divBoundary S A₂ :=
      hB₁_bd.symm.trans (hbd_eq.trans hB₂_bd)
    rw [hB₁_eq, hB₂_eq, hA_bd_eq]
  · intro B hB
    obtain ⟨A₀, hA₀_raw, hB_eq, hB_bd_eq⟩ := hB_bd hB
    have hA₀_le_B : A₀ ≤ B := by
      rw [hB_eq]
      exact le_subgraphSUnion (fun A hA => hsub_raw A hA.1) ⟨hA₀_raw, rfl⟩
    rcases exists_private_of_mem_coreRawDivision hC.isCore hA₀_raw with
      ⟨v, hvA₀, hv_priv⟩ | ⟨e, heA₀, he_priv⟩
    · left
      refine ⟨v, hA₀_le_B.vertexSet_mono hvA₀, fun B' hB' hne hvB' => ?_⟩
      obtain ⟨A₁, _, hB'_eq, hB'_bd⟩ := hB_bd hB'
      rw [hB'_eq, vertexSet_subgraphSUnion] at hvB'
      obtain ⟨A', ⟨hA'_raw, hA'_bd⟩, hvA'⟩ := mem_iUnion₂.mp hvB'
      have hne_A : A' ≠ A₀ := fun heq => by
        subst heq
        exact hne (by rw [hB_eq, hB'_eq, hA'_bd])
      exact hv_priv A' hA'_raw hne_A hvA'
    · right
      refine ⟨e, hA₀_le_B.edgeSet_mono heA₀, fun B' hB' hne heB' => ?_⟩
      obtain ⟨A₁, _, hB'_eq, _⟩ := hB_bd hB'
      rw [hB'_eq, edgeSet_subgraphSUnion (fun A hA => hsub_raw A hA.1)] at heB'
      obtain ⟨A', ⟨hA'_raw, hA'_bd⟩, heA'⟩ := mem_iUnion₂.mp heB'
      have hne_A : A' ≠ A₀ := fun heq => by
        subst heq
        exact hne (by rw [hB_eq, hB'_eq, hA'_bd])
      exact he_priv A' hA'_raw hne_A heA'

/-- Every division `𝒜` of a society `S` is finite. -/
theorem IsSocietyDivision.finite {S : Society α β} {𝒜 : Set (Graph α β)}
    (hdiv : IsSocietyDivision S 𝒜) : 𝒜.Finite := by
  have hrange : (divBoundary S) '' 𝒜 ⊆ 𝒫 V(S.G) := by
    rintro _ ⟨A, hA, rfl⟩ v hv
    exact (hdiv.sub_of_mem hA).vertexSet_mono hv.1
  exact ((S.finite_V.powerset).subset hrange).of_finite_image hdiv.boundary_injOn

/-- For each `B ∈ coreDivision S C`, `divBoundary S B ⊆ V(C)` and every two distinct vertices in
`divBoundary S B` are adjacent in `C`. -/
theorem boundary_isClique_in_core {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {B : Graph α β} (hB : B ∈ coreDivision S C) :
    divBoundary S B ⊆ V(C) ∧
      ∀ u ∈ divBoundary S B, ∀ v ∈ divBoundary S B, u ≠ v → C.Adj u v := by
  have hdiv := isSocietyDivision_coreDivision hC
  obtain ⟨X, ⟨A₀, hA₀_raw, rfl⟩, rfl⟩ := hB
  let B₀ := subgraphSUnion S.G {A ∈ coreRawDivision S C | divBoundary S A = divBoundary S A₀}
  have hB₀_mem : B₀ ∈ coreDivision S C := ⟨divBoundary S A₀, ⟨A₀, hA₀_raw, rfl⟩, rfl⟩
  have hbd_eq : divBoundary S B₀ = divBoundary S A₀ := lemma_8_6_claim_3 hC ⟨A₀, hA₀_raw, rfl⟩
  have hA₀_C : divBoundary S A₀ = V(A₀) ∩ V(C) := (lemma_8_6_claim_2 hC hA₀_raw).symm
  have hsub_C : divBoundary S B₀ ⊆ V(C) := by
    rw [hbd_eq, hA₀_C]
    exact inter_subset_right
  refine ⟨hsub_C, fun u hu v hv huv => ?_⟩
  have hu_A₀ : u ∈ divBoundary S A₀ := hbd_eq ▸ hu
  have hv_A₀ : v ∈ divBoundary S A₀ := hbd_eq ▸ hv
  obtain ⟨P, hP_A₀, hP_inter⟩ := internal_path_of_mem_coreRawDivision hC hA₀_raw hu_A₀ hv_A₀
  have hA₀_le : A₀ ≤ S.G := sub_of_mem_coreRawDivision hC.isCore hA₀_raw
  have hP_G : IsGraphPathWithEnds S.G P u v := hP_A₀.mono hA₀_le
  have hP_C : V(P) ∩ V(C) = {u, v} := by
    refine subset_antisymm ?_ ?_
    · intro z ⟨hzP, hzC⟩
      have hz_bd : z ∈ divBoundary S A₀ := by
        rw [hA₀_C]
        exact ⟨hP_A₀.le.vertexSet_mono hzP, hzC⟩
      exact hP_inter ⟨hzP, hz_bd⟩
    · rintro z (rfl | rfl)
      · exact ⟨hP_A₀.left_mem, hsub_C hu⟩
      · exact ⟨hP_A₀.right_mem, hsub_C hv⟩
  exact (hC.isCore.adj_iff u (hsub_C hu) v (hsub_C hv) huv).mpr ⟨P, hP_G, hP_C⟩

end GraphMinor.GM13
