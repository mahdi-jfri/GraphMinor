module

public import GraphMinor.GM13.Section6
public import GraphMinor.GM10.BranchWidth
public import GraphMinor.GM10.TreeWidth
public import GraphMinor.GM10.Section8

/-!
# Graph Minors XIII, Section 3 (Part 1): Branch-width and Balanced Separations (3.1)

This file establishes the bridge between `GraphBranchWidthLE` on `Graph α β` and
`GM10.branchWidth` on `Hypergraph α β`, proves monotonicity of `GraphBranchWidthLE` under
subgraphs, and formalizes Lemma (3.1) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 70–72), following the
tangle duality proof via X (4.3) and X (4.5).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}

/-- View a finite `Graph α β` as a `Hypergraph α β` with the same vertices, edges, and incidence
relation. -/
def graphToHypergraph (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    Hypergraph α β where
  vertexSet := V(G)
  edgeSet := E(G)
  Inc e v := G.Inc e v
  vertex_mem_of_inc _ _ h := h.vertex_mem
  edge_mem_of_inc _ _ h := h.edge_mem
  vertexSet_finite := hV
  edgeSet_finite := hE

/-- Every edge of a graph `G` has 1 or 2 ends in `graphToHypergraph G hV hE`. -/
lemma graphToHypergraph_isGraph (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (graphToHypergraph G hV hE).IsGraph := by
  intro e he
  change {v | G.Inc e v}.Nonempty ∧ {v | G.Inc e v}.ncard ≤ 2
  rcases (G.edge_mem_iff_exists_isLink e).mp he with ⟨x, y, hxy⟩
  have hsub : {v | G.Inc e v} ⊆ ({x, y} : Set α) := by
    rintro v ⟨z, hvz⟩
    rcases G.eq_or_eq_of_isLink_of_isLink hvz hxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (mem_singleton_iff.mpr rfl)
  refine ⟨⟨x, y, hxy⟩, ?_⟩
  exact le_trans (ncard_le_ncard hsub ((finite_singleton y).insert x))
    ((ncard_insert_le x {y}).trans (by simp))

/-- The maximum edge size `γ(G)` of a graph `G` is at most `2`. -/
lemma maxEdgeSize_graphToHypergraph_le_two (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    GM10.maxEdgeSize (graphToHypergraph G hV hE) ≤ 2 := by
  unfold GM10.maxEdgeSize
  by_cases hne : E(G).Nonempty
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨e, he, rfl⟩
    exact (graphToHypergraph_isGraph G hV hE e he).2
  · have hemp : (graphToHypergraph G hV hE).edgeSet = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hemp]

/-- If `E(G)` is nonempty, `1 ≤ maxEdgeSize (graphToHypergraph G hV hE)`. -/
lemma one_le_maxEdgeSize_graphToHypergraph (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hne : E(G).Nonempty) :
    1 ≤ GM10.maxEdgeSize (graphToHypergraph G hV hE) := by
  rcases hne with ⟨e, he⟩
  have h1 : 1 ≤ GM10.edgeSize (graphToHypergraph G hV hE) e := by
    have hends_ne := (graphToHypergraph_isGraph G hV hE e he).1
    exact (ncard_pos ((graphToHypergraph G hV hE).vertexSet_finite.subset
      (fun _ hv => (graphToHypergraph G hV hE).vertex_mem_of_inc hv))).mpr hends_ne
  have hmem : GM10.edgeSize (graphToHypergraph G hV hE) e ∈
      GM10.edgeSize (graphToHypergraph G hV hE) '' (graphToHypergraph G hV hE).edgeSet :=
    ⟨e, he, rfl⟩
  exact h1.trans (le_csSup (hE.image _).bddAbove hmem)

/-- When `τ` and `σ` are inverse bijections between `E(G)` and `leafSet T`, the edge orders in
`IsGraphBranchDecomposition` and `GM10.IsBranchDecomposition` coincide. -/
lemma graphBranchEdgeOrder_eq_branchEdgeOrder {ι : Type*} [Fintype ι]
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (T : SimpleGraph ι) (τ : β → ι) (σ : ι → β)
    (hτ : MapsTo τ E(G) (GM10.leafSet T))
    (hσ : MapsTo σ (GM10.leafSet T) E(G))
    (hinv : InvOn σ τ E(G) (GM10.leafSet T)) (e : Sym2 ι) :
    graphBranchEdgeOrder G T τ e =
      GM10.branchEdgeOrder (graphToHypergraph G hV hE) T σ e := by
  unfold graphBranchEdgeOrder GM10.branchEdgeOrder
  congr 1
  ext v
  simp only [graphToHypergraph, mem_sep_iff]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f₁, hf₁, f₂, hf₂, hnr, hi₁, hi₂⟩
    refine ⟨τ f₁, hτ hf₁, τ f₂, hτ hf₂, hnr, ?_, ?_⟩
    · rwa [hinv.1 hf₁]
    · rwa [hinv.1 hf₂]
  · rintro ⟨t₁, ht₁, t₂, ht₂, hnr, hi₁, hi₂⟩
    refine ⟨σ t₁, hσ ht₁, σ t₂, hσ ht₂, ?_, hi₁, hi₂⟩
    rwa [hinv.2 ht₁, hinv.2 ht₂]

/-- When `τ` and `σ` are inverse bijections between `E(G)` and `leafSet T`, the decomposition widths
in `GM13` and `GM10` coincide. -/
lemma graphBranchDecompWidth_eq_branchDecompWidth {ι : Type*} [Fintype ι]
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (T : SimpleGraph ι) (τ : β → ι) (σ : ι → β)
    (hτ : MapsTo τ E(G) (GM10.leafSet T))
    (hσ : MapsTo σ (GM10.leafSet T) E(G))
    (hinv : InvOn σ τ E(G) (GM10.leafSet T)) :
    graphBranchDecompWidth G T τ =
      GM10.branchDecompWidth (graphToHypergraph G hV hE) T σ := by
  unfold graphBranchDecompWidth GM10.branchDecompWidth
  congr 1
  ext w
  simp only [mem_image]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [graphBranchEdgeOrder_eq_branchEdgeOrder G hV hE T τ σ hτ hσ hinv e]

/-- Equivalence between `GraphBranchWidthLE G ω` and `GM10.branchWidth (graphToHypergraph G hV hE) ≤ ω`. -/
lemma graphBranchWidthLE_iff_branchWidth_le (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (ω : ℕ) :
    GraphBranchWidthLE G ω ↔ GM10.branchWidth (graphToHypergraph G hV hE) ≤ ω := by
  constructor
  · rintro (hle1 | ⟨ι, hfin_ι, T, τ, hbd, hw⟩)
    · rw [GM10.branchWidth_eq_zero_of_ncard_edgeSet_le_one hle1]
      exact Nat.zero_le _
    · rcases hbd.isTernaryOrEmpty with hemp | hT
      · have hleaf_emp : GM10.leafSet T = ∅ := eq_empty_of_isEmpty _
        have hE_emp : E(G) = ∅ := by
          rw [← image_eq_empty (f := τ), hbd.bijOn.image_eq, hleaf_emp]
        have hle1 : (graphToHypergraph G hV hE).edgeSet.ncard ≤ 1 := by
          change E(G).ncard ≤ 1
          rw [hE_emp, ncard_empty]
          exact Nat.zero_le _
        rw [GM10.branchWidth_eq_zero_of_ncard_edgeSet_le_one hle1]
        exact Nat.zero_le _
      · have hleaf_ne : (GM10.leafSet T).Nonempty :=
          nonempty_of_ncard_ne_zero (by have := hT.two_le_ncard_leafSet; omega)
        rcases hleaf_ne with ⟨t₀, ht₀⟩
        rcases hbd.bijOn.surjOn ht₀ with ⟨e₀, he₀, _⟩
        have : Nonempty β := ⟨e₀⟩
        let σ : ι → β := invFunOn τ E(G)
        have hinv : InvOn σ τ E(G) (GM10.leafSet T) := hbd.bijOn.invOn_invFunOn
        have hbij_σ : BijOn σ (GM10.leafSet T) E(G) :=
          hinv.symm.bijOn hbd.bijOn.2.2.mapsTo_invFunOn hbd.bijOn.1
        have hbd_GM10 : GM10.IsBranchDecomposition (graphToHypergraph G hV hE) T σ :=
          ⟨hT, hbij_σ⟩
        have hw_eq := graphBranchDecompWidth_eq_branchDecompWidth G hV hE T τ σ
          hbd.bijOn.1 hbij_σ.1 hinv
        exact (GM10.branchWidth_le_of_isBranchDecomposition hbd_GM10).trans (hw_eq ▸ hw)
  · intro hbw
    by_cases hle1 : E(G).ncard ≤ 1
    · exact Or.inl hle1
    · push Not at hle1
      have hne : E(G).Nonempty := nonempty_of_ncard_ne_zero (by omega)
      have hγ1 : 1 ≤ GM10.maxEdgeSize (graphToHypergraph G hV hE) :=
        one_le_maxEdgeSize_graphToHypergraph G hV hE hne
      obtain ⟨ι, hfin_ι, T, σ, hbd, hw_eq⟩ :=
        GM10.exists_branchDecomposition_eq_branchWidth hγ1 hle1
      have : Nonempty ι := hbd.isTernaryTree.isTree.connected.nonempty
      let τ : β → ι := invFunOn σ (GM10.leafSet T)
      have hinv : InvOn τ σ (GM10.leafSet T) E(G) := hbd.bijOn.invOn_invFunOn
      have hbij_τ : BijOn τ E(G) (GM10.leafSet T) :=
        hinv.symm.bijOn hbd.bijOn.2.2.mapsTo_invFunOn hbd.bijOn.1
      have hbd_G : IsGraphBranchDecomposition G T τ := ⟨Or.inr hbd.isTernaryTree, hbij_τ⟩
      have hw_eq' := graphBranchDecompWidth_eq_branchDecompWidth G hV hE T τ σ
        hbij_τ.1 hbd.bijOn.1 hinv.symm
      exact Or.inr ⟨ι, hfin_ι, T, τ, hbd_G, by omega⟩

/-- Convert a subhypergraph `A ≤ graphToHypergraph G hV hE` to a subgraph `A' ≤ G`. -/
def subhypergraphToSubgraph {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    (A : Hypergraph α β) (hA : A ≤ graphToHypergraph G hV hE) : Graph α β where
  vertexSet := A.vertexSet
  edgeSet := A.edgeSet
  IsLink e u v := e ∈ A.edgeSet ∧ G.IsLink e u v
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := G.eq_or_eq_of_isLink_of_isLink h1.2 h2.2
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun he => ?_, fun ⟨u, v, he, _⟩ => he⟩
    rcases (G.edge_mem_iff_exists_isLink e).mp (hA.edgeSet_subset he) with ⟨u, v, huv⟩
    exact ⟨u, v, he, huv⟩
  left_mem_of_isLink e u v h := by
    have hincG : (graphToHypergraph G hV hE).Inc e u := ⟨v, h.2⟩
    have hincA : A.Inc e u := (GM10.inc_iff_of_le hA h.1).mpr hincG
    exact A.vertex_mem_of_inc hincA

@[simp]
lemma subhypergraphToSubgraph_vertexSet {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    (A : Hypergraph α β) (hA : A ≤ graphToHypergraph G hV hE) :
    V(subhypergraphToSubgraph A hA) = A.vertexSet := rfl

@[simp]
lemma subhypergraphToSubgraph_edgeSet {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    (A : Hypergraph α β) (hA : A ≤ graphToHypergraph G hV hE) :
    E(subhypergraphToSubgraph A hA) = A.edgeSet := rfl

lemma subhypergraphToSubgraph_le {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    (A : Hypergraph α β) (hA : A ≤ graphToHypergraph G hV hE) :
    subhypergraphToSubgraph A hA ≤ G where
  vertexSet_mono := hA.vertexSet_subset
  isLink_mono _ _ _ h := h.2

@[simp]
lemma graphToHypergraph_subhypergraphToSubgraph {G : Graph α β} {hV : V(G).Finite}
    {hE : E(G).Finite} (A : Hypergraph α β) (hA : A ≤ graphToHypergraph G hV hE) :
    graphToHypergraph (subhypergraphToSubgraph A hA) A.vertexSet_finite A.edgeSet_finite = A := by
  refine Hypergraph.ext rfl rfl ?_
  funext e u
  apply propext
  change (∃ v, e ∈ A.edgeSet ∧ G.IsLink e u v) ↔ A.Inc e u
  constructor
  · rintro ⟨v, he, huv⟩
    exact (GM10.inc_iff_of_le hA he).mpr ⟨v, huv⟩
  · intro hincA
    have he : e ∈ A.edgeSet := A.edge_mem_of_inc hincA
    rcases (GM10.inc_iff_of_le hA he).mp hincA with ⟨v, huv⟩
    exact ⟨v, he, huv⟩

lemma graphToHypergraph_le_of_le {G H : Graph α β} {hVG : V(G).Finite} {hEG : E(G).Finite}
    (hHG : H ≤ G) :
    graphToHypergraph H (hVG.subset hHG.vertexSet_mono)
      (hEG.subset hHG.edgeSet_mono) ≤
      graphToHypergraph G hVG hEG where
  vertexSet_subset := hHG.vertexSet_mono
  edgeSet_subset := hHG.edgeSet_mono
  ends_eq e he := by
    ext v
    change G.Inc e v ↔ H.Inc e v
    refine ⟨fun ⟨w, hgw⟩ => ?_, fun ⟨w, hhw⟩ => ⟨w, hHG.isLink_mono hhw⟩⟩
    rcases (H.edge_mem_iff_exists_isLink e).mp he with ⟨x, y, hxy⟩
    have hgxy : G.IsLink e x y := hHG.isLink_mono hxy
    rcases G.eq_or_eq_of_isLink_of_isLink hgw hgxy with rfl | rfl
    · exact ⟨y, hxy⟩
    · exact ⟨x, hxy.symm⟩

lemma isSeparation_graphToHypergraph_of_isGraphSeparation {G A B : Graph α β}
    {hVG : V(G).Finite} {hEG : E(G).Finite} (hsep : IsGraphSeparation G A B) :
    (graphToHypergraph G hVG hEG).IsSeparation
      (graphToHypergraph A (hVG.subset hsep.1.vertexSet_mono)
        (hEG.subset hsep.1.edgeSet_mono))
      (graphToHypergraph B (hVG.subset hsep.2.1.vertexSet_mono)
        (hEG.subset hsep.2.1.edgeSet_mono)) := by
  rw [GM10.isSeparation_iff_of_le (graphToHypergraph_le_of_le hsep.1)
    (graphToHypergraph_le_of_le hsep.2.1)]
  exact ⟨hsep.2.2.1, hsep.2.2.2.1, disjoint_iff_inter_eq_empty.mp hsep.2.2.2.2⟩

lemma isGraphSeparation_subhypergraphToSubgraph {G : Graph α β} {hVG : V(G).Finite}
    {hEG : E(G).Finite} {A B : Hypergraph α β}
    (hsep : (graphToHypergraph G hVG hEG).IsSeparation A B) :
    IsGraphSeparation G (subhypergraphToSubgraph A hsep.left_le)
      (subhypergraphToSubgraph B hsep.right_le) :=
  ⟨subhypergraphToSubgraph_le A hsep.left_le,
    subhypergraphToSubgraph_le B hsep.right_le,
    hsep.vertexSet_union, hsep.edgeSet_union, hsep.disjoint_edgeSet⟩

/-- For any hypergraph `H` with `maxEdgeSize H ≤ ω`, `branchWidth H ≤ ω`, and `1 ≤ ω`,
`tangleNumber H ≤ ω`. -/
lemma tangleNumber_le_of_branchWidth_le {H : Hypergraph α β} {ω : ℕ}
    (hω : 1 ≤ ω) (hγ : GM10.maxEdgeSize H ≤ ω) (hbw : GM10.branchWidth H ≤ ω) :
    GM10.tangleNumber H ≤ ω := by
  by_cases hcase : GM10.maxEdgeSize H = 0 ∧ H.vertexSet.Nonempty
  · rw [GM10.tangleNumber_eq_one_of_maxEdgeSize_eq_zero hcase.1 hcase.2]
    exact hω
  · rw [← GM10.theorem_4_3_proof H hcase]
    exact max_le hbw hγ

/-- For any hypergraph `H`, `branchWidth H ≤ tangleNumber H`. -/
lemma branchWidth_le_tangleNumber (H : Hypergraph α β) :
    GM10.branchWidth H ≤ GM10.tangleNumber H := by
  by_cases hcase : GM10.maxEdgeSize H = 0 ∧ H.vertexSet.Nonempty
  · rw [GM10.branchWidth_eq_zero_of_maxEdgeSize_eq_zero hcase.1]
    exact Nat.zero_le _
  · rw [← GM10.theorem_4_3_proof H hcase]
    exact le_max_left _ _

/-- The set `𝒯` of separations in the proof of **Graph Minors XIII, (3.1)** (page 71):
"Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $\le \omega$ with
$$|Z - V(A)| + \frac{1}{2} |Z \cap V(A \cap B)| > \frac{2}{3} |Z|.$$" -/
def unbalancedSepTangle (H : Hypergraph α β) (ω : ℕ) (Z : Set α) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | H.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < ω + 1 ∧
    4 * Z.ncard < 6 * (Z \ p.1.vertexSet).ncard + 3 * (Z ∩ (p.1.vertexSet ∩ p.2.vertexSet)).ncard}

/-- Claim (1)(i) in the proof of **Graph Minors XIII, (3.1)** (page 71):
"(1)(i) *If $(A, B) \in \mathscr{T}$ then $V(A) \ne V(G)$,*" -/
lemma theorem_3_1_claim_1_i {H : Hypergraph α β} {ω : ℕ} {Z : Set α} (hZ : Z ⊆ H.vertexSet)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ unbalancedSepTangle H ω Z) :
    A.vertexSet ≠ H.vertexSet := by
  intro heq
  have hZ_fin : Z.Finite := H.vertexSet_finite.subset hZ
  have hdiff : Z \ A.vertexSet = ∅ :=
    eq_empty_of_forall_notMem fun x hx => hx.2 (heq ▸ hZ hx.1)
  have hinter : (Z ∩ (A.vertexSet ∩ B.vertexSet)).ncard ≤ Z.ncard :=
    ncard_le_ncard inter_subset_left hZ_fin
  have hlt : 4 * Z.ncard <
      6 * (Z \ A.vertexSet).ncard + 3 * (Z ∩ (A.vertexSet ∩ B.vertexSet)).ncard := hAB.2.2
  rw [hdiff, ncard_empty] at hlt
  omega

/-- Claim (1)(ii) in the proof of **Graph Minors XIII, (3.1)** (page 71):
"(ii) *if $(A_1, B_1), (A_2, B_2) \in \mathscr{T}$ then $B_1$ is not a subgraph of $A_2$*" -/
lemma theorem_3_1_claim_1_ii {H : Hypergraph α β} {ω : ℕ} {Z : Set α} (hZ : Z ⊆ H.vertexSet)
    {A₁ B₁ A₂ B₂ : Hypergraph α β}
    (h1 : (A₁, B₁) ∈ unbalancedSepTangle H ω Z)
    (h2 : (A₂, B₂) ∈ unbalancedSepTangle H ω Z) :
    ¬ B₁ ≤ A₂ := by
  intro hle
  have hZ_fin : Z.Finite := H.vertexSet_finite.subset hZ
  have hZB₁_eq : (Z \ A₁.vertexSet) ∪ (Z ∩ (A₁.vertexSet ∩ B₁.vertexSet)) = Z ∩ B₁.vertexSet := by
    ext x
    simp only [mem_union, mem_sdiff, mem_inter_iff]
    constructor
    · rintro (⟨hxZ, hxA₁⟩ | ⟨hxZ, _, hxB₁⟩)
      · have hxU : x ∈ A₁.vertexSet ∪ B₁.vertexSet := h1.1.vertexSet_union.symm ▸ hZ hxZ
        exact ⟨hxZ, hxU.resolve_left hxA₁⟩
      · exact ⟨hxZ, hxB₁⟩
    · rintro ⟨hxZ, hxB₁⟩
      by_cases hxA₁ : x ∈ A₁.vertexSet
      · exact Or.inr ⟨hxZ, hxA₁, hxB₁⟩
      · exact Or.inl ⟨hxZ, hxA₁⟩
  have hdisj₁ : Disjoint (Z \ A₁.vertexSet) (Z ∩ (A₁.vertexSet ∩ B₁.vertexSet)) :=
    disjoint_left.mpr fun _ hx1 hx2 => hx1.2 hx2.2.1
  have hcard_ZB₁ : (Z \ A₁.vertexSet).ncard + (Z ∩ (A₁.vertexSet ∩ B₁.vertexSet)).ncard =
      (Z ∩ B₁.vertexSet).ncard := by
    rw [← ncard_union_eq hdisj₁ (hZ_fin.subset sdiff_subset) (hZ_fin.subset inter_subset_left),
      hZB₁_eq]
  have hZ_eq₂ : (Z \ A₂.vertexSet) ∪ (Z ∩ A₂.vertexSet) = Z := sdiff_union_inter Z A₂.vertexSet
  have hdisj₂ : Disjoint (Z \ A₂.vertexSet) (Z ∩ A₂.vertexSet) :=
    disjoint_left.mpr fun _ hx1 hx2 => hx1.2 hx2.2
  have hZ_split₂ : (Z \ A₂.vertexSet).ncard + (Z ∩ A₂.vertexSet).ncard = Z.ncard := by
    rw [← ncard_union_eq hdisj₂ (hZ_fin.subset sdiff_subset) (hZ_fin.subset inter_subset_left),
      hZ_eq₂]
  have hinter_le₂ : (Z ∩ (A₂.vertexSet ∩ B₂.vertexSet)).ncard ≤ (Z ∩ A₂.vertexSet).ncard :=
    ncard_le_ncard (inter_subset_inter_right Z inter_subset_left) (hZ_fin.subset inter_subset_left)
  have hB₁_le_A₂ : (Z ∩ B₁.vertexSet).ncard ≤ (Z ∩ A₂.vertexSet).ncard :=
    ncard_le_ncard (inter_subset_inter_right Z hle.vertexSet_subset)
      (hZ_fin.subset inter_subset_left)
  have hlt₁ : 4 * Z.ncard <
      6 * (Z \ A₁.vertexSet).ncard + 3 * (Z ∩ (A₁.vertexSet ∩ B₁.vertexSet)).ncard := h1.2.2
  have hlt₂ : 4 * Z.ncard <
      6 * (Z \ A₂.vertexSet).ncard + 3 * (Z ∩ (A₂.vertexSet ∩ B₂.vertexSet)).ncard := h2.2.2
  omega

/-- Claim (1)(iii) in the proof of **Graph Minors XIII, (3.1)** (page 71):
"(iii) *if $A_1, A_2, A_3$ are mutually edge-disjoint subgraphs of $G$ with union $G$, then not all
of $(A_1, A_2 \cup A_3), (A_2, A_3 \cup A_1), (A_3, A_1 \cup A_2)$ belong to $\mathscr{T}$.*" -/
lemma theorem_3_1_claim_1_iii {H : Hypergraph α β} {ω : ℕ} {Z : Set α} (hZ : Z ⊆ H.vertexSet) :
    ¬ ∃ A₁ A₂ A₃ : Hypergraph α β,
      A₁ ≤ H ∧ A₂ ≤ H ∧ A₃ ≤ H ∧
      Disjoint A₁.edgeSet A₂.edgeSet ∧
      Disjoint A₁.edgeSet A₃.edgeSet ∧
      Disjoint A₂.edgeSet A₃.edgeSet ∧
      A₁ ∪ A₂ ∪ A₃ = H ∧
      (A₁, A₂ ∪ A₃) ∈ unbalancedSepTangle H ω Z ∧
      (A₂, A₃ ∪ A₁) ∈ unbalancedSepTangle H ω Z ∧
      (A₃, A₁ ∪ A₂) ∈ unbalancedSepTangle H ω Z := by
  rintro ⟨A₁, A₂, A₃, _, _, _, _, _, _, hU, hm1, hm2, hm3⟩
  have hZ_fin : Z.Finite := H.vertexSet_finite.subset hZ
  let S := hZ_fin.toFinset
  have hcard_filter : ∀ (P : Set α), (Z ∩ P).ncard = ∑ x ∈ S, if x ∈ P then 1 else 0 := by
    intro P
    have heq : (hZ_fin.inter_of_left P).toFinset = S.filter (· ∈ P) := by
      ext x
      simp [S, Finite.mem_toFinset]
    rw [ncard_eq_toFinset_card _ (hZ_fin.inter_of_left P), heq, Finset.card_filter]
  have hdiff_eq : ∀ (P : Set α), (Z \ P).ncard = ∑ x ∈ S, if x ∉ P then 1 else 0 := by
    intro P
    have hsub : Z \ P ⊆ Z := sdiff_subset
    have heq : (hZ_fin.subset hsub).toFinset = S.filter (· ∉ P) := by
      ext x
      simp [S, Finite.mem_toFinset]
    rw [ncard_eq_toFinset_card _ (hZ_fin.subset hsub), heq, Finset.card_filter]
  have h1 : 4 * Z.ncard <
      6 * (Z \ A₁.vertexSet).ncard + 3 * (Z ∩ (A₁.vertexSet ∩ (A₂ ∪ A₃).vertexSet)).ncard :=
    hm1.2.2
  have h2 : 4 * Z.ncard <
      6 * (Z \ A₂.vertexSet).ncard + 3 * (Z ∩ (A₂.vertexSet ∩ (A₃ ∪ A₁).vertexSet)).ncard :=
    hm2.2.2
  have h3 : 4 * Z.ncard <
      6 * (Z \ A₃.vertexSet).ncard + 3 * (Z ∩ (A₃.vertexSet ∩ (A₁ ∪ A₂).vertexSet)).ncard :=
    hm3.2.2
  have hZ_card : Z.ncard = ∑ _x ∈ S, 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, ncard_eq_toFinset_card Z hZ_fin]
  have hsum_le :
      (6 * (Z \ A₁.vertexSet).ncard + 3 * (Z ∩ (A₁.vertexSet ∩ (A₂ ∪ A₃).vertexSet)).ncard) +
      (6 * (Z \ A₂.vertexSet).ncard + 3 * (Z ∩ (A₂.vertexSet ∩ (A₃ ∪ A₁).vertexSet)).ncard) +
      (6 * (Z \ A₃.vertexSet).ncard + 3 * (Z ∩ (A₃.vertexSet ∩ (A₁ ∪ A₂).vertexSet)).ncard) ≤
      12 * Z.ncard := by
    rw [hdiff_eq, hdiff_eq, hdiff_eq, hcard_filter, hcard_filter, hcard_filter, hZ_card,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxZ : x ∈ Z := (Finite.mem_toFinset hZ_fin).mp hx
    have hxU : x ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := by
      have hVU : (A₁ ∪ A₂ ∪ A₃).vertexSet = H.vertexSet := congrArg Hypergraph.vertexSet hU
      exact hVU.symm ▸ hZ hxZ
    simp only [GM10.union_vertexSet, mem_union, mem_inter_iff] at hxU ⊢
    by_cases hx1 : x ∈ A₁.vertexSet <;>
      by_cases hx2 : x ∈ A₂.vertexSet <;>
      by_cases hx3 : x ∈ A₃.vertexSet <;>
      simp_all
  omega

/-- **Graph Minors XIII, (3.1) Lemma** (page 71):
"*Let $G$ be a graph with branch-width $\le \omega$, where $\omega \ge 2$, and let $Z \subseteq
V(G)$. Then there is a separation $(A, B)$ of $G$ of order $\le \omega$ with*
$$|Z - V(A)|, |Z - V(B)| \le \frac{2}{3} |Z| - \frac{1}{2} |Z \cap V(A \cap B)|.$$" -/
theorem theorem_3_1_proof (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (ω : ℕ) (hω : 2 ≤ ω) (hbw : GraphBranchWidthLE G ω)
    (Z : Set α) (hZ : Z ⊆ V(G)) :
    ∃ A B : Graph α β, IsGraphSeparation G A B ∧
      graphSeparationOrder A B ≤ ω ∧
      6 * (Z \ V(A)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard ∧
      6 * (Z \ V(B)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard := by
  let H := graphToHypergraph G hVG hEG
  let 𝒯 := unbalancedSepTangle H ω Z
  have hbw_H : GM10.branchWidth H ≤ ω :=
    (graphBranchWidthLE_iff_branchWidth_le G hVG hEG ω).mp hbw
  have hγ_H : GM10.maxEdgeSize H ≤ ω :=
    (maxEdgeSize_graphToHypergraph_le_two G hVG hEG).trans hω
  have hθ_H : GM10.tangleNumber H ≤ ω :=
    tangleNumber_le_of_branchWidth_le (by omega) hγ_H hbw_H
  have hnot_ax1 : ¬ GM10.TangleAxiom1 H (ω + 1) 𝒯 := by
    intro hax1
    have hax2 : GM10.TangleAxiom2 H 𝒯 :=
      GM10.theorem_4_5_proof (by omega) (fun _ _ h => h.1) (fun _ _ h => h.2.1) hax1
        (fun _ _ _ _ h1 h2 => theorem_3_1_claim_1_ii hZ h1 h2)
        (theorem_3_1_claim_1_iii hZ)
    have h𝒯 : GM10.IsTangle H (ω + 1) 𝒯 :=
      ⟨by omega, fun _ _ h => h.1, fun _ _ h => h.2.1, hax1, hax2,
        fun _ _ h => theorem_3_1_claim_1_i hZ h⟩
    have hle := h𝒯.le_tangleNumber
    omega
  unfold GM10.TangleAxiom1 at hnot_ax1
  push Not at hnot_ax1
  rcases hnot_ax1 with ⟨A, B, hsep, hord, hnotAB, hnotBA⟩
  have hbalA : 6 * (Z \ A.vertexSet).ncard + 3 * (Z ∩ (A.vertexSet ∩ B.vertexSet)).ncard ≤
      4 * Z.ncard := by
    by_contra! hgt
    exact hnotAB ⟨hsep, hord, hgt⟩
  have hbalB : 6 * (Z \ B.vertexSet).ncard + 3 * (Z ∩ (A.vertexSet ∩ B.vertexSet)).ncard ≤
      4 * Z.ncard := by
    by_contra! hgt
    rw [inter_comm A.vertexSet B.vertexSet] at hgt
    exact hnotBA ⟨hsep.symm, by rwa [GM10.separationOrder_comm], hgt⟩
  refine ⟨subhypergraphToSubgraph A hsep.left_le, subhypergraphToSubgraph B hsep.right_le,
    isGraphSeparation_subhypergraphToSubgraph hsep, ?_, hbalA, hbalB⟩
  change (A.vertexSet ∩ B.vertexSet).ncard ≤ ω
  change (A.vertexSet ∩ B.vertexSet).ncard < ω + 1 at hord
  omega

/-- Any tangle `𝒯'` of order `θ` in a subhypergraph `H' ≤ H` lifts to a tangle of order `θ` in `H`. -/
lemma isTangle_subhypergraph_lift {H H' : Hypergraph α β} (hH' : H' ≤ H) {θ : ℕ}
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : GM10.IsTangle H' θ 𝒯') :
    GM10.IsTangle H θ {p | H.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
      (H' ∩ p.1, H' ∩ p.2) ∈ 𝒯'} where
  one_le := h𝒯'.one_le
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have hsep' : H'.IsSeparation (H' ∩ A) (H' ∩ B) := hsep.inter_left hH'
    have hsub : ((H' ∩ A) ∩ (H' ∩ B)).vertexSet ⊆ (A ∩ B).vertexSet := by
      intro x hx
      exact ⟨hx.1.2, hx.2.2⟩
    have hord' : separationOrder (H' ∩ A) (H' ∩ B) < θ :=
      (ncard_le_ncard hsub (A ∩ B).vertexSet_finite).trans_lt hord
    rcases h𝒯'.axiom1 hsep' hord' with hm | hm
    · exact Or.inl ⟨hsep, hord, hm⟩
    · exact Or.inr ⟨hsep.symm, by rwa [GM10.separationOrder_comm], hm⟩
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hU := by
    apply h𝒯'.axiom2 h1.2.2 h2.2.2 h3.2.2
    have hle1 : H' ∩ A₁ ≤ H' := GM10.inter_le_left hH' h1.1.left_le
    have hle2 : H' ∩ A₂ ≤ H' := GM10.inter_le_left hH' h2.1.left_le
    have hle3 : H' ∩ A₃ ≤ H' := GM10.inter_le_left hH' h3.1.left_le
    have hU_le : (H' ∩ A₁) ∪ (H' ∩ A₂) ∪ (H' ∩ A₃) ≤ H' :=
      GM10.union_le (GM10.union_le hle1 hle2) hle3
    have hVU : (A₁ ∪ A₂ ∪ A₃).vertexSet = H.vertexSet := congrArg Hypergraph.vertexSet hU
    have hEU : (A₁ ∪ A₂ ∪ A₃).edgeSet = H.edgeSet := congrArg Hypergraph.edgeSet hU
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
    · ext x
      simp only [GM10.union_vertexSet, GM10.inter_vertexSet, mem_union, mem_inter_iff]
      refine ⟨fun h => hU_le.vertexSet_subset h, fun hxH' => ?_⟩
      have hxH : x ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hVU.symm ▸ hH'.vertexSet_subset hxH'
      rcases hxH with (hx1 | hx2) | hx3
      · exact Or.inl (Or.inl ⟨hxH', hx1⟩)
      · exact Or.inl (Or.inr ⟨hxH', hx2⟩)
      · exact Or.inr ⟨hxH', hx3⟩
    · ext e
      simp only [GM10.union_edgeSet, GM10.inter_edgeSet, mem_union, mem_inter_iff]
      refine ⟨fun h => hU_le.edgeSet_subset h, fun heH' => ?_⟩
      have heH : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := hEU.symm ▸ hH'.edgeSet_subset heH'
      rcases heH with (he1 | he2) | he3
      · exact Or.inl (Or.inl ⟨heH', he1⟩)
      · exact Or.inl (Or.inr ⟨heH', he2⟩)
      · exact Or.inr ⟨heH', he3⟩
  axiom3 A B hAB hVA := by
    apply h𝒯'.axiom3 hAB.2.2
    change H'.vertexSet ∩ A.vertexSet = H'.vertexSet
    rw [hVA, inter_eq_self_of_subset_left hH'.vertexSet_subset]

/-- If `H' ≤ H`, then `tangleNumber H' ≤ tangleNumber H`. -/
lemma tangleNumber_le_of_le {H H' : Hypergraph α β} (hH' : H' ≤ H) :
    GM10.tangleNumber H' ≤ GM10.tangleNumber H := by
  by_cases h0 : GM10.tangleNumber H' = 0
  · omega
  · obtain ⟨𝒯', h𝒯'⟩ := GM10.exists_isTangle_of_le_tangleNumber (G := H') (by omega) le_rfl
    exact (isTangle_subhypergraph_lift hH' h𝒯').le_tangleNumber

/-- Monotonicity of `GraphBranchWidthLE` with respect to subgraphs when `2 ≤ ω`. -/
lemma GraphBranchWidthLE.mono {G G' : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hG' : G' ≤ G) {ω : ℕ} (hω : 2 ≤ ω) (hbw : GraphBranchWidthLE G ω) :
    GraphBranchWidthLE G' ω := by
  have hVG' : V(G').Finite := hVG.subset hG'.vertexSet_mono
  have hEG' : E(G').Finite := hEG.subset hG'.edgeSet_mono
  rw [graphBranchWidthLE_iff_branchWidth_le G' hVG' hEG' ω]
  have hbw_G : GM10.branchWidth (graphToHypergraph G hVG hEG) ≤ ω :=
    (graphBranchWidthLE_iff_branchWidth_le G hVG hEG ω).mp hbw
  have hγ_G : GM10.maxEdgeSize (graphToHypergraph G hVG hEG) ≤ ω :=
    (maxEdgeSize_graphToHypergraph_le_two G hVG hEG).trans hω
  have hθ_G : GM10.tangleNumber (graphToHypergraph G hVG hEG) ≤ ω :=
    tangleNumber_le_of_branchWidth_le (by omega) hγ_G hbw_G
  exact (branchWidth_le_tangleNumber _).trans
    ((tangleNumber_le_of_le (graphToHypergraph_le_of_le hG')).trans hθ_G)

end GraphMinor.GM13
