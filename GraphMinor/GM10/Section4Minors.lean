module

public import GraphMinor.GM10.BranchWidth
public import GraphMinor.GM10.Section2Six
public import GraphMinor.GM10.Section6

/-!
# Graph Minors X, Section 4: Branch-Width of Minors and Small Branch-Width

This file formalizes **(4.1)** and parts **(i)** and **(ii)** of **(4.2)** of
Robertson and Seymour, *Graph Minors. X. Obstructions to Tree-Decomposition*,
J. Combin. Theory Ser. B **52** (1991), 153–190 (pages 164–165):

- **(4.1)** (`theorem_4_1`): If `H` is a minor of a graph `G`, then `β(H) ≤ β(G)`.
- **(4.2)(i)** (`branchWidth_eq_zero_iff_components_le_one_edge`): A graph `G` has branch-width `0`
  if and only if every component of `G` has `≤ 1` edge.
- **(4.2)(ii)** (`branchWidth_le_one_iff_components_le_one_deg_ge_two`): A graph `G` has
  branch-width `≤ 1` if and only if every component of `G` has `≤ 1` vertex of valency `≥ 2`.
-/

@[expose] public section

namespace GraphMinor.GM10

open Graph SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

/-! ## Helper lemmas on `Hypergraph.ofGraph` -/

/-- Every edge of `Hypergraph.ofGraph G hV hE` is incident with at least one vertex. -/
theorem nonempty_ends_ofGraph {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {e : β} (he : e ∈ (Hypergraph.ofGraph G hV hE).edgeSet) :
    ((Hypergraph.ofGraph G hV hE).ends e).Nonempty := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.inc_left⟩

/-- Every edge of `Hypergraph.ofGraph G hV hE` has size `≥ 1`. -/
theorem one_le_edgeSize_ofGraph {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {e : β} (he : e ∈ (Hypergraph.ofGraph G hV hE).edgeSet) :
    1 ≤ edgeSize (Hypergraph.ofGraph G hV hE) e :=
  (Set.ncard_pos (ends_finite (Hypergraph.ofGraph G hV hE) e)).2 (nonempty_ends_ofGraph he)

/-- When `E(G)` is nonempty, `1 ≤ maxEdgeSize (Hypergraph.ofGraph G hV hE)`. -/
theorem one_le_maxEdgeSize_ofGraph {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    (hne : (Hypergraph.ofGraph G hV hE).edgeSet.Nonempty) :
    1 ≤ maxEdgeSize (Hypergraph.ofGraph G hV hE) := by
  obtain ⟨e, he⟩ := hne
  exact (one_le_edgeSize_ofGraph he).trans (edgeSize_le_maxEdgeSize he)

/-- Every edge of `Hypergraph.ofGraph G hV hE` has size `≤ 2`. -/
theorem edgeSize_ofGraph_le_two (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (e : β) :
    edgeSize (Hypergraph.ofGraph G hV hE) e ≤ 2 := by
  by_cases he : e ∈ E(G)
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
    have hsub : (Hypergraph.ofGraph G hV hE).ends e ⊆ {x, y} := by
      intro z hz
      exact hz.eq_or_eq_of_isLink hxy
    have hle1 : edgeSize (Hypergraph.ofGraph G hV hE) e ≤ ({x, y} : Set α).ncard :=
      Set.ncard_le_ncard hsub (by simp)
    have hle2 : ({x, y} : Set α).ncard ≤ 2 := (Set.ncard_insert_le x {y}).trans (by simp)
    exact hle1.trans hle2
  · have hemp : (Hypergraph.ofGraph G hV hE).ends e = ∅ := by
      ext z
      change G.Inc e z ↔ z ∈ (∅ : Set α)
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h ↦ he h.edge_mem
    simp [edgeSize, hemp]

/-- `Hypergraph.ofGraph G hV hE` is a graph in the sense of `Hypergraph.IsGraph`. -/
theorem ofGraph_isGraph (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (Hypergraph.ofGraph G hV hE).IsGraph :=
  fun e he ↦ ⟨nonempty_ends_ofGraph he, edgeSize_ofGraph_le_two G hV hE e⟩

/-- In any branch-decomposition `(T, τ)` of `G`, if `t₁ ∈ leafSet T` has unique neighbor `w` in `T`,
then `branchEdgeBoundary G {τ t₁}` has cardinality at most `branchEdgeOrder G T τ s(t₁, w)`. -/
theorem ncard_branchEdgeBoundary_singleton_le_branchEdgeOrder [Fintype ι]
    {G : Hypergraph α β} {T : SimpleGraph ι} {τ : ι → β}
    (hbd : IsBranchDecomposition G T τ) {t₁ w : ι}
    (ht₁ : t₁ ∈ leafSet T) (hadj : T.Adj t₁ w) :
    (branchEdgeBoundary G {τ t₁}).ncard ≤ branchEdgeOrder G T τ s(t₁, w) := by
  have hT := hbd.isTernaryTree
  have hcomp := treeComponent_eq_singleton_of_isLeaf hT hadj ht₁
  have hsub : branchEdgeBoundary G {τ t₁} ⊆
      {v ∈ G.vertexSet | ∃ x₁ ∈ leafSet T, ∃ x₂ ∈ leafSet T,
        ¬ (T.deleteEdges {s(t₁, w)}).Reachable x₁ x₂ ∧ G.Inc (τ x₁) v ∧ G.Inc (τ x₂) v} := by
    rintro v ⟨hv, ⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂ne⟩, hinc₂⟩⟩
    rw [Set.mem_singleton_iff] at he₁
    subst he₁
    obtain ⟨t₂, ht₂, rfl⟩ := hbd.bijOn.surjOn he₂G
    have ht₂_ne : t₂ ≠ t₁ := fun h ↦ he₂ne (Set.mem_singleton_iff.2 (congrArg τ h))
    have hnot_reach : ¬ (T.deleteEdges {s(t₁, w)}).Reachable t₁ t₂ := by
      intro hreach
      have ht₂_mem : t₂ ∈ treeComponent T t₁ s(t₁, w) := hreach
      rw [hcomp, Set.mem_singleton_iff] at ht₂_mem
      exact ht₂_ne ht₂_mem
    exact ⟨hv, t₁, ht₁, t₂, ht₂, hnot_reach, hinc₁, hinc₂⟩
  exact Set.ncard_le_ncard hsub (G.vertexSet_finite.subset fun _ h ↦ h.1)

/-! ## Proof of (4.1) -/

/-- For a minor `H = contract G' C` of `G` and any `X ⊆ E(G)`, the vertex boundary of
`X ∩ E(H)` in `H` has cardinality at most the vertex boundary of `X` in `G`
(Graph Minors X, Section 4, proof of (4.1), page 164). -/
theorem ncard_branchEdgeBoundary_contract_le {G G' : Graph α β} {C : Set β}
    (hG' : G' ≤ G) (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(contract G' C).Finite) (hEH : E(contract G' C).Finite)
    {X : Set β} (hX : X ⊆ (Hypergraph.ofGraph G hV hE).edgeSet) :
    (branchEdgeBoundary (Hypergraph.ofGraph (contract G' C) hVH hEH)
      (X ∩ (Hypergraph.ofGraph (contract G' C) hVH hEH).edgeSet)).ncard ≤
      (branchEdgeBoundary (Hypergraph.ofGraph G hV hE) X).ncard := by
  let G_hyp := Hypergraph.ofGraph G hV hE
  let H_hyp := Hypergraph.ofGraph (contract G' C) hVH hEH
  have hEH_sub : H_hyp.edgeSet ⊆ G_hyp.edgeSet := by
    change E(contract G' C) ⊆ E(G)
    have h1 : E(contract G' C) = E(G') \ C := by simp [contract]
    rw [h1]
    exact Set.sdiff_subset.trans hG'.edgeSet_mono
  have hsepG := isSeparation_sepLeft_sepRight G_hyp X
  have hsepH := minorImageSubhypergraph_isSeparation hG' hV hE hVH hEH hsepG
  have hA_edge : (minorImageSubhypergraph G' C hVH hEH (sepLeft G_hyp X)).edgeSet =
      X ∩ H_hyp.edgeSet := by
    change (X ∩ G_hyp.edgeSet) ∩ H_hyp.edgeSet = X ∩ H_hyp.edgeSet
    rw [Set.inter_assoc, Set.inter_eq_right.2 hEH_sub]
  have hle1 : (branchEdgeBoundary H_hyp (X ∩ H_hyp.edgeSet)).ncard ≤
      separationOrder (minorImageSubhypergraph G' C hVH hEH (sepLeft G_hyp X))
        (minorImageSubhypergraph G' C hVH hEH (sepRight G_hyp X)) := by
    rw [← hA_edge]
    exact Set.ncard_le_ncard (branchEdgeBoundary_subset_of_isSeparation hsepH)
      (Hypergraph.vertexSet_finite (_ ∩ _))
  have hle2 := minorImageSubhypergraph_separationOrder_le hG' hV hE hVH hEH hsepG
  have heq3 := separationOrder_sepLeft_sepRight G_hyp hX
  change (branchEdgeBoundary H_hyp (X ∩ H_hyp.edgeSet)).ncard ≤ (branchEdgeBoundary G_hyp X).ncard
  omega

/-- **Graph Minors X, (4.1)** (page 164):
"(4.1) *If $H$ is a minor of a graph $G$, then $\beta(H) \le \beta(G)$.*" -/
theorem theorem_4_1_proof {G : Graph α β} {H : Graph (Set α) β}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hminor : IsMinor H G) :
    branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ branchWidth (Hypergraph.ofGraph G hV hE) := by
  classical
  obtain ⟨G', hG', C, hC, rfl⟩ := hminor
  let G_hyp := Hypergraph.ofGraph G hV hE
  let H_hyp := Hypergraph.ofGraph (contract G' C) hVH hEH
  change branchWidth H_hyp ≤ branchWidth G_hyp
  by_cases hcardH : 2 ≤ H_hyp.edgeSet.ncard
  · have hEH_sub : H_hyp.edgeSet ⊆ G_hyp.edgeSet := by
      change E(contract G' C) ⊆ E(G)
      have h1 : E(contract G' C) = E(G') \ C := by simp [contract]
      rw [h1]
      exact Set.sdiff_subset.trans hG'.edgeSet_mono
    have hcardG : 2 ≤ G_hyp.edgeSet.ncard :=
      hcardH.trans (Set.ncard_le_ncard hEH_sub G_hyp.edgeSet_finite)
    have hneG : G_hyp.edgeSet.Nonempty := by
      by_contra! hemp
      rw [hemp, Set.ncard_empty] at hcardG
      omega
    have hγG : 1 ≤ maxEdgeSize G_hyp := one_le_maxEdgeSize_ofGraph hneG
    obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγG hcardG
    let k := branchWidth G_hyp
    have hw : branchDecompWidth G_hyp T τ ≤ k := hw_eq.le
    have hT := hbd.isTernaryTree
    let αG (v : ι) (e : Sym2 ι) : Set β := τ '' (leafSet T \ treeComponent T v e)
    let αH (v : ι) (e : Sym2 ι) : Set β := αG v e ∩ H_hyp.edgeSet
    have hαG : IsExactTreeLabelling G_hyp.edgeSet (edgeConnFunc G_hyp k)
        (singletonEdges G_hyp) T αG :=
      isExactTreeLabelling_of_isBranchDecomposition hbd hw
    have hαH_eff : ∀ u e, IsTreeIncidence T u e →
        IsEfficient H_hyp.edgeSet (edgeConnFunc H_hyp k) (αH u e) := by
      intro u e he
      have heffG := hαG.1.isEfficient he
      refine ⟨Set.inter_subset_right, ?_⟩
      have hle1 : (branchEdgeBoundary H_hyp (αG u e ∩ H_hyp.edgeSet)).ncard ≤
          (branchEdgeBoundary G_hyp (αG u e)).ncard :=
        ncard_branchEdgeBoundary_contract_le hG' hV hE hVH hEH heffG.1
      have hle2 := heffG.2
      dsimp [αH, edgeConnFunc, kappa0] at hle2 ⊢
      omega
    have hαG_leaf : ∀ v ∈ leafSet T, ∀ w, T.Adj v w →
        αG v s(v, w) = G_hyp.edgeSet \ {τ v} := by
      intro v hleaf w hadj
      have hcomp := treeComponent_eq_singleton_of_isLeaf hT hadj hleaf
      dsimp [αG]
      rw [hcomp]
      ext x
      simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, ⟨ht, ht_ne⟩, rfl⟩
        exact ⟨hbd.bijOn.mapsTo ht, fun h ↦ ht_ne (hbd.bijOn.injOn ht hleaf h)⟩
      · rintro ⟨hxE, hx_ne⟩
        obtain ⟨t, ht, rfl⟩ := hbd.bijOn.surjOn hxE
        exact ⟨t, ⟨ht, fun h ↦ hx_ne (congrArg τ h)⟩, rfl⟩
    have hαH : IsExactTreeLabelling H_hyp.edgeSet (edgeConnFunc H_hyp k)
        (singletonEdges H_hyp) T αH := by
      refine ⟨⟨hT, hαH_eff, ?_, ?_, ?_⟩, ?_⟩
      · intro u w hadj
        dsimp [αH]
        rw [hαG.1.compl_eq hadj]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_sdiff]
        exact ⟨fun ⟨⟨_, hx_not⟩, hxH⟩ ↦ ⟨hxH, fun h ↦ hx_not h.1⟩,
          fun ⟨hxH, hx_not⟩ ↦ ⟨⟨hEH_sub hxH, fun h ↦ hx_not ⟨h, hxH⟩⟩, hxH⟩⟩
      · intro v e he hleaf
        obtain ⟨w, hadj, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he
        by_cases hτ : τ v ∈ H_hyp.edgeSet
        · right
          refine ⟨{τ v}, ⟨τ v, hτ, rfl⟩, ?_⟩
          dsimp [αH]
          rw [hαG_leaf v hleaf w hadj]
          ext x
          simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨_, hxH⟩ | rfl)
            · exact hxH
            · exact hτ
          · intro hxH
            by_cases hx : x = τ v
            · exact Or.inr hx
            · exact Or.inl ⟨⟨hEH_sub hxH, hx⟩, hxH⟩
        · left
          dsimp [αH]
          rw [hαG_leaf v hleaf w hadj]
          ext x
          simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
          exact ⟨fun h ↦ h.2, fun hxH ↦ ⟨⟨hEH_sub hxH, fun h ↦ hτ (h ▸ hxH)⟩, hxH⟩⟩
      · intro u f₁ f₂ f₃ hf₁ hf₂ hf₃ h12 h13 h23
        have hunionG := hαG.1.degree_three_union_eq hf₁ hf₂ hf₃ h12 h13 h23
        dsimp [αH]
        ext x
        simp only [Set.mem_union, Set.mem_inter_iff]
        constructor
        · rintro ((⟨_, hxH⟩ | ⟨_, hxH⟩) | ⟨_, hxH⟩) <;> exact hxH
        · intro hxH
          have hxG : x ∈ αG u f₁ ∪ αG u f₂ ∪ αG u f₃ := hunionG.symm ▸ hEH_sub hxH
          rcases hxG with (h1 | h2) | h3
          · exact Or.inl (Or.inl ⟨h1, hxH⟩)
          · exact Or.inl (Or.inr ⟨h2, hxH⟩)
          · exact Or.inr ⟨h3, hxH⟩
      · intro u f₁ f₂ hfork
        have hdisjG := hαG.2 hfork
        dsimp [IsExactFork, αH] at hdisjG ⊢
        rw [← Set.subset_empty_iff, ← hdisjG]
        exact fun x ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ ↦ ⟨h1, h2⟩
    have h𝒜H : ∀ A ∈ singletonEdges H_hyp, IsEfficient H_hyp.edgeSet (edgeConnFunc H_hyp k) A := by
      rintro A ⟨f, hfH, rfl⟩
      obtain ⟨v, hv_leaf, rfl⟩ := hbd.bijOn.surjOn (hEH_sub hfH)
      obtain ⟨w, hadj, _⟩ := hT.exists_adj_of_isLeaf hv_leaf
      have heff_vw := hαH_eff v s(v, w) (isTreeIncidence_iff_adj.2 hadj)
      have heq : H_hyp.edgeSet \ αH v s(v, w) = {τ v} := by
        dsimp [αH]
        rw [hαG_leaf v hv_leaf w hadj]
        ext x
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hxH, hnot⟩
          by_contra hx_ne
          exact hnot ⟨⟨hEH_sub hxH, hx_ne⟩, hxH⟩
        · rintro rfl
          exact ⟨hfH, fun ⟨⟨_, hne⟩, _⟩ ↦ hne rfl⟩
      have hcompl : IsEfficient H_hyp.edgeSet (edgeConnFunc H_hyp k)
          (H_hyp.edgeSet \ αH v s(v, w)) :=
        ⟨Set.sdiff_subset, by
          rw [← (isConnectivityFunction_edgeConnFunc H_hyp k).compl_eq heff_vw.1]
          exact heff_vw.2⟩
      rwa [heq] at hcompl
    obtain ⟨ι', _, T', τ', hbd', hw'⟩ :=
      exists_branchDecomposition_of_exactTreeLabelling_of_isEfficient h𝒜H hcardH hαH
    have hmem : branchDecompWidth H_hyp T' τ' ∈
        {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
          IsBranchDecomposition H_hyp T τ ∧ branchDecompWidth H_hyp T τ = w} :=
      ⟨ι', inferInstance, T', τ', hbd', rfl⟩
    exact (Nat.sInf_le hmem).trans hw'
  · rw [branchWidth_eq_zero_of_ncard_edgeSet_le_one (by omega)]
    exact Nat.zero_le _

/-! ## Proof of (4.2)(i) -/

/-- If `e ∈ G.edgeSet` is incident with `v`, then `e ∈ (componentOfVertex G v).edgeSet`. -/
theorem mem_edgeSet_componentOfVertex_of_inc {G : Hypergraph α β} {v : α} {e : β}
    (he : e ∈ G.edgeSet) (hinc : G.Inc e v) :
    e ∈ (componentOfVertex G v).edgeSet := by
  refine ⟨he, fun x hx ↦ ⟨G.vertex_mem_of_inc hx, ?_⟩, v, hinc⟩
  by_cases hvx : v = x
  · exact hvx ▸ SimpleGraph.Reachable.refl v
  · exact SimpleGraph.Adj.reachable ⟨hvx, e, hinc, hx⟩

/-- A graph `G` has branch-width `0` if and only if no two distinct edges of `G` share a vertex
(Graph Minors X, Section 4, proof of (4.2)(i), page 165). -/
theorem branchWidth_ofGraph_eq_zero_iff_disjoint_edges
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) :
    branchWidth (Hypergraph.ofGraph G hV hE) = 0 ↔
      ∀ e₁ ∈ (Hypergraph.ofGraph G hV hE).edgeSet,
      ∀ e₂ ∈ (Hypergraph.ofGraph G hV hE).edgeSet, e₁ ≠ e₂ →
      ∀ v, ¬ ((Hypergraph.ofGraph G hV hE).Inc e₁ v ∧ (Hypergraph.ofGraph G hV hE).Inc e₂ v) := by
  let G_hyp := Hypergraph.ofGraph G hV hE
  change branchWidth G_hyp = 0 ↔ _
  constructor
  · rintro hbw e₁ he₁ e₂ he₂ hne v ⟨hinc₁, hinc₂⟩
    have hcard : 2 ≤ G_hyp.edgeSet.ncard := by
      have hsub : ({e₁, e₂} : Set β) ⊆ G_hyp.edgeSet := by
        rintro x (rfl | rfl) <;> assumption
      have h2 : ({e₁, e₂} : Set β).ncard = 2 := Set.ncard_pair hne
      exact h2 ▸ Set.ncard_le_ncard hsub G_hyp.edgeSet_finite
    have hγ : 1 ≤ maxEdgeSize G_hyp := one_le_maxEdgeSize_ofGraph ⟨e₁, he₁⟩
    obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγ hcard
    obtain ⟨t₁, ht₁, hτ₁⟩ := hbd.bijOn.surjOn he₁
    obtain ⟨w, hadj, _⟩ := hbd.isTernaryTree.exists_adj_of_isLeaf ht₁
    have hmem : v ∈ branchEdgeBoundary G_hyp {τ t₁} := by
      rw [hτ₁]
      exact ⟨G_hyp.vertex_mem_of_inc hinc₁, ⟨e₁, Set.mem_singleton e₁, hinc₁⟩,
        ⟨e₂, ⟨he₂, hne.symm⟩, hinc₂⟩⟩
    have hpos : 1 ≤ (branchEdgeBoundary G_hyp {τ t₁}).ncard :=
      (Set.ncard_pos (branchEdgeBoundary_finite G_hyp _)).2 ⟨v, hmem⟩
    have hle1 := ncard_branchEdgeBoundary_singleton_le_branchEdgeOrder hbd ht₁ hadj
    have hle2 := branchEdgeOrder_le_branchDecompWidth (G := G_hyp) (τ := τ) (T.mem_edgeSet.2 hadj)
    omega
  · intro hdisj
    by_cases hcard : 2 ≤ G_hyp.edgeSet.ncard
    · have hne : G_hyp.edgeSet.Nonempty := by
        by_contra! hemp
        rw [hemp, Set.ncard_empty] at hcard
        omega
      have hγ : 1 ≤ maxEdgeSize G_hyp := one_le_maxEdgeSize_ofGraph hne
      obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγ hcard
      rw [← hw_eq]
      apply Nat.eq_zero_of_le_zero
      rw [branchDecompWidth_le_iff]
      intro e he
      have hemp : {v ∈ G_hyp.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
          ¬ (T.deleteEdges {e}).Reachable t₁ t₂ ∧ G_hyp.Inc (τ t₁) v ∧ G_hyp.Inc (τ t₂) v} = ∅ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, t₁, ht₁, t₂, ht₂, hnot_reach, hinc₁, hinc₂⟩
        have hne_t : t₁ ≠ t₂ := fun h ↦ hnot_reach (h ▸ SimpleGraph.Reachable.refl t₁)
        have hne_τ : τ t₁ ≠ τ t₂ := fun h ↦ hne_t (hbd.bijOn.injOn ht₁ ht₂ h)
        exact hdisj (τ t₁) (hbd.bijOn.mapsTo ht₁) (τ t₂) (hbd.bijOn.mapsTo ht₂) hne_τ v
          ⟨hinc₁, hinc₂⟩
      simp [branchEdgeOrder, hemp]
    · exact branchWidth_eq_zero_of_ncard_edgeSet_le_one (by omega)

/-- Part (i) of **Graph Minors X, (4.2)** (page 165):
A graph `G` has branch-width `0` if and only if every component of `G` has `≤ 1` edge. -/
theorem branchWidth_eq_zero_iff_components_le_one_edge
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) :
    branchWidth (Hypergraph.ofGraph G hV hE) = 0 ↔
      ∀ C, IsConnectedComponent (Hypergraph.ofGraph G hV hE) C → C.edgeSet.ncard ≤ 1 := by
  let G_hyp := Hypergraph.ofGraph G hV hE
  rw [branchWidth_ofGraph_eq_zero_iff_disjoint_edges hV hE]
  constructor
  · intro hdisj C hC
    rw [Set.ncard_le_one_iff C.edgeSet_finite]
    intro e₁ e₂ he₁ he₂
    by_contra hne
    have he₁G : e₁ ∈ G_hyp.edgeSet := hC.1.1.edgeSet_subset he₁
    have he₂G : e₂ ∈ G_hyp.edgeSet := hC.1.1.edgeSet_subset he₂
    obtain ⟨u, hu_inc⟩ := nonempty_ends_ofGraph he₁G
    obtain ⟨v, hv_inc⟩ := nonempty_ends_ofGraph he₂G
    have huC : u ∈ C.vertexSet :=
      C.vertex_mem_of_inc ((inc_iff_of_le hC.1.1 he₁).2 hu_inc)
    have hvC : v ∈ C.vertexSet :=
      C.vertex_mem_of_inc ((inc_iff_of_le hC.1.1 he₂).2 hv_inc)
    obtain ⟨w⟩ := hC.1.2.2 u huC v hvC
    have hwalk_ends : ∀ {x y : α} (p : C.skeleton.Walk x y),
        G_hyp.Inc e₁ x → G_hyp.Inc e₁ y := by
      intro x y p
      induction p with
      | nil => exact id
      | @cons a b c hadj p' ih =>
        intro hinc_a
        obtain ⟨_, e, hinc_ea, hinc_eb⟩ := id hadj
        have heC : e ∈ C.edgeSet := C.edge_mem_of_inc hinc_ea
        have heG : e ∈ G_hyp.edgeSet := hC.1.1.edgeSet_subset heC
        have hinc_eaG : G_hyp.Inc e a := (inc_iff_of_le hC.1.1 heC).1 hinc_ea
        have hinc_ebG : G_hyp.Inc e b := (inc_iff_of_le hC.1.1 heC).1 hinc_eb
        have he_eq : e = e₁ := by
          by_contra hne_e
          exact hdisj e₁ he₁G e heG (Ne.symm hne_e) a ⟨hinc_a, hinc_eaG⟩
        exact ih (he_eq ▸ hinc_ebG)
    exact hdisj e₁ he₁G e₂ he₂G hne v ⟨hwalk_ends w hu_inc, hv_inc⟩
  · intro hcomp e₁ he₁ e₂ he₂ hne v ⟨hinc₁, hinc₂⟩
    have hvG : v ∈ G_hyp.vertexSet := G_hyp.vertex_mem_of_inc hinc₁
    have hG_graph : G_hyp.IsGraph := ofGraph_isGraph G hV hE
    have hC := isConnectedComponent_componentOfVertex hG_graph hvG
    have he₁C : e₁ ∈ (componentOfVertex G_hyp v).edgeSet :=
      mem_edgeSet_componentOfVertex_of_inc he₁ hinc₁
    have he₂C : e₂ ∈ (componentOfVertex G_hyp v).edgeSet :=
      mem_edgeSet_componentOfVertex_of_inc he₂ hinc₂
    have hle := hcomp (componentOfVertex G_hyp v) hC
    have hsub : ({e₁, e₂} : Set β) ⊆ (componentOfVertex G_hyp v).edgeSet := by
      rintro x (rfl | rfl) <;> assumption
    have h2 : ({e₁, e₂} : Set β).ncard = 2 := Set.ncard_pair hne
    have hge : 2 ≤ (componentOfVertex G_hyp v).edgeSet.ncard :=
      h2 ▸ Set.ncard_le_ncard hsub (componentOfVertex G_hyp v).edgeSet_finite
    omega

/-! ## Proof of (4.2)(ii) -/

/-- For any bias `ℬ` on `G.edgeSet` for `edgeConnFunc G k`, `∅ ∈ ℬ`. -/
theorem empty_mem_of_isBias_edgeConnFunc {G : Hypergraph α β} {k : ℕ} {ℬ : Set (Set β)}
    (hbias : IsBias G.edgeSet (edgeConnFunc G k) ℬ) :
    ∅ ∈ ℬ := by
  have heff : IsEfficient G.edgeSet (edgeConnFunc G k) ∅ := by
    refine ⟨Set.empty_subset _, ?_⟩
    simp [edgeConnFunc, kappa0, branchEdgeBoundary_empty]
  rcases hbias.mem_or_compl_mem heff with h | h
  · exact h
  · rw [Set.sdiff_empty] at h
    exfalso
    exact hbias.union_ne h h h (by simp)

/-- For any bias `ℬ` on `G.edgeSet` for `edgeConnFunc G k`, if `X ∈ ℬ`, `Y ∈ ℬ`, and `X ∪ Y` is
efficient, then `X ∪ Y ∈ ℬ`. -/
theorem union_mem_of_isBias_edgeConnFunc {G : Hypergraph α β} {k : ℕ} {ℬ : Set (Set β)}
    (hbias : IsBias G.edgeSet (edgeConnFunc G k) ℬ) {X Y : Set β}
    (hX : X ∈ ℬ) (hY : Y ∈ ℬ) (heff : IsEfficient G.edgeSet (edgeConnFunc G k) (X ∪ Y)) :
    X ∪ Y ∈ ℬ := by
  rcases hbias.mem_or_compl_mem heff with h | h
  · exact h
  · exfalso
    have hU : X ∪ Y ∪ (G.edgeSet \ (X ∪ Y)) = G.edgeSet :=
      Set.union_sdiff_cancel heff.1
    exact hbias.union_ne hX hY h hU

/-- For any vertex `v ∈ G.vertexSet`, the edge set of `componentOfVertex G v` has empty vertex
boundary in `G`. -/
theorem branchEdgeBoundary_componentOfVertex_eq_empty {G : Hypergraph α β} (v : α) :
    branchEdgeBoundary G (componentOfVertex G v).edgeSet = ∅ := by
  ext w
  simp only [branchEdgeBoundary, Set.mem_sep_iff, Set.mem_sdiff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, ⟨e₁, he₁C, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂notC⟩, hinc₂⟩⟩
  have hwC : w ∈ (componentOfVertex G v).vertexSet := he₁C.2.1 hinc₁
  apply he₂notC
  refine ⟨he₂G, fun z hz ↦ ⟨G.vertex_mem_of_inc hz, ?_⟩, w, hinc₂⟩
  by_cases hwz : w = z
  · exact hwz ▸ hwC.2
  · exact hwC.2.trans (SimpleGraph.Adj.reachable ⟨hwz, e₂, hinc₂, hz⟩)

/-- Part (ii) of **Graph Minors X, (4.2)** (page 165):
A graph `G` has branch-width `≤ 1` if and only if every component of `G` has `≤ 1` vertex of
valency `≥ 2`.

The printed proof names only a two-edge circuit and a three-edge path as minor
obstructions. These miss the graph consisting of one edge and a loop at each end,
which has only one non-loop edge. The forward proof below corrects this loop case
by bounding the leaf cut at an edge joining two vertices of valency at least two.
`Section4LoopExample` verifies the counterexample to the named-obstruction argument. -/
theorem branchWidth_le_one_iff_components_le_one_deg_ge_two
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) :
    branchWidth (Hypergraph.ofGraph G hV hE) ≤ 1 ↔
      ∀ C, IsConnectedComponent (Hypergraph.ofGraph G hV hE) C →
        {v ∈ C.vertexSet |
          2 ≤ {e ∈ (Hypergraph.ofGraph G hV hE).edgeSet |
            (Hypergraph.ofGraph G hV hE).Inc e v}.ncard}.ncard ≤ 1 := by
  classical
  let G_hyp := Hypergraph.ofGraph G hV hE
  have hG_graph : G_hyp.IsGraph := ofGraph_isGraph G hV hE
  constructor
  · intro hbw C hC
    rw [Set.ncard_le_one_iff (C.vertexSet_finite.subset fun _ h ↦ h.1)]
    rintro u v ⟨huC, hu_deg⟩ ⟨hvC, hv_deg⟩
    by_contra hne
    obtain ⟨w_walk⟩ := hC.1.2.2 u huC v hvC
    obtain ⟨p, hp⟩ := w_walk.toPath
    cases p with
    | nil => exact hne rfl
    | @cons _ w _ hadj p' =>
      have hp_cons := hp.support_nodup
      have hu_not_mem : u ∉ p'.support := by
        intro hu_mem
        have hnodup : (u :: p'.support).Nodup := hp_cons
        exact (List.nodup_cons.1 hnodup).1 hu_mem
      obtain ⟨huw_ne, e₁, hinc₁u_C, hinc₁w_C⟩ := id hadj
      have he₁C : e₁ ∈ C.edgeSet := C.edge_mem_of_inc hinc₁u_C
      have he₁G : e₁ ∈ G_hyp.edgeSet := hC.1.1.edgeSet_subset he₁C
      have hinc₁u : G_hyp.Inc e₁ u := (inc_iff_of_le hC.1.1 he₁C).1 hinc₁u_C
      have hinc₁w : G_hyp.Inc e₁ w := (inc_iff_of_le hC.1.1 he₁C).1 hinc₁w_C
      have hw_deg : 2 ≤ {e ∈ G_hyp.edgeSet | G_hyp.Inc e w}.ncard := by
        cases p' with
        | nil => exact hv_deg
        | @cons _ w₂ _ hadj₂ p'' =>
          have hw₂_ne_u : w₂ ≠ u := by
            intro h
            apply hu_not_mem
            rw [← h]
            simp
          obtain ⟨hw_w₂_ne, e₂, hinc₂w_C, hinc₂w₂_C⟩ := id hadj₂
          have he₂C : e₂ ∈ C.edgeSet := C.edge_mem_of_inc hinc₂w_C
          have he₂G : e₂ ∈ G_hyp.edgeSet := hC.1.1.edgeSet_subset he₂C
          have hinc₂w : G_hyp.Inc e₂ w := (inc_iff_of_le hC.1.1 he₂C).1 hinc₂w_C
          have hinc₂w₂ : G_hyp.Inc e₂ w₂ := (inc_iff_of_le hC.1.1 he₂C).1 hinc₂w₂_C
          have he₁₂_ne : e₁ ≠ e₂ := by
            intro heq
            subst heq
            have hsub : ({u, w, w₂} : Set α) ⊆ G_hyp.ends e₁ := by
              rintro x (rfl | rfl | rfl)
              · exact hinc₁u
              · exact hinc₁w
              · exact hinc₂w₂
            have h3 : ({u, w, w₂} : Set α).ncard = 3 := by
              rw [Set.ncard_insert_of_notMem, Set.ncard_pair hw_w₂_ne]
              simp [huw_ne, hw₂_ne_u.symm]
            have hle2 : edgeSize G_hyp e₁ ≤ 2 := edgeSize_ofGraph_le_two G hV hE e₁
            have hge3 : 3 ≤ edgeSize G_hyp e₁ :=
              h3 ▸ Set.ncard_le_ncard hsub (ends_finite G_hyp e₁)
            omega
          have hsub_e : ({e₁, e₂} : Set β) ⊆ {e ∈ G_hyp.edgeSet | G_hyp.Inc e w} := by
            rintro x (rfl | rfl)
            · exact ⟨he₁G, hinc₁w⟩
            · exact ⟨he₂G, hinc₂w⟩
          have h2 : ({e₁, e₂} : Set β).ncard = 2 := Set.ncard_pair he₁₂_ne
          exact h2 ▸ Set.ncard_le_ncard hsub_e (G_hyp.edgeSet_finite.subset fun _ h ↦ h.1)
      have hex_other : ∀ x : α, 2 ≤ {e ∈ G_hyp.edgeSet | G_hyp.Inc e x}.ncard →
          ∃ e ∈ G_hyp.edgeSet \ {e₁}, G_hyp.Inc e x := by
        intro x hx_deg
        by_contra! hno
        have hsub : {e ∈ G_hyp.edgeSet | G_hyp.Inc e x} ⊆ {e₁} := by
          intro e ⟨heG, hinc⟩
          by_contra he_ne
          exact hno e ⟨heG, he_ne⟩ hinc
        have hle1 : {e ∈ G_hyp.edgeSet | G_hyp.Inc e x}.ncard ≤ 1 :=
          (Set.ncard_le_ncard hsub (Set.finite_singleton e₁)).trans (by simp)
        omega
      obtain ⟨eu, heu, hinc_eu⟩ := hex_other u hu_deg
      obtain ⟨ew, hew, hinc_ew⟩ := hex_other w hw_deg
      have hu_bd : u ∈ branchEdgeBoundary G_hyp {e₁} :=
        ⟨G_hyp.vertex_mem_of_inc hinc₁u, ⟨e₁, Set.mem_singleton e₁, hinc₁u⟩, ⟨eu, heu, hinc_eu⟩⟩
      have hw_bd : w ∈ branchEdgeBoundary G_hyp {e₁} :=
        ⟨G_hyp.vertex_mem_of_inc hinc₁w, ⟨e₁, Set.mem_singleton e₁, hinc₁w⟩, ⟨ew, hew, hinc_ew⟩⟩
      have hbd_ge2 : 2 ≤ (branchEdgeBoundary G_hyp {e₁}).ncard := by
        have hsub : ({u, w} : Set α) ⊆ branchEdgeBoundary G_hyp {e₁} := by
          rintro x (rfl | rfl) <;> assumption
        have h2 : ({u, w} : Set α).ncard = 2 := Set.ncard_pair huw_ne
        exact h2 ▸ Set.ncard_le_ncard hsub (branchEdgeBoundary_finite G_hyp _)
      have hcardG : 2 ≤ G_hyp.edgeSet.ncard := by
        have hsub : ({e₁, eu} : Set β) ⊆ G_hyp.edgeSet := by
          rintro x (rfl | rfl)
          · exact he₁G
          · exact heu.1
        have h2 : ({e₁, eu} : Set β).ncard = 2 := Set.ncard_pair (Ne.symm heu.2)
        exact h2 ▸ Set.ncard_le_ncard hsub G_hyp.edgeSet_finite
      have hγG : 1 ≤ maxEdgeSize G_hyp := one_le_maxEdgeSize_ofGraph ⟨e₁, he₁G⟩
      obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγG hcardG
      obtain ⟨t₁, ht₁, hτ₁⟩ := hbd.bijOn.surjOn he₁G
      obtain ⟨z, hadj_z, _⟩ := hbd.isTernaryTree.exists_adj_of_isLeaf ht₁
      have hle1 : (branchEdgeBoundary G_hyp {e₁}).ncard ≤ branchEdgeOrder G_hyp T τ s(t₁, z) := by
        rw [← hτ₁]
        exact ncard_branchEdgeBoundary_singleton_le_branchEdgeOrder hbd ht₁ hadj_z
      have hle2 :=
        branchEdgeOrder_le_branchDecompWidth (G := G_hyp) (τ := τ) (T.mem_edgeSet.2 hadj_z)
      have hbw' : branchWidth G_hyp ≤ 1 := hbw
      omega
  · intro hcomp
    change branchWidth G_hyp ≤ 1
    by_cases hcard : 2 ≤ G_hyp.edgeSet.ncard
    · have hX_eff_of_sub : ∀ {C : Hypergraph α β}, IsConnectedComponent G_hyp C →
          ∀ {X : Set β}, X ⊆ C.edgeSet → IsEfficient G_hyp.edgeSet (edgeConnFunc G_hyp 1) X := by
        intro C hC X hX
        refine ⟨hX.trans hC.1.1.edgeSet_subset, ?_⟩
        have hsub : branchEdgeBoundary G_hyp X ⊆
            {v ∈ C.vertexSet | 2 ≤ {e ∈ G_hyp.edgeSet | G_hyp.Inc e v}.ncard} := by
          rintro v ⟨_, ⟨e₁, he₁X, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂notX⟩, hinc₂⟩⟩
          have he₁C : e₁ ∈ C.edgeSet := hX he₁X
          have he₁G : e₁ ∈ G_hyp.edgeSet := hC.1.1.edgeSet_subset he₁C
          have hvC : v ∈ C.vertexSet :=
            C.vertex_mem_of_inc ((inc_iff_of_le hC.1.1 he₁C).2 hinc₁)
          have hne : e₁ ≠ e₂ := fun h ↦ he₂notX (h ▸ he₁X)
          have hsub_e : ({e₁, e₂} : Set β) ⊆ {e ∈ G_hyp.edgeSet | G_hyp.Inc e v} := by
            rintro x (rfl | rfl)
            · exact ⟨he₁G, hinc₁⟩
            · exact ⟨he₂G, hinc₂⟩
          have h2 : ({e₁, e₂} : Set β).ncard = 2 := Set.ncard_pair hne
          exact ⟨hvC, h2 ▸ Set.ncard_le_ncard hsub_e (G_hyp.edgeSet_finite.subset fun _ h ↦ h.1)⟩
        have hle1 : (branchEdgeBoundary G_hyp X).ncard ≤ 1 :=
          (Set.ncard_le_ncard hsub (C.vertexSet_finite.subset fun _ h ↦ h.1)).trans (hcomp C hC)
        dsimp [edgeConnFunc, kappa0]
        omega
      have h𝒜 : ∀ A ∈ singletonEdges G_hyp,
          IsEfficient G_hyp.edgeSet (edgeConnFunc G_hyp 1) A := by
        rintro _ ⟨e, heG, rfl⟩
        obtain ⟨v, hv_inc⟩ := nonempty_ends_ofGraph heG
        have hvG : v ∈ G_hyp.vertexSet := G_hyp.vertex_mem_of_inc hv_inc
        have hC := isConnectedComponent_componentOfVertex hG_graph hvG
        have heC : e ∈ (componentOfVertex G_hyp v).edgeSet :=
          mem_edgeSet_componentOfVertex_of_inc heG hv_inc
        exact hX_eff_of_sub hC (Set.singleton_subset_iff.2 heC)
      have hno_bias :
          ¬ ∃ ℬ, BiasExtends G_hyp.edgeSet (edgeConnFunc G_hyp 1) (singletonEdges G_hyp) ℬ := by
        rintro ⟨ℬ, hbias, hsub_sing⟩
        have hemp_mem : ∅ ∈ ℬ := empty_mem_of_isBias_edgeConnFunc hbias
        have hcomp_mem : ∀ v ∈ G_hyp.vertexSet, (componentOfVertex G_hyp v).edgeSet ∈ ℬ := by
          intro v hvG
          let C := componentOfVertex G_hyp v
          have hC : IsConnectedComponent G_hyp C :=
            isConnectedComponent_componentOfVertex hG_graph hvG
          have hsub_ind : ∀ X : Set β, X.Finite → X ⊆ C.edgeSet → X ∈ ℬ := by
            intro X hX_fin
            refine Set.Finite.induction_on X hX_fin (fun _ ↦ hemp_mem) ?_
            intro a s _ _ ih has_sub
            have haC : a ∈ C.edgeSet := has_sub (Set.mem_insert a s)
            have hsC : s ⊆ C.edgeSet := (Set.subset_insert a s).trans has_sub
            have ha_mem : ({a} : Set β) ∈ ℬ :=
              hsub_sing ⟨a, hC.1.1.edgeSet_subset haC, rfl⟩
            have hs_mem : s ∈ ℬ := ih hsC
            have heff_ins : IsEfficient G_hyp.edgeSet (edgeConnFunc G_hyp 1) ({a} ∪ s) := by
              rw [Set.singleton_union]
              exact hX_eff_of_sub hC has_sub
            have hunion := union_mem_of_isBias_edgeConnFunc hbias ha_mem hs_mem heff_ins
            simpa using hunion
          exact hsub_ind C.edgeSet C.edgeSet_finite Set.Subset.rfl
        have hunion_verts : ∀ S : Set α, S.Finite → S ⊆ G_hyp.vertexSet →
            (⋃ v ∈ S, (componentOfVertex G_hyp v).edgeSet) ⊆ G_hyp.edgeSet ∧
            branchEdgeBoundary G_hyp (⋃ v ∈ S, (componentOfVertex G_hyp v).edgeSet) = ∅ ∧
            (⋃ v ∈ S, (componentOfVertex G_hyp v).edgeSet) ∈ ℬ := by
          intro S hS_fin
          refine Set.Finite.induction_on S hS_fin ?_ ?_
          · intro _
            simp [branchEdgeBoundary_empty, hemp_mem]
          · intro v s _ _ ih hvs_sub
            have hvG : v ∈ G_hyp.vertexSet := hvs_sub (Set.mem_insert v s)
            have hsG : s ⊆ G_hyp.vertexSet := (Set.subset_insert v s).trans hvs_sub
            obtain ⟨hs_subE, hs_bd, hs_mem⟩ := ih hsG
            have hv_subE : (componentOfVertex G_hyp v).edgeSet ⊆ G_hyp.edgeSet :=
              (componentOfVertex_le G_hyp v).edgeSet_subset
            have hv_bd : branchEdgeBoundary G_hyp (componentOfVertex G_hyp v).edgeSet = ∅ :=
              branchEdgeBoundary_componentOfVertex_eq_empty v
            have hv_mem : (componentOfVertex G_hyp v).edgeSet ∈ ℬ := hcomp_mem v hvG
            rw [Set.biUnion_insert]
            have hbd_u : branchEdgeBoundary G_hyp
                ((componentOfVertex G_hyp v).edgeSet ∪
                  ⋃ x ∈ s, (componentOfVertex G_hyp x).edgeSet) = ∅ := by
              rw [← Set.subset_empty_iff]
              rintro w ⟨_, ⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂not⟩, hinc₂⟩⟩
              rcases he₁ with he₁v | he₁s
              · have hw_in : w ∈ branchEdgeBoundary G_hyp (componentOfVertex G_hyp v).edgeSet :=
                  ⟨G_hyp.vertex_mem_of_inc hinc₁, ⟨e₁, he₁v, hinc₁⟩,
                    ⟨e₂, ⟨he₂G, fun h ↦ he₂not (Or.inl h)⟩, hinc₂⟩⟩
                rw [hv_bd] at hw_in
                exact hw_in
              · have hw_in : w ∈ branchEdgeBoundary G_hyp
                    (⋃ x ∈ s, (componentOfVertex G_hyp x).edgeSet) :=
                  ⟨G_hyp.vertex_mem_of_inc hinc₁, ⟨e₁, he₁s, hinc₁⟩,
                    ⟨e₂, ⟨he₂G, fun h ↦ he₂not (Or.inr h)⟩, hinc₂⟩⟩
                rw [hs_bd] at hw_in
                exact hw_in
            have hsub_u : (componentOfVertex G_hyp v).edgeSet ∪
                (⋃ x ∈ s, (componentOfVertex G_hyp x).edgeSet) ⊆ G_hyp.edgeSet :=
              Set.union_subset hv_subE hs_subE
            have heff_u : IsEfficient G_hyp.edgeSet (edgeConnFunc G_hyp 1)
                ((componentOfVertex G_hyp v).edgeSet ∪
                  ⋃ x ∈ s, (componentOfVertex G_hyp x).edgeSet) := by
              refine ⟨hsub_u, ?_⟩
              simp [edgeConnFunc, kappa0, hbd_u]
            exact ⟨hsub_u, hbd_u, union_mem_of_isBias_edgeConnFunc hbias hv_mem hs_mem heff_u⟩
        obtain ⟨_, _, hV_mem⟩ :=
          hunion_verts G_hyp.vertexSet G_hyp.vertexSet_finite Set.Subset.rfl
        have hU_eq : (⋃ v ∈ G_hyp.vertexSet, (componentOfVertex G_hyp v).edgeSet) =
            G_hyp.edgeSet := by
          ext e
          rw [Set.mem_iUnion₂]
          constructor
          · rintro ⟨v, _, heC⟩
            exact (componentOfVertex_le G_hyp v).edgeSet_subset heC
          · intro heG
            obtain ⟨v, hv_inc⟩ := nonempty_ends_ofGraph heG
            have hvG : v ∈ G_hyp.vertexSet := G_hyp.vertex_mem_of_inc hv_inc
            exact ⟨v, hvG, mem_edgeSet_componentOfVertex_of_inc heG hv_inc⟩
        rw [hU_eq] at hV_mem
        exact hbias.union_ne hV_mem hV_mem hV_mem (by simp)
      obtain ⟨ι, _, T, α, hα⟩ := theorem_3_4_proof G_hyp.edgeSet_finite
        (isConnectivityFunction_edgeConnFunc G_hyp 1) h𝒜 hno_bias
      obtain ⟨ι', _, T', τ', hbd', hw'⟩ :=
        exists_branchDecomposition_of_exactTreeLabelling_of_isEfficient h𝒜 hcard hα
      have hmem : branchDecompWidth G_hyp T' τ' ∈
          {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
            IsBranchDecomposition G_hyp T τ ∧ branchDecompWidth G_hyp T τ = w} :=
        ⟨ι', inferInstance, T', τ', hbd', rfl⟩
      exact (Nat.sInf_le hmem).trans hw'
    · rw [branchWidth_eq_zero_of_ncard_edgeSet_le_one (by omega)]
      omega

end GraphMinor.GM10
