module

public import GraphMinor.GM22.Section7d4

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII – Section 7.4 (Part 5): Claim (10) and Theorem 7.4

This file completes the formalization of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (page 556):

- `lemma_7_4_claim_10`: Claim (10) of (7.4) (page 556).
- `theorem_7_4`: **Graph Minors XXII, (7.4)** (pages 552–556).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Proof of Claim (10) of Theorem 7.4 (page 556) -/

set_option maxHeartbeats 800000 in
/-- **Graph Minors XXII, (7.4) Claim (10)** (page 556):
"(10) *For $1 \le i \le t$ there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |\bar{\pi}(A'_i)|$ and with $D(A'_i) \subseteq ins(F)$.*" -/
theorem lemma_7_4_claim_10
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal)
    (hA'_mem : ∀ j : Fin t, A_fam' j ∈ 𝒜)
    (h_iii_disj : ∀ j : Fin t, Disjoint (D (A_fam' j)) Δ)
    (i : Fin t) :
    ¬ ∃ F : Set S, IsOArc F ∧ c.Γ.IsNormal F ∧
      (F ∩ c.Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ c.ins F := by
  rintro ⟨F, hOArc, hNorm, hF_lt_π, hDA'_sub⟩
  let G := R_G.G.toGraph
  have hΓ_le_G : c.Γ_emb ≤ G := c.hJ.Γ_le.trans Graph.deleteVerts_le
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface c.hJ.isSphere
  have hT : IsTangle c.Γ.toHypergraph c.ord c.T := c.hJ.hasMetric.1.2.1
  have hπ_eq_len : (Set.range (πS (A_fam' i))).ncard = πLen (A_fam' i) := by
    rw [Set.ncard_range_of_injective (c.hJ.π_valid (A_fam' i) (hA'_mem i)).2.2.1, Nat.card_fin]
  have hF_lt_len : (F ∩ c.Γ.V).ncard < πLen (A_fam' i) := hπ_eq_len ▸ hF_lt_π
  have hlen_le_3 : πLen (A_fam' i) ≤ 3 := (c.hJ.π_valid (A_fam' i) (hA'_mem i)).2.1
  have hF_lt_ord : (F ∩ c.Γ.V).ncard < c.ord := by
    have := c.hJ.four_le_θ; have := c.hJ.θ_le_ord; omega
  let Δ₁ := c.ins F
  have hIns : IsTangleIns c.Γ c.T F Δ₁ := c.hJ.ins_spec F hOArc hNorm hF_lt_ord
  let C_Γ₀ := (PaintingOrDrawing.drawing c.Γ).inter Δ₁
  let D_Γ₀ := (PaintingOrDrawing.drawing c.Γ).interOutside Δ₁
  have hC₀D₀_T : (C_Γ₀, D_Γ₀) ∈ c.T := hIns.2.2
  have hsep_Γ₀ : c.Γ.toHypergraph.IsSeparation C_Γ₀ D_Γ₀ := hT.isSeparation hC₀D₀_T
  have hord_Γ₀_lt : separationOrder C_Γ₀ D_Γ₀ < πLen (A_fam' i) := by
    have hsub : (C_Γ₀ ∩ D_Γ₀).vertexSet ⊆ F ∩ c.Γ.V := by
      rintro x ⟨⟨hxV, hxΔ₁⟩, ⟨_, hxOut⟩⟩
      refine ⟨?_, hxV⟩
      rw [← hIns.2.1]
      exact ⟨subset_closure hxΔ₁, hxOut⟩
    exact lt_of_le_of_lt
      (Set.ncard_le_ncard hsub (c.Γ.finite_V.subset inter_subset_right)) hF_lt_len
  -- Step 1: Check `(A_fam' i)_Γ ≤ C_Γ₀` and `K₁_Γ ≤ D_Γ₀` using 7.1(i).
  let K_Γ := subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G K c.hJ.sep_NK.1.2.1
  let A_Γ_of : ∀ A : Graph α β, Hypergraph S (Set S) :=
    fun A => (PaintingOrDrawing.drawing c.Γ).inter (D A)
  have hA'i_Γ_le : A_Γ_of (A_fam' i) ≤ C_Γ₀ := by
    rw [GM10.le_iff_of_le (subHypergraphOfSubgraph_eq_drawing_inter c.hJ (hA'_mem i)).2.2.left_le
      hsep_Γ₀.left_le]
    exact ⟨inter_subset_inter_right _ hDA'_sub,
      fun e ⟨he, heD⟩ => ⟨he, heD.trans hDA'_sub⟩⟩
  let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ)}
  let K₁ := graphUnion K (subgraphSUnion G 𝒜_far)
  have h71_i := (theorem_7_1_proof c.hJ).1.1
  -- No vertex `v ∈ c.Γ.V ∩ Δ₁` can have `c.ιV v ∈ V(K₁)`.
  have hno_v_K₁_Δ₁ : ∀ v ∈ c.Γ.V, v ∈ Δ₁ → c.ιV v ∉ V(K₁) := by
    intro v hvV hvΔ₁ hvK₁
    have hdist_ge : θ ≤ subsetTangleDist c.Γ c.ord c.d {v} (Set.univ \ Δ) :=
      h71_i v hvV hvK₁
    obtain ⟨x₀, hx₀D⟩ := GM14.IsClosedDisc.nonempty (c.hJ.disc_D (A_fam' i) (hA'_mem i)).1
    obtain ⟨z, hzA, hx₀z⟩ := GM11.exists_atom c.Γ x₀
    have hv_atom : ({v} : Set S) ∈ c.Γ.A := Or.inl (Or.inl ⟨v, hvV, rfl⟩)
    have hd_le := GM12.dist_le_of_oarc_disc hS c.hJ.hasMetric hOArc hNorm hF_lt_ord
      hIns.1 hIns.2.1 hIns.2.2 hv_atom hzA ⟨v, rfl, hvΔ₁⟩ ⟨x₀, hx₀z, hDA'_sub hx₀D⟩
    have hx₀_not_Δ : x₀ ∈ Set.univ \ Δ :=
      ⟨mem_univ x₀, Set.disjoint_left.mp (h_iii_disj i) hx₀D⟩
    have hsub_le : subsetTangleDist c.Γ c.ord c.d {v} (Set.univ \ Δ) ≤ c.d {v} z :=
      subsetTangleDist_le_of_mem hv_atom hzA ⟨v, rfl, rfl⟩ ⟨x₀, hx₀z, hx₀_not_Δ⟩
    have := c.hJ.four_le_θ
    omega
  have hK_Γ_le : K_Γ ≤ D_Γ₀ := by
    rw [GM10.le_iff_of_le (subHypergraphOfSubgraph_le c.Γ c.ιV c.ιE hΓ_le_G K c.hJ.sep_NK.1.2.1)
      hsep_Γ₀.right_le]
    refine ⟨?_, ?_⟩
    · rintro v ⟨hvK, hvV⟩
      refine ⟨hvV, subset_closure ⟨mem_univ v, fun hvΔ₁ => ?_⟩⟩
      exact hno_v_K₁_Δ₁ v hvV hvΔ₁ (Or.inl hvK)
    · rintro e ⟨heK, heE⟩
      have heN : c.ιE e ∈ E(N) := by
        rw [congr_arg Graph.edgeSet c.hJ.N_eq, edgeSet_graphUnion, edgeSet_graphUnion]
        exact Or.inl (Or.inl ⟨e, heE, rfl⟩)
      exact False.elim (Set.disjoint_left.mp c.hJ.sep_NK.1.2.2.2.2 heN heK)
  have hfar_Γ_le : ∀ A ∈ 𝒜_far, A_Γ_of A ≤ D_Γ₀ := by
    rintro A ⟨hA, hAdist⟩
    have ⟨hA_eq, _, hsep_A⟩ := subHypergraphOfSubgraph_eq_drawing_inter c.hJ hA
    rw [GM10.le_iff_of_le hsep_A.left_le hsep_Γ₀.right_le]
    have hfar_le_G : ∀ A' ∈ 𝒜_far, A' ≤ G := fun A' hA' => c.hJ.le_of_mem_𝒜 A' hA'.1
    have hA_le_K₁ : A ≤ K₁ :=
      (le_subgraphSUnion hfar_le_G ⟨hA, hAdist⟩).trans
        (le_graphUnion_right (Compatible.of_le_le c.hJ.sep_NK.1.2.1 (subgraphSUnion_le hfar_le_G)))
    refine ⟨?_, ?_⟩
    · rintro v ⟨hvV, hvD⟩
      have hv_A : v ∈ (subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G A (c.hJ.le_of_mem_𝒜 A hA)).vertexSet := by
        rw [hA_eq]; exact ⟨hvV, hvD⟩
      refine ⟨hvV, subset_closure ⟨mem_univ v, fun hvΔ₁ => ?_⟩⟩
      exact hno_v_K₁_Δ₁ v hvV hvΔ₁ (hA_le_K₁.vertexSet_mono hv_A.1)
    · rintro e ⟨heE, heD⟩
      obtain ⟨x₀, _⟩ := heE.1
      have he_pre : IsPreconnected e :=
        (GM11.PaintingOrDrawing.edge_props (Γ := PaintingOrDrawing.drawing c.Γ) heE).1
      have hdisF : Disjoint e (frontier Δ₁) := by
        rw [← GM11.subBd_eq_frontier, hIns.2.1]
        exact disjoint_left.mpr fun y hye hyF =>
          (heE.2.1 hye).2 (hNorm ⟨hyF, (heE.2.1 hye).1⟩)
      have hdisF' : Disjoint e (frontier (closure (Set.univ \ Δ₁))) := by
        refine Disjoint.mono_right ?_ hdisF
        intro y hy
        have hy1 : y ∈ frontier (Set.univ \ Δ₁) := frontier_closure_subset hy
        rwa [← compl_eq_univ_sdiff, frontier_compl] at hy1
      obtain ⟨u₀, v₀, hl₀⟩ := c.Γ.toGraph.exists_isLink_of_mem_edgeSet heE
      have hu₀_cl : u₀ ∈ closure e :=
        ((by rw [hl₀.2.2.2]; exact Set.mem_insert u₀ {v₀} : u₀ ∈ closure e ∩ c.Γ.V)).1
      have hu₀_D : u₀ ∈ D A :=
        (c.hJ.disc_D A hA).1.isCompact.isClosed.closure_subset_iff.mpr heD hu₀_cl
      have hu₀_A : u₀ ∈ (subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G A (c.hJ.le_of_mem_𝒜 A hA)).vertexSet := by
        rw [hA_eq]; exact ⟨hl₀.left_mem, hu₀_D⟩
      have hu₀_not_Δ₁ : u₀ ∉ Δ₁ := fun hu₀Δ₁ =>
        hno_v_K₁_Δ₁ u₀ hl₀.left_mem hu₀Δ₁ (hA_le_K₁.vertexSet_mono hu₀_A.1)
      have hx₀_not_Δ₁ : x₀ ∉ Δ₁ := by
        intro hx₀Δ₁
        have he_sub_Δ₁ : e ⊆ Δ₁ :=
          GM12.subset_of_disjoint_frontier he_pre hIns.1.isCompact.isClosed hdisF ‹x₀ ∈ e› hx₀Δ₁
        exact hu₀_not_Δ₁ (hIns.1.isCompact.isClosed.closure_subset_iff.mpr he_sub_Δ₁ hu₀_cl)
      exact ⟨heE, GM12.subset_of_disjoint_frontier he_pre isClosed_closure hdisF' ‹x₀ ∈ e›
        (subset_closure ⟨mem_univ x₀, hx₀_not_Δ₁⟩)⟩
  -- Step 2: Uncross `(C_Γ₀, D_Γ₀)` on `c.Γ.toHypergraph` to a separation `(C_Γ, D_Γ) ∈ c.T`
  -- of order `< πLen (A_fam' i)` such that every `A ∈ 𝒜` has `A_Γ_of A ≤ C_Γ ∨ A_Γ_of A ≤ D_Γ`.
  let GoodSep (C_Γ D_Γ : Hypergraph S (Set S)) : Prop :=
    (C_Γ, D_Γ) ∈ c.T ∧
    separationOrder C_Γ D_Γ < πLen (A_fam' i) ∧
    A_Γ_of (A_fam' i) ≤ C_Γ ∧
    K_Γ ≤ D_Γ ∧
    ∀ A ∈ 𝒜_far, A_Γ_of A ≤ D_Γ
  have hGoodSep₀ : GoodSep C_Γ₀ D_Γ₀ :=
    ⟨hC₀D₀_T, hord_Γ₀_lt, hA'i_Γ_le, hK_Γ_le, hfar_Γ_le⟩
  let S_score : Set ℕ := {n : ℕ | ∃ C_Γ D_Γ, GoodSep C_Γ D_Γ ∧
    {A ∈ 𝒜 | A_Γ_of A ≤ C_Γ ∨ A_Γ_of A ≤ D_Γ}.ncard = n}
  have hS_ne : S_score.Nonempty :=
    ⟨_, C_Γ₀, D_Γ₀, hGoodSep₀, rfl⟩
  have hS_bdd : BddAbove S_score := by
    refine ⟨𝒜.ncard, ?_⟩
    rintro n ⟨C_Γ, D_Γ, _, rfl⟩
    exact Set.ncard_le_ncard (fun _ h => h.1) c.hJ.finite_𝒜
  obtain ⟨C_Γ, D_Γ, hGS, hmax_eq⟩ := Nat.sSup_mem hS_ne hS_bdd
  have hmax : ∀ C_Γ' D_Γ', GoodSep C_Γ' D_Γ' →
      {A ∈ 𝒜 | A_Γ_of A ≤ C_Γ' ∨ A_Γ_of A ≤ D_Γ'}.ncard ≤
        {A ∈ 𝒜 | A_Γ_of A ≤ C_Γ ∨ A_Γ_of A ≤ D_Γ}.ncard := by
    intro C_Γ' D_Γ' h'
    rw [hmax_eq]
    exact le_csSup hS_bdd ⟨C_Γ', D_Γ', h', rfl⟩
  rcases hGS with ⟨hCD_T, hord_CD_lt, hA'i_le_CΓ, hK_le_DΓ, hfar_le_DΓ⟩
  have hsep_CD_Γ : c.Γ.toHypergraph.IsSeparation C_Γ D_Γ := hT.isSeparation hCD_T
  -- Prove that every `A ∈ 𝒜` has `A_Γ_of A ≤ C_Γ ∨ A_Γ_of A ≤ D_Γ`.
  have hall_split : ∀ A ∈ 𝒜, A_Γ_of A ≤ C_Γ ∨ A_Γ_of A ≤ D_Γ := by
    intro A hA
    by_contra hnot_split
    have hdist_A : subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ := by
      by_contra! hge
      exact hnot_split (Or.inr (hfar_le_DΓ A ⟨hA, hge⟩))
    have hGood : IsGoodMember c.ιV c.ιE c.Γ πLen πS A :=
      lemma_7_4_claim_4 c hc_ext hA hdist_A
    have hAK : A ⊓ K = Graph.noEdge W β := by
      by_contra hne
      exact not_le_of_gt hdist_A (c.hJ.dist_D_of_inter_K A hA hne)
    obtain ⟨B, hB_le_G, hsep_AB, hV_AB, hK_le_B, hA'_le_B⟩ :=
      exists_separation_of_mem_𝒜 c.hJ hA hAK
    let A_Γ := A_Γ_of A
    let B_Γ := (PaintingOrDrawing.drawing c.Γ).interOutside (D A)
    obtain ⟨hA_Γ_eq, hAB_T, hsep_AB_Γ⟩ := subHypergraphOfSubgraph_eq_drawing_inter c.hJ hA
    obtain ⟨hB_Γ_eq, _⟩ :=
      subHypergraphOfSubgraph_eq_drawing_interOutside_of_good c.hJ hA hGood hsep_AB hV_AB
    have hK_le_BΓ : K_Γ ≤ B_Γ := by
      dsimp only [K_Γ, B_Γ]
      rw [← hB_Γ_eq]
      exact subHypergraphOfSubgraph_mono c.Γ c.ιV c.ιE hΓ_le_G c.hJ.sep_NK.1.2.1 hB_le_G hK_le_B
    have hA'_le_BΓ : ∀ A' ∈ 𝒜, A' ≠ A → A_Γ_of A' ≤ B_Γ := by
      intro A' hA' hne
      dsimp only [A_Γ_of, B_Γ]
      rw [← (subHypergraphOfSubgraph_eq_drawing_inter c.hJ hA').1, ← hB_Γ_eq]
      exact subHypergraphOfSubgraph_mono c.Γ c.ιV c.ιE hΓ_le_G
        (c.hJ.le_of_mem_𝒜 A' hA') hB_le_G (hA'_le_B A' hA' hne)
    have hA_ne_A'i : A ≠ A_fam' i := fun h => hnot_split (Or.inl (h ▸ hA'i_le_CΓ))
    have hCD_Γ_fin : (C_Γ.vertexSet ∩ D_Γ.vertexSet).Finite :=
      c.Γ.finite_V.subset (inter_subset_left.trans hsep_CD_Γ.left_le.vertexSet_subset)
    have hAB_Γ_fin : (A_Γ.vertexSet ∩ B_Γ.vertexSet).Finite :=
      c.Γ.finite_V.subset (inter_subset_left.trans hsep_AB_Γ.left_le.vertexSet_subset)
    have hAB_Γ_sub_CD : A_Γ.vertexSet ∩ B_Γ.vertexSet ⊆ C_Γ.vertexSet ∪ D_Γ.vertexSet := by
      rw [← GM10.union_vertexSet, hsep_CD_Γ.union_eq]
      exact inter_subset_left.trans hsep_AB_Γ.left_le.vertexSet_subset
    have hid1 := uncross_ncard_identity hCD_Γ_fin hAB_Γ_fin hAB_Γ_sub_CD
    have hid2 := uncross_ncard_identity
      (inter_comm C_Γ.vertexSet D_Γ.vertexSet ▸ hCD_Γ_fin) hAB_Γ_fin
      (union_comm C_Γ.vertexSet D_Γ.vertexSet ▸ hAB_Γ_sub_CD)
    rw [inter_comm D_Γ.vertexSet C_Γ.vertexSet] at hid2
    have hnot_both := not_both_boundary_diff_gt_of_isGoodMember c.hJ hA hGood hsep_CD_Γ
    have hA'_Γ_le : ∀ A' ∈ 𝒜, A_Γ_of A' ≤ c.Γ.toHypergraph :=
      fun A' hA' => (subHypergraphOfSubgraph_eq_drawing_inter c.hJ hA').2.2.left_le
    have hK_Γ_le_Γ : K_Γ ≤ c.Γ.toHypergraph :=
      subHypergraphOfSubgraph_le c.Γ c.ιV c.ιE hΓ_le_G K c.hJ.sep_NK.1.2.1
    by_cases hle1 : separationOrder (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) ≤ separationOrder C_Γ D_Γ
    · -- `(A_Γ ∪ C_Γ, B_Γ ∩ D_Γ)` is a `GoodSep` that strictly increases the score!
      have hord1_lt : separationOrder (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) < πLen (A_fam' i) :=
        lt_of_le_of_lt hle1 hord_CD_lt
      have hord1_ord : separationOrder (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) < c.ord := by
        have := c.hJ.four_le_θ; have := c.hJ.θ_le_ord; omega
      have hGS1 : GoodSep (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) := by
        refine ⟨GM10.theorem_2_2_proof hT hAB_T hCD_T hord1_ord, hord1_lt,
          hA'i_le_CΓ.trans (GM10.le_union_right hsep_AB_Γ.left_le hsep_CD_Γ.left_le),
          le_inter_of_le hK_Γ_le_Γ hsep_AB_Γ.right_le hsep_CD_Γ.right_le hK_le_BΓ hK_le_DΓ,
          fun A' hA' => ?_⟩
        have hne : A' ≠ A := fun h => not_le_of_gt hdist_A (h ▸ hA'.2)
        exact le_inter_of_le (hA'_Γ_le A' hA'.1) hsep_AB_Γ.right_le hsep_CD_Γ.right_le
          (hA'_le_BΓ A' hA'.1 hne) (hfar_le_DΓ A' hA')
      have hssub : {A' ∈ 𝒜 | A_Γ_of A' ≤ C_Γ ∨ A_Γ_of A' ≤ D_Γ} ⊂
          {A' ∈ 𝒜 | A_Γ_of A' ≤ A_Γ ∪ C_Γ ∨ A_Γ_of A' ≤ B_Γ ∩ D_Γ} := by
        refine ⟨fun A' ⟨hA', hsplit⟩ => ⟨hA', ?_⟩,
          fun hsub => hnot_split (hsub ⟨hA, Or.inl (GM10.le_union_left hsep_AB_Γ.left_le hsep_CD_Γ.left_le)⟩).2⟩
        have hne : A' ≠ A := fun h => hnot_split (h ▸ hsplit)
        rcases hsplit with hC | hD
        · exact Or.inl (hC.trans (GM10.le_union_right hsep_AB_Γ.left_le hsep_CD_Γ.left_le))
        · exact Or.inr (le_inter_of_le (hA'_Γ_le A' hA') hsep_AB_Γ.right_le hsep_CD_Γ.right_le
            (hA'_le_BΓ A' hA' hne) hD)
      exact not_lt_of_ge (hmax (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) hGS1)
        (Set.ncard_lt_ncard hssub (c.hJ.finite_𝒜.subset fun _ h => h.1))
    · -- Otherwise `separationOrder C_Γ D_Γ < separationOrder (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ)`,
      -- so `separationOrder (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) ≤ separationOrder C_Γ D_Γ`.
      push Not at hle1
      have hgt_C : ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard <
          ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard := by
        change (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard <
          ((A_Γ.vertexSet ∪ C_Γ.vertexSet) ∩ (B_Γ.vertexSet ∩ D_Γ.vertexSet)).ncard at hle1
        omega
      have hle_D : ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard ≤
          ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard := by
        by_contra! hgt_D
        exact hnot_both ⟨hgt_C, hgt_D⟩
      have hle2 : separationOrder (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) ≤ separationOrder C_Γ D_Γ := by
        change ((B_Γ.vertexSet ∩ C_Γ.vertexSet) ∩ (A_Γ.vertexSet ∪ D_Γ.vertexSet)).ncard ≤
          (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard
        rw [inter_comm (B_Γ.vertexSet ∩ C_Γ.vertexSet)]
        omega
      have hord2_lt : separationOrder (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) < πLen (A_fam' i) :=
        lt_of_le_of_lt hle2 hord_CD_lt
      have hord2_ord : separationOrder (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) < c.ord := by
        have := c.hJ.four_le_θ; have := c.hJ.θ_le_ord; omega
      have hsep2 : c.Γ.toHypergraph.IsSeparation (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) :=
        (hsep_AB_Γ.union_inter hsep_CD_Γ.symm).symm
      have hGS2 : GoodSep (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) := by
        refine ⟨mem_tangle_of_right_le hT hCD_T hsep2 hord2_ord
            (GM10.le_union_right hsep_AB_Γ.left_le hsep_CD_Γ.right_le),
          hord2_lt,
          le_inter_of_le (hA'_Γ_le (A_fam' i) (hA'_mem i)) hsep_AB_Γ.right_le hsep_CD_Γ.left_le
            (hA'_le_BΓ (A_fam' i) (hA'_mem i) (Ne.symm hA_ne_A'i)) hA'i_le_CΓ,
          hK_le_DΓ.trans (GM10.le_union_right hsep_AB_Γ.left_le hsep_CD_Γ.right_le),
          fun A' hA' => (hfar_le_DΓ A' hA').trans
            (GM10.le_union_right hsep_AB_Γ.left_le hsep_CD_Γ.right_le)⟩
      have hssub : {A' ∈ 𝒜 | A_Γ_of A' ≤ C_Γ ∨ A_Γ_of A' ≤ D_Γ} ⊂
          {A' ∈ 𝒜 | A_Γ_of A' ≤ B_Γ ∩ C_Γ ∨ A_Γ_of A' ≤ A_Γ ∪ D_Γ} := by
        refine ⟨fun A' ⟨hA', hsplit⟩ => ⟨hA', ?_⟩,
          fun hsub => hnot_split (hsub ⟨hA, Or.inr (GM10.le_union_left hsep_AB_Γ.left_le hsep_CD_Γ.right_le)⟩).2⟩
        have hne : A' ≠ A := fun h => hnot_split (h ▸ hsplit)
        rcases hsplit with hC | hD
        · exact Or.inl (le_inter_of_le (hA'_Γ_le A' hA') hsep_AB_Γ.right_le hsep_CD_Γ.left_le
            (hA'_le_BΓ A' hA' hne) hC)
        · exact Or.inr (hD.trans (GM10.le_union_right hsep_AB_Γ.left_le hsep_CD_Γ.right_le))
      exact not_lt_of_ge (hmax (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) hGS2)
        (Set.ncard_lt_ncard hssub (c.hJ.finite_𝒜.subset fun _ h => h.1))
  -- Step 3: Extend `(C_Γ, D_Γ)` to a separation `(C, D_sep)` of `G` and contradict Claim (9).
  let 𝒜_C := {A ∈ 𝒜 | subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ ∧ A_Γ_of A ≤ C_Γ}
  let 𝒜_D := {A ∈ 𝒜 | A ∉ 𝒜_C}
  have h𝒜_D_le : ∀ A ∈ 𝒜_D, A_Γ_of A ≤ D_Γ := by
    rintro A ⟨hA, hnot_C⟩
    by_cases hdist : subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ
    · exact (hall_split A hA).resolve_left (fun hC => hnot_C ⟨hA, hdist, hC⟩)
    · push Not at hdist
      exact hfar_le_DΓ A ⟨hA, hdist⟩
  let Γ_C_emb := embSubgraph c.Γ c.ιV c.ιE C_Γ
  let Γ_D_emb := embSubgraph c.Γ c.ιV c.ιE D_Γ
  have hΓC_le_G : Γ_C_emb ≤ G := (embSubgraph_le c.Γ c.ιV c.ιE hsep_CD_Γ.left_le).trans hΓ_le_G
  have hΓD_le_G : Γ_D_emb ≤ G := (embSubgraph_le c.Γ c.ιV c.ιE hsep_CD_Γ.right_le).trans hΓ_le_G
  have hNW_le_G : Graph.noEdge W β ≤ G :=
    Graph.noEdge_le_iff.mpr (c.hJ.sep_NK.2.trans (inter_subset_left.trans c.hJ.sep_NK.1.1.vertexSet_mono))
  have h𝒜C_le : ∀ A ∈ 𝒜_C, A ≤ G := fun A hA => c.hJ.le_of_mem_𝒜 A hA.1
  have h𝒜D_le : ∀ A ∈ 𝒜_D, A ≤ G := fun A hA => c.hJ.le_of_mem_𝒜 A hA.1
  let C := graphUnion (graphUnion Γ_C_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜_C)
  let D_sep := graphUnion (graphUnion (graphUnion Γ_D_emb (Graph.noEdge W β)) K) (subgraphSUnion G 𝒜_D)
  have hC_le_G : C ≤ G :=
    graphUnion_le (graphUnion_le hΓC_le_G hNW_le_G) (subgraphSUnion_le h𝒜C_le)
  have hD_le_G : D_sep ≤ G :=
    graphUnion_le (graphUnion_le (graphUnion_le hΓD_le_G hNW_le_G) c.hJ.sep_NK.1.2.1)
      (subgraphSUnion_le h𝒜D_le)
  have hΓ_disj_W : Disjoint V(c.Γ_emb) W := by
    rw [Set.disjoint_left]
    intro x hxΓ hxW
    have hx_del := c.hJ.Γ_le.vertexSet_mono hxΓ
    rw [Graph.vertexSet_deleteVerts] at hx_del
    exact hx_del.2 hxW
  have hsep_CD_G : IsGraphSeparation G C D_sep := by
    refine ⟨hC_le_G, hD_le_G, ?_, ?_, ?_⟩
    · refine Subset.antisymm (union_subset hC_le_G.vertexSet_mono hD_le_G.vertexSet_mono) ?_
      intro x hxG
      have hxNK : x ∈ V(N) ∪ V(K) := c.hJ.sep_NK.1.2.2.1.symm ▸ hxG
      rcases hxNK with hxN | hxK
      · rw [congr_arg Graph.vertexSet c.hJ.N_eq, vertexSet_graphUnion, vertexSet_graphUnion,
          Graph.vertexSet_noEdge, vertexSet_subgraphSUnion] at hxN
        rcases hxN with (⟨s, hsV, rfl⟩ | hxW) | hxU
        · have hs_CD : s ∈ C_Γ.vertexSet ∪ D_Γ.vertexSet := by
            rw [← GM10.union_vertexSet, hsep_CD_Γ.union_eq]
            exact hsV
          rcases hs_CD with hsC | hsD
          · exact Or.inl (Or.inl (Or.inl ⟨s, hsC, rfl⟩))
          · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨s, hsD, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inr hxW))
        · obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hxU
          by_cases hAC : A ∈ 𝒜_C
          · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨A, hAC, hxA⟩))
          · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨A, ⟨hA, hAC⟩, hxA⟩))
      · exact Or.inr (Or.inl (Or.inr hxK))
    · refine Subset.antisymm (union_subset hC_le_G.edgeSet_mono hD_le_G.edgeSet_mono) ?_
      intro e heG
      have heNK : e ∈ E(N) ∪ E(K) := c.hJ.sep_NK.1.2.2.2.1.symm ▸ heG
      rcases heNK with heN | heK
      · rw [congr_arg Graph.edgeSet c.hJ.N_eq, edgeSet_graphUnion, edgeSet_graphUnion,
          Graph.edgeSet_noEdge, union_empty, edgeSet_subgraphSUnion c.hJ.le_of_mem_𝒜] at heN
        rcases heN with ⟨e₀, he₀E, rfl⟩ | heU
        · have he₀_CD : e₀ ∈ C_Γ.edgeSet ∪ D_Γ.edgeSet := by
            rw [← GM10.union_edgeSet, hsep_CD_Γ.union_eq]
            exact he₀E
          rcases he₀_CD with he₀C | he₀D
          · apply Or.inl
            rw [edgeSet_graphUnion, edgeSet_graphUnion,
              edgeSet_embSubgraph c.Γ c.ιV c.ιE hsep_CD_Γ.left_le]
            exact Or.inl (Or.inl ⟨e₀, he₀C, rfl⟩)
          · apply Or.inr
            rw [edgeSet_graphUnion, edgeSet_graphUnion, edgeSet_graphUnion,
              edgeSet_embSubgraph c.Γ c.ιV c.ιE hsep_CD_Γ.right_le]
            exact Or.inl (Or.inl (Or.inl ⟨e₀, he₀D, rfl⟩))
        · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heU
          by_cases hAC : A ∈ 𝒜_C
          · apply Or.inl
            rw [edgeSet_graphUnion, edgeSet_subgraphSUnion h𝒜C_le]
            exact Or.inr (mem_iUnion₂.mpr ⟨A, hAC, heA⟩)
          · apply Or.inr
            rw [edgeSet_graphUnion, edgeSet_subgraphSUnion h𝒜D_le]
            exact Or.inr (mem_iUnion₂.mpr ⟨A, ⟨hA, hAC⟩, heA⟩)
      · apply Or.inr
        rw [edgeSet_graphUnion, edgeSet_graphUnion]
        exact Or.inl (Or.inr heK)
    · rw [Set.disjoint_left]
      intro e heC heD
      rw [edgeSet_graphUnion, edgeSet_graphUnion,
        edgeSet_embSubgraph c.Γ c.ιV c.ιE hsep_CD_Γ.left_le,
        Graph.edgeSet_noEdge, union_empty, edgeSet_subgraphSUnion h𝒜C_le] at heC
      rw [edgeSet_graphUnion, edgeSet_graphUnion, edgeSet_graphUnion,
        edgeSet_embSubgraph c.Γ c.ιV c.ιE hsep_CD_Γ.right_le,
        Graph.edgeSet_noEdge, union_empty, edgeSet_subgraphSUnion h𝒜D_le] at heD
      have hCD_disj_E : Disjoint C_Γ.edgeSet D_Γ.edgeSet :=
        Set.disjoint_iff_inter_eq_empty.mpr hsep_CD_Γ.edgeSet_inter_eq
      rcases heC with ⟨e₁, he₁C, rfl⟩ | heUC
      · rcases heD with (⟨e₂, he₂D, hee⟩ | heK) | heUD
        · obtain rfl := c.ιE.injective hee
          exact Set.disjoint_left.mp hCD_disj_E he₁C he₂D
        · have he₁_D : e₁ ∈ D_Γ.edgeSet :=
            hK_le_DΓ.edgeSet_subset ⟨heK, hsep_CD_Γ.left_le.edgeSet_subset he₁C⟩
          exact Set.disjoint_left.mp hCD_disj_E he₁C he₁_D
        · obtain ⟨A', hA', heA'⟩ := mem_iUnion₂.mp heUD
          have he₁_A' : e₁ ∈ (A_Γ_of A').edgeSet :=
            (mem_drawing_inter_DA_edgeSet c.hJ hA'.1).mpr
              ⟨heA', hsep_CD_Γ.left_le.edgeSet_subset he₁C⟩
          exact Set.disjoint_left.mp hCD_disj_E he₁C ((h𝒜_D_le A' hA').edgeSet_subset he₁_A')
      · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heUC
        rcases heD with (⟨e₂, he₂D, rfl⟩ | heK) | heUD
        · have he₂_A : e₂ ∈ (A_Γ_of A).edgeSet :=
            (mem_drawing_inter_DA_edgeSet c.hJ hA.1).mpr
              ⟨heA, hsep_CD_Γ.right_le.edgeSet_subset he₂D⟩
          exact Set.disjoint_left.mp hCD_disj_E (hA.2.2.edgeSet_subset he₂_A) he₂D
        · have heN : e ∈ E(N) := by
            rw [congr_arg Graph.edgeSet c.hJ.N_eq, edgeSet_graphUnion,
              edgeSet_subgraphSUnion c.hJ.le_of_mem_𝒜]
            exact Or.inr (mem_iUnion₂.mpr ⟨A, hA.1, heA⟩)
          exact Set.disjoint_left.mp c.hJ.sep_NK.1.2.2.2.2 heN heK
        · obtain ⟨A', hA', heA'⟩ := mem_iUnion₂.mp heUD
          have hne : A ≠ A' := fun h => hA'.2 (h ▸ hA)
          exact Set.disjoint_left.mp (c.hJ.edge_disjoint_𝒜 A hA.1 A' hA'.1 hne) heA heA'
  have hW_CD : W ⊆ V(C) ∩ V(D_sep) :=
    fun w hw => ⟨Or.inl (Or.inr hw), Or.inl (Or.inl (Or.inr hw))⟩
  have hdist_A'i : subsetTangleDist c.Γ c.ord c.d (D (A_fam' i)) (Set.univ \ Δ) < θ := by
    by_contra! hge
    have h1 : 1 ≤ subsetTangleDist c.Γ c.ord c.d (D (A_fam' i)) (Set.univ \ Δ) := by
      have := c.hJ.four_le_θ; omega
    have hsub_Δ := subset_of_one_le_subsetTangleDist_compl c.hJ.hasMetric h1
    obtain ⟨x₀, hx₀⟩ := GM14.IsClosedDisc.nonempty (c.hJ.disc_D (A_fam' i) (hA'_mem i)).1
    exact Set.disjoint_left.mp (h_iii_disj i) hx₀ (hsub_Δ hx₀)
  have hA'i_le_C : A_fam' i ≤ C :=
    (le_subgraphSUnion h𝒜C_le ⟨hA'_mem i, hdist_A'i, hA'i_le_CΓ⟩).trans
      (le_graphUnion_right (Compatible.of_le_le (graphUnion_le hΓC_le_G hNW_le_G) (subgraphSUnion_le h𝒜C_le)))
  have hK_le_D : K ≤ D_sep :=
    (le_graphUnion_right (Compatible.of_le_le (graphUnion_le hΓD_le_G hNW_le_G) c.hJ.sep_NK.1.2.1)).trans
      (le_graphUnion_left _ _)
  have hfar_le_D : ∀ A ∈ 𝒜,
      θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) → A ≤ D_sep := by
    intro A hA hdist
    have hAD : A ∈ 𝒜_D := ⟨hA, fun hAC => not_le_of_gt hAC.2.1 hdist⟩
    exact (le_subgraphSUnion h𝒜D_le hAD).trans
      (le_graphUnion_right (Compatible.of_le_le
        (graphUnion_le (graphUnion_le hΓD_le_G hNW_le_G) c.hJ.sep_NK.1.2.1)
        (subgraphSUnion_le h𝒜D_le)))
  have hCΓ_V : C_Γ.vertexSet = c.ιV ⁻¹' V(C) ∩ c.Γ.V := by
    ext s
    refine ⟨fun hsC => ⟨Or.inl (Or.inl ⟨s, hsC, rfl⟩), hsep_CD_Γ.left_le.vertexSet_subset hsC⟩, ?_⟩
    rintro ⟨(⟨s', hs'C, hss'⟩ | hsW) | hsUC, hsV⟩
    · obtain rfl := c.ιV.injective hss'; exact hs'C
    · exact False.elim (Set.disjoint_left.mp hΓ_disj_W ⟨s, hsV, rfl⟩ hsW)
    · rw [vertexSet_subgraphSUnion] at hsUC
      obtain ⟨A, hA, hsA⟩ := mem_iUnion₂.mp hsUC
      have hs_AΓ : s ∈ (A_Γ_of A).vertexSet :=
        (mem_drawing_inter_DA_vertexSet c.hJ hA.1).mpr ⟨hsA, hsV⟩
      exact hA.2.2.vertexSet_subset hs_AΓ
  have hCΓ_E : C_Γ.edgeSet = c.ιE ⁻¹' E(C) ∩ c.Γ.E := by
    ext e₀
    rw [mem_inter_iff, mem_preimage, edgeSet_graphUnion, edgeSet_graphUnion,
      edgeSet_embSubgraph c.Γ c.ιV c.ιE hsep_CD_Γ.left_le,
      Graph.edgeSet_noEdge, union_empty, edgeSet_subgraphSUnion h𝒜C_le]
    refine ⟨fun he₀C => ⟨Or.inl ⟨e₀, he₀C, rfl⟩, hsep_CD_Γ.left_le.edgeSet_subset he₀C⟩, ?_⟩
    rintro ⟨⟨e₁, he₁C, hee₁⟩ | heUC, he₀E⟩
    · obtain rfl := c.ιE.injective hee₁; exact he₁C
    · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heUC
      have he₀_AΓ : e₀ ∈ (A_Γ_of A).edgeSet :=
        (mem_drawing_inter_DA_edgeSet c.hJ hA.1).mpr ⟨heA, he₀E⟩
      exact hA.2.2.edgeSet_subset he₀_AΓ
  have hDΓ_V : D_Γ.vertexSet = c.ιV ⁻¹' V(D_sep) ∩ c.Γ.V := by
    ext s
    refine ⟨fun hsD => ⟨Or.inl (Or.inl (Or.inl ⟨s, hsD, rfl⟩)), hsep_CD_Γ.right_le.vertexSet_subset hsD⟩, ?_⟩
    rintro ⟨((⟨s', hs'D, hss'⟩ | hsW) | hsK) | hsUD, hsV⟩
    · obtain rfl := c.ιV.injective hss'; exact hs'D
    · exact False.elim (Set.disjoint_left.mp hΓ_disj_W ⟨s, hsV, rfl⟩ hsW)
    · exact hK_le_DΓ.vertexSet_subset ⟨hsK, hsV⟩
    · rw [vertexSet_subgraphSUnion] at hsUD
      obtain ⟨A, hA, hsA⟩ := mem_iUnion₂.mp hsUD
      have hs_AΓ : s ∈ (A_Γ_of A).vertexSet :=
        (mem_drawing_inter_DA_vertexSet c.hJ hA.1).mpr ⟨hsA, hsV⟩
      exact (h𝒜_D_le A hA).vertexSet_subset hs_AΓ
  have hDΓ_E : D_Γ.edgeSet = c.ιE ⁻¹' E(D_sep) ∩ c.Γ.E := by
    ext e₀
    rw [mem_inter_iff, mem_preimage, edgeSet_graphUnion, edgeSet_graphUnion, edgeSet_graphUnion,
      edgeSet_embSubgraph c.Γ c.ιV c.ιE hsep_CD_Γ.right_le,
      Graph.edgeSet_noEdge, union_empty, edgeSet_subgraphSUnion h𝒜D_le]
    refine ⟨fun he₀D => ⟨Or.inl (Or.inl ⟨e₀, he₀D, rfl⟩), hsep_CD_Γ.right_le.edgeSet_subset he₀D⟩, ?_⟩
    rintro ⟨(⟨e₁, he₁D, hee₁⟩ | heK) | heUD, he₀E⟩
    · obtain rfl := c.ιE.injective hee₁; exact he₁D
    · exact hK_le_DΓ.edgeSet_subset ⟨heK, he₀E⟩
    · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heUD
      have he₀_AΓ : e₀ ∈ (A_Γ_of A).edgeSet :=
        (mem_drawing_inter_DA_edgeSet c.hJ hA.1).mpr ⟨heA, he₀E⟩
      exact (h𝒜_D_le A hA).edgeSet_subset he₀_AΓ
  exact lemma_7_4_claim_9 c hc_ext hA'_mem h_iii_disj i
    ⟨C, D_sep, hsep_CD_G, hW_CD, hA'i_le_C, hK_le_D, hfar_le_D,
      C_Γ, D_Γ, hCΓ_V, hCΓ_E, hDΓ_V, hDΓ_E, hCD_T, hord_CD_lt⟩

/-! ## 2. Proof of Theorem 7.4 (pages 552–556) -/

/-- **Graph Minors XXII, (7.4)** (pages 552–553):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 4$ with the following property.
Let (J1)–(J7) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be sufficient for $\phi$. Let
$A_1, \ldots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \ldots, A_t\}$. Let $A'_1, \ldots, A'_t \in \mathcal{A}$, and
suppose that"
"(i) for $1 \le i \le t$, $(A'_i, \pi(A'_i) + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A'_i)) \ge \theta$ and $D(A'_i) \cap \Delta = \emptyset$,
(iv) for $1 \le i < j \le t$, $d(D(A'_i), D(A'_j)) \ge \theta$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_4_proof
    (q δ τ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV₀ : S ↪ α) (ιE₀ : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ₀ : Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord₀ : ℕ) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins₀ : Set S → Set S) (d₀ : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV₀ : αH → Graph α β) (φE₀ : βH → β)
        (hJ₀ : SystemJ1ToJ6 ιV₀ ιE₀ R_G W 𝒜 πLen πS Γ₀ orient θ ord₀ T₀ ins₀ d₀ D N K Δ v_star δ R_H φV₀ φE₀),
        ConditionJ7 ιV₀ ιE₀ R_G.G.toGraph W 𝒜 πLen πS Γ₀ T₀ →
        IsSufficientFor W 𝒜 ℬ K R_H φV₀ φE₀ →
        ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
        t ≤ τ →
        (∀ i : Fin t, A_fam i ∈ ℬ) →
        (∀ i : Fin t, A_fam' i ∈ 𝒜) →
        (∀ A ∈ ℬ \ Set.range A_fam,
          θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D A) (Set.univ \ Δ)) →
        ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
        (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
          (hπi : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
          (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
          HasSameDeltaFolio
            (subRootedDigraph R_G.G (A_fam' i) hA'i
              (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
            (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
        (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
        (∀ i : Fin t, θ ≤ subsetTangleDist Γ₀ ord₀ d₀ {v_star} (D (A_fam' i))) →
        (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
        (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D (A_fam' i)) (D (A_fam' j))) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV₀ v_star}) Graph.deleteVerts_le
            R_G.roots hJ₀.roots_mem_deleteVerts_v_star)
          R_H := by
  obtain ⟨θ, hθ_five, h73_spec⟩ := theorem_7_3_proof q δ τ
  refine ⟨θ, by omega, ?_⟩
  intro S _ _ α β αH βH ιV₀ ιE₀ R_G W 𝒜 ℬ πLen πS Γ₀ orient ord₀ T₀ ins₀ d₀ D N K Δ v_star R_H
    φV₀ φE₀ hJ₀ hJ7₀ hSuff₀ t A_fam A_fam' ht_le hA_mem_ℬ hA'_mem hdist_other₀ hlen h_i₀
    h_ii h_iii_dist₀ h_iii_disj h_iv₀
  -- Step 1: Build the initial configuration `c₀` and choose an extremal configuration `c` by Claim (1).
  let c₀ : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam' :=
    { ιV := ιV₀
      ιE := ιE₀
      Γ := Γ₀
      ord := ord₀
      T := T₀
      ins := ins₀
      d := d₀
      φV := φV₀
      φE := φE₀
      ιV_eq := fun _ _ => rfl
      hJ := hJ₀
      hJ7 := hJ7₀
      hSuff := hSuff₀
      hdist_other := hdist_other₀
      h_iii_dist := h_iii_dist₀
      h_iv := h_iv₀ }
  obtain ⟨c, hc_ext⟩ := lemma_7_4_claim_1 c₀
  -- Step 2: By Claim (8), `ℬ_star = ℬ ∪ {A ∈ 𝒜 | θ ≤ d(D A, Σ \ Δ)}` is adequate for `c.φ`.
  let ℬ_star := ℬ ∪ {A ∈ 𝒜 | θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ)}
  have hAdeq_star : IsAdequateFor c.ιV c.ιE W 𝒜 ℬ_star c.Γ K R_H c.φV c.φE :=
    lemma_7_4_claim_8 c hc_ext
  have hA_mem_star : ∀ i : Fin t, A_fam i ∈ ℬ_star :=
    fun i => Or.inl (hA_mem_ℬ i)
  have hdist_other_star : ∀ A ∈ ℬ_star \ Set.range A_fam,
      θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) := by
    rintro A ⟨hA_ℬ | hA_far, hA_not_range⟩
    · exact c.hdist_other A ⟨hA_ℬ, hA_not_range⟩
    · exact hA_far.2
  -- Step 3: Transport hypothesis (i) along `c.ιV_eq`.
  have h_i : ∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
      (hπi : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (c.ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
      (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (fun k : Fin (πLen (A_fam i)) =>
          c.ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
      HasSameDeltaFolio
        (subRootedDigraph R_G.G (A_fam' i) hA'i
          (seqConcat (fun k : Fin (πLen (A_fam i)) =>
            c.ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
        (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (c.ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ := by
    intro i hAi hA'i hπi hπ'i
    have hseq1 : (c.ιV ∘ πS (A_fam i)) = (ιV₀ ∘ πS (A_fam i)) := by
      ext k
      exact c.ιV_eq (πS (A_fam i) k) (Or.inr ⟨A_fam i, c.hSuff.subset (hA_mem_ℬ i), k, rfl⟩)
    have hseq2 : (fun k : Fin (πLen (A_fam i)) =>
        c.ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) =
        (fun k : Fin (πLen (A_fam i)) =>
          ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) := by
      ext k
      exact c.ιV_eq _ (Or.inr ⟨A_fam' i, hA'_mem i, _, rfl⟩)
    revert hπi hπ'i
    rw [hseq1, hseq2]
    intro hπi hπ'i αH' βH' R_H' hDet'
    exact h_i₀ i hAi hA'i hπi hπ'i R_H' hDet'
  -- Step 4: By Claim (10), hypothesis (v) of 7.3 holds for `c`.
  have h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ c.Γ.IsNormal F ∧
      (F ∩ c.Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ c.ins F :=
    fun i => lemma_7_4_claim_10 c hc_ext hA'_mem h_iii_disj i
  -- Step 5: Apply Theorem 7.3 to `c` and `ℬ_star`.
  have hModel := h73_spec c.ιV c.ιE R_G W 𝒜 ℬ_star πLen πS c.Γ orient c.ord c.T c.ins c.d
    D N K Δ v_star R_H c.φV c.φE c.hJ hAdeq_star t A_fam A_fam' ht_le hA_mem_star hA'_mem
    hdist_other_star hlen h_i h_ii c.h_iii_dist h_iii_disj c.h_iv h_v
  have hv_star_eq : c.ιV v_star = ιV₀ v_star := c.ιV_eq v_star (Or.inl rfl)
  simpa only [hv_star_eq] using hModel

end GraphMinor.GM22
