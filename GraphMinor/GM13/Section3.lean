module

public import GraphMinor.GM13.Section3a

/-!
# Graph Minors XIII, Section 3 (Part 2): Sparsity of Bounded Branch-width Graphs (3.2) and Algorithm (3.3)

This file formalizes Lemma (3.2) and Algorithm (3.3) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110
(pages 72–74).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}

/-- For any family of bags `χ : ι → Set α` on a finite tree `T : SimpleGraph ι` covering a nonempty
hypergraph `H` and satisfying the tree-decomposition edge and path-intersection axioms, there exist
`v ∈ H.vertexSet` and `t : ι` such that `v ∈ χ t` and every edge incident with `v` has all its ends
in `χ t`. -/
lemma exists_vertex_bag_contains_ends {H : Hypergraph α β} (hne : H.vertexSet.Nonempty)
    {ι : Type w} [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree) (χ : ι → Set α)
    (hU : (⋃ t : ι, χ t) = H.vertexSet)
    (hE : ∀ e ∈ H.edgeSet, ∃ t : ι, H.ends e ⊆ χ t)
    (hinter : ∀ ⦃t₁ t₃ t₂ : ι⦄, GM10.OnTreePath T t₁ t₂ t₃ → χ t₁ ∩ χ t₂ ⊆ χ t₃) :
    ∃ v ∈ H.vertexSet, ∃ t : ι, v ∈ χ t ∧ ∀ e ∈ H.edgeSet, H.Inc e v → H.ends e ⊆ χ t := by
  classical
  suffices ∀ (n : ℕ) (ι₀ : Type w) [Fintype ι₀] (T₀ : SimpleGraph ι₀), T₀.IsTree →
      ∀ (χ₀ : ι₀ → Set α), (⋃ t : ι₀, χ₀ t) = H.vertexSet →
        (∀ e ∈ H.edgeSet, ∃ t : ι₀, H.ends e ⊆ χ₀ t) →
        (∀ ⦃t₁ t₃ t₂ : ι₀⦄, GM10.OnTreePath T₀ t₁ t₂ t₃ → χ₀ t₁ ∩ χ₀ t₂ ⊆ χ₀ t₃) →
        Fintype.card ι₀ = n →
        ∃ v ∈ H.vertexSet, ∃ t : ι₀, v ∈ χ₀ t ∧ ∀ e ∈ H.edgeSet, H.Inc e v → H.ends e ⊆ χ₀ t from
    this (Fintype.card ι) ι T hT χ hU hE hinter rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι₀ _ T₀ hT₀ χ₀ hU₀ hE₀ hinter₀ hcard
    by_cases hle1 : Fintype.card ι₀ ≤ 1
    · have : Subsingleton ι₀ := Fintype.card_le_one_iff_subsingleton.mp hle1
      rcases hne with ⟨v, hvH⟩
      have hvU : v ∈ ⋃ t : ι₀, χ₀ t := hU₀.symm ▸ hvH
      rcases mem_iUnion.mp hvU with ⟨t, hvt⟩
      refine ⟨v, hvH, t, hvt, fun e he _ => ?_⟩
      rcases hE₀ e he with ⟨s, hs⟩
      exact Subsingleton.elim s t ▸ hs
    · have : Nontrivial ι₀ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨t₀, hdeg1⟩ := hT₀.exists_vert_degree_one_of_nontrivial
      obtain ⟨t₁, hadj, huniq⟩ := T₀.degree_eq_one_iff_existsUnique_adj.mp hdeg1
      dsimp only at hadj huniq
      have ht₁_ne : t₁ ≠ t₀ := hadj.ne.symm
      by_cases hsub01 : χ₀ t₀ ⊆ χ₀ t₁
      · let S : Set ι₀ := {t₀}ᶜ
        let T' := T₀.induce S
        let χ' : S → Set α := fun x => χ₀ x.1
        have hT' : T'.IsTree := GM10.isTree_induce_compl_singleton hT₀ hdeg1
        let x₁ : S := ⟨t₁, ht₁_ne⟩
        have hU' : (⋃ x : S, χ' x) = H.vertexSet := by
          ext w
          simp only [mem_iUnion, ← hU₀]
          refine ⟨fun ⟨x, hx⟩ => ⟨x.1, hx⟩, fun ⟨t, ht⟩ => ?_⟩
          by_cases ht0 : t = t₀
          · exact ⟨x₁, hsub01 (ht0 ▸ ht)⟩
          · exact ⟨⟨t, ht0⟩, ht⟩
        have hE' : ∀ e ∈ H.edgeSet, ∃ x : S, H.ends e ⊆ χ' x := by
          intro e he
          rcases hE₀ e he with ⟨t, ht⟩
          by_cases ht0 : t = t₀
          · exact ⟨x₁, (ht0 ▸ ht).trans hsub01⟩
          · exact ⟨⟨t, ht0⟩, ht⟩
        have hinter' : ∀ ⦃a c b : S⦄, GM10.OnTreePath T' a b c → χ' a ∩ χ' b ⊆ χ' c :=
          fun _ _ _ hp => hinter₀ (GM10.onTreePath_of_induce_compl_singleton hT₀ hT'.connected hp)
        have hlt : Fintype.card S < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
            (by rintro ⟨⟨x, hx⟩, rfl⟩; exact hx rfl)
        obtain ⟨v, hvH, x, hvx, hends⟩ := ih (Fintype.card S) hlt S T' hT' χ' hU' hE' hinter' rfl
        exact ⟨v, hvH, x.1, hvx, hends⟩
      · obtain ⟨v, hv0, hv1⟩ := not_subset.mp hsub01
        have hvH : v ∈ H.vertexSet := hU₀ ▸ mem_iUnion.mpr ⟨t₀, hv0⟩
        refine ⟨v, hvH, t₀, hv0, fun e he hinc => ?_⟩
        rcases hE₀ e he with ⟨s, hs⟩
        by_cases hs0 : s = t₀
        · exact hs0 ▸ hs
        · exfalso
          have hpath : GM10.OnTreePath T₀ t₀ s t₁ := by
            intro p hp
            cases p with
            | nil => exact (hs0 rfl).elim
            | @cons _ w _ hadj_w q =>
              have hw : w = t₁ := huniq w hadj_w
              subst hw
              exact List.mem_cons_of_mem t₀ q.start_mem_support
          exact hv1 (hinter₀ hpath ⟨hv0, hs hinc⟩)

/-- Every nonempty finite simple graph `G` with `GraphBranchWidthLE G ω` (`2 ≤ ω`) has a vertex
`v ∈ V(G)` incident with at most `3 * ω / 2 - 1` edges of `G`. -/
lemma exists_vertex_degree_le_of_isSimpleGraph {G : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hne : V(G).Nonempty)
    (hSimp : IsSimpleGraph G) {ω : ℕ} (hω : 2 ≤ ω) (hbw : GraphBranchWidthLE G ω) :
    ∃ v ∈ V(G), {e ∈ E(G) | G.Inc e v}.ncard ≤ 3 * ω / 2 - 1 := by
  let H := graphToHypergraph G hVG hEG
  have hbw_H : GM10.branchWidth H ≤ ω :=
    (graphBranchWidthLE_iff_branchWidth_le G hVG hEG ω).mp hbw
  have hγ_H : GM10.maxEdgeSize H ≤ 2 := maxEdgeSize_graphToHypergraph_le_two G hVG hEG
  have htw_le : GM10.treeWidthPlusOne H ≤ 3 * ω / 2 := by
    have h51 := (GM10.theorem_5_1_proof H).2
    omega
  obtain ⟨ι, _, T, τ, htd, hw_eq⟩ := GM10.exists_treeDecomposition_eq_treeWidthPlusOne H
  have hU : (⋃ t : ι, (τ t).vertexSet) = H.vertexSet := by
    ext v
    simp [htd.vertex_mem_iff]
  have hE : ∀ e ∈ H.edgeSet, ∃ t : ι, H.ends e ⊆ (τ t).vertexSet := by
    intro e he
    obtain ⟨t, ht⟩ := htd.edge_mem_iff.mp he
    exact ⟨t, htd.ends_subset_vertexSet_of_edge_mem ht⟩
  have hinter : ∀ ⦃t₁ t₃ t₂ : ι⦄, GM10.OnTreePath T t₁ t₂ t₃ →
      (τ t₁).vertexSet ∩ (τ t₂).vertexSet ⊆ (τ t₃).vertexSet :=
    fun _ _ _ hp => (htd.inter_le hp).vertexSet_subset
  obtain ⟨v, hvG, t, hvt, hends⟩ := exists_vertex_bag_contains_ends hne htd.isTree
    (fun s => (τ s).vertexSet) hU hE hinter
  refine ⟨v, hvG, ?_⟩
  let I_v := {e ∈ E(G) | G.Inc e v}
  let f : β → α := fun e => if h : G.Inc e v then h.choose else v
  have hmaps : MapsTo f I_v ((τ t).vertexSet \ {v}) := by
    rintro e ⟨heE, hinc⟩
    have hlink : G.IsLink e v (f e) := by
      dsimp only [f]
      rw [dite_eq_left_of_eq_true (eq_true hinc)]
      exact hinc.choose_spec
    have hinc_fe : H.Inc e (f e) := ⟨v, hlink.symm⟩
    have hne_v : f e ≠ v := fun heq => hSimp.1 e heE v (heq ▸ hlink)
    exact ⟨hends e heE hinc hinc_fe, hne_v⟩
  have hinj : InjOn f I_v := by
    rintro e₁ ⟨he₁, hinc₁⟩ e₂ ⟨he₂, hinc₂⟩ hfe
    have hlink₁ : G.IsLink e₁ v (f e₁) := by
      dsimp only [f]; rw [dite_eq_left_of_eq_true (eq_true hinc₁)]; exact hinc₁.choose_spec
    have hlink₂ : G.IsLink e₂ v (f e₁) := by
      rw [hfe]; dsimp only [f]; rw [dite_eq_left_of_eq_true (eq_true hinc₂)]; exact hinc₂.choose_spec
    exact hSimp.2 e₁ he₁ e₂ he₂ v (f e₁) hlink₁ hlink₂
  have hcard_le : I_v.ncard ≤ ((τ t).vertexSet \ {v}).ncard :=
    ncard_le_ncard_of_injOn f hmaps hinj ((τ t).vertexSet_finite.subset sdiff_subset)
  have hbag_split : ((τ t).vertexSet \ {v}).ncard + 1 = (τ t).vertexSet.ncard :=
    ncard_sdiff_singleton_add_one hvt (τ t).vertexSet_finite
  have hbag_le : (τ t).vertexSet.ncard ≤ 3 * ω / 2 :=
    (GM10.ncard_vertexSet_le_treeDecompWidthPlusOne τ t).trans (hw_eq.trans_le htw_le)
  change I_v.ncard ≤ 3 * ω / 2 - 1
  omega

/-- **Graph Minors XIII, (3.2) Lemma** (page 72):
"If $\omega \ge 2$ is an integer and $G$ is a simple graph with branch-width $\le \omega$, then
$|E(G)| \le (\frac{3}{2}\omega - 1) |V(G)|$." -/
theorem theorem_3_2_proof (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hSimp : IsSimpleGraph G) (ω : ℕ) (hω : 2 ≤ ω) (hbw : GraphBranchWidthLE G ω) :
    E(G).ncard ≤ (3 * ω / 2 - 1) * V(G).ncard ∧
      2 * E(G).ncard ≤ (3 * ω - 2) * V(G).ncard := by
  suffices hmain : ∀ (n : ℕ) (G₀ : Graph α β) (hVG₀ : V(G₀).Finite) (hEG₀ : E(G₀).Finite),
      IsSimpleGraph G₀ → GraphBranchWidthLE G₀ ω → V(G₀).ncard = n →
      E(G₀).ncard ≤ (3 * ω / 2 - 1) * V(G₀).ncard by
    have h1 := hmain V(G).ncard G hVG hEG hSimp hbw rfl
    refine ⟨h1, ?_⟩
    have h2 : 2 * (3 * ω / 2 - 1) ≤ 3 * ω - 2 := by omega
    calc
      2 * E(G).ncard ≤ 2 * ((3 * ω / 2 - 1) * V(G).ncard) := Nat.mul_le_mul_left 2 h1
      _ = 2 * (3 * ω / 2 - 1) * V(G).ncard := (Nat.mul_assoc _ _ _).symm
      _ ≤ (3 * ω - 2) * V(G).ncard := Nat.mul_le_mul_right _ h2
  intro n
  induction n with
  | zero =>
    intro G₀ hVG₀ hEG₀ _ _ hcard0
    have hV_emp : V(G₀) = ∅ := (ncard_eq_zero hVG₀).mp hcard0
    have hE_emp : E(G₀) = ∅ := by
      ext e
      simp only [mem_empty_iff_false, iff_false]
      intro he
      rcases (G₀.edge_mem_iff_exists_isLink e).mp he with ⟨x, y, hxy⟩
      have hx : x ∈ V(G₀) := G₀.left_mem_of_isLink hxy
      rw [hV_emp] at hx
      exact hx
    rw [hE_emp, hcard0, ncard_empty, Nat.mul_zero]
  | succ n ih =>
    intro G₀ hVG₀ hEG₀ hSimp₀ hbw₀ hcard
    have hne : V(G₀).Nonempty := nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨v, hvG₀, hdeg_v⟩ :=
      exists_vertex_degree_le_of_isSimpleGraph hVG₀ hEG₀ hne hSimp₀ hω hbw₀
    let G' := deleteVertices G₀ {v}
    have hG'_le : G' ≤ G₀ := induce_le sdiff_subset
    have hVG' : V(G').Finite := hVG₀.subset hG'_le.vertexSet_mono
    have hEG' : E(G').Finite := hEG₀.subset hG'_le.edgeSet_mono
    have hSimp' : IsSimpleGraph G' :=
      ⟨fun e he v hlink => hSimp₀.1 e (hG'_le.edgeSet_mono he) v (hG'_le.isLink_mono hlink),
        fun e₁ he₁ e₂ he₂ u w hl₁ hl₂ =>
          hSimp₀.2 e₁ (hG'_le.edgeSet_mono he₁) e₂ (hG'_le.edgeSet_mono he₂) u w
            (hG'_le.isLink_mono hl₁) (hG'_le.isLink_mono hl₂)⟩
    have hbw' : GraphBranchWidthLE G' ω := hbw₀.mono hVG₀ hEG₀ hG'_le hω
    have hVG'_eq : V(G') = V(G₀) \ {v} := rfl
    have hcard' : V(G').ncard = n := by
      have h1 := ncard_sdiff_singleton_add_one hvG₀ hVG₀
      rw [← hVG'_eq, hcard] at h1
      omega
    have hih := ih G' hVG' hEG' hSimp' hbw' hcard'
    have hE_sub : E(G₀) ⊆ E(G') ∪ {e ∈ E(G₀) | G₀.Inc e v} := by
      intro e he
      by_cases hinc : G₀.Inc e v
      · exact Or.inr ⟨he, hinc⟩
      · left
        rcases (G₀.edge_mem_iff_exists_isLink e).mp he with ⟨x, y, hxy⟩
        have hx : x ∈ V(G₀) \ {v} := ⟨G₀.left_mem_of_isLink hxy, fun hxv => hinc ⟨y, hxv ▸ hxy⟩⟩
        have hy : y ∈ V(G₀) \ {v} :=
          ⟨G₀.left_mem_of_isLink hxy.symm, fun hyv => hinc ⟨x, hyv ▸ hxy.symm⟩⟩
        exact (G'.edge_mem_iff_exists_isLink e).mpr ⟨x, y, ⟨hxy, hx, hy⟩⟩
    have hE_le : E(G₀).ncard ≤ E(G').ncard + {e ∈ E(G₀) | G₀.Inc e v}.ncard :=
      (ncard_le_ncard hE_sub (hEG'.union (hEG₀.subset (fun _ h => h.1)))).trans
        (ncard_union_le E(G') {e ∈ E(G₀) | G₀.Inc e v})
    rw [hcard]
    rw [hcard'] at hih
    calc
      E(G₀).ncard ≤ E(G').ncard + {e ∈ E(G₀) | G₀.Inc e v}.ncard := hE_le
      _ ≤ (3 * ω / 2 - 1) * n + (3 * ω / 2 - 1) := Nat.add_le_add hih hdeg_v
      _ = (3 * ω / 2 - 1) * (n + 1) := by ring

/-- Step (5), nonemptiness of `E(A)` and `E(B)`, in **Graph Minors XIII, Algorithm (3.3)** (page 74):
"To verify (iii) we observe that $E(A) \ne \emptyset \ne E(B)$; for if $E(A) = \emptyset$, say, then
$B = R$ since $R$ has no isolated vertices, and so
$$
|Z - V(A)| \le \frac{2}{3}|Z| - \frac{1}{2}|Z \cap V(A)|,
$$
that is, $|Z| \le \frac{3}{2}|Z \cap V(A)|$, which is impossible since $|Z| = 3\omega$ and
$$
|Z \cap V(A)| \le |V(A)| = |V(A \cap B)| \le \omega.
$$" -/
lemma algorithm_3_3_step_5_nonempty {R A B : Graph α β} (hVR : V(R).Finite)
    (hsep : IsGraphSeparation R A B)
    (hno_iso : ∀ v ∈ V(R), ∃ e ∈ E(R), R.Inc e v)
    {Z : Set α} (hZ : Z ⊆ V(R)) {ω : ℕ} (hω : 1 ≤ ω) (hZ_card : Z.ncard = 3 * ω)
    (hord : graphSeparationOrder A B ≤ ω)
    (hbalA : 6 * (Z \ V(A)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard)
    (hbalB : 6 * (Z \ V(B)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard) :
    E(A).Nonempty ∧ E(B).Nonempty := by
  have hZ_fin : Z.Finite := hVR.subset hZ
  have hVA_fin : V(A).Finite := hVR.subset hsep.1.vertexSet_mono
  have hVB_fin : V(B).Finite := hVR.subset hsep.2.1.vertexSet_mono
  refine ⟨?_, ?_⟩
  · by_contra hEA_not
    have hEA_emp : E(A) = ∅ := not_nonempty_iff_eq_empty.mp hEA_not
    have hVR_sub_VB : V(R) ⊆ V(B) := by
      intro v hvR
      rcases hno_iso v hvR with ⟨e, heR, w, hlink⟩
      have heB : e ∈ E(B) := by
        have heU : e ∈ E(A) ∪ E(B) := hsep.2.2.2.1 ▸ heR
        rw [hEA_emp, empty_union] at heU
        exact heU
      rcases (B.edge_mem_iff_exists_isLink e).mp heB with ⟨x, y, hxyB⟩
      have hxyR : R.IsLink e x y := hsep.2.1.isLink_mono hxyB
      rcases R.eq_or_eq_of_isLink_of_isLink hlink hxyR with rfl | rfl
      · exact B.left_mem_of_isLink hxyB
      · exact B.left_mem_of_isLink hxyB.symm
    have hVA_inter : V(A) ∩ V(B) = V(A) :=
      inter_eq_self_of_subset_left (hsep.1.vertexSet_mono.trans hVR_sub_VB)
    have hVA_le : V(A).ncard ≤ ω := by
      unfold graphSeparationOrder at hord
      rwa [hVA_inter] at hord
    have hZA_le : (Z ∩ (V(A) ∩ V(B))).ncard ≤ ω := by
      rw [hVA_inter]
      exact (ncard_le_ncard inter_subset_right hVA_fin).trans hVA_le
    have hZ_split : (Z \ V(A)).ncard + (Z ∩ (V(A) ∩ V(B))).ncard = Z.ncard := by
      rw [hVA_inter, ← ncard_union_eq
        (disjoint_left.mpr fun _ hx1 hx2 => hx1.2 hx2.2)
        (hZ_fin.subset sdiff_subset) (hZ_fin.subset inter_subset_left),
        sdiff_union_inter]
    omega
  · by_contra hEB_not
    have hEB_emp : E(B) = ∅ := not_nonempty_iff_eq_empty.mp hEB_not
    have hVR_sub_VA : V(R) ⊆ V(A) := by
      intro v hvR
      rcases hno_iso v hvR with ⟨e, heR, w, hlink⟩
      have heA : e ∈ E(A) := by
        have heU : e ∈ E(A) ∪ E(B) := hsep.2.2.2.1 ▸ heR
        rw [hEB_emp, union_empty] at heU
        exact heU
      rcases (A.edge_mem_iff_exists_isLink e).mp heA with ⟨x, y, hxyA⟩
      have hxyR : R.IsLink e x y := hsep.1.isLink_mono hxyA
      rcases R.eq_or_eq_of_isLink_of_isLink hlink hxyR with rfl | rfl
      · exact A.left_mem_of_isLink hxyA
      · exact A.left_mem_of_isLink hxyA.symm
    have hVB_inter : V(A) ∩ V(B) = V(B) :=
      inter_eq_self_of_subset_right (hsep.2.1.vertexSet_mono.trans hVR_sub_VA)
    have hVB_le : V(B).ncard ≤ ω := by
      unfold graphSeparationOrder at hord
      rwa [hVB_inter] at hord
    have hZB_le : (Z ∩ (V(A) ∩ V(B))).ncard ≤ ω := by
      rw [hVB_inter]
      exact (ncard_le_ncard inter_subset_right hVB_fin).trans hVB_le
    have hZ_split : (Z \ V(B)).ncard + (Z ∩ (V(A) ∩ V(B))).ncard = Z.ncard := by
      rw [hVB_inter, ← ncard_union_eq
        (disjoint_left.mpr fun _ hx1 hx2 => hx1.2 hx2.2)
        (hZ_fin.subset sdiff_subset) (hZ_fin.subset inter_subset_left),
        sdiff_union_inter]
    omega

/-- Step (5), bound on the orders of the two new edges, in **Graph Minors XIII, Algorithm (3.3)**
(page 74):
"$$
\begin{aligned}
|(Z \cup V(A)) \cap V(B)| &= |Z - V(A)| + |V(A) \cap V(B)| \\
&\le \frac{2}{3}|Z| + |V(A \cap B)| \le 2\omega + \omega = 3\omega.
\end{aligned}
$$
Similarly, $|(Z \cup V(B)) \cap V(A)| \le 3\omega$." -/
lemma algorithm_3_3_step_5_order {R A B : Graph α β} (hVR : V(R).Finite)
    (hsep : IsGraphSeparation R A B)
    {Z : Set α} (hZ : Z ⊆ V(R)) {ω : ℕ} (hZ_card : Z.ncard ≤ 3 * ω)
    (hord : graphSeparationOrder A B ≤ ω)
    (hbalA : 6 * (Z \ V(A)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard)
    (hbalB : 6 * (Z \ V(B)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard) :
    ((Z ∪ V(A)) ∩ V(B)).ncard ≤ 3 * ω ∧ ((Z ∪ V(B)) ∩ V(A)).ncard ≤ 3 * ω := by
  have hZ_fin : Z.Finite := hVR.subset hZ
  have hAB_fin : (V(A) ∩ V(B)).Finite := (hVR.subset hsep.1.vertexSet_mono).subset inter_subset_left
  have hsubA : (Z ∪ V(A)) ∩ V(B) ⊆ (Z \ V(A)) ∪ (V(A) ∩ V(B)) := by
    rintro x ⟨hxZ | hxA, hxB⟩
    · by_cases hxA : x ∈ V(A)
      · exact Or.inr ⟨hxA, hxB⟩
      · exact Or.inl ⟨hxZ, hxA⟩
    · exact Or.inr ⟨hxA, hxB⟩
  have hsubB : (Z ∪ V(B)) ∩ V(A) ⊆ (Z \ V(B)) ∪ (V(A) ∩ V(B)) := by
    rintro x ⟨hxZ | hxB, hxA⟩
    · by_cases hxB : x ∈ V(B)
      · exact Or.inr ⟨hxA, hxB⟩
      · exact Or.inl ⟨hxZ, hxB⟩
    · exact Or.inr ⟨hxA, hxB⟩
  have hleA : ((Z ∪ V(A)) ∩ V(B)).ncard ≤ (Z \ V(A)).ncard + (V(A) ∩ V(B)).ncard :=
    (ncard_le_ncard hsubA ((hZ_fin.subset sdiff_subset).union hAB_fin)).trans
      (ncard_union_le _ _)
  have hleB : ((Z ∪ V(B)) ∩ V(A)).ncard ≤ (Z \ V(B)).ncard + (V(A) ∩ V(B)).ncard :=
    (ncard_le_ncard hsubB ((hZ_fin.subset sdiff_subset).union hAB_fin)).trans
      (ncard_union_le _ _)
  unfold graphSeparationOrder at hord
  omega

/-- Step (6) in **Graph Minors XIII, Algorithm (3.3)** (page 74):
"From (3.1), $G_i$ has branch-width $> \omega$, and so $G_{i+1}$ has branch-width $\ge \omega$ (we
leave as an exercise the fact that deleting an edge reduces branch-width by at most one, except when
branch-width $\le 2$ which does not occur here since $\omega \ge 2$)." -/
lemma algorithm_3_3_step_6_deleteEdge (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    {g : β} (hg : g ∈ E(G)) {ω : ℕ} (hω : 2 ≤ ω)
    (hbw' : GraphBranchWidthLE (G.deleteEdges {g}) ω) :
    GraphBranchWidthLE G (ω + 1) := by
  let H := graphToHypergraph G hVG hEG
  let G' := G.deleteEdges {g}
  have hG'_le : G' ≤ G := Graph.deleteEdges_le
  have hVG' : V(G').Finite := hVG.subset hG'_le.vertexSet_mono
  have hEG' : E(G').Finite := hEG.subset hG'_le.edgeSet_mono
  let H' := graphToHypergraph G' hVG' hEG'
  have hbw_H' : GM10.branchWidth H' ≤ ω :=
    (graphBranchWidthLE_iff_branchWidth_le G' hVG' hEG' ω).mp hbw'
  have hγ_H' : GM10.maxEdgeSize H' ≤ ω :=
    (maxEdgeSize_graphToHypergraph_le_two G' hVG' hEG').trans hω
  have hθ_H' : GM10.tangleNumber H' ≤ ω :=
    tangleNumber_le_of_branchWidth_le (by omega) hγ_H' hbw_H'
  rw [graphBranchWidthLE_iff_branchWidth_le G hVG hEG (ω + 1)]
  refine (branchWidth_le_tangleNumber H).trans ?_
  by_contra! hgt
  obtain ⟨𝒯, h𝒯⟩ :=
    GM10.exists_isTangle_of_le_tangleNumber (G := H) (θ := ω + 2) (by omega) (by omega)
  have hH_graph : H.IsGraph := graphToHypergraph_isGraph G hVG hEG
  rcases (hH_graph g hg).1 with ⟨u, hu⟩
  let W : Set α := {u}
  have hW : W ⊆ H.vertexSet := singleton_subset_iff.mpr (H.vertex_mem_of_inc hu)
  have hW_lt : W.ncard < ω + 2 := by
    rw [ncard_singleton]
    omega
  have h𝒯_del : GM10.IsTangle (H.deleteVertices W) (ω + 2 - W.ncard)
      (GM10.deleteVerticesTangle H W 𝒯 (ω + 2)) :=
    GM10.theorem_8_5_proof hH_graph h𝒯 hW hW_lt
  rw [ncard_singleton] at h𝒯_del
  have hdel_le : H.deleteVertices W ≤ H' := by
    refine ⟨sdiff_subset, ?_, ?_⟩
    · rintro e ⟨heG, hnoW⟩
      change e ∈ E(G) \ {g}
      refine ⟨heG, ?_⟩
      rintro rfl
      exact hnoW u (mem_singleton u) hu
    · rintro e ⟨heG, hnoW⟩
      ext v
      change G'.Inc e v ↔ G.Inc e v ∧ ∀ w ∈ W, ¬ G.Inc e w
      have he_ne_g : e ≠ g := fun h => hnoW u (mem_singleton u) (h ▸ hu)
      have hinc_iff : G'.Inc e v ↔ G.Inc e v := by
        change (∃ w, G'.IsLink e v w) ↔ (∃ w, G.IsLink e v w)
        refine exists_congr fun w => ?_
        rw [Graph.deleteEdges_isLink]
        simp [he_ne_g]
      rw [hinc_iff]
      exact ⟨fun hv => ⟨hv, hnoW⟩, fun hv => hv.1⟩
  have hle1 : ω + 1 ≤ GM10.tangleNumber (H.deleteVertices W) := h𝒯_del.le_tangleNumber
  have hle2 : GM10.tangleNumber (H.deleteVertices W) ≤ GM10.tangleNumber H' :=
    tangleNumber_le_of_le hdel_le
  omega

/-- **Graph Minors XIII, (3.3) Algorithm** (page 72):
"*Input:* A graph $G$ with $|E(G)| \ge 2$.
*Output:* A subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of width $\le 3\omega$, such
that either $G' = G$ or $G'$ has branch-width $\ge \omega$.
*Running time:* $O(v^2 + \varepsilon)$."

This is the correctness of the method. The RAM program, which builds the simple subgraph `H₂`
and runs the greedy leaf-splitting loop of Steps (1)–(6), and its `O(v^2 + \varepsilon)` time
bound are `GM13.algorithm_3_3` in `Results.lean`. -/
theorem algorithm_3_3_correct (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hE2 : 2 ≤ E(G).ncard) (ω : ℕ) (hω : 2 ≤ ω) :
    ∃ (G' : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
      G' ≤ G ∧
      2 ≤ E(G').ncard ∧
      IsGraphBranchDecomposition G' T τ ∧
      graphBranchDecompWidth G' T τ ≤ 3 * ω ∧
      (G' = G ∨ ¬ GraphBranchWidthLE G' ω) ∧
      (G' = G ∨ ¬ GraphBranchWidthLE G' (ω - 1)) := by
  by_cases hbwG : GraphBranchWidthLE G ω
  · have hbw3 : GraphBranchWidthLE G (3 * ω) := by
      rcases hbwG with hle1 | ⟨ι, hfin, T, τ, hbd, hw⟩
      · omega
      · exact Or.inr ⟨ι, hfin, T, τ, hbd, hw.trans (by omega)⟩
    rcases hbw3 with hle1 | ⟨ι, hfin, T, τ, hbd, hw⟩
    · omega
    · exact ⟨G, ι, hfin, T, τ, le_rfl, hE2, hbd, hw, Or.inl rfl, Or.inl rfl⟩
  · let S : Set ℕ := {m : ℕ | ∃ G' ≤ G, ¬ GraphBranchWidthLE G' ω ∧ E(G').ncard = m}
    have hS_ne : S.Nonempty := ⟨E(G).ncard, G, le_rfl, hbwG, rfl⟩
    obtain ⟨G', hG'_le, hnot_bw, hm_eq⟩ := Nat.sInf_mem hS_ne
    have hVG' : V(G').Finite := hVG.subset hG'_le.vertexSet_mono
    have hEG' : E(G').Finite := hEG.subset hG'_le.edgeSet_mono
    have hE2' : 2 ≤ E(G').ncard := by
      by_contra! hlt2
      exact hnot_bw (Or.inl (by omega))
    obtain ⟨g, hg⟩ : E(G').Nonempty := nonempty_of_ncard_ne_zero (by omega)
    let G₀ := G'.deleteEdges {g}
    have hG₀_le_G' : G₀ ≤ G' := Graph.deleteEdges_le
    have hG₀_le_G : G₀ ≤ G := hG₀_le_G'.trans hG'_le
    have hEG₀_eq : E(G₀) = E(G') \ {g} := Graph.edgeSet_deleteEdges G' {g}
    have hcard_G₀ : E(G₀).ncard < sInf S := by
      have h1 := ncard_sdiff_singleton_add_one hg hEG'
      rw [← hEG₀_eq, hm_eq] at h1
      omega
    have hbw_G₀ : GraphBranchWidthLE G₀ ω := by
      by_contra hnot₀
      have hmem : E(G₀).ncard ∈ S := ⟨G₀, hG₀_le_G, hnot₀, rfl⟩
      have hle := Nat.sInf_le hmem
      omega
    have hbw_G' : GraphBranchWidthLE G' (ω + 1) :=
      algorithm_3_3_step_6_deleteEdge G' hVG' hEG' hg hω hbw_G₀
    rcases hbw_G' with hle1 | ⟨ι, hfin, T, τ, hbd, hw⟩
    · omega
    · have hnot_bw_sub1 : ¬ GraphBranchWidthLE G' (ω - 1) := by
        intro hbw1
        apply hnot_bw
        rcases hbw1 with h1 | ⟨ι₁, hfin₁, T₁, τ₁, hbd₁, hw₁⟩
        · exact Or.inl h1
        · exact Or.inr ⟨ι₁, hfin₁, T₁, τ₁, hbd₁, hw₁.trans (by omega)⟩
      exact ⟨G', ι, hfin, T, τ, hG'_le, hE2', hbd, hw.trans (by omega),
        Or.inr hnot_bw, Or.inr hnot_bw_sub1⟩

/-- **Graph Minors XIII, (3.3) Algorithm** (page 72), numbered alias for `algorithm_3_3_correct`. -/
theorem theorem_3_3_proof (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hE2 : 2 ≤ E(G).ncard) (ω : ℕ) (hω : 2 ≤ ω) :
    ∃ (G' : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
      G' ≤ G ∧
      2 ≤ E(G').ncard ∧
      IsGraphBranchDecomposition G' T τ ∧
      graphBranchDecompWidth G' T τ ≤ 3 * ω ∧
      (G' = G ∨ ¬ GraphBranchWidthLE G' ω) ∧
      (G' = G ∨ ¬ GraphBranchWidthLE G' (ω - 1)) := by
  obtain ⟨G', ι, hfin, T, τ, hle, hE2', hbd, hw, h1, h2⟩ :=
    algorithm_3_3_correct G hVG hEG hE2 ω hω
  exact ⟨G', ι, hfin, T, τ, hle, hE2', hbd, hw, h1, h2⟩

end GraphMinor.GM13
