module

public import GraphMinor.GM22.Section8c1
public import GraphMinor.GM22.Section7d2c
import GraphMinor.GM12.Section4
import GraphMinor.GM11.Walks

/-!
# Graph Minors XXII, Section 8 (Part c2: Claim 12 and Condition (J7) in Theorem 8.3)

This file proves Claim (12) and the verification of Condition `(J7)` for the family `𝒜'` in the
proof of Theorem (8.3) of Robertson and Seymour, *Graph Minors. XXII. Irrelevant Vertices in
Linkage Problems*, J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 562–563):

- `exists_walk_toEmbeddedGraph_of_toGraph`: lifts a walk in `H.toGraph` to `H.toEmbeddedGraph ιV ιE`.
- `lemma_8_3_claim_12`: Claim (12) of the proof of (8.3).
- `conditionJ7_8_3`: verifies Condition `(J7)` for `𝒜'`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM14.Whitney

universe u v w

variable {α : Type u} {β : Type v}
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## 1. Walk and Path Transport from `H.toGraph` to `H.toEmbeddedGraph` -/

omit [T2Space S] in
/-- Any walk in `H.toGraph` from `a` to `b` maps to a walk in `H.toEmbeddedGraph ιV ιE` from
`ιV a` to `ιV b` with mapped support and edges. -/
theorem exists_walk_toEmbeddedGraph_of_toGraph {H : Drawing S} {ιV : S ↪ α} {ιE : Set S ↪ β}
    {a b : S} (W₀ : GraphWalk H.toGraph a b) :
    ∃ W : GraphWalk (H.toEmbeddedGraph ιV ιE) (ιV a) (ιV b),
      W.support = W₀.support.map ιV ∧ W.edges = W₀.edges.map ιE := by
  induction W₀ with
  | @nil u hu =>
    exact ⟨.nil ⟨u, hu, rfl⟩, rfl, rfl⟩
  | @cons u v w e hlink rest ih =>
    obtain ⟨W_rest, hsupp, hedges⟩ := ih
    have hlink_emb : (H.toEmbeddedGraph ιV ιE).IsLink (ιE e) (ιV u) (ιV v) :=
      ⟨e, u, v, hlink, rfl, rfl, rfl⟩
    refine ⟨.cons hlink_emb W_rest, ?_, ?_⟩
    · rw [GraphWalk.support_cons, GraphWalk.support_cons, List.map_cons, hsupp]
    · rw [GraphWalk.edges_cons, GraphWalk.edges_cons, List.map_cons, hedges]

omit [T2Space S] in
/-- If `H.toGraph` is a path from `a` to `b`, then `H.toEmbeddedGraph ιV ιE` is a path from
`ιV a` to `ιV b`. -/
theorem isGraphPathWithEnds_self_toEmbeddedGraph {H : Drawing S} {ιV : S ↪ α} {ιE : Set S ↪ β}
    {a b : S} (hP : IsGraphPathWithEnds H.toGraph H.toGraph a b) :
    IsGraphPathWithEnds (H.toEmbeddedGraph ιV ιE) (H.toEmbeddedGraph ιV ιE) (ιV a) (ιV b) := by
  obtain ⟨_, W₀, hs₀, hV₀, hE₀⟩ := hP
  obtain ⟨W, hsupp, hedges⟩ := exists_walk_toEmbeddedGraph_of_toGraph (ιV := ιV) (ιE := ιE) W₀
  have hs : W.IsSimple := by
    change W.support.Nodup
    rw [hsupp]
    exact hs₀.map ιV.injective
  have hV₀' : H.V = {x | x ∈ W₀.support} := hV₀
  have hE₀' : H.E = {e | e ∈ W₀.edges} := hE₀
  refine ⟨le_rfl, W, hs, ?_, ?_⟩
  · change ιV '' H.V = {x | x ∈ W.support}
    rw [hV₀', hsupp]
    ext x
    simp
  · change ιE '' H.E = {e | e ∈ W.edges}
    rw [hE₀', hedges]
    ext e
    simp

/-- If `IsGraphSeparation G₀ C D`, any walk in `G₀` starting in `V(C) \ V(D)` and disjoint from
`V(C) ∩ V(D)` ends in `V(C) \ V(D)`. -/
theorem walk_end_mem_left_sdiff_of_disjoint_sep {G₀ C D : Graph α β}
    (hsep : IsGraphSeparation G₀ C D) {u v : α} (W : GraphWalk G₀ u v)
    (hu : u ∈ V(C) \ V(D)) (hdisj : Disjoint {x | x ∈ W.support} (V(C) ∩ V(D))) :
    v ∈ V(C) \ V(D) := by
  induction W with
  | nil _ => exact hu
  | @cons x y z e hlink rest ih =>
    have hx_not_inter : x ∉ V(C) ∩ V(D) :=
      disjoint_left.mp hdisj (by simp [GraphWalk.support])
    have hy_not_inter : y ∉ V(C) ∩ V(D) :=
      disjoint_left.mp hdisj (by simp [GraphWalk.support, rest.start_mem_support])
    have he_CD : e ∈ E(C) ∪ E(D) := hsep.2.2.2.1 ▸ hlink.edge_mem
    have hy_CD : y ∈ V(C) \ V(D) := by
      rcases he_CD with heC | heD
      · have hlinkC : C.IsLink e x y := (hsep.1.isLink_iff heC).mpr hlink
        have hyC : y ∈ V(C) := hlinkC.right_mem
        exact ⟨hyC, fun hyD => hy_not_inter ⟨hyC, hyD⟩⟩
      · have hlinkD : D.IsLink e x y := (hsep.2.1.isLink_iff heD).mpr hlink
        exact (hu.2 hlinkD.left_mem).elim
    exact ih hy_CD (Disjoint.mono_left (fun w hw => List.mem_cons_of_mem x hw) hdisj)

/-- If `IsGraphSeparation G₀ C D` and `W : GraphWalk G₀ u v` has `u ∈ V(C)` and `v ∉ V(C)`, then
some vertex in `W.support` lies in `V(C) ∩ V(D)`. -/
theorem exists_mem_inter_of_walk_sep {G₀ C D : Graph α β}
    (hsep : IsGraphSeparation G₀ C D) {u v : α} (W : GraphWalk G₀ u v)
    (hu : u ∈ V(C)) (hv : v ∉ V(C)) :
    ∃ z ∈ W.support, z ∈ V(C) ∩ V(D) := by
  by_contra! hno
  have hu_diff : u ∈ V(C) \ V(D) := ⟨hu, fun huD => hno u W.start_mem_support ⟨hu, huD⟩⟩
  have hdisj : Disjoint {x | x ∈ W.support} (V(C) ∩ V(D)) :=
    disjoint_left.mpr fun z hz hzCD => hno z hz hzCD
  exact hv (walk_end_mem_left_sdiff_of_disjoint_sep hsep W hu_diff hdisj).1

omit [TopologicalSpace S] [T2Space S] in
/-- A tangle `T` cannot contain both `(A, B)` and `(B, A)`. -/
theorem tangle_not_both {G : Hypergraph S (Set S)} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle G ord T) {A B : Hypergraph S (Set S)}
    (hAB : (A, B) ∈ T) (hBA : (B, A) ∈ T) : False :=
  hT.axiom2 hAB hAB hBA (by rw [GM10.union_self, (hT.isSeparation hAB).union_eq])

/-! ## 2. Proof of Claim (12) of Theorem 8.3 (page 562) -/

set_option maxHeartbeats 600000 in
/-- **Graph Minors XXII, (8.3) Claim (12)** (Section 8, page 562):
*There is no $$A \in \mathcal{A}'$$ and separation $$(C, D)$$ of $$G \setminus W$$ of order
$$< |\bar{\pi}(A)|$$ with $$A \setminus W \subseteq C$$ and
$$(C \cap \Gamma, D \cap \Gamma) \in \mathcal{T}$$.* -/
theorem lemma_8_3_claim_12
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    ∀ A ∈ 𝒜', ¬ ∃ (C D : Graph α β) (C_Γ D_Γ : Hypergraph S (Set S)),
      IsGraphSeparation (R_G.G.toGraph.deleteVerts W) C D ∧
      (V(C) ∩ V(D)).ncard < πLen A ∧
      A.deleteVerts W ≤ C ∧
      C_Γ.vertexSet = ιV ⁻¹' V(C) ∩ Γ.V ∧ C_Γ.edgeSet = ιE ⁻¹' E(C) ∩ Γ.E ∧
      D_Γ.vertexSet = ιV ⁻¹' V(D) ∩ Γ.V ∧ D_Γ.edgeSet = ιE ⁻¹' E(D) ∩ Γ.E ∧
      (C_Γ, D_Γ) ∈ T := by
  intro 𝒜' A ⟨hA, hdist5⟩ ⟨C, D, C_Γ, D_Γ, hsep, hord_lt, hA_le_C, hCV, hCE, hDV, hDE, hCD_T⟩
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hT : IsTangle Γ.toHypergraph ord T := h83.hyp_iv.2.1.1.2.1
  have hsep_Γ : Γ.toHypergraph.IsSeparation C_Γ D_Γ := hT.isSeparation hCD_T
  have hord_Γ : separationOrder C_Γ D_Γ < ord := hT.order_lt hCD_T
  have hle_C_Γ : C_Γ ≤ Γ.toHypergraph := hsep_Γ.left_le
  have hle_D_Γ : D_Γ ≤ Γ.toHypergraph := hsep_Γ.right_le
  have hπ_le3 : πLen A ≤ 3 := (h83.hyp_vii A hA).1
  have hfin_CD : (V(C) ∩ V(D)).Finite :=
    h83.finite_V.subset ((inter_subset_left.trans hsep.1.vertexSet_mono).trans
      Graph.deleteVerts_le.vertexSet_mono)
  -- Step 1: By pigeonhole on `Fin (πLen A)`, one of the `πLen A` disjoint paths `P i` from
  -- `πA A i` to `ιV (t i)` avoids `V(C) ∩ V(D)`.
  obtain ⟨P, t, hPt, hP_disj, -⟩ := h83.hyp_viii A hA
  have hex_i : ∃ i : Fin (πLen A), Disjoint V(P i) (V(C) ∩ V(D)) := by
    by_contra! hmeet'
    have hmeet : ∀ i : Fin (πLen A), ∃ z ∈ V(P i), z ∈ V(C) ∩ V(D) :=
      fun i => Set.not_disjoint_iff.mp (hmeet' i)
    choose z hzP hzCD using hmeet
    have hz_inj : Function.Injective z := by
      intro i j hzij
      by_contra hne
      exact disjoint_left.mp (hP_disj hne) (hzP i) (hzij ▸ hzP j)
    have hrange_sub : Set.range z ⊆ V(C) ∩ V(D) := by
      rintro _ ⟨i, rfl⟩
      exact hzCD i
    have hcard_le : (Set.range z).ncard ≤ (V(C) ∩ V(D)).ncard :=
      Set.ncard_le_ncard hrange_sub hfin_CD
    rw [Set.ncard_range_of_injective hz_inj, Nat.card_fin] at hcard_le
    omega
  obtain ⟨i₀, hi₀_disj⟩ := hex_i
  have ht_Pi : t i₀ ∈ PiSet := (hPt i₀).1
  have ht_C₀ : t i₀ ∈ C₀.V := h83.hyp_iii.1 ht_Pi
  have ht_ΓV : t i₀ ∈ Γ.V := h83.hyp_ii.1.1 ht_C₀
  have hπ_in_Z : πA A i₀ ∈ Z ∩ V(A) := (h83.hyp_vii A hA).2.2 ▸ ⟨i₀, rfl⟩
  have hπ_not_W : πA A i₀ ∉ W := (h83.hyp_vi.1 hπ_in_Z.1).2
  have hπ_in_C : πA A i₀ ∈ V(C) :=
    hA_le_C.vertexSet_mono (by rw [Graph.vertexSet_deleteVerts]; exact ⟨hπ_in_Z.2, hπ_not_W⟩)
  obtain ⟨hP_le_JW, W_P, _, hVP_eq, _⟩ := (hPt i₀).2
  have hJW_le_GW : J.deleteVerts W ≤ R_G.G.toGraph.deleteVerts W := by
    refine ⟨?_, fun e x y hlk => ?_⟩
    · rw [Graph.vertexSet_deleteVerts, Graph.vertexSet_deleteVerts]
      exact sdiff_subset_sdiff h83.hyp_v.1.vertexSet_mono Subset.rfl
    · rw [Graph.deleteVerts_isLink] at hlk ⊢
      exact ⟨hlk.1.mono h83.hyp_v.1, hlk.2⟩
  have hP_le_GW : P i₀ ≤ R_G.G.toGraph.deleteVerts W := hP_le_JW.trans hJW_le_GW
  obtain ⟨W_G, hsupp_G, _⟩ := W_P.exists_transfer (G' := R_G.G.toGraph.deleteVerts W)
    (fun _ _ _ _ hlk => hlk.mono hP_le_GW)
    (fun x hx => hP_le_GW.vertexSet_mono (W_P.mem_vertexSet_of_mem_support hx))
  have hsupp_disj : Disjoint {x | x ∈ W_G.support} (V(C) ∩ V(D)) := by
    refine Disjoint.mono_left (fun x hx => ?_) hi₀_disj
    rw [hVP_eq, mem_ofPred_eq, ← hsupp_G]
    exact hx
  have hπ_diff : πA A i₀ ∈ V(C) \ V(D) :=
    ⟨hπ_in_C, fun hD => disjoint_left.mp hsupp_disj W_G.start_mem_support ⟨hπ_in_C, hD⟩⟩
  have ht_in_CD : ιV (t i₀) ∈ V(C) \ V(D) :=
    walk_end_mem_left_sdiff_of_disjoint_sep hsep W_G hπ_diff hsupp_disj
  have ht_CΓ : t i₀ ∈ C_Γ.vertexSet := by
    rw [hCV]
    exact ⟨ht_in_CD.1, ht_ΓV⟩
  have ht_not_DΓ : t i₀ ∉ D_Γ.vertexSet := by
    rw [hDV]
    exact fun h => ht_in_CD.2 h.1
  -- Step 2: Analyze `E₀ := C_Γ.edgeSet` in `Γ.toGraph`.
  obtain ⟨G₀, P_sub, hSub⟩ := exists_subData h83.hyp_i.2
  let E₀ : Set (Set S) := C_Γ.edgeSet
  have hE₀_sub : E₀ ⊆ Γ.E := hle_C_Γ.edgeSet_subset
  have hcompl_E₀ : Γ.E \ E₀ = D_Γ.edgeSet := by
    ext e
    simp only [mem_sdiff, E₀]
    constructor
    · intro ⟨heΓ, he_not_C⟩
      have he_union : e ∈ C_Γ.edgeSet ∪ D_Γ.edgeSet :=
        (isSeparation_iff_of_le hle_C_Γ hle_D_Γ).mp hsep_Γ |>.2.1 ▸ heΓ
      exact he_union.resolve_left he_not_C
    · intro heD
      have he_disj : C_Γ.edgeSet ∩ D_Γ.edgeSet = ∅ :=
        (isSeparation_iff_of_le hle_C_Γ hle_D_Γ).mp hsep_Γ |>.2.2
      exact ⟨hle_D_Γ.edgeSet_subset heD, fun heC => by
        have : e ∈ (∅ : Set (Set S)) := he_disj ▸ ⟨heC, heD⟩
        exact this⟩
  have hverts_E₀_sub : verts Γ.toGraph E₀ ⊆ C_Γ.vertexSet := by
    rintro v ⟨e, heC, w, hlk⟩
    have hinc : Γ.toHypergraph.Inc e v := by
      refine ⟨hlk.1, hlk.2.1, ?_⟩
      have : v ∈ closure e ∩ Γ.V := hlk.2.2.2 ▸ Or.inl rfl
      exact this.1
    have hincC : C_Γ.Inc e v := (GM10.inc_iff_of_le hle_C_Γ heC).mpr hinc
    exact C_Γ.vertex_mem_of_inc hincC
  have hverts_compl_sub : verts Γ.toGraph (Γ.E \ E₀) ⊆ D_Γ.vertexSet := by
    rw [hcompl_E₀]
    rintro v ⟨e, heD, w, hlk⟩
    have hinc : Γ.toHypergraph.Inc e v := by
      refine ⟨hlk.1, hlk.2.1, ?_⟩
      have : v ∈ closure e ∩ Γ.V := hlk.2.2.2 ▸ Or.inl rfl
      exact this.1
    have hincD : D_Γ.Inc e v := (GM10.inc_iff_of_le hle_D_Γ heD).mpr hinc
    exact D_Γ.vertex_mem_of_inc hincD
  have hbd_sub_inter : bdry Γ.toGraph E₀ ⊆ C_Γ.vertexSet ∩ D_Γ.vertexSet :=
    fun _ ⟨h1, h2⟩ => ⟨hverts_E₀_sub h1, hverts_compl_sub h2⟩
  have hinter_map_sub : ιV '' (C_Γ.vertexSet ∩ D_Γ.vertexSet) ⊆ V(C) ∩ V(D) := by
    rintro _ ⟨v, ⟨hvC, hvD⟩, rfl⟩
    rw [hCV] at hvC
    rw [hDV] at hvD
    exact ⟨hvC.1, hvD.1⟩
  have hsep_ord_le : separationOrder C_Γ D_Γ ≤ (V(C) ∩ V(D)).ncard := by
    unfold separationOrder
    change (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard ≤ (V(C) ∩ V(D)).ncard
    rw [← Set.ncard_image_of_injective _ ιV.injective]
    exact Set.ncard_le_ncard hinter_map_sub hfin_CD
  have hbd_card_le : (bdry Γ.toGraph E₀).ncard ≤ 2 := by
    have hle : (bdry Γ.toGraph E₀).ncard ≤ separationOrder C_Γ D_Γ :=
      Set.ncard_le_ncard hbd_sub_inter (Γ.finite_V.subset
        (inter_subset_left.trans hle_C_Γ.vertexSet_subset))
    omega
  have hE₀_ne : E₀.Nonempty := by
    obtain ⟨g, hgE, hig⟩ := SubDataSepGeneral.exists_inc_of_mem_V hSub ht_ΓV
    by_cases hgC : g ∈ E₀
    · exact ⟨g, hgC⟩
    · exfalso
      exact ht_not_DΓ (hverts_compl_sub ⟨g, ⟨hgE, hgC⟩, hig⟩)
  have hcompl_ne : (Γ.E \ E₀).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, hcompl_E₀] at hemp
    let Q₀ : Graph S (Set S) := Graph.noEdge {t i₀} (Set S)
    have hQ₀_path : IsGraphPathWithEnds Γ.toGraph Q₀ (t i₀) (t i₀) := by
      refine ⟨⟨singleton_subset_iff.mpr ht_ΓV, fun _ _ _ h => h.elim⟩,
        .nil (mem_singleton (t i₀)), List.nodup_singleton (t i₀), ?_, ?_⟩
      · ext z; exact mem_singleton_iff.trans List.mem_singleton.symm
      · ext g; exact iff_of_false id List.not_mem_nil
    have hbd_Q₀ : bdry Γ.toGraph E(Q₀) ⊆ {t i₀, t i₀} := by
      rintro _ ⟨⟨_, hg, _⟩, _⟩
      exact hg.elim
    have hDC_T : (D_Γ, C_Γ) ∈ T :=
      path_sep_mem_tangle hT hord hQ₀_path hbd_Q₀ hsep_Γ.symm
        (by rw [GM10.separationOrder_comm]; exact hord_Γ)
        (by rw [hemp]; exact empty_subset _)
    exact tangle_not_both hT hCD_T hDC_T
  -- Step 3: Apply `SubDataSepGeneral.sep_general` to `E₀`.
  obtain ⟨e₀, x, y, Q, _, hxy, hbd_eq, _, hQ_path, hQ_cases⟩ :=
    SubDataSepGeneral.sep_general hSub hE₀_sub hbd_card_le hE₀_ne hcompl_ne
  have hE₀_eq_Q : E₀ = E(Q) ∧ verts Γ.toGraph E₀ = V(Q) := by
    rcases hQ_cases with h1 | ⟨hDE_eq, _⟩
    · exact h1
    · exfalso
      have hbd_Q : bdry Γ.toGraph E(Q) ⊆ {x, y} := by
        rw [← hDE_eq, bdry_compl hE₀_sub, hbd_eq]
      have hDC_T : (D_Γ, C_Γ) ∈ T :=
        path_sep_mem_tangle hT hord hQ_path hbd_Q hsep_Γ.symm
          (by rw [GM10.separationOrder_comm]; exact hord_Γ)
          (by rw [← hcompl_E₀]; exact subset_of_eq hDE_eq)
      exact tangle_not_both hT hCD_T hDC_T
  -- Step 4: Deduce `V(C) ∩ V(D) = {ιV x, ιV y}` and `vA A ∈ V(Q)`.
  have hx_inter : x ∈ C_Γ.vertexSet ∩ D_Γ.vertexSet :=
    hbd_sub_inter (hbd_eq ▸ Or.inl rfl)
  have hy_inter : y ∈ C_Γ.vertexSet ∩ D_Γ.vertexSet :=
    hbd_sub_inter (hbd_eq ▸ Or.inr rfl)
  have hxy_sub_CD : ({ιV x, ιV y} : Set α) ⊆ V(C) ∩ V(D) := by
    rintro z (rfl | rfl)
    · exact hinter_map_sub ⟨x, hx_inter, rfl⟩
    · exact hinter_map_sub ⟨y, hy_inter, rfl⟩
  have hCD_eq_pair : V(C) ∩ V(D) = {ιV x, ιV y} := by
    have hcard2 : ({ιV x, ιV y} : Set α).ncard = 2 :=
      Set.ncard_pair (fun h => hxy (ιV.injective h))
    exact (Set.eq_of_subset_of_ncard_le hxy_sub_CD (by omega) hfin_CD).symm
  -- Use `hyp_xi` to show `ιV (vA A) ∈ V(C)` and `vA A ∈ V(Q)`.
  obtain ⟨hvA_V, u_ξ, hu_ξ_ZA, P_ξ, hP_ξ_path, hP_ξ_inter⟩ := h83.hyp_xi A hA
  have hu_ξ_not_W : u_ξ ∉ W := (h83.hyp_vi.1 hu_ξ_ZA.1).2
  have hu_ξ_C : u_ξ ∈ V(C) :=
    hA_le_C.vertexSet_mono (by rw [Graph.vertexSet_deleteVerts]; exact ⟨hu_ξ_ZA.2, hu_ξ_not_W⟩)
  have hvA_in_C : ιV (vA A) ∈ V(C) := by
    by_contra hvA_not_C
    obtain ⟨hle_ξ, W_ξ, _, hV_ξ, _⟩ := hP_ξ_path.symm
    obtain ⟨W_ξG, hsupp_ξ, _⟩ := W_ξ.exists_transfer (G' := R_G.G.toGraph.deleteVerts W)
      (fun _ _ _ _ hlk => hlk.mono hle_ξ)
      (fun z hz => hle_ξ.vertexSet_mono (W_ξ.mem_vertexSet_of_mem_support hz))
    obtain ⟨z, hz_supp, hz_CD⟩ := exists_mem_inter_of_walk_sep hsep W_ξG hu_ξ_C hvA_not_C
    have hz_Pξ : z ∈ V(P_ξ) := by
      rw [hV_ξ, mem_ofPred_eq, ← hsupp_ξ]
      exact hz_supp
    have hz_ΓV : z ∈ ιV '' Γ.V := by
      rw [hCD_eq_pair] at hz_CD
      rcases hz_CD with rfl | rfl
      · exact ⟨x, hle_C_Γ.vertexSet_subset hx_inter.1, rfl⟩
      · exact ⟨y, hle_C_Γ.vertexSet_subset hy_inter.1, rfl⟩
    have hz_eq : z = ιV (vA A) := by
      have : z ∈ V(P_ξ) ∩ (ιV '' Γ.V) := ⟨hz_Pξ, hz_ΓV⟩
      rwa [hP_ξ_inter, mem_singleton_iff] at this
    exact hvA_not_C (hz_eq ▸ hz_CD.1)
  have hvA_CΓ : vA A ∈ C_Γ.vertexSet := by
    rw [hCV]
    exact ⟨hvA_in_C, hvA_V⟩
  have hCΓ_sub_VQ : C_Γ.vertexSet ⊆ V(Q) := by
    intro v hvC
    have hvΓ : v ∈ Γ.V := hle_C_Γ.vertexSet_subset hvC
    obtain ⟨g, hgE, hig⟩ := SubDataSepGeneral.exists_inc_of_mem_V hSub hvΓ
    by_cases hg0 : g ∈ E₀
    · rw [← hE₀_eq_Q.2]
      exact ⟨g, hg0, hig⟩
    · have hvD : v ∈ D_Γ.vertexSet := hverts_compl_sub ⟨g, ⟨hgE, hg0⟩, hig⟩
      have hv_CD : ιV v ∈ V(C) ∩ V(D) := hinter_map_sub ⟨v, ⟨hvC, hvD⟩, rfl⟩
      rw [hCD_eq_pair] at hv_CD
      have hv_bd : v ∈ bdry Γ.toGraph E₀ := by
        rw [hbd_eq]
        rcases hv_CD with h | h
        · exact Or.inl (ιV.injective h)
        · exact Or.inr (ιV.injective h)
      rw [← hE₀_eq_Q.2]
      exact hv_bd.1
  have hvA_VQ : vA A ∈ V(Q) := hCΓ_sub_VQ hvA_CΓ
  have ht_VQ : t i₀ ∈ V(Q) := hCΓ_sub_VQ ht_CΓ
  -- Step 5: Connect `vA A` and `t i₀` inside `Q`, and apply `GM12.theorem_4_1_proof`.
  obtain ⟨hQ_le, W_Q, _, hVQ, _⟩ := hQ_path
  have hvA_WQ : vA A ∈ W_Q.support := by rwa [hVQ] at hvA_VQ
  have ht_WQ : t i₀ ∈ W_Q.support := by rwa [hVQ] at ht_VQ
  obtain ⟨W_x_vA, _, _⟩ := W_Q.exists_append_of_mem hvA_WQ
  obtain ⟨W_x_t, _, _⟩ := W_Q.exists_append_of_mem ht_WQ
  let W_join_Q : GraphWalk Q (vA A) (t i₀) := W_x_vA.reverse.append W_x_t
  obtain ⟨W_join_Γ, hsupp_join, _⟩ := W_join_Q.exists_transfer (G' := Γ.toGraph)
    (fun _ _ _ _ hlk => hlk.mono hQ_le)
    (fun z hz => hQ_le.vertexSet_mono (W_join_Q.mem_vertexSet_of_mem_support hz))
  obtain ⟨W_s, hs_s, hsub_s, _⟩ := GM09.exists_isSimple_subwalk W_join_Γ
  let P_draw := GM11.walkDrawing Γ W_s
  have hP_sub : P_draw.IsSubdrawing Γ := GM11.walkDrawing_isSubdrawing Γ W_s
  have hP_path : P_draw.IsPathBetween (vA A) (t i₀) := GM11.walkDrawing_isPathBetween Γ hs_s
  have hPV_sub : P_draw.V ⊆ C_Γ.vertexSet := by
    intro z hz
    rw [GM11.walkDrawing_V, mem_ofPred_eq] at hz
    have hz_join : z ∈ W_join_Q.support := by
      rw [← hsupp_join]
      exact hsub_s z hz
    have hz_Q : z ∈ V(Q) := W_join_Q.mem_vertexSet_of_mem_support hz_join
    rw [← hE₀_eq_Q.2] at hz_Q
    exact hverts_E₀_sub hz_Q
  have hd_le : d {vA A} {t i₀} ≤ 2 * separationOrder C_Γ D_Γ :=
    GM12.theorem_4_1_proof Γ P_draw ord T d C_Γ D_Γ (vA A) (t i₀)
      hS hConn h83.hyp_iv.2.1 hvA_V ht_ΓV hP_path hP_sub hCD_T hPV_sub
  have hd_C₀_le : subsetTangleDist Γ ord d {vA A} C₀.V ≤ d {vA A} {t i₀} :=
    subsetTangleDist_le_of_mem
      (Or.inl (Or.inl ⟨vA A, hvA_V, rfl⟩))
      (Or.inl (Or.inl ⟨t i₀, ht_ΓV, rfl⟩))
      ⟨vA A, rfl, rfl⟩ ⟨t i₀, rfl, ht_C₀⟩
  omega

/-! ## 3. Verification of Condition `(J7)` for `𝒜'` -/

/-- For a closed disc `D_A` with `subBd D_A ∩ Γ.U ⊆ Γ.V` and `IsTangleIns Γ T (subBd D_A) D_A`,
and `H := Γ.interSet D_A`:
1. `H.toGraph ≤ Γ.toGraph` and `H.toGraph.IsLink e x y ↔ e ∈ H.E ∧ Γ.toGraph.IsLink e x y`,
2. `verts Γ.toGraph H.E ⊆ H.V`,
3. `H.V ∩ verts Γ.toGraph (Γ.E \ H.E) ⊆ subBd D_A ∩ Γ.V`,
4. `bdry Γ.toGraph H.E ⊆ subBd D_A ∩ Γ.V`,
5. `H.V \ verts Γ.toGraph H.E ⊆ subBd D_A ∩ Γ.V`,
6. for any `E₁ ⊆ H.E` with `(bdry Γ.toGraph E₁).ncard < ord`,
   `(drawingEdgeSepA Γ E₁, drawingEdgeSepB Γ E₁) ∈ T`. -/
theorem interSet_disc_graph_props
    {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hSph : IsSphere S) (hSub : IsSubdivisionOfSimpleThreeConnected Γ.toGraph)
    (hT : IsTangle Γ.toHypergraph ord T) (hord : 4 ≤ ord)
    {D_A : Set S} (hDisc : IsClosedDisc D_A)
    (hNorm : subBd D_A ∩ Γ.U ⊆ Γ.V)
    (hIns : IsTangleIns Γ T (subBd D_A) D_A) :
    let H := Γ.interSet D_A
    H.toGraph ≤ Γ.toGraph ∧
    (∀ e x y, H.toGraph.IsLink e x y ↔ e ∈ H.E ∧ Γ.toGraph.IsLink e x y) ∧
    verts Γ.toGraph H.E ⊆ H.V ∧
    H.V ∩ verts Γ.toGraph (Γ.E \ H.E) ⊆ subBd D_A ∩ Γ.V ∧
    bdry Γ.toGraph H.E ⊆ subBd D_A ∩ Γ.V ∧
    H.V \ verts Γ.toGraph H.E ⊆ subBd D_A ∩ Γ.V ∧
    (∀ E₁ ⊆ H.E, (bdry Γ.toGraph E₁).ncard < ord →
      (drawingEdgeSepA Γ E₁, drawingEdgeSepB Γ E₁) ∈ T) := by
  intro H
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hSph
  have hClosed : IsClosed D_A := hDisc.isClosed
  have hH_sub : H.IsSubdrawing Γ := GM11.interSet_isSub
  have hle : H.toGraph ≤ Γ.toGraph := by
    refine ⟨hH_sub.1, fun e x y hlk => ?_⟩
    obtain ⟨heH, hxH, hyH, hcl⟩ := hlk
    refine ⟨hH_sub.2 heH, hH_sub.1 hxH, hH_sub.1 hyH, ?_⟩
    rw [← hcl]
    have he_sub : e ⊆ D_A := (GM11.mem_interSet_E_iff.mp heH).2
    have hcl_sub : closure e ⊆ D_A := hClosed.closure_subset_iff.mpr he_sub
    ext z
    simp only [mem_inter_iff]
    exact ⟨fun ⟨hze, hzV⟩ => ⟨hze, (GM11.mem_interSet_V_iff hClosed).mpr ⟨hzV, hcl_sub hze⟩⟩,
      fun ⟨hze, hzH⟩ => ⟨hze, hH_sub.1 hzH⟩⟩
  have hLink : ∀ e x y, H.toGraph.IsLink e x y ↔ e ∈ H.E ∧ Γ.toGraph.IsLink e x y :=
    fun e x y => ⟨fun h => ⟨h.1, h.mono hle⟩, fun ⟨he, h⟩ => (hle.isLink_iff he).mpr h⟩
  have hverts_in : verts Γ.toGraph H.E ⊆ H.V := by
    rintro x ⟨e, heH, y, hlk⟩
    exact ((hLink e x y).mpr ⟨heH, hlk⟩).left_mem
  obtain ⟨Δ_c, hΔc_disc, hbd_c, hΔc_eq, _⟩ :=
    exists_complementary_closedDisc_in_sphere hSph hDisc
  have hverts_out : H.V ∩ verts Γ.toGraph (Γ.E \ H.E) ⊆ subBd D_A ∩ Γ.V := by
    rintro x ⟨hxH, e, ⟨heΓ, he_not_H⟩, y, hlk⟩
    obtain ⟨hxV, hxD⟩ := (GM11.mem_interSet_V_iff hClosed).mp hxH
    have he_disj_bd : Disjoint e (subBd D_A) := by
      rw [Set.disjoint_left]
      intro z hze hz_bd
      exact (heΓ.2.1 hze).2 (hNorm ⟨hz_bd, (heΓ.2.1 hze).1⟩)
    have he_not_sub : ¬ e ⊆ D_A := fun hsub =>
      he_not_H (GM11.mem_interSet_E_iff.mpr ⟨heΓ, hsub⟩)
    obtain ⟨z₀, hz₀e, hz₀_not_D⟩ := Set.not_subset.mp he_not_sub
    have he_disj_fr : Disjoint e (frontier Δ_c) := by
      rwa [← GM11.subBd_eq_frontier, hbd_c]
    have he_sub_Δc : e ⊆ Δ_c :=
      isPreconnected_subset_of_disjoint_frontier' heΓ.2.2.1.isConnected.isPreconnected
        hΔc_disc.isClosed he_disj_fr hz₀e (hΔc_eq ▸ Or.inl ⟨mem_univ z₀, hz₀_not_D⟩)
    have hx_cl : x ∈ closure e := by
      have : x ∈ closure e ∩ Γ.V := hlk.2.2.2 ▸ Or.inl rfl
      exact this.1
    have hx_Δc : x ∈ Δ_c := hΔc_disc.isClosed.closure_subset_iff.mpr he_sub_Δc hx_cl
    rcases (hΔc_eq ▸ hx_Δc : x ∈ (Set.univ \ D_A) ∪ subBd D_A) with hx_out | hx_bd
    · exact (hx_out.2 hxD).elim
    · exact ⟨hx_bd, hxV⟩
  have hbd_sub : bdry Γ.toGraph H.E ⊆ subBd D_A ∩ Γ.V :=
    fun _ ⟨h1, h2⟩ => hverts_out ⟨hverts_in h1, h2⟩
  obtain ⟨_, _, hSubData⟩ := exists_subData hSub
  have hiso_sub : H.V \ verts Γ.toGraph H.E ⊆ subBd D_A ∩ Γ.V := by
    rintro x ⟨hxH, hx_not_in⟩
    have hxV : x ∈ Γ.V := hH_sub.1 hxH
    obtain ⟨g, hgE, hig⟩ := SubDataSepGeneral.exists_inc_of_mem_V hSubData hxV
    have hg_not_H : g ∉ H.E := fun hgH => hx_not_in ⟨g, hgH, hig⟩
    exact hverts_out ⟨hxH, g, ⟨hgE, hg_not_H⟩, hig⟩
  have hSep_T : ∀ E₁ ⊆ H.E, (bdry Γ.toGraph E₁).ncard < ord →
      (drawingEdgeSepA Γ E₁, drawingEdgeSepB Γ E₁) ∈ T := by
    intro E₁ hE₁ hcard_lt
    have hIns_T := hIns.2.2
    have hord_E₁ : separationOrder (drawingEdgeSepA Γ E₁) (drawingEdgeSepB Γ E₁) < ord := by
      rwa [separationOrder, inter_vertexSet_drawingEdgeSep]
    have hE₁_sub_ins : (drawingEdgeSepA Γ E₁).edgeSet ⊆
        ((PaintingOrDrawing.drawing Γ).inter D_A).edgeSet := by
      rintro e ⟨he₁, _⟩
      have heH : e ∈ H.E := hE₁ he₁
      exact GM11.mem_interSet_E_iff.mp heH
    exact GM10.theorem_2_9_proof hT hIns_T (isSeparation_drawingEdgeSep Γ E₁) hord_E₁
      (Or.inr (Or.inr ⟨by omega, hE₁_sub_ins⟩))
  exact ⟨hle, hLink, hverts_in, hverts_out, hbd_sub, hiso_sub, hSep_T⟩

/-- If `E₁ ⊆ H.E` is nonempty and `(bdry Γ.toGraph E₁).ncard ≤ 2`, then `E₁` is the edge set of a
path `Q` in `H.toGraph` joining the two vertices of `bdry Γ.toGraph E₁`, with
`verts Γ.toGraph E₁ = V(Q)`. -/
theorem path_of_subset_interSet_E
    {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hSph : IsSphere S) (hSub : IsSubdivisionOfSimpleThreeConnected Γ.toGraph)
    (hT : IsTangle Γ.toHypergraph ord T) (hord : 4 ≤ ord)
    {D_A : Set S} (hDisc : IsClosedDisc D_A)
    (hNorm : subBd D_A ∩ Γ.U ⊆ Γ.V)
    (hIns : IsTangleIns Γ T (subBd D_A) D_A)
    {E₁ : Set (Set S)} (hE₁ : E₁ ⊆ (Γ.interSet D_A).E)
    (hne : E₁.Nonempty) (hc : (bdry Γ.toGraph E₁).ncard ≤ 2) :
    ∃ (x y : S) (Q : Graph S (Set S)),
      x ≠ y ∧ bdry Γ.toGraph E₁ = {x, y} ∧
      IsGraphPathWithEnds (Γ.interSet D_A).toGraph Q x y ∧
      E₁ = E(Q) ∧ verts Γ.toGraph E₁ = V(Q) := by
  let H := Γ.interSet D_A
  obtain ⟨hle_H, hLink_H, hverts_H, _, _, _, hSep_T⟩ :=
    interSet_disc_graph_props hSph hSub hT hord hDisc hNorm hIns
  have hH_sub : H.IsSubdrawing Γ := GM11.interSet_isSub
  have hE₁_Γ : E₁ ⊆ Γ.E := hE₁.trans hH_sub.2
  have hA_in_T : (drawingEdgeSepA Γ E₁, drawingEdgeSepB Γ E₁) ∈ T :=
    hSep_T E₁ hE₁ (by omega)
  obtain ⟨_, _, hSubData⟩ := exists_subData hSub
  have hcompl_ne : (Γ.E \ E₁).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨g₀, hg₀⟩ := hne
    obtain ⟨v₀, _, hlk₀⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet (hE₁_Γ hg₀)
    let Q₀ : Graph S (Set S) := Graph.noEdge {v₀} (Set S)
    have hQ₀_path : IsGraphPathWithEnds Γ.toGraph Q₀ v₀ v₀ := by
      refine ⟨⟨singleton_subset_iff.mpr hlk₀.left_mem, fun _ _ _ h => h.elim⟩,
        .nil (mem_singleton v₀), List.nodup_singleton v₀, ?_, ?_⟩
      · ext z; exact mem_singleton_iff.trans List.mem_singleton.symm
      · ext g; exact iff_of_false id List.not_mem_nil
    have hbd_Q₀ : bdry Γ.toGraph E(Q₀) ⊆ {v₀, v₀} := fun _ ⟨⟨_, hg, _⟩, _⟩ => hg.elim
    have hord_BA : separationOrder (drawingEdgeSepB Γ E₁) (drawingEdgeSepA Γ E₁) < ord := by
      rw [GM10.separationOrder_comm, separationOrder, inter_vertexSet_drawingEdgeSep]
      omega
    have hB_in_T : (drawingEdgeSepB Γ E₁, drawingEdgeSepA Γ E₁) ∈ T :=
      path_sep_mem_tangle hT hord hQ₀_path hbd_Q₀ (isSeparation_drawingEdgeSep Γ E₁).symm hord_BA
        (by change Γ.E \ E₁ ⊆ E(Q₀); rw [hemp]; exact empty_subset _)
    exact tangle_not_both hT hA_in_T hB_in_T
  obtain ⟨_, x, y, Q, _, hxy, hbd_eq, _, hQ_path, hQ_cases⟩ :=
    SubDataSepGeneral.sep_general hSubData hE₁_Γ hc hne hcompl_ne
  have hE₁_eq : E₁ = E(Q) ∧ verts Γ.toGraph E₁ = V(Q) := by
    rcases hQ_cases with h1 | ⟨hcompl_eq, _⟩
    · exact h1
    · exfalso
      have hbd_Q : bdry Γ.toGraph E(Q) ⊆ {x, y} := by
        rw [← hcompl_eq, bdry_compl hE₁_Γ, hbd_eq]
      have hord_BA : separationOrder (drawingEdgeSepB Γ E₁) (drawingEdgeSepA Γ E₁) < ord := by
        rw [GM10.separationOrder_comm, separationOrder, inter_vertexSet_drawingEdgeSep]
        omega
      have hB_in_T : (drawingEdgeSepB Γ E₁, drawingEdgeSepA Γ E₁) ∈ T :=
        path_sep_mem_tangle hT hord hQ_path hbd_Q (isSeparation_drawingEdgeSep Γ E₁).symm hord_BA
          (subset_of_eq hcompl_eq)
      exact tangle_not_both hT hA_in_T hB_in_T
  have hQ_le_H : Q ≤ H.toGraph := by
    refine ⟨?_, fun e u v hlk => ?_⟩
    · rw [← hE₁_eq.2]
      exact (fun z ⟨e, he, hinc⟩ => hverts_H ⟨e, hE₁ he, hinc⟩)
    · have heQ : e ∈ E(Q) := hlk.edge_mem
      rw [← hE₁_eq.1] at heQ
      exact (hLink_H e u v).mpr ⟨hE₁ heQ, hlk.mono hQ_path.1⟩
  obtain ⟨_, W_Q, hs_Q, hVQ, hEQ⟩ := hQ_path
  exact ⟨x, y, Q, hxy, hbd_eq, ⟨hQ_le_H, W_Q, hs_Q, hVQ, hEQ⟩, hE₁_eq.1, hE₁_eq.2⟩

set_option maxHeartbeats 800000 in
/-- Verification of Condition `(J7)` for `𝒜' = {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}`
in the proof of Theorem 8.3 (page 562). -/
theorem conditionJ7_8_3
    {q δ h θ : ℕ}
    {ιV ιV' : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {D : Graph α β → Set S}
    (hιV'_Γ : ∀ v ∈ Γ.V, ιV' v = ιV v)
    (hπS_eq : ∀ A ∈ 𝒜, ∀ i : Fin (πLen A), ιV' (πS A i) = πA A i)
    (hπS_inj : ∀ A ∈ 𝒜, Function.Injective (πS A))
    (hD_disc : ∀ A ∈ 𝒜, IsClosedDisc (D A))
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = Set.range (πS A) ∩ Γ.V)
    (hD_inter_emb : ∀ A ∈ 𝒜,
      (Γ.interSet (D A)).toEmbeddedGraph ιV' ιE = (Γ.toEmbeddedGraph ιV' ιE) ⊓ A)
    (hins : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D A)) (D A)) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    ConditionJ7 ιV' ιE R_G.G.toGraph W 𝒜' πLen πS Γ T := by
  intro 𝒜'
  have hT : IsTangle Γ.toHypergraph ord T := h83.hyp_iv.2.1.1.2.1
  have hπBar_eq : ∀ A ∈ 𝒜, ιV' '' Set.range (πS A) = Z ∩ V(A) := by
    intro A hA
    rw [← (h83.hyp_vii A hA).2.2]
    ext x
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hπS_eq A hA i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨πS A i, ⟨i, rfl⟩, hπS_eq A hA i⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: `path_in_A`.
    intro A hA' u hu v hv
    rw [hπBar_eq A hA'.1] at hu hv ⊢
    exact h83.hyp_ix A hA'.1 u hu v hv
  · -- Part 2: `no_small_sep`.
    intro A hA' ⟨C, D_G, C_Γ, D_Γ, hsep, hlt, hle, hCV, hCE, hDV, hDE, hCD_T⟩
    have hpre_eq : ∀ X : Set α, ιV' ⁻¹' X ∩ Γ.V = ιV ⁻¹' X ∩ Γ.V := by
      intro X
      ext s
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_left fun hs => by rw [hιV'_Γ s hs]
    rw [hpre_eq] at hCV hDV
    exact lemma_8_3_claim_12 h83 hord A hA'
      ⟨C, D_G, C_Γ, D_Γ, hsep, hlt, hle, hCV, hCE, hDV, hDE, hCD_T⟩
  · -- Part 3: `structure_Γ_inter_A`.
    intro A hA'
    have hA : A ∈ 𝒜 := hA'.1
    let H := Γ.interSet (D A)
    let GA := (Γ.toEmbeddedGraph ιV' ιE) ⊓ A
    let πBar := ιV' '' Set.range (πS A)
    let S_A := Set.range (πS A) ∩ Γ.V
    have hGA_eq : H.toEmbeddedGraph ιV' ιE = GA := hD_inter_emb A hA
    obtain ⟨hle_H, hLink_H, hverts_H, hverts_out, hbd_sub, hiso_sub, _⟩ :=
      interSet_disc_graph_props h83.hyp_i.1 h83.hyp_i.2 hT hord
        (hD_disc A hA) (hD_norm A hA) (hins A hA)
    rw [hD_bdV A hA] at hverts_out hbd_sub hiso_sub
    have hπ_le3 : πLen A ≤ 3 := (h83.hyp_vii A hA).1
    have hrange_fin : (Set.range (πS A)).Finite := Set.finite_range (πS A)
    have hrange_card : (Set.range (πS A)).ncard = πLen A := by
      rw [Set.ncard_range_of_injective (hπS_inj A hA), Nat.card_fin]
    have hSA_sub_range : S_A ⊆ Set.range (πS A) := inter_subset_left
    have hSA_card_le : S_A.ncard ≤ πLen A :=
      hrange_card ▸ Set.ncard_le_ncard hSA_sub_range hrange_fin
    -- Case 1: `H.E = ∅`.
    by_cases hHE : H.E.Nonempty
    · -- Case 2: `H.E.Nonempty`.
      have hbd_card_le3 : (bdry Γ.toGraph H.E).ncard ≤ 3 :=
        (Set.ncard_le_ncard hbd_sub (hrange_fin.subset hSA_sub_range)).trans
          (hSA_card_le.trans hπ_le3)
      by_cases hbd_le2 : (bdry Γ.toGraph H.E).ncard ≤ 2
      · -- Subcase 2a: `(bdry Γ.toGraph H.E).ncard ≤ 2`.
        obtain ⟨x, y, Q, hxy, hbd_eq, hQ_path, hHE_eq, hverts_eq⟩ :=
          path_of_subset_interSet_E h83.hyp_i.1 h83.hyp_i.2 hT hord
            (hD_disc A hA) (hD_norm A hA) (hins A hA) Subset.rfl hHE hbd_le2
        have hx_bd : x ∈ bdry Γ.toGraph H.E := hbd_eq ▸ Or.inl rfl
        have hy_bd : y ∈ bdry Γ.toGraph H.E := hbd_eq ▸ Or.inr rfl
        have hx_SA : x ∈ S_A := hbd_sub hx_bd
        have hy_SA : y ∈ S_A := hbd_sub hy_bd
        have hx_VQ : x ∈ V(Q) := hverts_eq ▸ hx_bd.1
        have hy_VQ : y ∈ V(Q) := hverts_eq ▸ hy_bd.1
        have hx_π : ιV' x ∈ πBar := ⟨x, hx_SA.1, rfl⟩
        have hy_π : ιV' y ∈ πBar := ⟨y, hy_SA.1, rfl⟩
        by_cases hHV_eq : H.V = V(Q)
        · -- `H.toGraph = Q` is a path from `x` to `y` (`Alternative 2`).
          have hH_eq_Q : H.toGraph = Q :=
            (Compatible.of_le_le le_rfl hQ_path.1).ext hHV_eq hHE_eq
          have hH_path : IsGraphPathWithEnds H.toGraph H.toGraph x y :=
            hH_eq_Q.symm ▸ hQ_path
          right; left
          refine ⟨ιV' x, hx_π, ιV' y, hy_π, ?_⟩
          rw [← hD_inter_emb A hA]
          exact isGraphPathWithEnds_self_toEmbeddedGraph hH_path
        · -- `(H.V \ V(Q)).Nonempty`: single isolated vertex `z ∈ S_A \ {x, y}` (`Alternative 3`).
          have hne_diff : (H.V \ V(Q)).Nonempty := by
            by_contra hemp
            rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
            exact hHV_eq (Subset.antisymm hemp (hverts_eq ▸ hverts_H))
          obtain ⟨z, hzH, hz_not_Q⟩ := hne_diff
          have hz_SA : z ∈ S_A := hiso_sub ⟨hzH, hverts_eq.symm ▸ hz_not_Q⟩
          have hzx : z ≠ x := fun h => hz_not_Q (h ▸ hx_VQ)
          have hzy : z ≠ y := fun h => hz_not_Q (h ▸ hy_VQ)
          have hxyz_sub_SA : ({x, y, z} : Set S) ⊆ S_A := by
            rintro w (rfl | rfl | rfl)
            · exact hx_SA
            · exact hy_SA
            · exact hz_SA
          have hcard3_xyz : ({x, y, z} : Set S).ncard = 3 := by
            rw [Set.ncard_insert_of_notMem (by simp [hxy, hzx.symm]),
              Set.ncard_pair hzy.symm]
          have hSA_ge3 : 3 ≤ S_A.ncard :=
            hcard3_xyz ▸ Set.ncard_le_ncard hxyz_sub_SA (hrange_fin.subset hSA_sub_range)
          have hlen3 : πLen A = 3 := by omega
          have hSA_eq_xyz : S_A = {x, y, z} :=
            (Set.eq_of_subset_of_ncard_le hxyz_sub_SA (by omega)
              (hrange_fin.subset hSA_sub_range)).symm
          have hrange_eq_SA : Set.range (πS A) = S_A :=
            (Set.eq_of_subset_of_ncard_le hSA_sub_range (by omega) hrange_fin).symm
          have hrange_sub_ΓV : Set.range (πS A) ⊆ Γ.V :=
            hrange_eq_SA.symm ▸ inter_subset_right
          have hz_π : ιV' z ∈ πBar := ⟨z, hz_SA.1, rfl⟩
          -- `vertexValency GA (ιV' z) = 0`.
          have hval0 : vertexValency GA (ιV' z) = 0 := by
            have hno_inc : ∀ e w, ¬ GA.IsLink e (ιV' z) w := by
              intro e w hlk
              rw [← hGA_eq] at hlk
              rcases hlk with ⟨e₀, x₀, y₀, hlk₀, rfl, hx₀, rfl⟩
              obtain rfl : x₀ = z := ιV'.injective hx₀
              have hz_in : x₀ ∈ verts Γ.toGraph H.E :=
                ⟨e₀, hlk₀.1, y₀, hlk₀.mono hle_H⟩
              exact hz_not_Q (hverts_eq ▸ hz_in)
            unfold vertexValency
            have h1 : {e ∈ E(GA) | ∃ w ≠ ιV' z, GA.IsLink e (ιV' z) w} = ∅ := by
              ext e; simp only [mem_sep_iff, mem_empty_iff_false, iff_false, not_and]
              rintro _ ⟨w, _, hlk⟩; exact hno_inc e w hlk
            have h2 : {e ∈ E(GA) | GA.IsLink e (ιV' z) (ιV' z)} = ∅ := by
              ext e; simp only [mem_sep_iff, mem_empty_iff_false, iff_false, not_and]
              exact fun _ hlk => hno_inc e (ιV' z) hlk
            rw [h1, h2, Set.ncard_empty]
          -- `GA.deleteVerts {ιV' z}` is a path from `ιV' x` to `ιV' y`.
          have hHV_eq_union : H.V = V(Q) ∪ {z} := by
            refine Subset.antisymm (fun w hw => ?_)
              (union_subset (hverts_eq ▸ hverts_H) (singleton_subset_iff.mpr hzH))
            by_cases hwQ : w ∈ V(Q)
            · exact Or.inl hwQ
            · have hw_SA : w ∈ S_A := hiso_sub ⟨hw, hverts_eq.symm ▸ hwQ⟩
              rw [hSA_eq_xyz] at hw_SA
              rcases hw_SA with rfl | rfl | rfl
              · exact (hwQ hx_VQ).elim
              · exact (hwQ hy_VQ).elim
              · exact Or.inr rfl
          obtain ⟨hQ_le, W_Q, hs_Q, hVQ, hEQ⟩ := hQ_path
          obtain ⟨W_QH, hsupp_QH, hedges_QH⟩ := W_Q.exists_transfer (G' := H.toGraph)
            (fun _ _ _ _ hlk => hlk.mono hQ_le)
            (fun w hw => hQ_le.vertexSet_mono (W_Q.mem_vertexSet_of_mem_support hw))
          obtain ⟨W_emb, hsupp_emb, hedges_emb⟩ :=
            exists_walk_toEmbeddedGraph_of_toGraph (ιV := ιV') (ιE := ιE) W_QH
          rw [hsupp_QH] at hsupp_emb
          rw [hedges_QH] at hedges_emb
          have hW_emb_GA : ∀ w ∈ W_emb.support, w ∈ V(GA.deleteVerts {ιV' z}) := by
            intro w hw
            rw [hsupp_emb, List.mem_map] at hw
            obtain ⟨s, hs, rfl⟩ := hw
            have hsQ : s ∈ V(Q) := by rwa [hVQ]
            have hsH : s ∈ H.V := (hverts_eq ▸ hverts_H) hsQ
            have hsz : s ≠ z := fun h => hz_not_Q (h ▸ hsQ)
            rw [Graph.vertexSet_deleteVerts, ← hGA_eq]
            exact ⟨⟨s, hsH, rfl⟩, fun h => hsz (ιV'.injective h)⟩
          have hlink_del : ∀ e u v, e ∈ W_emb.edges →
              (H.toEmbeddedGraph ιV' ιE).IsLink e u v →
              (GA.deleteVerts {ιV' z}).IsLink e u v := by
            intro e u v _ hlk
            rcases hlk with ⟨e₀, u₀, v₀, hlk₀, rfl, rfl, rfl⟩
            have hu₀_VQ : u₀ ∈ V(Q) :=
              hverts_eq ▸ ⟨e₀, hlk₀.1, v₀, hlk₀.mono hle_H⟩
            have hv₀_VQ : v₀ ∈ V(Q) :=
              hverts_eq ▸ ⟨e₀, hlk₀.1, u₀, hlk₀.symm.mono hle_H⟩
            have hu₀_ne : u₀ ≠ z := fun h => hz_not_Q (h ▸ hu₀_VQ)
            have hv₀_ne : v₀ ≠ z := fun h => hz_not_Q (h ▸ hv₀_VQ)
            rw [Graph.deleteVerts_isLink, ← hGA_eq]
            exact ⟨⟨e₀, u₀, v₀, hlk₀, rfl, rfl, rfl⟩,
              fun h => hu₀_ne (ιV'.injective h), fun h => hv₀_ne (ιV'.injective h)⟩
          obtain ⟨W_del, hsupp_del, hedges_del⟩ :=
            W_emb.exists_transfer (G' := GA.deleteVerts {ιV' z}) hlink_del hW_emb_GA
          have hs_del : W_del.IsSimple := by
            change W_del.support.Nodup
            rw [hsupp_del, hsupp_emb]
            exact hs_Q.map ιV'.injective
          have hpath_del : IsGraphPathWithEnds (GA.deleteVerts {ιV' z})
              (GA.deleteVerts {ιV' z}) (ιV' x) (ιV' y) := by
            refine ⟨le_rfl, W_del, hs_del, ?_, ?_⟩
            · ext w
              change w ∈ V(GA.deleteVerts {ιV' z}) ↔ w ∈ W_del.support
              rw [hsupp_del, hsupp_emb, Graph.vertexSet_deleteVerts, ← hGA_eq]
              simp only [Drawing.toEmbeddedGraph, mem_image, List.mem_map, mem_sdiff,
                mem_singleton_iff]
              constructor
              · rintro ⟨⟨s, hsH, rfl⟩, hne_z⟩
                have hs_ne : s ≠ z := fun h => hne_z (congrArg ιV' h)
                have hsQ : s ∈ V(Q) := (hHV_eq_union ▸ hsH).resolve_right hs_ne
                rw [hVQ] at hsQ
                exact ⟨s, hsQ, rfl⟩
              · rintro ⟨s, hsW, rfl⟩
                have hsQ : s ∈ V(Q) := by rwa [hVQ]
                exact ⟨⟨s, (hverts_eq ▸ hverts_H) hsQ, rfl⟩,
                  fun h => hz_not_Q (ιV'.injective h ▸ hsQ)⟩
            · ext e
              change e ∈ E(GA.deleteVerts {ιV' z}) ↔ e ∈ W_del.edges
              rw [hedges_del, hedges_emb]
              simp only [List.mem_map]
              constructor
              · intro he_del
                have he_GA : e ∈ E(H.toEmbeddedGraph ιV' ιE) :=
                  hGA_eq.symm ▸ Graph.deleteVerts_le.edgeSet_mono he_del
                obtain ⟨e₀, he₀H, rfl⟩ := he_GA
                have he₀Q : e₀ ∈ W_Q.edges := by
                  have he₀_EQ : e₀ ∈ E(Q) := hHE_eq ▸ he₀H
                  rwa [hEQ] at he₀_EQ
                exact ⟨e₀, he₀Q, rfl⟩
              · rintro ⟨e₀, he₀W, rfl⟩
                have he₀Q : e₀ ∈ E(Q) := by rwa [hEQ]
                obtain ⟨u₀, v₀, hlk₀⟩ := Q.exists_isLink_of_mem_edgeSet he₀Q
                have hlkH : H.toGraph.IsLink e₀ u₀ v₀ := hlk₀.mono hQ_le
                have hu₀_ne : u₀ ≠ z := fun h => hz_not_Q (h ▸ hlk₀.left_mem)
                have hv₀_ne : v₀ ≠ z := fun h => hz_not_Q (h ▸ hlk₀.right_mem)
                have hlk_del' : (GA.deleteVerts {ιV' z}).IsLink (ιE e₀) (ιV' u₀) (ιV' v₀) := by
                  rw [Graph.deleteVerts_isLink, ← hGA_eq]
                  exact ⟨⟨e₀, u₀, v₀, hlkH, rfl, rfl, rfl⟩,
                    fun h => hu₀_ne (ιV'.injective h), fun h => hv₀_ne (ιV'.injective h)⟩
                exact hlk_del'.edge_mem
          right; right; left
          exact ⟨hlen3, hrange_sub_ΓV, ιV' z, hz_π, hval0,
            ιV' x, ⟨hx_π, fun h => hzx.symm (ιV'.injective h)⟩,
            ιV' y, ⟨hy_π, fun h => hzy.symm (ιV'.injective h)⟩, hpath_del⟩
      · -- Subcase 2b: `(bdry Γ.toGraph H.E).ncard = 3`.
        have hbd_card3 : (bdry Γ.toGraph H.E).ncard = 3 := by omega
        have hbd_le_SA : (bdry Γ.toGraph H.E).ncard ≤ S_A.ncard :=
          Set.ncard_le_ncard hbd_sub (hrange_fin.subset hSA_sub_range)
        have hlen3 : πLen A = 3 := by omega
        have hSA_card3 : S_A.ncard = 3 := by omega
        have hbd_eq_SA : bdry Γ.toGraph H.E = S_A :=
          Set.eq_of_subset_of_ncard_le hbd_sub (by omega) (hrange_fin.subset hSA_sub_range)
        have hSA_eq_range : S_A = Set.range (πS A) :=
          Set.eq_of_subset_of_ncard_le hSA_sub_range (by omega) hrange_fin
        have hrange_sub_ΓV : Set.range (πS A) ⊆ Γ.V :=
          hSA_eq_range ▸ inter_subset_right
        have hHV_eq_verts : H.V = verts Γ.toGraph H.E := by
          refine Subset.antisymm (fun w hw => ?_) hverts_H
          by_contra hw_not
          have hw_SA : w ∈ S_A := hiso_sub ⟨hw, hw_not⟩
          rw [← hbd_eq_SA] at hw_SA
          exact hw_not hw_SA.1
        by_cases hGood : IsGoodMember ιV' ιE Γ πLen πS A
        · right; right; right
          exact ⟨hlen3, hGood⟩
        · -- If `¬ IsGoodMember`, then some pair `s₁, s₂ ∈ S_A` has no walk in
          -- `H.toGraph.deleteVerts {s₃}` avoiding the third vertex `s₃ ∈ S_A`.
          have hex_no_walk : ∃ s₁ s₂ s₃ : S,
              s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ ∧
              S_A = {s₁, s₂, s₃} ∧
              ¬ Nonempty (GraphWalk (H.toGraph.deleteVerts {s₃}) s₁ s₂) := by
            by_contra! hall_walk
            apply hGood
            refine ⟨hrange_sub_ΓV, ?_⟩
            rintro u ⟨s₁, hs₁_π, rfl⟩ v ⟨s₂, hs₂_π, rfl⟩
            have hs₁_SA : s₁ ∈ S_A := hSA_eq_range.symm ▸ hs₁_π
            have hs₂_SA : s₂ ∈ S_A := hSA_eq_range.symm ▸ hs₂_π
            have hs₁_HV : s₁ ∈ H.V := hverts_H (hbd_eq_SA.symm ▸ hs₁_SA).1
            by_cases hs₁₂ : s₁ = s₂
            · subst hs₁₂
              have hs₁_GA : ιV' s₁ ∈ V(GA) := by
                rw [← hGA_eq]
                exact ⟨s₁, hs₁_HV, rfl⟩
              obtain ⟨P₀, hP₀, hP₀_int⟩ := exists_trivial_path_self hs₁_GA
              exact ⟨P₀, hP₀, by rw [hP₀_int]; exact Set.empty_disjoint _⟩
            · obtain ⟨s₃, hs₁₃, hs₂₃, hrange_triple⟩ :=
                range_πS_eq_triple_of_len_three hlen3 (hπS_inj A hA) hs₁_π hs₂_π hs₁₂
              have hSA_triple : S_A = {s₁, s₂, s₃} := hSA_eq_range.trans hrange_triple
              obtain ⟨W_del⟩ := hall_walk s₁ s₂ s₃ hs₁₂ hs₁₃ hs₂₃ hSA_triple
              obtain ⟨W_s, hs_s, _, _⟩ := GM09.exists_isSimple_subwalk W_del
              have hdel_le_H : H.toGraph.deleteVerts {s₃} ≤ H.toGraph := Graph.deleteVerts_le
              obtain ⟨W_H, hsupp_H, _⟩ := W_s.exists_transfer (G' := H.toGraph)
                (fun _ _ _ _ hlk => hlk.mono hdel_le_H)
                (fun z hz => hdel_le_H.vertexSet_mono (W_s.mem_vertexSet_of_mem_support hz))
              obtain ⟨W_emb, hsupp_emb, hedges_emb⟩ :=
                exists_walk_toEmbeddedGraph_of_toGraph (ιV := ιV') (ιE := ιE) W_H
              have hs_emb : W_emb.IsSimple := by
                change W_emb.support.Nodup
                rw [hsupp_emb, hsupp_H]
                exact hs_s.map ιV'.injective
              let P_emb := walkSubgraph W_emb
              have hP_emb : IsGraphPathWithEnds GA P_emb (ιV' s₁) (ιV' s₂) := by
                rw [← hGA_eq]
                exact isGraphPathWithEnds_walkSubgraph hs_emb
              refine ⟨P_emb, hP_emb, ?_⟩
              rw [Set.disjoint_left]
              rintro w hw_int ⟨s, hs_π, rfl⟩
              have hw_diff : ιV' s ∈ V(P_emb) \ {ιV' s₁, ιV' s₂} :=
                IsGraphPathWithEnds.pathInternalVerts_subset hP_emb hw_int
              have hs_in_triple : s ∈ ({s₁, s₂, s₃} : Set S) := hrange_triple ▸ hs_π
              rcases hs_in_triple with rfl | rfl | rfl
              · exact hw_diff.2 (Or.inl rfl)
              · exact hw_diff.2 (Or.inr rfl)
              · have hs₃_supp : ιV' s ∈ W_emb.support := by
                  have := hw_diff.1
                  rwa [vertexSet_walkSubgraph, mem_ofPred_eq] at this
                rw [hsupp_emb, hsupp_H, List.mem_map_of_injective ιV'.injective] at hs₃_supp
                have hs₃_del : s ∈ V(H.toGraph.deleteVerts {s}) :=
                  W_s.mem_vertexSet_of_mem_support hs₃_supp
                rw [Graph.vertexSet_deleteVerts] at hs₃_del
                exact hs₃_del.2 rfl
          obtain ⟨s₁, s₂, s₃, hs₁₂, hs₁₃, hs₂₃, hSA_triple, hno_walk⟩ := hex_no_walk
          have hs₁_bd : s₁ ∈ bdry Γ.toGraph H.E := hbd_eq_SA.symm ▸ hSA_triple.symm ▸ Or.inl rfl
          have hs₂_bd : s₂ ∈ bdry Γ.toGraph H.E :=
            hbd_eq_SA.symm ▸ hSA_triple.symm ▸ Or.inr (Or.inl rfl)
          have hs₃_bd : s₃ ∈ bdry Γ.toGraph H.E :=
            hbd_eq_SA.symm ▸ hSA_triple.symm ▸ Or.inr (Or.inr rfl)
          have hs₁_HV : s₁ ∈ H.V := hverts_H hs₁_bd.1
          have hs₂_HV : s₂ ∈ H.V := hverts_H hs₂_bd.1
          have hs₃_HV : s₃ ∈ H.V := hverts_H hs₃_bd.1
          -- Partition `H.E` into `E₁` (edges meeting the `s₁`-component of `H \ {s₃}`) and `E₂`.
          let V₁ : Set S :=
            {w ∈ H.V \ {s₃} | Nonempty (GraphWalk (H.toGraph.deleteVerts {s₃}) s₁ w)}
          let E₁ : Set (Set S) := {e ∈ H.E | ∃ w ∈ V₁, H.toGraph.Inc e w}
          let E₂ : Set (Set S) := H.E \ E₁
          have hs₁_V₁ : s₁ ∈ V₁ := by
            refine ⟨⟨hs₁_HV, hs₁₃⟩, ⟨.nil ?_⟩⟩
            rw [Graph.vertexSet_deleteVerts]
            exact ⟨hs₁_HV, hs₁₃⟩
          have hs₂_not_V₁ : s₂ ∉ V₁ := fun h => hno_walk h.2
          have hs₃_not_V₁ : s₃ ∉ V₁ := fun h => h.1.2 rfl
          have hlink_V₁ : ∀ {e x y}, H.toGraph.IsLink e x y → x ∈ V₁ → y ≠ s₃ → y ∈ V₁ := by
            intro e x y hlk hx hy₃
            obtain ⟨⟨hxH, hx₃⟩, ⟨W_x⟩⟩ := hx
            have hlk_del : (H.toGraph.deleteVerts {s₃}).IsLink e x y := by
              rw [Graph.deleteVerts_isLink]
              exact ⟨hlk, hx₃, hy₃⟩
            exact ⟨⟨hlk.right_mem, hy₃⟩, ⟨W_x.append (.cons hlk_del (.nil hlk_del.right_mem))⟩⟩
          have hverts_E₁ : verts Γ.toGraph E₁ ⊆ V₁ ∪ {s₃} := by
            rintro x ⟨e, ⟨heH, w, hwV₁, y₀, hlk_wy₀⟩, y, hlk_xy⟩
            have hlk_H_xy : H.toGraph.IsLink e x y := (hLink_H e x y).mpr ⟨heH, hlk_xy⟩
            by_cases hxs₃ : x = s₃
            · exact Or.inr hxs₃
            · left
              rcases H.toGraph.eq_or_eq_of_isLink_of_isLink hlk_wy₀ hlk_H_xy with rfl | rfl
              · exact hwV₁
              · exact hlink_V₁ hlk_H_xy.symm hwV₁ hxs₃
          have hverts_E₂ : verts Γ.toGraph E₂ ⊆ H.V \ V₁ := by
            rintro x ⟨e, ⟨heH, he_not_E₁⟩, y, hlk_xy⟩
            have hlk_H : H.toGraph.IsLink e x y := (hLink_H e x y).mpr ⟨heH, hlk_xy⟩
            exact ⟨hlk_H.left_mem, fun hxV₁ => he_not_E₁ ⟨heH, x, hxV₁, y, hlk_H⟩⟩
          have hbd_E₁_sub : bdry Γ.toGraph E₁ ⊆ {s₁, s₃} := by
            rintro x ⟨hx_in, g, ⟨hgE, hg_not_E₁⟩, y, hlk_g⟩
            have hx_V₁_s₃ : x ∈ V₁ ∪ {s₃} := hverts_E₁ hx_in
            by_cases hgH : g ∈ H.E
            · have hx_E₂ : x ∈ verts Γ.toGraph E₂ := ⟨g, ⟨hgH, hg_not_E₁⟩, y, hlk_g⟩
              have hx_not_V₁ : x ∉ V₁ := (hverts_E₂ hx_E₂).2
              exact Or.inr (hx_V₁_s₃.resolve_left hx_not_V₁)
            · have hx_HV : x ∈ H.V := by
                rcases hx_in with ⟨e₀, he₀, y₀, hlk₀⟩
                exact hverts_H ⟨e₀, he₀.1, y₀, hlk₀⟩
              have hx_SA : x ∈ S_A := hverts_out ⟨hx_HV, g, ⟨hgE, hgH⟩, y, hlk_g⟩
              rw [hSA_triple] at hx_SA
              rcases hx_SA with rfl | rfl | rfl
              · exact Or.inl rfl
              · exact (hs₂_not_V₁ (hx_V₁_s₃.resolve_right hs₂₃)).elim
              · exact Or.inr rfl
          have hbd_E₂_sub : bdry Γ.toGraph E₂ ⊆ {s₂, s₃} := by
            rintro x ⟨hx_in, g, ⟨hgE, hg_not_E₂⟩, y, hlk_g⟩
            have hx_not_V₁ : x ∈ H.V \ V₁ := hverts_E₂ hx_in
            by_cases hgH : g ∈ H.E
            · have hgE₁ : g ∈ E₁ := by
                by_contra hnot
                exact hg_not_E₂ ⟨hgH, hnot⟩
              have hx_E₁ : x ∈ verts Γ.toGraph E₁ := ⟨g, hgE₁, y, hlk_g⟩
              exact Or.inr ((hverts_E₁ hx_E₁).resolve_left hx_not_V₁.2)
            · have hx_SA : x ∈ S_A := hverts_out ⟨hx_not_V₁.1, g, ⟨hgE, hgH⟩, y, hlk_g⟩
              rw [hSA_triple] at hx_SA
              rcases hx_SA with rfl | rfl | rfl
              · exact (hx_not_V₁.2 hs₁_V₁).elim
              · exact Or.inl rfl
              · exact Or.inr rfl
          have hE₁_ne : E₁.Nonempty := by
            obtain ⟨e₁, he₁H, y₁, hlk₁⟩ := hs₁_bd.1
            have hlk₁_H : H.toGraph.IsLink e₁ s₁ y₁ := (hLink_H e₁ s₁ y₁).mpr ⟨he₁H, hlk₁⟩
            exact ⟨e₁, he₁H, s₁, hs₁_V₁, y₁, hlk₁_H⟩
          have hE₂_ne : E₂.Nonempty := by
            obtain ⟨e₂, he₂H, y₂, hlk₂⟩ := hs₂_bd.1
            have he₂_not_E₁ : e₂ ∉ E₁ := by
              intro he₂_1
              have hs₂_in : s₂ ∈ verts Γ.toGraph E₁ := ⟨e₂, he₂_1, y₂, hlk₂⟩
              rcases hverts_E₁ hs₂_in with hs₂_1 | hs₂_3
              · exact hs₂_not_V₁ hs₂_1
              · exact hs₂₃ hs₂_3
            exact ⟨e₂, he₂H, he₂_not_E₁⟩
          have hc₁ : (bdry Γ.toGraph E₁).ncard ≤ 2 :=
            (Set.ncard_le_ncard hbd_E₁_sub (Set.toFinite _)).trans (Set.ncard_pair hs₁₃).le
          have hc₂ : (bdry Γ.toGraph E₂).ncard ≤ 2 :=
            (Set.ncard_le_ncard hbd_E₂_sub (Set.toFinite _)).trans (Set.ncard_pair hs₂₃).le
          obtain ⟨x₁, y₁, Q₁, hxy₁, hbd₁_eq, hQ₁_path, hE₁_eq, hverts₁_eq⟩ :=
            path_of_subset_interSet_E h83.hyp_i.1 h83.hyp_i.2 hT hord
              (hD_disc A hA) (hD_norm A hA) (hins A hA) (fun _ h => h.1) hE₁_ne hc₁
          obtain ⟨x₂, y₂, Q₂, hxy₂, hbd₂_eq, hQ₂_path, hE₂_eq, hverts₂_eq⟩ :=
            path_of_subset_interSet_E h83.hyp_i.1 h83.hyp_i.2 hT hord
              (hD_disc A hA) (hD_norm A hA) (hins A hA) sdiff_subset hE₂_ne hc₂
          have hbd₁_pair : bdry Γ.toGraph E₁ = {s₁, s₃} :=
            Set.eq_of_subset_of_ncard_le hbd_E₁_sub
              (by rw [hbd₁_eq, Set.ncard_pair hxy₁, Set.ncard_pair hs₁₃])
              (Set.toFinite _)
          have hbd₂_pair : bdry Γ.toGraph E₂ = {s₂, s₃} :=
            Set.eq_of_subset_of_ncard_le hbd_E₂_sub
              (by rw [hbd₂_eq, Set.ncard_pair hxy₂, Set.ncard_pair hs₂₃])
              (Set.toFinite _)
          have hQ₁_ends : IsGraphPathWithEnds H.toGraph Q₁ s₁ s₃ := by
            have hs₁_in : s₁ ∈ ({x₁, y₁} : Set S) := hbd₁_eq ▸ hbd₁_pair ▸ Or.inl rfl
            have hs₃_in : s₃ ∈ ({x₁, y₁} : Set S) := hbd₁_eq ▸ hbd₁_pair ▸ Or.inr rfl
            rcases hs₁_in with rfl | rfl <;> rcases hs₃_in with rfl | rfl
            · exact (hs₁₃ rfl).elim
            · exact hQ₁_path
            · exact hQ₁_path.symm
            · exact (hs₁₃ rfl).elim
          have hQ₂_ends : IsGraphPathWithEnds H.toGraph Q₂ s₃ s₂ := by
            have hs₂_in : s₂ ∈ ({x₂, y₂} : Set S) := hbd₂_eq ▸ hbd₂_pair ▸ Or.inl rfl
            have hs₃_in : s₃ ∈ ({x₂, y₂} : Set S) := hbd₂_eq ▸ hbd₂_pair ▸ Or.inr rfl
            rcases hs₃_in with rfl | rfl <;> rcases hs₂_in with rfl | rfl
            · exact (hs₂₃ rfl).elim
            · exact hQ₂_path
            · exact hQ₂_path.symm
            · exact (hs₂₃ rfl).elim
          -- Concatenate `Q₁` and `Q₂` at `s₃` to show `H.toGraph` is a path from `s₁` to `s₂`.
          obtain ⟨hQ₁_le, W₁, hs₁_W, hVQ₁, hEQ₁⟩ := hQ₁_ends
          obtain ⟨hQ₂_le, W₂, hs₂_W, hVQ₂, hEQ₂⟩ := hQ₂_ends
          obtain ⟨W₁H, hsupp₁, hedges₁⟩ := W₁.exists_transfer (G' := H.toGraph)
            (fun _ _ _ _ hlk => hlk.mono hQ₁_le)
            (fun z hz => hQ₁_le.vertexSet_mono (W₁.mem_vertexSet_of_mem_support hz))
          obtain ⟨W₂H, hsupp₂, hedges₂⟩ := W₂.exists_transfer (G' := H.toGraph)
            (fun _ _ _ _ hlk => hlk.mono hQ₂_le)
            (fun z hz => hQ₂_le.vertexSet_mono (W₂.mem_vertexSet_of_mem_support hz))
          let W_full := W₁H.append W₂H
          have hs_full : W_full.IsSimple := by
            change (W₁H.append W₂H).support.Nodup
            have hs₁_WH : W₁H.support.Nodup := hsupp₁ ▸ hs₁_W
            have hs₂_WH : W₂H.support.Nodup := hsupp₂ ▸ hs₂_W
            rw [GraphWalk.support_append, List.nodup_append]
            refine ⟨hs₁_WH, hs₂_WH.sublist (List.tail_sublist _), ?_⟩
            intro z hz₁ _ hz₂ rfl
            have hz_VQ₁ : z ∈ V(Q₁) := by rw [hVQ₁, mem_ofPred_eq, ← hsupp₁]; exact hz₁
            have hz_W₂ : z ∈ W₂.support.tail := by rwa [← hsupp₂]
            have hz_ne_s₃ : z ≠ s₃ := by
              have hnd₂ : W₂.support.Nodup := hs₂_W
              rw [W₂.support_eq_cons, List.nodup_cons] at hnd₂
              exact fun h => hnd₂.1 (h ▸ hz_W₂)
            have hz_VQ₂ : z ∈ V(Q₂) := by
              rw [hVQ₂]
              exact List.mem_of_mem_tail hz_W₂
            have hz_V₁ : z ∈ V₁ :=
              (hverts_E₁ (hverts₁_eq.symm ▸ hz_VQ₁)).resolve_right hz_ne_s₃
            exact (hverts_E₂ (hverts₂_eq.symm ▸ hz_VQ₂)).2 hz_V₁
          change E₂ = E(Q₂) at hE₂_eq
          change verts Γ.toGraph E₂ = V(Q₂) at hverts₂_eq
          have hHE_union : H.E = E₁ ∪ E₂ := by
            ext e
            simp only [E₂, mem_union, mem_sdiff]
            exact ⟨fun h => by by_cases h1 : e ∈ E₁; exact Or.inl h1; exact Or.inr ⟨h, h1⟩,
              fun h => h.elim (fun h1 => h1.1) (fun h2 => h2.1)⟩
          have hHV_union : H.V = V(Q₁) ∪ V(Q₂) := by
            rw [hHV_eq_verts, ← hverts₁_eq, ← hverts₂_eq, hHE_union]
            ext z
            simp only [verts, mem_union, mem_ofPred_eq]
            exact ⟨fun ⟨e, he, hinc⟩ => he.elim (fun h1 => Or.inl ⟨e, h1, hinc⟩)
              (fun h2 => Or.inr ⟨e, h2, hinc⟩),
              fun h => h.elim (fun ⟨e, h1, hinc⟩ => ⟨e, Or.inl h1, hinc⟩)
                (fun ⟨e, h2, hinc⟩ => ⟨e, Or.inr h2, hinc⟩)⟩
          have hH_path : IsGraphPathWithEnds H.toGraph H.toGraph s₁ s₂ := by
            refine ⟨le_rfl, W_full, hs_full, ?_, ?_⟩
            · change H.V = {x | x ∈ W_full.support}
              rw [hHV_union, hVQ₁, hVQ₂]
              ext z
              simp only [W_full, mem_union, mem_ofPred_eq, GraphWalk.mem_support_append,
                hsupp₁, hsupp₂]
            · change H.E = {e | e ∈ W_full.edges}
              rw [hHE_union, hE₁_eq, hE₂_eq, hEQ₁, hEQ₂]
              ext e
              simp only [W_full, mem_union, mem_ofPred_eq, GraphWalk.edges_append,
                List.mem_append, hedges₁, hedges₂]
          right; left
          refine ⟨ιV' s₁, ⟨s₁, hs₁_bd |> hbd_sub |> hSA_sub_range, rfl⟩,
            ιV' s₂, ⟨s₂, hs₂_bd |> hbd_sub |> hSA_sub_range, rfl⟩, ?_⟩
          rw [← hD_inter_emb A hA]
          exact isGraphPathWithEnds_self_toEmbeddedGraph hH_path
    · -- Case 1 (`H.E = ∅`): `V(GA) ⊆ πBar ∧ E(GA) = ∅`.
      rw [Set.not_nonempty_iff_eq_empty] at hHE
      have hverts_emp : verts Γ.toGraph H.E = ∅ := by
        rw [hHE]
        ext z; simp [verts]
      have hHV_sub_SA : H.V ⊆ S_A := by
        have := hiso_sub
        rwa [hverts_emp, sdiff_empty] at this
      left
      rw [← hD_inter_emb A hA]
      refine ⟨?_, ?_⟩
      · rintro _ ⟨s, hsH, rfl⟩
        exact ⟨s, hSA_sub_range (hHV_sub_SA hsH), rfl⟩
      · change ιE '' H.E = ∅
        rw [hHE, image_empty]

end GraphMinor.GM22
