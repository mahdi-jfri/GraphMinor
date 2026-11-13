module

public import GraphMinor.GM22.Section7d3

/-!
# Graph Minors XXII – Section 7.4 (Part 4): Claim (9)

This file formalizes **Claim (9)** of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 555–556):

- `uncross_ncard_identity`: four-set cardinality identity for uncrossing separations.
- `subHypergraphOfSubgraph` and `embSubgraph`: correspondence between subgraphs of $G$ and
  subhypergraphs of $\Gamma.\text{toHypergraph}$.
- `not_both_boundary_diff_gt_of_isGoodMember`: path-in-$\Gamma \cap A$ uncrossing bound for a good
  member $A \in \mathcal{A}$.
- `lemma_7_4_claim_9`: Claim (9) of (7.4) (pages 555–556).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Uncrossing Cardinality Identity and Tangle Monotonicity Helpers -/

omit [TopologicalSpace S] [T2Space S] in
/-- For any four sets `VA, VB, VC, VD` with `(VC ∩ VD).Finite`, `(VA ∩ VB).Finite`, and
`VA ∩ VB ⊆ VC ∪ VD`, we have
`((VA ∪ VC) ∩ (VB ∩ VD)).ncard + ((VC ∩ VD) \ VB).ncard = (VC ∩ VD).ncard + ((VA ∩ VB) \ VC).ncard`. -/
theorem uncross_ncard_identity {X : Type*} {VA VB VC VD : Set X}
    (hFin_CD : (VC ∩ VD).Finite) (hFin_AB : (VA ∩ VB).Finite)
    (hAB_sub : VA ∩ VB ⊆ VC ∪ VD) :
    ((VA ∪ VC) ∩ (VB ∩ VD)).ncard + ((VC ∩ VD) \ VB).ncard =
      (VC ∩ VD).ncard + ((VA ∩ VB) \ VC).ncard := by
  let I := VB ∩ (VC ∩ VD)
  let R₁ := (VA ∩ VB) \ VC
  let R₂ := (VC ∩ VD) \ VB
  have hI_fin : I.Finite := hFin_CD.subset inter_subset_right
  have hR₁_fin : R₁.Finite := hFin_AB.subset sdiff_subset
  have hR₂_fin : R₂.Finite := hFin_CD.subset sdiff_subset
  have h1_eq : (VA ∪ VC) ∩ (VB ∩ VD) = I ∪ R₁ := by
    ext x
    simp only [I, R₁, mem_inter_iff, mem_union, mem_sdiff]
    have hx_sub : x ∈ VA ∧ x ∈ VB → x ∈ VC ∨ x ∈ VD := fun h => hAB_sub h
    tauto
  have h2_eq : VC ∩ VD = I ∪ R₂ := by
    ext x
    simp only [I, R₂, mem_inter_iff, mem_union, mem_sdiff]
    tauto
  have hdisj₁ : Disjoint I R₁ := by
    rw [Set.disjoint_left]
    exact fun _ hxI hxR₁ => hxR₁.2 hxI.2.1
  have hdisj₂ : Disjoint I R₂ := by
    rw [Set.disjoint_left]
    exact fun _ hxI hxR₂ => hxR₂.2 hxI.1
  have h1_card : ((VA ∪ VC) ∩ (VB ∩ VD)).ncard = I.ncard + R₁.ncard := by
    rw [h1_eq, Set.ncard_union_eq hdisj₁ hI_fin hR₁_fin]
  have h2_card : (VC ∩ VD).ncard = I.ncard + R₂.ncard := by
    rw [h2_eq, Set.ncard_union_eq hdisj₂ hI_fin hR₂_fin]
  change ((VA ∪ VC) ∩ (VB ∩ VD)).ncard + R₂.ncard = (VC ∩ VD).ncard + R₁.ncard
  omega

omit [TopologicalSpace S] [T2Space S] in
/-- Helper: `H₁ ≤ H₂ ∩ H₃` when `H₁, H₂, H₃ ≤ G` and `H₁ ≤ H₂`, `H₁ ≤ H₃`. -/
theorem le_inter_of_le {X Y : Type*} {G H₁ H₂ H₃ : Hypergraph X Y}
    (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (h₃ : H₃ ≤ G) (hle₂ : H₁ ≤ H₂) (hle₃ : H₁ ≤ H₃) :
    H₁ ≤ H₂ ∩ H₃ :=
  (GM10.le_iff_of_le h₁ (GM10.inter_le h₂ h₃)).mpr
    ⟨subset_inter hle₂.vertexSet_subset hle₃.vertexSet_subset,
     subset_inter hle₂.edgeSet_subset hle₃.edgeSet_subset⟩

omit [TopologicalSpace S] [T2Space S] in
/-- If `(C, D) ∈ 𝒯` in a tangle `𝒯` of order `ord` in `H`, and `(C', D')` is a separation of `H` of
order `< ord` with `D ≤ D'`, then `(C', D') ∈ 𝒯`. -/
theorem mem_tangle_of_right_le {X Y : Type*} {H : Hypergraph X Y} {ord : ℕ}
    {𝒯 : Set (Hypergraph X Y × Hypergraph X Y)} (h𝒯 : IsTangle H ord 𝒯)
    {C D C' D' : Hypergraph X Y} (hCD : (C, D) ∈ 𝒯)
    (hsep' : H.IsSeparation C' D') (hord' : separationOrder C' D' < ord)
    (hD_le : D ≤ D') :
    (C', D') ∈ 𝒯 := by
  rcases h𝒯.axiom1 hsep' hord' with h | h
  · exact h
  · exfalso
    have hsep := h𝒯.isSeparation hCD
    refine h𝒯.axiom2 hCD h h ?_
    have hle1 : C ∪ D' ∪ D' ≤ H :=
      GM10.union_le (GM10.union_le hsep.left_le hsep'.right_le) hsep'.right_le
    have hle2 : H ≤ C ∪ D' ∪ D' := by
      rw [GM10.le_iff_of_le le_rfl hle1, ← hsep.vertexSet_union, ← hsep.edgeSet_union]
      exact ⟨union_subset (subset_union_left.trans subset_union_left)
          (hD_le.vertexSet_subset.trans (subset_union_right.trans subset_union_left)),
        union_subset (subset_union_left.trans subset_union_left)
          (hD_le.edgeSet_subset.trans (subset_union_right.trans subset_union_left))⟩
    exact le_antisymm hle1 hle2

/-! ## 2. Subhypergraphs Induced by Subgraphs of $G$ -/

omit [T2Space S] in
/-- For a drawing `Γ` embedded in `G` via `ιV, ιE` (with `Γ.toEmbeddedGraph ιV ιE ≤ G`), any
subgraph `M ≤ G` induces a subhypergraph of `Γ.toHypergraph` with vertex set `ιV ⁻¹' V(M) ∩ Γ.V`
and edge set `ιE ⁻¹' E(M) ∩ Γ.E`. -/
def subHypergraphOfSubgraph (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G)
    (M : Graph α β) (hM : M ≤ G) : Hypergraph S (Set S) where
  vertexSet := ιV ⁻¹' V(M) ∩ Γ.V
  edgeSet := ιE ⁻¹' E(M) ∩ Γ.E
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∈ ιE ⁻¹' E(M)
  vertex_mem_of_inc := by
    rintro e v ⟨⟨heΓ, hvΓ, hv_cl⟩, heM⟩
    refine ⟨?_, hvΓ⟩
    obtain ⟨x₀, y₀, hl₀⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet heΓ
    have hv_pair : v ∈ ({x₀, y₀} : Set S) := by
      rw [← hl₀.2.2.2]
      exact ⟨hv_cl, hvΓ⟩
    have he_emb : ιE e ∈ E(Γ.toEmbeddedGraph ιV ιE) := ⟨e, heΓ, rfl⟩
    have hlG : G.IsLink (ιE e) (ιV x₀) (ιV y₀) :=
      (hΓ.isLink_iff he_emb).mp ⟨e, x₀, y₀, hl₀, rfl, rfl, rfl⟩
    have hlM : M.IsLink (ιE e) (ιV x₀) (ιV y₀) := (hM.isLink_iff heM).mpr hlG
    rcases hv_pair with rfl | rfl
    · exact hlM.left_mem
    · exact hlM.right_mem
  edge_mem_of_inc := fun _ _ h => ⟨h.2, h.1.1⟩
  vertexSet_finite := Γ.finite_V.subset inter_subset_right
  edgeSet_finite := Γ.finite_edges.subset inter_subset_right

omit [T2Space S] in
@[simp]
theorem subHypergraphOfSubgraph_vertexSet (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G) (M : Graph α β) (hM : M ≤ G) :
    (subHypergraphOfSubgraph Γ ιV ιE hΓ M hM).vertexSet = ιV ⁻¹' V(M) ∩ Γ.V := rfl

omit [T2Space S] in
@[simp]
theorem subHypergraphOfSubgraph_edgeSet (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G) (M : Graph α β) (hM : M ≤ G) :
    (subHypergraphOfSubgraph Γ ιV ιE hΓ M hM).edgeSet = ιE ⁻¹' E(M) ∩ Γ.E := rfl

omit [T2Space S] in
theorem subHypergraphOfSubgraph_le (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G) (M : Graph α β) (hM : M ≤ G) :
    subHypergraphOfSubgraph Γ ιV ιE hΓ M hM ≤ Γ.toHypergraph := by
  refine ⟨inter_subset_right, inter_subset_right, fun e he => ?_⟩
  ext v
  exact ⟨fun h => ⟨h, he.1⟩, fun h => h.1⟩

omit [T2Space S] in
theorem subHypergraphOfSubgraph_mono (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G)
    {M₁ M₂ : Graph α β} (h₁ : M₁ ≤ G) (h₂ : M₂ ≤ G) (hle : M₁ ≤ M₂) :
    subHypergraphOfSubgraph Γ ιV ιE hΓ M₁ h₁ ≤ subHypergraphOfSubgraph Γ ιV ιE hΓ M₂ h₂ := by
  rw [GM10.le_iff_of_le (subHypergraphOfSubgraph_le Γ ιV ιE hΓ M₁ h₁)
    (subHypergraphOfSubgraph_le Γ ιV ιE hΓ M₂ h₂)]
  exact ⟨inter_subset_inter_left _ (preimage_mono hle.vertexSet_mono),
    inter_subset_inter_left _ (preimage_mono hle.edgeSet_mono)⟩

omit [T2Space S] in
theorem subHypergraphOfSubgraph_subgraphUnion (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G)
    {M₁ M₂ : Graph α β} (h₁ : M₁ ≤ G) (h₂ : M₂ ≤ G) :
    subHypergraphOfSubgraph Γ ιV ιE hΓ (subgraphUnion G M₁ M₂) (subgraphUnion_le h₁ h₂) =
      subHypergraphOfSubgraph Γ ιV ιE hΓ M₁ h₁ ∪ subHypergraphOfSubgraph Γ ιV ιE hΓ M₂ h₂ := by
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (subHypergraphOfSubgraph_le Γ ιV ιE hΓ _ (subgraphUnion_le h₁ h₂))
    (GM10.union_le (subHypergraphOfSubgraph_le Γ ιV ιE hΓ M₁ h₁)
      (subHypergraphOfSubgraph_le Γ ιV ιE hΓ M₂ h₂)) ?_ ?_
  · change ιV ⁻¹' V(subgraphUnion G M₁ M₂) ∩ Γ.V =
      (ιV ⁻¹' V(M₁) ∩ Γ.V) ∪ (ιV ⁻¹' V(M₂) ∩ Γ.V)
    rw [vertexSet_subgraphUnion, preimage_union, union_inter_distrib_right]
  · change ιE ⁻¹' E(subgraphUnion G M₁ M₂) ∩ Γ.E =
      (ιE ⁻¹' E(M₁) ∩ Γ.E) ∪ (ιE ⁻¹' E(M₂) ∩ Γ.E)
    rw [edgeSet_subgraphUnion h₁ h₂, preimage_union, union_inter_distrib_right]

omit [T2Space S] in
theorem subHypergraphOfSubgraph_subgraphInter (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G)
    {M₁ M₂ : Graph α β} (h₁ : M₁ ≤ G) (h₂ : M₂ ≤ G) :
    subHypergraphOfSubgraph Γ ιV ιE hΓ (subgraphInter G M₁ M₂) (subgraphInter_le h₁) =
      subHypergraphOfSubgraph Γ ιV ιE hΓ M₁ h₁ ∩ subHypergraphOfSubgraph Γ ιV ιE hΓ M₂ h₂ := by
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (subHypergraphOfSubgraph_le Γ ιV ιE hΓ _ (subgraphInter_le h₁))
    (GM10.inter_le (subHypergraphOfSubgraph_le Γ ιV ιE hΓ M₁ h₁)
      (subHypergraphOfSubgraph_le Γ ιV ιE hΓ M₂ h₂)) ?_ ?_
  · ext x
    simp only [subHypergraphOfSubgraph_vertexSet, GM10.inter_vertexSet, vertexSet_subgraphInter,
      mem_inter_iff, mem_preimage]
    tauto
  · ext e
    simp only [subHypergraphOfSubgraph_edgeSet, GM10.inter_edgeSet, edgeSet_subgraphInter h₁ h₂,
      mem_inter_iff, mem_preimage]
    tauto

omit [T2Space S] in
theorem isSeparation_subHypergraphOfSubgraph (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {G C D : Graph α β} (hΓ : Γ.toEmbeddedGraph ιV ιE ≤ G)
    (hsep : IsGraphSeparation G C D) :
    Γ.toHypergraph.IsSeparation
      (subHypergraphOfSubgraph Γ ιV ιE hΓ C hsep.1)
      (subHypergraphOfSubgraph Γ ιV ιE hΓ D hsep.2.1) := by
  rw [GM10.isSeparation_iff_of_le (subHypergraphOfSubgraph_le Γ ιV ιE hΓ C hsep.1)
    (subHypergraphOfSubgraph_le Γ ιV ιE hΓ D hsep.2.1)]
  have hVG : Γ.V ⊆ ιV ⁻¹' V(G) := fun x hx => hΓ.vertexSet_mono ⟨x, hx, rfl⟩
  have hEG : Γ.E ⊆ ιE ⁻¹' E(G) := fun e he => hΓ.edgeSet_mono ⟨e, he, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · change (ιV ⁻¹' V(C) ∩ Γ.V) ∪ (ιV ⁻¹' V(D) ∩ Γ.V) = Γ.V
    rw [← union_inter_distrib_right, ← preimage_union, hsep.2.2.1, inter_eq_right.mpr hVG]
  · change (ιE ⁻¹' E(C) ∩ Γ.E) ∪ (ιE ⁻¹' E(D) ∩ Γ.E) = Γ.E
    rw [← union_inter_distrib_right, ← preimage_union, hsep.2.2.2.1, inter_eq_right.mpr hEG]
  · change (ιE ⁻¹' E(C) ∩ Γ.E) ∩ (ιE ⁻¹' E(D) ∩ Γ.E) = ∅
    ext e
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false]
    exact fun ⟨⟨heC, _⟩, ⟨heD, _⟩⟩ => Set.disjoint_left.mp hsep.2.2.2.2 heC heD

omit [T2Space S] in
/-- Conversely, any subhypergraph `H_Γ ≤ Γ.toHypergraph` embeds as a subgraph of
`Γ.toEmbeddedGraph ιV ιE` with vertex set `ιV '' H_Γ.vertexSet` and edge set `ιE '' H_Γ.edgeSet`. -/
def embSubgraph (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    (H_Γ : Hypergraph S (Set S)) : Graph α β :=
  ((Γ.toEmbeddedGraph ιV ιE).induce (ιV '' H_Γ.vertexSet)).restrict (ιE '' H_Γ.edgeSet)

omit [T2Space S] in
theorem embSubgraph_le (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {H_Γ : Hypergraph S (Set S)} (hH : H_Γ ≤ Γ.toHypergraph) :
    embSubgraph Γ ιV ιE H_Γ ≤ Γ.toEmbeddedGraph ιV ιE :=
  restrict_le.trans ((Γ.toEmbeddedGraph ιV ιE).induce_le (image_mono hH.vertexSet_subset))

omit [T2Space S] in
@[simp]
theorem vertexSet_embSubgraph (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    (H_Γ : Hypergraph S (Set S)) :
    V(embSubgraph Γ ιV ιE H_Γ) = ιV '' H_Γ.vertexSet := rfl

omit [T2Space S] in
@[simp]
theorem edgeSet_embSubgraph (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    {H_Γ : Hypergraph S (Set S)} (hH : H_Γ ≤ Γ.toHypergraph) :
    E(embSubgraph Γ ιV ιE H_Γ) = ιE '' H_Γ.edgeSet := by
  unfold embSubgraph
  rw [edgeSet_restrict, inter_eq_right]
  rintro _ ⟨e₀, he₀, rfl⟩
  have he₀_Γ : e₀ ∈ Γ.E := hH.edgeSet_subset he₀
  obtain ⟨x₀, y₀, hl₀⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he₀_Γ
  have hx₀_cl : x₀ ∈ closure e₀ :=
    ((by rw [hl₀.2.2.2]; exact Set.mem_insert x₀ {y₀} : x₀ ∈ closure e₀ ∩ Γ.V)).1
  have hy₀_cl : y₀ ∈ closure e₀ :=
    ((by rw [hl₀.2.2.2]; exact Set.mem_insert_of_mem x₀ rfl : y₀ ∈ closure e₀ ∩ Γ.V)).1
  have hx₀_inc : H_Γ.Inc e₀ x₀ :=
    (GM10.inc_iff_of_le hH he₀).mpr ⟨he₀_Γ, hl₀.left_mem, hx₀_cl⟩
  have hy₀_inc : H_Γ.Inc e₀ y₀ :=
    (GM10.inc_iff_of_le hH he₀).mpr ⟨he₀_Γ, hl₀.right_mem, hy₀_cl⟩
  exact ⟨ιV x₀, ιV y₀, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩,
    ⟨x₀, H_Γ.vertex_mem_of_inc hx₀_inc, rfl⟩, ⟨y₀, H_Γ.vertex_mem_of_inc hy₀_inc, rfl⟩⟩

/-! ## 3. Disc Separations of $\Gamma$ for Members of $\mathcal{A}$ -/

/-- Under `(J1)`–`(J6)`, for any `A ∈ 𝒜`, the subhypergraph of `Γ.toHypergraph` induced by `A` is
`(PaintingOrDrawing.drawing Γ).inter (D A)`, and the disc separation
`((PaintingOrDrawing.drawing Γ).inter (D A), (PaintingOrDrawing.drawing Γ).interOutside (D A))`
belongs to `T` and is a separation of `Γ.toHypergraph`. -/
theorem subHypergraphOfSubgraph_eq_drawing_inter {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A : Graph α β} (hA : A ∈ 𝒜) :
    let hΓ := hJ.Γ_le.trans Graph.deleteVerts_le
    let A_Γ := (PaintingOrDrawing.drawing Γ).inter (D A)
    let B_Γ := (PaintingOrDrawing.drawing Γ).interOutside (D A)
    subHypergraphOfSubgraph Γ ιV ιE hΓ A (hJ.le_of_mem_𝒜 A hA) = A_Γ ∧
    (A_Γ, B_Γ) ∈ T ∧
    Γ.toHypergraph.IsSeparation A_Γ B_Γ := by
  intro hΓ A_Γ B_Γ
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  obtain ⟨hDisc, hNorm, hDA_eq⟩ := hJ.disc_D A hA
  have hClosed : IsClosed (D A) := hDisc.isCompact.isClosed
  have hOArc : IsOArc (subBd (D A)) := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hDisc]
    exact hDisc.isOArc_discBd
  have hV_sub : Γ.V ⊆ ιV ⁻¹' V(R_G.G.toGraph) :=
    fun v hv => hΓ.vertexSet_mono ⟨v, hv, rfl⟩
  have hbd_sub : subBd (D A) ∩ Γ.V ⊆ Set.range (πS A) := by
    rw [hJ.π_bar_eq_bd_inter A hA]
    exact inter_subset_inter_right (subBd (D A)) hV_sub
  have hcard_le : (subBd (D A) ∩ Γ.V).ncard ≤ 3 := by
    calc (subBd (D A) ∩ Γ.V).ncard
      _ ≤ (Set.range (πS A)).ncard := ncard_le_ncard hbd_sub (Set.finite_range (πS A))
      _ = πLen A := by rw [Set.ncard_range_of_injective (hJ.π_valid A hA).2.2.1, Nat.card_fin]
      _ ≤ 3 := (hJ.π_valid A hA).2.1
  have hcard_lt : (subBd (D A) ∩ Γ.V).ncard < ord := by
    have := hJ.four_le_θ; have := hJ.θ_le_ord; omega
  have hIns : IsTangleIns Γ T (subBd (D A)) (D A) := by
    have hspec := hJ.ins_spec (subBd (D A)) hOArc hNorm hcard_lt
    rwa [← hDA_eq] at hspec
  have hT : IsTangle Γ.toHypergraph ord T := hJ.hasMetric.1.2.1
  have hsep : Γ.toHypergraph.IsSeparation A_Γ B_Γ := hT.isSeparation hIns.2.2
  refine ⟨?_, hIns.2.2, hsep⟩
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (subHypergraphOfSubgraph_le Γ ιV ιE hΓ A (hJ.le_of_mem_𝒜 A hA)) hsep.left_le ?_ ?_
  · ext x
    change (ιV x ∈ V(A) ∧ x ∈ Γ.V) ↔ x ∈ Γ.V ∧ x ∈ D A
    have hV_eq := congr_arg Graph.vertexSet (hJ.Γ_inter_D A hA)
    constructor
    · rintro ⟨hxA, hxV⟩
      have hx_inter : ιV x ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A) := ⟨⟨x, hxV, rfl⟩, hxA⟩
      rw [← hV_eq] at hx_inter
      rcases hx_inter with ⟨x₁, hx₁, hxx₁⟩
      obtain rfl := ιV.injective hxx₁
      exact (mem_interSet_V_iff hClosed).mp hx₁
    · rintro ⟨hxV, hxD⟩
      have hx_inter : ιV x ∈ V((Γ.interSet (D A)).toEmbeddedGraph ιV ιE) :=
        ⟨x, (mem_interSet_V_iff hClosed).mpr ⟨hxV, hxD⟩, rfl⟩
      rw [hV_eq] at hx_inter
      exact ⟨hx_inter.2, hxV⟩
  · ext e
    change (ιE e ∈ E(A) ∧ e ∈ Γ.E) ↔ e ∈ Γ.E ∧ e ⊆ D A
    have hcompat : (Γ.toEmbeddedGraph ιV ιE).Compatible A :=
      Compatible.of_le_le hΓ (hJ.le_of_mem_𝒜 A hA)
    have hE_eq := congr_arg Graph.edgeSet (hJ.Γ_inter_D A hA)
    rw [hcompat.edgeSet_inf] at hE_eq
    constructor
    · rintro ⟨heA, heE⟩
      have he_inter : ιE e ∈ E(Γ.toEmbeddedGraph ιV ιE) ∩ E(A) := ⟨⟨e, heE, rfl⟩, heA⟩
      rw [← hE_eq] at he_inter
      rcases he_inter with ⟨e₁, he₁, hee₁⟩
      obtain rfl := ιE.injective hee₁
      exact GM11.mem_interSet_E_iff.mp he₁
    · rintro ⟨heE, heD⟩
      have he_inter : ιE e ∈ E((Γ.interSet (D A)).toEmbeddedGraph ιV ιE) :=
        ⟨e, GM11.mem_interSet_E_iff.mpr ⟨heE, heD⟩, rfl⟩
      rw [hE_eq] at he_inter
      exact ⟨he_inter.2, heE⟩

theorem mem_drawing_inter_DA_vertexSet {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A : Graph α β} (hA : A ∈ 𝒜) {x : S} :
    x ∈ ((PaintingOrDrawing.drawing Γ).inter (D A)).vertexSet ↔ ιV x ∈ V(A) ∧ x ∈ Γ.V := by
  have heq := congr_arg Hypergraph.vertexSet (subHypergraphOfSubgraph_eq_drawing_inter hJ hA).1.symm
  exact Iff.of_eq (congr_arg (x ∈ ·) heq)

theorem mem_drawing_inter_DA_edgeSet {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A : Graph α β} (hA : A ∈ 𝒜) {e : Set S} :
    e ∈ ((PaintingOrDrawing.drawing Γ).inter (D A)).edgeSet ↔ ιE e ∈ E(A) ∧ e ∈ Γ.E := by
  have heq := congr_arg Hypergraph.edgeSet (subHypergraphOfSubgraph_eq_drawing_inter hJ hA).1.symm
  exact Iff.of_eq (congr_arg (e ∈ ·) heq)

/-- When `A ∈ 𝒜` is a good member and `(A, B)` is a separation of `G` with
`V(A) ∩ V(B) = ιV '' Set.range (πS A) ∪ W`, the subhypergraph of `Γ.toHypergraph` induced by `B`
is `B_Γ = (PaintingOrDrawing.drawing Γ).interOutside (D A)`, and
`(A_Γ ∩ B_Γ).vertexSet = Set.range (πS A)`. -/
theorem subHypergraphOfSubgraph_eq_drawing_interOutside_of_good {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A B : Graph α β} (hA : A ∈ 𝒜)
    (hGood : IsGoodMember ιV ιE Γ πLen πS A)
    (hsep_AB : IsGraphSeparation R_G.G.toGraph A B)
    (hV_AB : V(A) ∩ V(B) = (ιV '' Set.range (πS A)) ∪ W) :
    let hΓ := hJ.Γ_le.trans Graph.deleteVerts_le
    let A_Γ := (PaintingOrDrawing.drawing Γ).inter (D A)
    let B_Γ := (PaintingOrDrawing.drawing Γ).interOutside (D A)
    subHypergraphOfSubgraph Γ ιV ιE hΓ B hsep_AB.2.1 = B_Γ ∧
    (A_Γ ∩ B_Γ).vertexSet = Set.range (πS A) := by
  intro hΓ A_Γ B_Γ
  obtain ⟨hA_eq, _, hsep_Γ⟩ := subHypergraphOfSubgraph_eq_drawing_inter hJ hA
  have hClosed : IsClosed (D A) := (hJ.disc_D A hA).1.isCompact.isClosed
  have hV_sub_G : Γ.V ⊆ ιV ⁻¹' V(R_G.G.toGraph) :=
    fun v hv => hΓ.vertexSet_mono ⟨v, hv, rfl⟩
  have hAB_V : (A_Γ ∩ B_Γ).vertexSet = Set.range (πS A) := by
    ext x
    change (x ∈ Γ.V ∧ x ∈ D A) ∧ (x ∈ Γ.V ∧ x ∈ closure (Set.univ \ D A)) ↔
      x ∈ Set.range (πS A)
    rw [hJ.π_bar_eq_bd_inter A hA]
    have hbd : subBd (D A) = D A ∩ closure (Set.univ \ D A) := by
      unfold subBd
      rw [hClosed.closure_eq]
    rw [hbd]
    constructor
    · rintro ⟨⟨hxV, hxD⟩, _, hxOut⟩
      exact ⟨⟨hxD, hxOut⟩, hV_sub_G hxV⟩
    · rintro ⟨⟨hxD, hxOut⟩, hxG⟩
      have hxV : x ∈ Γ.V := hGood.1 (by rw [hJ.π_bar_eq_bd_inter A hA, hbd]; exact ⟨⟨hxD, hxOut⟩, hxG⟩)
      exact ⟨⟨hxV, hxD⟩, hxV, hxOut⟩
  refine ⟨?_, hAB_V⟩
  have hsep_ind := isSeparation_subHypergraphOfSubgraph Γ ιV ιE hΓ hsep_AB
  rw [hA_eq] at hsep_ind
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (subHypergraphOfSubgraph_le Γ ιV ιE hΓ B hsep_AB.2.1) hsep_Γ.right_le ?_ ?_
  · ext x
    change (ιV x ∈ V(B) ∧ x ∈ Γ.V) ↔ x ∈ B_Γ.vertexSet
    constructor
    · rintro ⟨hxB, hxV⟩
      by_cases hxD : x ∈ D A
      · have hxA_Γ : x ∈ ((PaintingOrDrawing.drawing Γ).inter (D A)).vertexSet := ⟨hxV, hxD⟩
        have hxA : ιV x ∈ V(A) := ((mem_drawing_inter_DA_vertexSet hJ hA).mp hxA_Γ).1
        have hxAB : ιV x ∈ V(A) ∩ V(B) := ⟨hxA, hxB⟩
        rw [hV_AB] at hxAB
        rcases hxAB with ⟨s, hs, hsx⟩ | hxW
        · obtain rfl := ιV.injective hsx
          rw [← hAB_V] at hs
          exact hs.2
        · have hx_del := hJ.Γ_le.vertexSet_mono ⟨x, hxV, rfl⟩
          rw [Graph.vertexSet_deleteVerts] at hx_del
          exact False.elim (hx_del.2 hxW)
      · exact ⟨hxV, subset_closure ⟨mem_univ x, hxD⟩⟩
    · intro hxB_Γ
      have hxV : x ∈ Γ.V := hsep_Γ.right_le.vertexSet_subset hxB_Γ
      refine ⟨?_, hxV⟩
      by_cases hxD : x ∈ D A
      · have hx_inter : x ∈ (A_Γ ∩ B_Γ).vertexSet := ⟨⟨hxV, hxD⟩, hxB_Γ⟩
        rw [hAB_V] at hx_inter
        have hx_AB : ιV x ∈ V(A) ∩ V(B) := by
          rw [hV_AB]
          exact Or.inl ⟨x, hx_inter, rfl⟩
        exact hx_AB.2
      · have hx_not_A : ιV x ∉ V(A) := by
          intro hxA
          exact hxD ((mem_drawing_inter_DA_vertexSet hJ hA).mpr ⟨hxA, hxV⟩).2
        have hx_union : ιV x ∈ V(A) ∪ V(B) := by
          rw [hsep_AB.2.2.1]
          exact hV_sub_G hxV
        exact hx_union.resolve_left hx_not_A
  · ext e
    have h1 := congr_arg (e ∈ ·) hsep_ind.edgeSet_union
    have h2 := congr_arg (e ∈ ·) hsep_ind.edgeSet_inter_eq
    have h3 := congr_arg (e ∈ ·) hsep_Γ.edgeSet_union
    have h4 := congr_arg (e ∈ ·) hsep_Γ.edgeSet_inter_eq
    simp only [GM10.inter_edgeSet, mem_union, mem_inter_iff, mem_empty_iff_false] at h1 h2 h3 h4
    tauto

/-! ## 4. Uncrossing Inequality for Good Members on $\Gamma$ -/

/-- For a good member `A ∈ 𝒜` and any separation `(C_Γ, D_Γ)` of `Γ.toHypergraph`, we cannot have
both `((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard < ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard`
and `((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard < ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard`. -/
theorem not_both_boundary_diff_gt_of_isGoodMember {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A : Graph α β} (hA : A ∈ 𝒜)
    (hGood : IsGoodMember ιV ιE Γ πLen πS A)
    {C_Γ D_Γ : Hypergraph S (Set S)}
    (hsep : Γ.toHypergraph.IsSeparation C_Γ D_Γ) :
    let A_Γ := (PaintingOrDrawing.drawing Γ).inter (D A)
    let B_Γ := (PaintingOrDrawing.drawing Γ).interOutside (D A)
    ¬ (((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard <
        ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard ∧
      ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard <
        ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard) := by
  intro A_Γ B_Γ ⟨hgt_C, hgt_D⟩
  have hClosed : IsClosed (D A) := (hJ.disc_D A hA).1.isCompact.isClosed
  have hV_sub_G : Γ.V ⊆ ιV ⁻¹' V(R_G.G.toGraph) :=
    fun v hv => (hJ.Γ_le.trans Graph.deleteVerts_le).vertexSet_mono ⟨v, hv, rfl⟩
  have hAB_V : A_Γ.vertexSet ∩ B_Γ.vertexSet = Set.range (πS A) := by
    ext x
    change (x ∈ Γ.V ∧ x ∈ D A) ∧ (x ∈ Γ.V ∧ x ∈ closure (Set.univ \ D A)) ↔
      x ∈ Set.range (πS A)
    rw [hJ.π_bar_eq_bd_inter A hA]
    have hbd : subBd (D A) = D A ∩ closure (Set.univ \ D A) := by
      unfold subBd; rw [hClosed.closure_eq]
    rw [hbd]
    exact ⟨fun ⟨⟨hxV, hxD⟩, _, hxOut⟩ => ⟨⟨hxD, hxOut⟩, hV_sub_G hxV⟩,
      fun ⟨⟨hxD, hxOut⟩, hxG⟩ =>
        let hxV := hGood.1 (by rw [hJ.π_bar_eq_bd_inter A hA, hbd]; exact ⟨⟨hxD, hxOut⟩, hxG⟩)
        ⟨⟨hxV, hxD⟩, hxV, hxOut⟩⟩
  have hAB_card : (A_Γ.vertexSet ∩ B_Γ.vertexSet).ncard ≤ 3 := by
    rw [hAB_V, Set.ncard_range_of_injective (hJ.π_valid A hA).2.2.1, Nat.card_fin]
    exact (hJ.π_valid A hA).2.1
  have hVC_union_VD : C_Γ.vertexSet ∪ D_Γ.vertexSet = Γ.V :=
    hsep.vertexSet_union
  have hdisj_diff : Disjoint ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet)
      ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet) := by
    rw [Set.disjoint_left]
    intro x ⟨hxAB, hxC⟩ ⟨_, hxD⟩
    have hxV : x ∈ Γ.V := hxAB.1.1
    rw [← hVC_union_VD] at hxV
    exact hxV.elim hxC hxD
  have hAB_fin : (A_Γ.vertexSet ∩ B_Γ.vertexSet).Finite :=
    Γ.finite_V.subset (inter_subset_left.trans inter_subset_left)
  have hsum_le : ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard +
      ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard ≤ 3 := by
    rw [← Set.ncard_union_eq hdisj_diff (hAB_fin.subset sdiff_subset) (hAB_fin.subset sdiff_subset)]
    exact (Set.ncard_le_ncard (union_subset sdiff_subset sdiff_subset) hAB_fin).trans hAB_card
  have hCD_zero : ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard = 0 := by omega
  have hCD_sub_B : C_Γ.vertexSet ∩ D_Γ.vertexSet ⊆ B_Γ.vertexSet := by
    rw [← Set.sdiff_eq_empty]
    exact (Set.ncard_eq_zero (Γ.finite_V.subset
      (sdiff_subset.trans (inter_subset_left.trans hsep.left_le.vertexSet_subset)))).mp hCD_zero
  obtain ⟨s_u, hs_u⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard ≠ 0)
  obtain ⟨s_v, hs_v⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard ≠ 0)
  have hs_u_π : s_u ∈ Set.range (πS A) := hAB_V ▸ hs_u.1
  have hs_v_π : s_v ∈ Set.range (πS A) := hAB_V ▸ hs_v.1
  have hs_u_C : s_u ∈ C_Γ.vertexSet \ D_Γ.vertexSet := by
    have hs_u_V : s_u ∈ C_Γ.vertexSet ∪ D_Γ.vertexSet := hVC_union_VD.symm ▸ hs_u.1.1.1
    exact ⟨hs_u_V.resolve_right hs_u.2, hs_u.2⟩
  have hs_v_not_C : s_v ∉ C_Γ.vertexSet \ D_Γ.vertexSet := fun h => hs_v.2 h.1
  obtain ⟨P, hP_path, hP_int⟩ :=
    hGood.2 (ιV s_u) ⟨s_u, hs_u_π, rfl⟩ (ιV s_v) ⟨s_v, hs_v_π, rfl⟩
  have hP_le_GA : P ≤ (Γ.toEmbeddedGraph ιV ιE) ⊓ A := hP_path.1
  have ⟨_, W_P, hW_simp, hVP, _⟩ := hP_path
  -- Along any walk in `P`, no single step can jump from `C_Γ \ D_Γ` to the complement of `C_Γ`
  -- without passing through `C_Γ ∩ D_Γ`.
  have hstep : ∀ {a b : α} {e : β}, P.IsLink e a b →
      a ∈ ιV '' (C_Γ.vertexSet \ D_Γ.vertexSet) →
      b ∉ ιV '' (C_Γ.vertexSet \ D_Γ.vertexSet) →
      b ∈ ιV '' (C_Γ.vertexSet ∩ D_Γ.vertexSet) := by
    intro a b e hl ha hb
    rcases ha with ⟨sa, hsa, rfl⟩
    have hlΓ : (Γ.toEmbeddedGraph ιV ιE).IsLink e (ιV sa) b :=
      hl.mono (hP_le_GA.trans inf_le_left)
    rcases hlΓ with ⟨e₀, x₀, y₀, hl₀, rfl, hxx₀, rfl⟩
    obtain rfl : x₀ = sa := ιV.injective hxx₀
    have he₀ : e₀ ∈ Γ.E := hl₀.edge_mem
    have hx₀_inc : Γ.toHypergraph.Inc e₀ x₀ :=
      ⟨he₀, hl₀.left_mem, ((by rw [hl₀.2.2.2]; exact Set.mem_insert x₀ {y₀} : x₀ ∈ closure e₀ ∩ Γ.V)).1⟩
    have hy₀_inc : Γ.toHypergraph.Inc e₀ y₀ :=
      ⟨he₀, hl₀.right_mem, ((by rw [hl₀.2.2.2]; exact Set.mem_insert_of_mem x₀ rfl : y₀ ∈ closure e₀ ∩ Γ.V)).1⟩
    have he₀_CD : e₀ ∈ C_Γ.edgeSet ∪ D_Γ.edgeSet :=
      hsep.edgeSet_union.symm ▸ he₀
    rcases he₀_CD with he₀C | he₀D
    · have hy₀_C : y₀ ∈ C_Γ.vertexSet :=
        C_Γ.vertex_mem_of_inc ((GM10.inc_iff_of_le hsep.left_le he₀C).mpr hy₀_inc)
      have hy₀_D : y₀ ∈ D_Γ.vertexSet := by
        by_contra hy₀_not_D
        exact hb ⟨y₀, ⟨hy₀_C, hy₀_not_D⟩, rfl⟩
      exact ⟨y₀, ⟨hy₀_C, hy₀_D⟩, rfl⟩
    · have hx₀_D : x₀ ∈ D_Γ.vertexSet :=
        D_Γ.vertex_mem_of_inc ((GM10.inc_iff_of_le hsep.right_le he₀D).mpr hx₀_inc)
      exact False.elim (hsa.2 hx₀_D)
  have hwalk_hit : ∀ {a b : α} (W₀ : GraphWalk P a b),
      a ∈ ιV '' (C_Γ.vertexSet \ D_Γ.vertexSet) →
      b ∉ ιV '' (C_Γ.vertexSet \ D_Γ.vertexSet) →
      ∃ z ∈ W₀.support, z ∈ ιV '' (C_Γ.vertexSet ∩ D_Γ.vertexSet) := by
    intro a b W₀
    induction W₀ with
    | nil _ =>
      intro ha hb
      exact False.elim (hb ha)
    | @cons a m b e hl rest ih =>
      intro ha hb
      by_cases hm : m ∈ ιV '' (C_Γ.vertexSet \ D_Γ.vertexSet)
      · obtain ⟨z, hz, hz_mem⟩ := ih hm hb
        exact ⟨z, List.mem_cons_of_mem _ hz, hz_mem⟩
      · exact ⟨m, List.mem_cons_of_mem _ rest.start_mem_support, hstep hl ha hm⟩
  obtain ⟨z, hz_supp, s_w, hs_w_CD, rfl⟩ :=
    hwalk_hit W_P ⟨s_u, hs_u_C, rfl⟩ (fun ⟨s, hs, hs_eq⟩ => hs_v_not_C (ιV.injective hs_eq ▸ hs))
  have hz_VP : ιV s_w ∈ V(P) := by rw [hVP]; exact hz_supp
  have hs_w_ne_u : s_w ≠ s_u := fun h => hs_u.2 (h ▸ hs_w_CD.2)
  have hs_w_ne_v : s_w ≠ s_v := fun h => hs_v.2 (h ▸ hs_w_CD.1)
  have hz_int : ιV s_w ∈ pathInternalVerts ((Γ.toEmbeddedGraph ιV ιE) ⊓ A) P := by
    rw [IsGraphPathWithEnds.pathInternalVerts_eq hP_path]
    refine ⟨hz_VP, ?_⟩
    rintro (h | h)
    · exact hs_w_ne_u (ιV.injective h)
    · exact hs_w_ne_v (ιV.injective h)
  have hz_not_π : ιV s_w ∉ ιV '' Set.range (πS A) :=
    Set.disjoint_left.mp hP_int hz_int
  have hs_w_A : s_w ∈ A_Γ.vertexSet := by
    have hz_GA : ιV s_w ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A) := hP_le_GA.vertexSet_mono hz_VP
    exact (mem_drawing_inter_DA_vertexSet hJ hA).mpr ⟨hz_GA.2, hsep.left_le.vertexSet_subset hs_w_CD.1⟩
  have hs_w_B : s_w ∈ B_Γ.vertexSet := hCD_sub_B hs_w_CD
  have hs_w_AB : s_w ∈ A_Γ.vertexSet ∩ B_Γ.vertexSet := ⟨hs_w_A, hs_w_B⟩
  rw [hAB_V] at hs_w_AB
  exact hz_not_π ⟨s_w, hs_w_AB, rfl⟩

/-! ## 5. Proof of Claim (9) of Theorem 7.4 (pages 555–556) -/

omit [TopologicalSpace S] [T2Space S] in
theorem le_subgraphInter_iff {G M M₁ M₂ : Graph α β}
    (h₁ : M₁ ≤ G) (h₂ : M₂ ≤ G) (hM : M ≤ G) :
    M ≤ subgraphInter G M₁ M₂ ↔ M ≤ M₁ ∧ M ≤ M₂ := by
  rw [(Compatible.of_le_le hM (subgraphInter_le h₁)).le_iff,
    (Compatible.of_le_le hM h₁).le_iff, (Compatible.of_le_le hM h₂).le_iff,
    vertexSet_subgraphInter, edgeSet_subgraphInter h₁ h₂, subset_inter_iff, subset_inter_iff]
  tauto

omit [TopologicalSpace S] [T2Space S] in
theorem isGraphSeparation_uncross_left {G A B C D : Graph α β}
    (hAB : IsGraphSeparation G A B) (hCD : IsGraphSeparation G C D) :
    IsGraphSeparation G (subgraphUnion G A C) (subgraphInter G B D) := by
  refine ⟨subgraphUnion_le hAB.1 hCD.1, subgraphInter_le hAB.2.1, ?_, ?_, ?_⟩
  · ext x
    rw [mem_union, vertexSet_subgraphUnion, vertexSet_subgraphInter, mem_union, mem_inter_iff]
    have h1 : x ∈ V(G) ↔ x ∈ V(A) ∨ x ∈ V(B) := by rw [← mem_union, hAB.2.2.1]
    have h2 : x ∈ V(G) ↔ x ∈ V(C) ∨ x ∈ V(D) := by rw [← mem_union, hCD.2.2.1]
    tauto
  · ext e
    rw [mem_union, edgeSet_subgraphUnion hAB.1 hCD.1,
      edgeSet_subgraphInter hAB.2.1 hCD.2.1, mem_union, mem_inter_iff]
    have h1 : e ∈ E(G) ↔ e ∈ E(A) ∨ e ∈ E(B) := by rw [← mem_union, hAB.2.2.2.1]
    have h2 : e ∈ E(G) ↔ e ∈ E(C) ∨ e ∈ E(D) := by rw [← mem_union, hCD.2.2.2.1]
    tauto
  · rw [edgeSet_subgraphUnion hAB.1 hCD.1,
      edgeSet_subgraphInter hAB.2.1 hCD.2.1, Set.disjoint_left]
    rintro e (heA | heC) ⟨heB, heD⟩
    · exact Set.disjoint_left.mp hAB.2.2.2.2 heA heB
    · exact Set.disjoint_left.mp hCD.2.2.2.2 heC heD

omit [TopologicalSpace S] [T2Space S] in
theorem isGraphSeparation_uncross_right {G A B C D : Graph α β}
    (hAB : IsGraphSeparation G A B) (hCD : IsGraphSeparation G C D) :
    IsGraphSeparation G (subgraphInter G B C) (subgraphUnion G A D) := by
  refine ⟨subgraphInter_le hAB.2.1, subgraphUnion_le hAB.1 hCD.2.1, ?_, ?_, ?_⟩
  · ext x
    rw [mem_union, vertexSet_subgraphInter, vertexSet_subgraphUnion, mem_inter_iff, mem_union]
    have h1 : x ∈ V(G) ↔ x ∈ V(A) ∨ x ∈ V(B) := by rw [← mem_union, hAB.2.2.1]
    have h2 : x ∈ V(G) ↔ x ∈ V(C) ∨ x ∈ V(D) := by rw [← mem_union, hCD.2.2.1]
    tauto
  · ext e
    rw [mem_union, edgeSet_subgraphInter hAB.2.1 hCD.1,
      edgeSet_subgraphUnion hAB.1 hCD.2.1, mem_inter_iff, mem_union]
    have h1 : e ∈ E(G) ↔ e ∈ E(A) ∨ e ∈ E(B) := by rw [← mem_union, hAB.2.2.2.1]
    have h2 : e ∈ E(G) ↔ e ∈ E(C) ∨ e ∈ E(D) := by rw [← mem_union, hCD.2.2.2.1]
    tauto
  · rw [edgeSet_subgraphInter hAB.2.1 hCD.1,
      edgeSet_subgraphUnion hAB.1 hCD.2.1, Set.disjoint_left]
    rintro e ⟨heB, heC⟩ (heA | heD)
    · exact Set.disjoint_left.mp hAB.2.2.2.2 heA heB
    · exact Set.disjoint_left.mp hCD.2.2.2.2 heC heD

omit [TopologicalSpace S] [T2Space S] in
theorem deleteVerts_mono {G₁ G₂ : Graph α β} {X : Set α} (h : G₁ ≤ G₂) :
    G₁.deleteVerts X ≤ G₂.deleteVerts X := by
  refine ⟨?_, fun e x y hl => ?_⟩
  · rw [Graph.vertexSet_deleteVerts, Graph.vertexSet_deleteVerts]
    exact sdiff_le_sdiff_right h.vertexSet_mono
  · rw [Graph.deleteVerts_isLink] at hl ⊢
    exact ⟨hl.1.mono h, hl.2⟩

/-- Predicate for a valid separation `(C, D)` of `G` in Claim (9) of Theorem 7.4. -/
def IsClaim9Separation {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (i : Fin t) (C D_sep : Graph α β) : Prop :=
  IsGraphSeparation R_G.G.toGraph C D_sep ∧
  W ⊆ V(C) ∩ V(D_sep) ∧
  A_fam' i ≤ C ∧
  K ≤ D_sep ∧
  (∀ A ∈ 𝒜, θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) → A ≤ D_sep) ∧
  ∃ C_Γ D_Γ : Hypergraph S (Set S),
    C_Γ.vertexSet = c.ιV ⁻¹' V(C) ∩ c.Γ.V ∧ C_Γ.edgeSet = c.ιE ⁻¹' E(C) ∩ c.Γ.E ∧
    D_Γ.vertexSet = c.ιV ⁻¹' V(D_sep) ∩ c.Γ.V ∧ D_Γ.edgeSet = c.ιE ⁻¹' E(D_sep) ∩ c.Γ.E ∧
    (C_Γ, D_Γ) ∈ c.T ∧
    (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard < πLen (A_fam' i)

set_option maxHeartbeats 800000 in
/-- **Graph Minors XXII, (7.4) Claim (9)** (pages 555–556):
"(9) *For $1 \le i \le t$, there is no separation $(C, D)$ of $G$ with $W \subseteq V(C \cap D)$ such that*
• *$A'_i \subseteq C$,*
• *$K \subseteq D$, and $A \subseteq D$ for all $A \in \mathcal{A}$ with $d(D(A), \Sigma \setminus \Delta) \ge \theta$, and*
• *$(\Gamma \cap C, \Gamma \cap D) \in \mathcal{T}$ and has order $< |\bar{\pi}(A'_i)|$.*" -/
theorem lemma_7_4_claim_9
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
    ¬ ∃ C D_sep : Graph α β, IsClaim9Separation c i C D_sep := by
  intro hex
  let G := R_G.G.toGraph
  have hΓ_le_G : c.Γ_emb ≤ G := c.hJ.Γ_le.trans Graph.deleteVerts_le
  have hT : IsTangle c.Γ.toHypergraph c.ord c.T := c.hJ.hasMetric.1.2.1
  let S_ord : Set ℕ := {n : ℕ | ∃ C D_sep : Graph α β,
    IsClaim9Separation c i C D_sep ∧ (V(C) ∩ V(D_sep)).ncard = n}
  have hS_ne : S_ord.Nonempty := by
    rcases hex with ⟨C₀, D₀, h₀⟩
    exact ⟨(V(C₀) ∩ V(D₀)).ncard, C₀, D₀, h₀, rfl⟩
  obtain ⟨C, D_sep, hCD, hmin_eq⟩ := Nat.sInf_mem hS_ne
  have hmin : ∀ C' D' : Graph α β, IsClaim9Separation c i C' D' →
      (V(C) ∩ V(D_sep)).ncard ≤ (V(C') ∩ V(D')).ncard := by
    intro C' D' h'
    rw [hmin_eq]
    exact Nat.sInf_le ⟨C', D', h', rfl⟩
  rcases hCD with ⟨hsep_CD, hW_CD, hA'i_le_C, hK_le_D, hfar_le_D,
    C_Γ₀, D_Γ₀, hCΓ_V, hCΓ_E, hDΓ_V, hDΓ_E, hCD_T₀, hord_CD_lt⟩
  let C_Γ := subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G C hsep_CD.1
  let D_Γ := subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G D_sep hsep_CD.2.1
  have hC_Γ_eq : C_Γ₀ = C_Γ :=
    GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (hT.isSeparation hCD_T₀).left_le
      (subHypergraphOfSubgraph_le c.Γ c.ιV c.ιE hΓ_le_G C hsep_CD.1) hCΓ_V hCΓ_E
  have hD_Γ_eq : D_Γ₀ = D_Γ :=
    GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (hT.isSeparation hCD_T₀).right_le
      (subHypergraphOfSubgraph_le c.Γ c.ιV c.ιE hΓ_le_G D_sep hsep_CD.2.1) hDΓ_V hDΓ_E
  subst hC_Γ_eq hD_Γ_eq
  have hsep_Γ_CD : c.Γ.toHypergraph.IsSeparation C_Γ D_Γ := hT.isSeparation hCD_T₀
  have hW_fin : W.Finite :=
    c.hJ.finite_V.subset ((hW_CD.trans inter_subset_left).trans hsep_CD.1.vertexSet_mono)
  have hCD_fin : (V(C) ∩ V(D_sep)).Finite :=
    c.hJ.finite_V.subset (inter_subset_left.trans hsep_CD.1.vertexSet_mono)
  have hΓ_disj_W : Disjoint V(c.Γ_emb) W := by
    rw [Set.disjoint_left]
    intro x hxΓ hxW
    have hx_del := c.hJ.Γ_le.vertexSet_mono hxΓ
    rw [Graph.vertexSet_deleteVerts] at hx_del
    exact hx_del.2 hxW
  have hCD_Γ_eq : (V(C) ∩ V(D_sep)) ∩ V(c.Γ_emb) = c.ιV '' (C_Γ.vertexSet ∩ D_Γ.vertexSet) := by
    ext x
    simp only [C_Γ, D_Γ, mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨hxC, hxD⟩, s, hsV, rfl⟩
      exact ⟨s, ⟨⟨hxC, hsV⟩, hxD, hsV⟩, rfl⟩
    · rintro ⟨s, ⟨⟨hxC, hsV⟩, hxD, _⟩, rfl⟩
      exact ⟨⟨hxC, hxD⟩, s, hsV, rfl⟩
  -- Case split on whether `(V(C) ∩ V(D_sep)).ncard ≥ πLen (A_fam' i) + W.ncard`.
  by_cases hge_ord : πLen (A_fam' i) + W.ncard ≤ (V(C) ∩ V(D_sep)).ncard
  · -- Then `V(C) ∩ V(D_sep)` is not contained in `V(c.Γ_emb) ∪ W`.
    have hnot_sub_ΓW : ¬ (V(C) ∩ V(D_sep) ⊆ V(c.Γ_emb) ∪ W) := by
      intro hsub
      have heq_un : V(C) ∩ V(D_sep) = ((V(C) ∩ V(D_sep)) ∩ V(c.Γ_emb)) ∪ W := by
        ext x
        exact ⟨fun hx => (hsub hx).elim (fun hxΓ => Or.inl ⟨hx, hxΓ⟩) Or.inr,
          fun hx => hx.elim (fun h => h.1) (fun hxW => hW_CD hxW)⟩
      have hdisj : Disjoint ((V(C) ∩ V(D_sep)) ∩ V(c.Γ_emb)) W :=
        Disjoint.mono_left inter_subset_right hΓ_disj_W
      have hcard_un : (V(C) ∩ V(D_sep)).ncard =
          (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard + W.ncard := by
        rw [heq_un, Set.ncard_union_eq hdisj (hCD_fin.subset inter_subset_left) hW_fin,
          hCD_Γ_eq, Set.ncard_image_of_injective _ c.ιV.injective]
      omega
    obtain ⟨v, hvCD, hv_not_ΓW⟩ := Set.not_subset.mp hnot_sub_ΓW
    rw [mem_union, not_or] at hv_not_ΓW
    rcases hv_not_ΓW with ⟨hv_not_Γ, hv_not_W⟩
    -- Check that `v ∈ V(A)` for some `A ∈ 𝒜` with `d(D A, Σ \ Δ) < θ`.
    have hex_A : ∃ A ∈ 𝒜, v ∈ V(A) ∧
        subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ := by
      by_contra! hno_A
      -- Otherwise every edge of `G` incident with `v` belongs to `E(D_sep)`, and `v ∉ V(A_fam' i)`.
      have hv_not_A'i : v ∉ V(A_fam' i) := by
        intro hvA'i
        have hdist_A'i : subsetTangleDist c.Γ c.ord c.d (D (A_fam' i)) (Set.univ \ Δ) < θ := by
          by_contra! hge
          have h1 : 1 ≤ subsetTangleDist c.Γ c.ord c.d (D (A_fam' i)) (Set.univ \ Δ) := by
            have := c.hJ.four_le_θ; omega
          have hsub_Δ := subset_of_one_le_subsetTangleDist_compl c.hJ.hasMetric h1
          obtain ⟨x₀, hx₀⟩ := GM14.IsClosedDisc.nonempty (c.hJ.disc_D (A_fam' i) (hA'_mem i)).1
          exact Set.disjoint_left.mp (h_iii_disj i) hx₀ (hsub_Δ hx₀)
        exact not_lt_of_ge (hno_A (A_fam' i) (hA'_mem i) hvA'i) hdist_A'i
      have hinc_D : ∀ {e y}, G.IsLink e v y → e ∈ E(D_sep) := by
        intro e y hlG
        have heG : e ∈ E(G) := hlG.edge_mem
        have heNK : e ∈ E(N) ∪ E(K) := c.hJ.sep_NK.1.2.2.2.1.symm ▸ heG
        rcases heNK with heN | heK
        · rw [c.hJ.N_eq, edgeSet_graphUnion, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
            edgeSet_subgraphSUnion c.hJ.le_of_mem_𝒜] at heN
          rcases heN with heΓ | heU
          · have hlΓ : c.Γ_emb.IsLink e v y := (hΓ_le_G.isLink_iff heΓ).mpr hlG
            exact False.elim (hv_not_Γ hlΓ.left_mem)
          · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heU
            have hlA : A.IsLink e v y := ((c.hJ.le_of_mem_𝒜 A hA).isLink_iff heA).mpr hlG
            have hdist_ge := hno_A A hA hlA.left_mem
            exact (hfar_le_D A hA hdist_ge).edgeSet_mono heA
        · exact hK_le_D.edgeSet_mono heK
      have hEC_no_v : ∀ {e x y}, C.IsLink e x y → x ≠ v ∧ y ≠ v := by
        intro e x y hlC
        have hlG : G.IsLink e x y := hlC.mono hsep_CD.1
        refine ⟨fun hxv => ?_, fun hyv => ?_⟩
        · subst hxv
          exact Set.disjoint_left.mp hsep_CD.2.2.2.2 hlC.edge_mem (hinc_D hlG)
        · subst hyv
          exact Set.disjoint_left.mp hsep_CD.2.2.2.2 hlC.edge_mem (hinc_D hlG.symm)
      let C' := C.deleteVerts {v}
      have hC'_le_C : C' ≤ C := Graph.deleteVerts_le
      have hC'_le_G : C' ≤ G := hC'_le_C.trans hsep_CD.1
      have hEC'_eq : E(C') = E(C) := by
        ext e
        refine ⟨fun he => hC'_le_C.edgeSet_mono he, fun he => ?_⟩
        obtain ⟨x, y, hlC⟩ := C.exists_isLink_of_mem_edgeSet he
        have ⟨hxv, hyv⟩ := hEC_no_v hlC
        have hlC' : C'.IsLink e x y := by
          rw [Graph.deleteVerts_isLink]
          exact ⟨hlC, hxv, hyv⟩
        exact hlC'.edge_mem
      have hsep_C'D : IsGraphSeparation G C' D_sep := by
        refine ⟨hC'_le_G, hsep_CD.2.1, ?_, hEC'_eq ▸ hsep_CD.2.2.2.1, hEC'_eq ▸ hsep_CD.2.2.2.2⟩
        ext x
        rw [mem_union, Graph.vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff]
        have hx_imp : x ∈ V(G) ↔ x ∈ V(C) ∨ x ∈ V(D_sep) := by
          rw [← mem_union, hsep_CD.2.2.1]
        have hvD : x = v → x ∈ V(D_sep) := fun h => h ▸ hvCD.2
        tauto
      have hW_C'D : W ⊆ V(C') ∩ V(D_sep) := by
        intro w hw
        rw [mem_inter_iff, Graph.vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff]
        exact ⟨⟨(hW_CD hw).1, fun h => hv_not_W (h ▸ hw)⟩, (hW_CD hw).2⟩
      have hA'i_le_C' : A_fam' i ≤ C' := by
        rw [(Compatible.of_le_le (c.hJ.le_of_mem_𝒜 (A_fam' i) (hA'_mem i)) hC'_le_G).le_iff]
        refine ⟨fun x hx => ?_, hEC'_eq ▸ hA'i_le_C.edgeSet_mono⟩
        rw [Graph.vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff]
        exact ⟨hA'i_le_C.vertexSet_mono hx, fun h => hv_not_A'i (h ▸ hx)⟩
      have hC'Γ_V : C_Γ.vertexSet = c.ιV ⁻¹' V(C') ∩ c.Γ.V := by
        ext s
        simp only [C_Γ, C', Graph.vertexSet_deleteVerts,
          mem_inter_iff, mem_preimage, mem_sdiff, mem_singleton_iff]
        exact ⟨fun ⟨hsC, hsV⟩ => ⟨⟨hsC, fun h => hv_not_Γ ⟨s, hsV, h⟩⟩, hsV⟩,
          fun ⟨⟨hsC, _⟩, hsV⟩ => ⟨hsC, hsV⟩⟩
      have hC'Γ_E : C_Γ.edgeSet = c.ιE ⁻¹' E(C') ∩ c.Γ.E := by
        rw [hEC'_eq]; rfl
      have hClaim9_C'D : IsClaim9Separation c i C' D_sep :=
        ⟨hsep_C'D, hW_C'D, hA'i_le_C', hK_le_D, hfar_le_D,
          C_Γ, D_Γ, hC'Γ_V, hC'Γ_E, rfl, rfl, hCD_T₀, hord_CD_lt⟩
      have hle_min := hmin C' D_sep hClaim9_C'D
      have hssub : V(C') ∩ V(D_sep) ⊂ V(C) ∩ V(D_sep) := by
        refine ⟨inter_subset_inter_left _ hC'_le_C.vertexSet_mono, fun h => ?_⟩
        have hv' := (h hvCD).1
        rw [Graph.vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff] at hv'
        exact hv'.2 rfl
      exact not_lt_of_ge hle_min (Set.ncard_lt_ncard hssub hCD_fin)
    rcases hex_A with ⟨A, hA, hvA, hdist_A⟩
    have hGood : IsGoodMember c.ιV c.ιE c.Γ πLen πS A :=
      lemma_7_4_claim_4 c hc_ext hA hdist_A
    have hAK : A ⊓ K = Graph.noEdge W β := by
      by_contra hne
      exact not_le_of_gt hdist_A (c.hJ.dist_D_of_inter_K A hA hne)
    obtain ⟨B, hB_le_G, hsep_AB, hV_AB, hK_le_B, hA'_le_B⟩ :=
      exists_separation_of_mem_𝒜 c.hJ hA hAK
    let A_Γ := (PaintingOrDrawing.drawing c.Γ).inter (D A)
    let B_Γ := (PaintingOrDrawing.drawing c.Γ).interOutside (D A)
    obtain ⟨hA_Γ_eq, hAB_T, hsep_Γ_AB⟩ := subHypergraphOfSubgraph_eq_drawing_inter c.hJ hA
    obtain ⟨hB_Γ_eq, hAB_V_eq⟩ :=
      subHypergraphOfSubgraph_eq_drawing_interOutside_of_good c.hJ hA hGood hsep_AB hV_AB
    -- Note `v ∉ V(B)` because `v ∈ V(A)` and `v ∉ V(c.Γ_emb) ∪ W ⊇ V(A) ∩ V(B)`.
    have hv_not_B : v ∉ V(B) := by
      intro hvB
      have hvAB : v ∈ V(A) ∩ V(B) := ⟨hvA, hvB⟩
      rw [hV_AB] at hvAB
      rcases hvAB with ⟨s, hs, rfl⟩ | hvW
      · exact hv_not_Γ ⟨s, hGood.1 hs, rfl⟩
      · exact hv_not_W hvW
    -- Thus `((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard < ((V(C) ∩ V(D_sep)) \ V(B)).ncard`.
    have hCD_diff_B_gt :
        ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard <
          ((V(C) ∩ V(D_sep)) \ V(B)).ncard := by
      rw [← Set.ncard_image_of_injective _ c.ιV.injective]
      refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (hCD_fin.subset sdiff_subset)
      · rintro _ ⟨s, ⟨⟨⟨hsC, hsV⟩, ⟨hsD, _⟩⟩, hs_not_B⟩, rfl⟩
        dsimp only [B_Γ] at hs_not_B
        rw [← hB_Γ_eq] at hs_not_B
        exact ⟨⟨hsC, hsD⟩, fun hB => hs_not_B ⟨hB, hsV⟩⟩
      · intro hsub
        obtain ⟨s, hs, hsv⟩ := hsub ⟨hvCD, hv_not_B⟩
        exact hv_not_Γ ⟨s, hs.1.1.2, hsv⟩
    -- And `((V(A) ∩ V(B)) \ V(C)).ncard = ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard`
    -- (and similarly for `D_sep`).
    have hAB_diff_C_eq :
        ((V(A) ∩ V(B)) \ V(C)).ncard = ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard := by
      rw [← Set.ncard_image_of_injective _ c.ιV.injective]
      congr 1
      ext x
      rw [hV_AB, ← hAB_V_eq]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩ | hxW, hx_not_C⟩
        · exact ⟨s, ⟨hs, fun hsC => hx_not_C hsC.1⟩, rfl⟩
        · exact False.elim (hx_not_C (hW_CD hxW).1)
      · rintro ⟨s, ⟨hs, hs_not_C⟩, rfl⟩
        have hsV : s ∈ c.Γ.V := hs.1.1
        exact ⟨Or.inl ⟨s, hs, rfl⟩, fun hxC => hs_not_C ⟨hxC, hsV⟩⟩
    have hAB_diff_D_eq :
        ((V(A) ∩ V(B)) \ V(D_sep)).ncard = ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard := by
      rw [← Set.ncard_image_of_injective _ c.ιV.injective]
      congr 1
      ext x
      rw [hV_AB, ← hAB_V_eq]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩ | hxW, hx_not_D⟩
        · exact ⟨s, ⟨hs, fun hsD => hx_not_D hsD.1⟩, rfl⟩
        · exact False.elim (hx_not_D (hW_CD hxW).2)
      · rintro ⟨s, ⟨hs, hs_not_D⟩, rfl⟩
        have hsV : s ∈ c.Γ.V := hs.1.1
        exact ⟨Or.inl ⟨s, hs, rfl⟩, fun hxD => hs_not_D ⟨hxD, hsV⟩⟩
    have hCD_Γ_fin : (C_Γ.vertexSet ∩ D_Γ.vertexSet).Finite :=
      c.Γ.finite_V.subset (inter_subset_left.trans hsep_Γ_CD.left_le.vertexSet_subset)
    have hAB_Γ_fin : (A_Γ.vertexSet ∩ B_Γ.vertexSet).Finite :=
      c.Γ.finite_V.subset (inter_subset_left.trans hsep_Γ_AB.left_le.vertexSet_subset)
    have hAB_Γ_sub_CD : A_Γ.vertexSet ∩ B_Γ.vertexSet ⊆ C_Γ.vertexSet ∪ D_Γ.vertexSet := by
      rw [← GM10.union_vertexSet, hsep_Γ_CD.union_eq]
      exact inter_subset_left.trans hsep_Γ_AB.left_le.vertexSet_subset
    have hAB_fin : (V(A) ∩ V(B)).Finite :=
      c.hJ.finite_V.subset (inter_subset_left.trans hsep_AB.1.vertexSet_mono)
    have hAB_sub_CD : V(A) ∩ V(B) ⊆ V(C) ∪ V(D_sep) := by
      rw [hsep_CD.2.2.1]
      exact inter_subset_left.trans hsep_AB.1.vertexSet_mono
    -- Part 1: Prove `((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard < ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard`.
    have hgt_C : ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard <
        ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet).ncard := by
      have hid_Γ := uncross_ncard_identity hCD_Γ_fin hAB_Γ_fin hAB_Γ_sub_CD
      by_cases hord_gt : (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard <
          ((A_Γ.vertexSet ∪ C_Γ.vertexSet) ∩ (B_Γ.vertexSet ∩ D_Γ.vertexSet)).ncard
      · omega
      · push Not at hord_gt
        -- Then `(A ∪ C, B ∩ D_sep)` is a valid Claim (9) separation!
        let C₁ := subgraphUnion G A C
        let D₁ := subgraphInter G B D_sep
        have hsep_C₁D₁ : IsGraphSeparation G C₁ D₁ :=
          isGraphSeparation_uncross_left hsep_AB hsep_CD
        have hW_C₁D₁ : W ⊆ V(C₁) ∩ V(D₁) := by
          intro w hw
          have hwAB : w ∈ V(A) ∩ V(B) := by rw [hV_AB]; exact Or.inr hw
          exact ⟨Or.inl hwAB.1, hwAB.2, (hW_CD hw).2⟩
        have hA'i_le_C₁ : A_fam' i ≤ C₁ :=
          hA'i_le_C.trans (le_subgraphUnion_right hsep_AB.1 hsep_CD.1)
        have hK_le_D₁ : K ≤ D₁ := by
          rw [le_subgraphInter_iff hsep_AB.2.1 hsep_CD.2.1 c.hJ.sep_NK.1.2.1]
          exact ⟨hK_le_B, hK_le_D⟩
        have hfar_le_D₁ : ∀ A' ∈ 𝒜,
            θ ≤ subsetTangleDist c.Γ c.ord c.d (D A') (Set.univ \ Δ) → A' ≤ D₁ := by
          intro A' hA' hdist'
          rw [le_subgraphInter_iff hsep_AB.2.1 hsep_CD.2.1 (c.hJ.le_of_mem_𝒜 A' hA')]
          have hne : A' ≠ A := fun h => not_le_of_gt hdist_A (h ▸ hdist')
          exact ⟨hA'_le_B A' hA' hne, hfar_le_D A' hA' hdist'⟩
        have hord_C₁D₁_lt : separationOrder (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) < πLen (A_fam' i) :=
          lt_of_le_of_lt hord_gt hord_CD_lt
        have hord_C₁D₁_ord : separationOrder (A_Γ ∪ C_Γ) (B_Γ ∩ D_Γ) < c.ord := by
          have := (c.hJ.π_valid (A_fam' i) (hA'_mem i)).2.1
          have := c.hJ.four_le_θ; have := c.hJ.θ_le_ord; omega
        have hC₁D₁_T : (A_Γ ∪ C_Γ, B_Γ ∩ D_Γ) ∈ c.T :=
          GM10.theorem_2_2_proof hT hAB_T hCD_T₀ hord_C₁D₁_ord
        have hC₁_Γ_eq : (A_Γ ∪ C_Γ).vertexSet = c.ιV ⁻¹' V(C₁) ∩ c.Γ.V ∧
            (A_Γ ∪ C_Γ).edgeSet = c.ιE ⁻¹' E(C₁) ∩ c.Γ.E := by
          have heq := subHypergraphOfSubgraph_subgraphUnion c.Γ c.ιV c.ιE hΓ_le_G hsep_AB.1 hsep_CD.1
          rw [hA_Γ_eq] at heq
          exact ⟨congr_arg Hypergraph.vertexSet heq.symm, congr_arg Hypergraph.edgeSet heq.symm⟩
        have hD₁_Γ_eq : (B_Γ ∩ D_Γ).vertexSet = c.ιV ⁻¹' V(D₁) ∩ c.Γ.V ∧
            (B_Γ ∩ D_Γ).edgeSet = c.ιE ⁻¹' E(D₁) ∩ c.Γ.E := by
          have heq := subHypergraphOfSubgraph_subgraphInter c.Γ c.ιV c.ιE hΓ_le_G hsep_AB.2.1 hsep_CD.2.1
          rw [hB_Γ_eq] at heq
          exact ⟨congr_arg Hypergraph.vertexSet heq.symm, congr_arg Hypergraph.edgeSet heq.symm⟩
        have hClaim9_1 : IsClaim9Separation c i C₁ D₁ :=
          ⟨hsep_C₁D₁, hW_C₁D₁, hA'i_le_C₁, hK_le_D₁, hfar_le_D₁,
            A_Γ ∪ C_Γ, B_Γ ∩ D_Γ, hC₁_Γ_eq.1, hC₁_Γ_eq.2, hD₁_Γ_eq.1, hD₁_Γ_eq.2,
            hC₁D₁_T, hord_C₁D₁_lt⟩
        have hle_min := hmin C₁ D₁ hClaim9_1
        rw [vertexSet_subgraphUnion, vertexSet_subgraphInter] at hle_min
        have hid_G := uncross_ncard_identity hCD_fin hAB_fin hAB_sub_CD
        rw [hAB_diff_C_eq] at hid_G
        omega
    -- Deduce `A ≠ A_fam' i`.
    have hA_ne_A'i : A ≠ A_fam' i := by
      intro hEq
      have hsub : (A_Γ.vertexSet ∩ B_Γ.vertexSet) \ C_Γ.vertexSet = ∅ := by
        rw [Set.sdiff_eq_empty]
        dsimp only [A_Γ]
        rw [← hA_Γ_eq]
        exact inter_subset_left.trans
          (inter_subset_inter_left _ (preimage_mono (hEq ▸ hA'i_le_C).vertexSet_mono))
      rw [hsub, Set.ncard_empty] at hgt_C
      omega
    -- Part 2: Prove `((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard < ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard`.
    have hgt_D : ((C_Γ.vertexSet ∩ D_Γ.vertexSet) \ B_Γ.vertexSet).ncard <
        ((A_Γ.vertexSet ∩ B_Γ.vertexSet) \ D_Γ.vertexSet).ncard := by
      have hid_Γ := uncross_ncard_identity
        (inter_comm C_Γ.vertexSet D_Γ.vertexSet ▸ hCD_Γ_fin) hAB_Γ_fin
        (union_comm C_Γ.vertexSet D_Γ.vertexSet ▸ hAB_Γ_sub_CD)
      rw [inter_comm D_Γ.vertexSet C_Γ.vertexSet] at hid_Γ
      by_cases hord_gt : (C_Γ.vertexSet ∩ D_Γ.vertexSet).ncard <
          ((A_Γ.vertexSet ∪ D_Γ.vertexSet) ∩ (B_Γ.vertexSet ∩ C_Γ.vertexSet)).ncard
      · omega
      · push Not at hord_gt
        -- Then `(B ∩ C, A ∪ D_sep)` is a valid Claim (9) separation!
        let C₂ := subgraphInter G B C
        let D₂ := subgraphUnion G A D_sep
        have hsep_C₂D₂ : IsGraphSeparation G C₂ D₂ :=
          isGraphSeparation_uncross_right hsep_AB hsep_CD
        have hW_C₂D₂ : W ⊆ V(C₂) ∩ V(D₂) := by
          intro w hw
          have hwAB : w ∈ V(A) ∩ V(B) := by rw [hV_AB]; exact Or.inr hw
          exact ⟨⟨hwAB.2, (hW_CD hw).1⟩, Or.inl hwAB.1⟩
        have hA'i_le_C₂ : A_fam' i ≤ C₂ := by
          rw [le_subgraphInter_iff hsep_AB.2.1 hsep_CD.1 (c.hJ.le_of_mem_𝒜 (A_fam' i) (hA'_mem i))]
          exact ⟨hA'_le_B (A_fam' i) (hA'_mem i) (Ne.symm hA_ne_A'i), hA'i_le_C⟩
        have hK_le_D₂ : K ≤ D₂ :=
          hK_le_D.trans (le_subgraphUnion_right hsep_AB.1 hsep_CD.2.1)
        have hfar_le_D₂ : ∀ A' ∈ 𝒜,
            θ ≤ subsetTangleDist c.Γ c.ord c.d (D A') (Set.univ \ Δ) → A' ≤ D₂ :=
          fun A' hA' hdist' =>
            (hfar_le_D A' hA' hdist').trans (le_subgraphUnion_right hsep_AB.1 hsep_CD.2.1)
        have h1 : subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G C₂ hsep_C₂D₂.1 = B_Γ ∩ C_Γ := by
          have heq := subHypergraphOfSubgraph_subgraphInter c.Γ c.ιV c.ιE hΓ_le_G hsep_AB.2.1 hsep_CD.1
          rwa [hB_Γ_eq] at heq
        have h2 : subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G D₂ hsep_C₂D₂.2.1 = A_Γ ∪ D_Γ := by
          have heq := subHypergraphOfSubgraph_subgraphUnion c.Γ c.ιV c.ιE hΓ_le_G hsep_AB.1 hsep_CD.2.1
          rwa [hA_Γ_eq] at heq
        have hC₂_Γ_eq : (B_Γ ∩ C_Γ).vertexSet = c.ιV ⁻¹' V(C₂) ∩ c.Γ.V ∧
            (B_Γ ∩ C_Γ).edgeSet = c.ιE ⁻¹' E(C₂) ∩ c.Γ.E :=
          ⟨congr_arg Hypergraph.vertexSet h1.symm, congr_arg Hypergraph.edgeSet h1.symm⟩
        have hD₂_Γ_eq : (A_Γ ∪ D_Γ).vertexSet = c.ιV ⁻¹' V(D₂) ∩ c.Γ.V ∧
            (A_Γ ∪ D_Γ).edgeSet = c.ιE ⁻¹' E(D₂) ∩ c.Γ.E :=
          ⟨congr_arg Hypergraph.vertexSet h2.symm, congr_arg Hypergraph.edgeSet h2.symm⟩
        have hsep_Γ_C₂D₂ : c.Γ.toHypergraph.IsSeparation (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) := by
          have hsep2 := isSeparation_subHypergraphOfSubgraph c.Γ c.ιV c.ιE hΓ_le_G hsep_C₂D₂
          rwa [h1, h2] at hsep2
        have hord_C₂D₂_lt : separationOrder (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) < πLen (A_fam' i) := by
          change ((B_Γ.vertexSet ∩ C_Γ.vertexSet) ∩ (A_Γ.vertexSet ∪ D_Γ.vertexSet)).ncard <
            πLen (A_fam' i)
          rw [inter_comm (B_Γ.vertexSet ∩ C_Γ.vertexSet)]
          exact lt_of_le_of_lt hord_gt hord_CD_lt
        have hord_C₂D₂_ord : separationOrder (B_Γ ∩ C_Γ) (A_Γ ∪ D_Γ) < c.ord := by
          have := (c.hJ.π_valid (A_fam' i) (hA'_mem i)).2.1
          have := c.hJ.four_le_θ; have := c.hJ.θ_le_ord; omega
        have hC₂D₂_T : (B_Γ ∩ C_Γ, A_Γ ∪ D_Γ) ∈ c.T :=
          mem_tangle_of_right_le hT hCD_T₀ hsep_Γ_C₂D₂ hord_C₂D₂_ord
            (GM10.le_union_right hsep_Γ_AB.left_le hsep_Γ_CD.right_le)
        have hClaim9_2 : IsClaim9Separation c i C₂ D₂ :=
          ⟨hsep_C₂D₂, hW_C₂D₂, hA'i_le_C₂, hK_le_D₂, hfar_le_D₂,
            B_Γ ∩ C_Γ, A_Γ ∪ D_Γ, hC₂_Γ_eq.1, hC₂_Γ_eq.2, hD₂_Γ_eq.1, hD₂_Γ_eq.2,
            hC₂D₂_T, hord_C₂D₂_lt⟩
        have hle_min := hmin C₂ D₂ hClaim9_2
        rw [vertexSet_subgraphInter, vertexSet_subgraphUnion, inter_comm (V(B) ∩ V(C))] at hle_min
        have hid_G := uncross_ncard_identity
          (inter_comm V(C) V(D_sep) ▸ hCD_fin) hAB_fin (union_comm V(C) V(D_sep) ▸ hAB_sub_CD)
        rw [inter_comm V(D_sep) V(C), hAB_diff_D_eq] at hid_G
        omega
    exact not_both_boundary_diff_gt_of_isGoodMember c.hJ hA hGood hsep_Γ_CD ⟨hgt_C, hgt_D⟩
  · -- Otherwise `(V(C) ∩ V(D_sep)).ncard < πLen (A_fam' i) + W.ncard`.
    -- Then `(C \ W, D_sep \ W)` is a separation of `G \ W` of order `< πLen (A_fam' i)`,
    -- contradicting `(J7)`.
    push Not at hge_ord
    let C_del := C.deleteVerts W
    let D_del := D_sep.deleteVerts W
    have hsep_del : IsGraphSeparation (G.deleteVerts W) C_del D_del := by
      have hC_del_le : C_del ≤ G.deleteVerts W := deleteVerts_mono hsep_CD.1
      have hD_del_le : D_del ≤ G.deleteVerts W := deleteVerts_mono hsep_CD.2.1
      refine ⟨hC_del_le, hD_del_le, ?_, ?_, ?_⟩
      · simp only [C_del, D_del, Graph.vertexSet_deleteVerts]
        rw [← union_sdiff_distrib, hsep_CD.2.2.1]
      · ext e
        refine ⟨fun he => he.elim (fun h => hC_del_le.edgeSet_mono h) (fun h => hD_del_le.edgeSet_mono h),
          fun he => ?_⟩
        obtain ⟨x, y, hl⟩ := (G.deleteVerts W).exists_isLink_of_mem_edgeSet he
        rw [Graph.deleteVerts_isLink] at hl
        have he_CD : e ∈ E(C) ∪ E(D_sep) := hsep_CD.2.2.2.1.symm ▸ hl.1.edge_mem
        rcases he_CD with heC | heD
        · have hlC : C.IsLink e x y := (hsep_CD.1.isLink_iff heC).mpr hl.1
          have hlC' : C_del.IsLink e x y := by
            rw [Graph.deleteVerts_isLink]
            exact ⟨hlC, hl.2.1, hl.2.2⟩
          exact Or.inl hlC'.edge_mem
        · have hlD : D_sep.IsLink e x y := (hsep_CD.2.1.isLink_iff heD).mpr hl.1
          have hlD' : D_del.IsLink e x y := by
            rw [Graph.deleteVerts_isLink]
            exact ⟨hlD, hl.2.1, hl.2.2⟩
          exact Or.inr hlD'.edge_mem
      · exact Disjoint.mono Graph.deleteVerts_le.edgeSet_mono
          Graph.deleteVerts_le.edgeSet_mono hsep_CD.2.2.2.2
    have hV_del_inter : V(C_del) ∩ V(D_del) = (V(C) ∩ V(D_sep)) \ W := by
      ext x
      simp only [C_del, D_del, Graph.vertexSet_deleteVerts, mem_inter_iff, mem_sdiff]
      tauto
    have hcard_del_lt : (V(C_del) ∩ V(D_del)).ncard < πLen (A_fam' i) := by
      have hunion : ((V(C) ∩ V(D_sep)) \ W) ∪ W = V(C) ∩ V(D_sep) :=
        sdiff_union_of_subset hW_CD
      have hcard_sum : ((V(C) ∩ V(D_sep)) \ W).ncard + W.ncard = (V(C) ∩ V(D_sep)).ncard := by
        rw [← Set.ncard_union_eq disjoint_sdiff_left (hCD_fin.subset sdiff_subset) hW_fin, hunion]
      rw [hV_del_inter]
      omega
    have hA'i_del_le : (A_fam' i).deleteVerts W ≤ C_del :=
      deleteVerts_mono hA'i_le_C
    have hC_Γ_del_V : C_Γ.vertexSet = c.ιV ⁻¹' V(C_del) ∩ c.Γ.V := by
      ext s
      simp only [C_Γ, C_del, Graph.vertexSet_deleteVerts,
        mem_inter_iff, mem_preimage, mem_sdiff]
      exact ⟨fun ⟨hsC, hsV⟩ => ⟨⟨hsC, fun hsW => Set.disjoint_left.mp hΓ_disj_W ⟨s, hsV, rfl⟩ hsW⟩, hsV⟩,
        fun ⟨⟨hsC, _⟩, hsV⟩ => ⟨hsC, hsV⟩⟩
    have hC_Γ_del_E : C_Γ.edgeSet = c.ιE ⁻¹' E(C_del) ∩ c.Γ.E := by
      ext e₀
      simp only [C_Γ, C_del, mem_inter_iff, mem_preimage]
      refine ⟨fun ⟨heC, heE⟩ => ⟨?_, heE⟩, fun ⟨heC', heE⟩ => ⟨Graph.deleteVerts_le.edgeSet_mono heC', heE⟩⟩
      obtain ⟨x₀, y₀, hl₀⟩ := c.Γ.toGraph.exists_isLink_of_mem_edgeSet heE
      have hl_emb : c.Γ_emb.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) :=
        ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
      have hlG : G.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) := hl_emb.mono hΓ_le_G
      have hlC : C.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) := (hsep_CD.1.isLink_iff heC).mpr hlG
      have hlC' : C_del.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) := by
        rw [Graph.deleteVerts_isLink]
        exact ⟨hlC, Set.disjoint_left.mp hΓ_disj_W ⟨x₀, hl₀.left_mem, rfl⟩,
          Set.disjoint_left.mp hΓ_disj_W ⟨y₀, hl₀.right_mem, rfl⟩⟩
      exact hlC'.edge_mem
    have hD_Γ_del_V : D_Γ.vertexSet = c.ιV ⁻¹' V(D_del) ∩ c.Γ.V := by
      ext s
      simp only [D_Γ, D_del, Graph.vertexSet_deleteVerts,
        mem_inter_iff, mem_preimage, mem_sdiff]
      exact ⟨fun ⟨hsD, hsV⟩ => ⟨⟨hsD, fun hsW => Set.disjoint_left.mp hΓ_disj_W ⟨s, hsV, rfl⟩ hsW⟩, hsV⟩,
        fun ⟨⟨hsD, _⟩, hsV⟩ => ⟨hsD, hsV⟩⟩
    have hD_Γ_del_E : D_Γ.edgeSet = c.ιE ⁻¹' E(D_del) ∩ c.Γ.E := by
      ext e₀
      simp only [D_Γ, D_del, mem_inter_iff, mem_preimage]
      refine ⟨fun ⟨heD, heE⟩ => ⟨?_, heE⟩, fun ⟨heD', heE⟩ => ⟨Graph.deleteVerts_le.edgeSet_mono heD', heE⟩⟩
      obtain ⟨x₀, y₀, hl₀⟩ := c.Γ.toGraph.exists_isLink_of_mem_edgeSet heE
      have hl_emb : c.Γ_emb.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) :=
        ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
      have hlG : G.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) := hl_emb.mono hΓ_le_G
      have hlD : D_sep.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) := (hsep_CD.2.1.isLink_iff heD).mpr hlG
      have hlD' : D_del.IsLink (c.ιE e₀) (c.ιV x₀) (c.ιV y₀) := by
        rw [Graph.deleteVerts_isLink]
        exact ⟨hlD, Set.disjoint_left.mp hΓ_disj_W ⟨x₀, hl₀.left_mem, rfl⟩,
          Set.disjoint_left.mp hΓ_disj_W ⟨y₀, hl₀.right_mem, rfl⟩⟩
      exact hlD'.edge_mem
    exact c.hJ7.no_small_sep (A_fam' i) (hA'_mem i)
      ⟨C_del, D_del, C_Γ, D_Γ, hsep_del, hcard_del_lt, hA'i_del_le,
        hC_Γ_del_V, hC_Γ_del_E, hD_Γ_del_V, hD_Γ_del_E, hCD_T₀⟩

end GraphMinor.GM22
