module

public import GraphMinor.GM22.Section2
public import GraphMinor.GM22.Section7d2e

/-!
# Graph Minors XXII – Section 7.4 (Part 3): Claims (5), (6), (7), and (8)

This file formalizes **Claims (5), (6), (7), and (8)** of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 554–555):

- `IsSufficientFor.isModelBasis`: if $\mathcal{B} \subseteq \mathcal{A}$ is sufficient for $\phi$,
  then $V(K \cup \bigcup(A : A \in \mathcal{B}))$ is a basis for $\phi$.
- `lemma_7_4_claim_5`: Claim (5) of (7.4) (page 554).
- `lemma_7_4_claim_6`: Claim (6) of (7.4) (page 554).
- `exists_separation_of_mem_𝒜`: for $A \in \mathcal{A}$ with $A \cap K = N_W$, existence of a
  separation $(A, B)$ of $G$ with $V(A \cap B) = \bar{\pi}(A) \cup W$, $K \subseteq B$, and
  $A' \subseteq B$ for all $A' \in \mathcal{A} \setminus \{A\}$.
- `exists_subgraph_same_effect_of_isGoodMember`: realizing the effect of $L \cap A$ on
  $\bar{\pi}(A) \cup W$ inside $(\Gamma \cap A) \cup N_W$ when $A$ is good.
- `lemma_7_4_claim_7`: Claim (7) of (7.4) (pages 554–555).
- `lemma_7_4_claim_8`: Claim (8) of (7.4) (page 555).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Basis from Sufficiency and Proof of Claim (5) (page 554) -/

omit [TopologicalSpace S] [T2Space S] in
/-- Monotonicity of `IsSufficientFor`: if $\mathcal{B} \subseteq \mathcal{B}' \subseteq \mathcal{A}$
and $\mathcal{B}$ is sufficient for $\phi'$, then $\mathcal{B}'$ is sufficient for $\phi'$. -/
theorem IsSufficientFor.mono {q : ℕ}
    {W : Set α} {𝒜 ℬ ℬ' : Set (Graph α β)} {K : Graph α β}
    {R_H : RootedDigraph αH βH q} {φV' : αH → Graph α β} {φE' : βH → β}
    (hSuff : IsSufficientFor W 𝒜 ℬ K R_H φV' φE')
    (hsub : ℬ ⊆ ℬ') (hℬ'_𝒜 : ℬ' ⊆ 𝒜) :
    IsSufficientFor W 𝒜 ℬ' K R_H φV' φE' where
  subset := hℬ'_𝒜
  mem_of_edge_inc_W := fun v hv A hA hInc => hsub (hSuff.mem_of_edge_inc_W v hv A hA hInc)
  φV_meets := fun v hv =>
    (hSuff.φV_meets v hv).mono (inter_subset_inter_right _ (union_subset_union_right _
      (biUnion_subset_biUnion_left hsub)))
  φE_mem := fun e he =>
    (union_subset_union_right _ (biUnion_subset_biUnion_left hsub)) (hSuff.φE_mem e he)
  mem_of_inter_K_ne_NW := fun A hA hne => hsub (hSuff.mem_of_inter_K_ne_NW A hA hne)

/-- Under `(J1)`–`(J6)`, if $\mathcal{B} \subseteq \mathcal{A}$ is sufficient for a model
$(\phi'_V, \phi'_E)$, then $V(K \cup \bigcup(A : A \in \mathcal{B}))$ is a basis for
$(\phi'_V, \phi'_E)$. -/
theorem IsSufficientFor.isModelBasis {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV φV' : αH → Graph α β} {φE φE' : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hSuff : IsSufficientFor W 𝒜 ℬ K R_H φV' φE') :
    let K' := graphUnion K (subgraphSUnion R_G.G.toGraph ℬ)
    IsModelBasis R_G R_H φV' φE' V(K') := by
  intro K'
  have hP_le : ∀ A ∈ ℬ, A ≤ R_G.G.toGraph :=
    fun A hB => hJ.le_of_mem_𝒜 A (hSuff.subset hB)
  have hK'_le : K' ≤ R_G.G.toGraph :=
    graphUnion_le hJ.sep_NK.1.2.1 (subgraphSUnion_le hP_le)
  have hEK' : E(K') = E(K) ∪ ⋃ A ∈ ℬ, E(A) := by
    rw [edgeSet_graphUnion, edgeSet_subgraphSUnion hP_le]
  have hVK' : V(K') = V(K) ∪ ⋃ A ∈ ℬ, V(A) := by
    rw [vertexSet_graphUnion, vertexSet_subgraphSUnion]
  refine ⟨hK'_le.vertexSet_mono, ?_, ?_, ?_, ?_⟩
  · intro i
    have hriW : R_G.roots i ∈ W := by
      rw [hJ.W_eq]
      exact ⟨i, rfl⟩
    exact Or.inl (hJ.sep_NK.2 hriW).2
  · intro e he
    have heK' : φE' e ∈ E(K') := by
      rw [hEK']
      exact hSuff.φE_mem e he
    have hlink_G : R_G.G.toGraph.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      R_G.G.isLink_of_mem (φE' e) (hK'_le.edgeSet_mono heK')
    have hlink_K' : K'.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      (hK'_le.isLink_iff heK').mpr hlink_G
    exact hlink_K'.right_mem
  · intro e he
    have heK' : φE' e ∈ E(K') := by
      rw [hEK']
      exact hSuff.φE_mem e he
    have hlink_G : R_G.G.toGraph.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      R_G.G.isLink_of_mem (φE' e) (hK'_le.edgeSet_mono heK')
    have hlink_K' : K'.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      (hK'_le.isLink_iff heK').mpr hlink_G
    exact hlink_K'.left_mem
  · intro v hv
    rw [Set.inter_comm, hVK']
    exact hSuff.φV_meets v hv

/-- **Graph Minors XXII, (7.4) Claim (5)** (page 554):
Let $Z$ be a basis for $\phi$ with $Z \subseteq V(K \cup \bigcup(A : A \in \mathcal{B}))$, and let
$L = \bigcup(\phi(v) : v \in V(H))$.
"(5) *If $L'$ is a subgraph of $L \cup \Gamma$ with $\phi(E(H)) \cap E(L') = \emptyset$ and with
the same effect on $Z$ as $L$, then $L' \cup \Gamma = L \cup \Gamma$, and if $L' \subseteq L$ then
$L' = L$.*" -/
theorem lemma_7_4_claim_5
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal)
    {Z : Set α}
    (hBasis : IsModelBasis R_G R_H c.φV c.φE Z)
    (hZ_sub : Z ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph ℬ)))
    {L' : Graph α β}
    (hL'_le : L' ≤ graphUnion c.L c.Γ_emb)
    (hL'_disj : Disjoint (c.φE '' E(R_H.G.toGraph)) E(L'))
    (heff : effectOn L' Z = effectOn c.L Z) :
    graphUnion L' c.Γ_emb = graphUnion c.L c.Γ_emb ∧ (L' ≤ c.L → L' = c.L) := by
  have hφ_le_G : ∀ P ∈ c.φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩
    exact c.hJ.isModel.subgraph_of_mem v hv
  have hL_le_G : c.L ≤ R_G.G.toGraph := subgraphSUnion_le hφ_le_G
  have hΓ_le_G : c.Γ_emb ≤ R_G.G.toGraph := c.hJ.Γ_le.trans Graph.deleteVerts_le
  have hLΓ_le_G : graphUnion c.L c.Γ_emb ≤ R_G.G.toGraph := graphUnion_le hL_le_G hΓ_le_G
  have hL'_le_G : L' ≤ R_G.G.toGraph := hL'_le.trans hLΓ_le_G
  have hL'_del : L' ≤ R_G.G.toGraph.deleteEdges (c.φE '' E(R_H.G.toGraph)) := by
    refine ⟨by rw [Graph.vertexSet_deleteEdges]; exact hL'_le_G.vertexSet_mono, fun e x y hl => ?_⟩
    rw [Graph.deleteEdges_isLink]
    exact ⟨hl.mono hL'_le_G, fun he => Set.disjoint_left.mp hL'_disj he hl.edge_mem⟩
  -- Apply 6.2 to obtain a model `(φ'V, c.φE)` in `L'`.
  obtain ⟨φ'V, hφ'V_spec, hMod'⟩ :=
    gm22_theorem_6_2 R_G R_H c.φV c.φE Z c.L L' c.hJ.isModel hBasis rfl hL'_del heff
  have hφ'_meets_ℬ : ∀ v ∈ V(R_H.G.toGraph),
      (V(φ'V v) ∩ (V(K) ∪ ⋃ A ∈ ℬ, V(A))).Nonempty := by
    intro v hv
    obtain ⟨z, hzZ, hzφ⟩ := hBasis.inter_φV_nonempty v hv
    have hz_inter : z ∈ V(c.φV v) ∩ Z := ⟨hzφ, hzZ⟩
    rw [← (hφ'V_spec v hv).2] at hz_inter
    have hz_KB : z ∈ V(K) ∪ ⋃ A ∈ ℬ, V(A) := by
      have := hZ_sub hz_inter.2
      rwa [vertexSet_graphUnion, vertexSet_subgraphSUnion] at this
    exact ⟨z, hz_inter.1, hz_KB⟩
  have hφ'_meets_𝒜 : ∀ v ∈ V(R_H.G.toGraph),
      (V(φ'V v) ∩ (V(K) ∪ ⋃ A ∈ 𝒜, V(A))).Nonempty := by
    intro v hv
    exact (hφ'_meets_ℬ v hv).mono
      (inter_subset_inter_right _ (union_subset_union_right _
        (biUnion_subset_biUnion_left c.hSuff.subset)))
  -- Check that `ℬ` is sufficient for `(φ'V, c.φE)`.
  have hSuff' : IsSufficientFor W 𝒜 ℬ K R_H φ'V c.φE :=
    { subset := c.hSuff.subset
      mem_of_edge_inc_W := fun v hv A hA ⟨e, he, w, hwW, y, hLink⟩ => by
        have he_L' : e ∈ E(L') :=
          (hφ'V_spec v hv).1.1.edgeSet_mono hLink.2.edge_mem
        have he_LΓ : e ∈ E(c.L) ∪ E(c.Γ_emb) := hL'_le.edgeSet_mono he_L'
        have hw_not_Γ : w ∉ V(c.Γ_emb) := by
          intro hwΓ
          have hw_del : w ∈ V(R_G.G.toGraph.deleteVerts W) := c.hJ.Γ_le.vertexSet_mono hwΓ
          rw [Graph.vertexSet_deleteVerts] at hw_del
          exact hw_del.2 hwW
        have he_not_Γ : e ∉ E(c.Γ_emb) := by
          intro heΓ
          have hLink_G : R_G.G.toGraph.IsLink e w y :=
            hLink.1.mono (c.hJ.le_of_mem_𝒜 A hA)
          have hLink_Γ : c.Γ_emb.IsLink e w y := (hΓ_le_G.isLink_iff heΓ).mpr hLink_G
          exact hw_not_Γ hLink_Γ.left_mem
        have he_L : e ∈ E(c.L) := he_LΓ.resolve_right he_not_Γ
        rw [ValidConfig74.L, edgeSet_subgraphSUnion hφ_le_G, mem_iUnion₂] at he_L
        rcases he_L with ⟨_, ⟨u, hu, rfl⟩, he_φu⟩
        have hLink_G : R_G.G.toGraph.IsLink e w y :=
          hLink.1.mono (c.hJ.le_of_mem_𝒜 A hA)
        have hLink_φu : (c.φV u).IsLink e w y :=
          ((c.hJ.isModel.subgraph_of_mem u hu).isLink_iff he_φu).mpr hLink_G
        have hLink_inter : (A ⊓ c.φV u).IsLink e w y := ⟨hLink.1, hLink_φu⟩
        exact c.hSuff.mem_of_edge_inc_W u hu A hA
          ⟨e, hLink_inter.edge_mem, w, hwW, y, hLink_inter⟩
      φV_meets := hφ'_meets_ℬ
      φE_mem := c.hSuff.φE_mem
      mem_of_inter_K_ne_NW := c.hSuff.mem_of_inter_K_ne_NW }
  let c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam' :=
    { c with
      φV := φ'V
      hJ := { c.hJ with isModel := hMod', φV_meets := hφ'_meets_𝒜 }
      hSuff := hSuff' }
  have hφ'_le_L' : ∀ P ∈ φ'V '' V(R_H.G.toGraph), P ≤ L' := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hφ'V_spec v hv).1.1
  have hφ'_le_G : ∀ P ∈ φ'V '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph :=
    fun P hP => (hφ'_le_L' P hP).trans hL'_le_G
  have hc'L_le_L' : c'.L ≤ L' :=
    subgraphSUnion_le_of_forall_le hφ'_le_G hL'_le_G hφ'_le_L'
  have hc'LΓ_le_L'Γ : graphUnion c'.L c.Γ_emb ≤ graphUnion L' c.Γ_emb := by
    rw [(Compatible.of_le_le (graphUnion_le (hc'L_le_L'.trans hL'_le_G) hΓ_le_G)
      (graphUnion_le hL'_le_G hΓ_le_G)).le_iff]
    exact ⟨union_subset_union_left _ hc'L_le_L'.vertexSet_mono,
      union_subset_union_left _ hc'L_le_L'.edgeSet_mono⟩
  have hL'Γ_le_LΓ : graphUnion L' c.Γ_emb ≤ graphUnion c.L c.Γ_emb :=
    graphUnion_le hL'_le (le_graphUnion_right (Compatible.of_le_le hL_le_G hΓ_le_G))
  have hm2_le : c.measure2 ≤ c'.measure2 := hc_ext.2.1 c' rfl
  have hc'Γ : c'.Γ_emb = c.Γ_emb := rfl
  unfold ValidConfig74.measure2 at hm2_le
  rw [hc'Γ] at hm2_le
  have hV_le1 : V(graphUnion c'.L c.Γ_emb).ncard ≤ V(graphUnion L' c.Γ_emb).ncard :=
    Set.ncard_le_ncard hc'LΓ_le_L'Γ.vertexSet_mono
      (c.hJ.finite_V.subset (graphUnion_le hL'_le_G hΓ_le_G).vertexSet_mono)
  have hV_le2 : V(graphUnion L' c.Γ_emb).ncard ≤ V(graphUnion c.L c.Γ_emb).ncard :=
    Set.ncard_le_ncard hL'Γ_le_LΓ.vertexSet_mono
      (c.hJ.finite_V.subset hLΓ_le_G.vertexSet_mono)
  have hE_le1 : E(graphUnion c'.L c.Γ_emb).ncard ≤ E(graphUnion L' c.Γ_emb).ncard :=
    Set.ncard_le_ncard hc'LΓ_le_L'Γ.edgeSet_mono
      (c.hJ.finite_E.subset (graphUnion_le hL'_le_G hΓ_le_G).edgeSet_mono)
  have hE_le2 : E(graphUnion L' c.Γ_emb).ncard ≤ E(graphUnion c.L c.Γ_emb).ncard :=
    Set.ncard_le_ncard hL'Γ_le_LΓ.edgeSet_mono
      (c.hJ.finite_E.subset hLΓ_le_G.edgeSet_mono)
  have hV_eq : V(graphUnion L' c.Γ_emb) = V(graphUnion c.L c.Γ_emb) :=
    Set.eq_of_subset_of_ncard_le hL'Γ_le_LΓ.vertexSet_mono (by omega)
      (c.hJ.finite_V.subset hLΓ_le_G.vertexSet_mono)
  have hE_eq : E(graphUnion L' c.Γ_emb) = E(graphUnion c.L c.Γ_emb) :=
    Set.eq_of_subset_of_ncard_le hL'Γ_le_LΓ.edgeSet_mono (by omega)
      (c.hJ.finite_E.subset hLΓ_le_G.edgeSet_mono)
  have hUnion_eq : graphUnion L' c.Γ_emb = graphUnion c.L c.Γ_emb :=
    (Compatible.of_le_le (graphUnion_le hL'_le_G hΓ_le_G) hLΓ_le_G).ext hV_eq hE_eq
  refine ⟨hUnion_eq, fun hL'_sub_L => ?_⟩
  have hm2_eq : c'.measure2 = c.measure2 := by
    unfold ValidConfig74.measure2
    rw [hc'Γ]
    omega
  have hm3_le : c.measure3 ≤ c'.measure3 := hc_ext.2.2 c' rfl hm2_eq
  unfold ValidConfig74.measure3 at hm3_le
  have hVL_le1 : V(c'.L).ncard ≤ V(L').ncard :=
    Set.ncard_le_ncard hc'L_le_L'.vertexSet_mono (c.hJ.finite_V.subset hL'_le_G.vertexSet_mono)
  have hVL_le2 : V(L').ncard ≤ V(c.L).ncard :=
    Set.ncard_le_ncard hL'_sub_L.vertexSet_mono (c.hJ.finite_V.subset hL_le_G.vertexSet_mono)
  have hEL_le1 : E(c'.L).ncard ≤ E(L').ncard :=
    Set.ncard_le_ncard hc'L_le_L'.edgeSet_mono (c.hJ.finite_E.subset hL'_le_G.edgeSet_mono)
  have hEL_le2 : E(L').ncard ≤ E(c.L).ncard :=
    Set.ncard_le_ncard hL'_sub_L.edgeSet_mono (c.hJ.finite_E.subset hL_le_G.edgeSet_mono)
  have hVL_eq : V(L') = V(c.L) :=
    Set.eq_of_subset_of_ncard_le hL'_sub_L.vertexSet_mono (by omega)
      (c.hJ.finite_V.subset hL_le_G.vertexSet_mono)
  have hEL_eq : E(L') = E(c.L) :=
    Set.eq_of_subset_of_ncard_le hL'_sub_L.edgeSet_mono (by omega)
      (c.hJ.finite_E.subset hL_le_G.edgeSet_mono)
  exact (Compatible.of_le_le hL'_le_G hL_le_G).ext hVL_eq hEL_eq

/-! ## 2. Proof of Claim (6) (page 554) -/

/-- **Graph Minors XXII, (7.4) Claim (6)** (page 554):
"(6) *$L$ is a forest, and every vertex of $L$ with degree at most 1 belongs to $Z$.*" -/
theorem lemma_7_4_claim_6
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal)
    {Z : Set α}
    (hBasis : IsModelBasis R_G R_H c.φV c.φE Z)
    (hZ_sub : Z ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph ℬ))) :
    IsGraphForest c.L ∧ ∀ v ∈ V(c.L), vertexValency c.L v ≤ 1 → v ∈ Z := by
  have hφ_le_G : ∀ P ∈ c.φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩
    exact c.hJ.isModel.subgraph_of_mem v hv
  have hL_le_G : c.L ≤ R_G.G.toGraph := subgraphSUnion_le hφ_le_G
  have hEL_fin : E(c.L).Finite := c.hJ.finite_E.subset hL_le_G.edgeSet_mono
  have hL_disj_φE : Disjoint (c.φE '' E(R_H.G.toGraph)) E(c.L) := by
    rw [Set.disjoint_left]
    rintro _ ⟨eH, heH, rfl⟩ heL
    rw [ValidConfig74.L, edgeSet_subgraphSUnion hφ_le_G, mem_iUnion₂] at heL
    rcases heL with ⟨_, ⟨v, hv, rfl⟩, he_φv⟩
    exact c.hJ.isModel.edge_not_mem_φV eH heH v hv he_φv
  have hvit : IsVitalFor c.L c.L (Z ∩ V(c.L)) := by
    refine ⟨le_rfl, inter_subset_right, fun L' hL'L heff => ?_⟩
    have hL'_le_LΓ : L' ≤ graphUnion c.L c.Γ_emb :=
      hL'L.trans (le_graphUnion_left c.L c.Γ_emb)
    have hL'_disj : Disjoint (c.φE '' E(R_H.G.toGraph)) E(L') :=
      hL_disj_φE.mono_right hL'L.edgeSet_mono
    have heff_Z : effectOn L' Z = effectOn c.L Z := by
      rw [effectOn_eq_iff_areConnectedIn] at heff ⊢
      intro u hu v hv
      by_cases huL : u ∈ V(c.L) <;> by_cases hvL : v ∈ V(c.L)
      · exact heff u ⟨hu, huL⟩ v ⟨hv, hvL⟩
      · constructor <;> intro hconn
        · exact (hvL (hL'L.vertexSet_mono hconn.right_mem)).elim
        · exact (hvL hconn.right_mem).elim
      · constructor <;> intro hconn
        · exact (huL (hL'L.vertexSet_mono hconn.left_mem)).elim
        · exact (huL hconn.left_mem).elim
      · constructor <;> intro hconn
        · exact (huL (hL'L.vertexSet_mono hconn.left_mem)).elim
        · exact (huL hconn.left_mem).elim
    exact (lemma_7_4_claim_5 c hc_ext hBasis hZ_sub hL'_le_LΓ hL'_disj heff_Z).2 hL'L
  have h22 := theorem_2_2_proof hEL_fin inter_subset_right hvit
  refine ⟨h22.1, fun v hvL hval => ?_⟩
  by_contra hvZ
  have h2 := h22.2.2 v ⟨hvL, fun h => hvZ h.1⟩
  omega

/-! ## 3. Separation $(A, B)$ of $G$ for $A \in \mathcal{A}$ with $A \cap K = N_W$ -/

/-- Under `(J1)`–`(J6)`, for any $A \in \mathcal{A}$ with $A \cap K = N_W$, there is a subgraph
$B \le G$ such that $(A, B)$ is a separation of $G$, $V(A) \cap V(B) = \bar{\pi}(A) \cup W$,
$K \le B$, and $A' \le B$ for all $A' \in \mathcal{A}$ with $A' \ne A$. -/
theorem exists_separation_of_mem_𝒜 {q : ℕ}
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
    {A : Graph α β} (hA : A ∈ 𝒜) (hAK : A ⊓ K = Graph.noEdge W β) :
    let πBar := ιV '' Set.range (πS A)
    ∃ B ≤ R_G.G.toGraph,
      IsGraphSeparation R_G.G.toGraph A B ∧
      V(A) ∩ V(B) = πBar ∪ W ∧
      K ≤ B ∧
      ∀ A' ∈ 𝒜, A' ≠ A → A' ≤ B := by
  intro πBar
  let G := R_G.G.toGraph
  let S_A := πBar ∪ W
  have hA_le : A ≤ G := hJ.le_of_mem_𝒜 A hA
  have hπ_sub : πBar ⊆ V(A) := fun x hx => (hJ.image_range_πS_subset hA hx).1
  have hW_sub : W ⊆ V(A) := hJ.W_subset_V A hA
  have hSA_sub_A : S_A ⊆ V(A) := union_subset hπ_sub hW_sub
  have hSA_sub_G : S_A ⊆ V(G) := hSA_sub_A.trans hA_le.vertexSet_mono
  -- Any link of `G` whose edge is not in `E(A)` has both endpoints outside `V(A) \ S_A`.
  have hlink_not_int : ∀ {e x y}, G.IsLink e x y → e ∉ E(A) → x ∈ V(A) → x ∈ S_A := by
    intro e x y hl heA hxA
    have heG : e ∈ E(G) := hl.edge_mem
    have heNK : e ∈ E(N) ∪ E(K) := hJ.sep_NK.1.2.2.2.1.symm ▸ heG
    rcases heNK with heN | heK
    · rw [hJ.N_eq, edgeSet_graphUnion, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
        edgeSet_subgraphSUnion hJ.le_of_mem_𝒜] at heN
      rcases heN with heΓ | heU
      · have hΓ_le_G : Γ.toEmbeddedGraph ιV ιE ≤ G := hJ.Γ_le.trans Graph.deleteVerts_le
        have hlΓ : (Γ.toEmbeddedGraph ιV ιE).IsLink e x y := (hΓ_le_G.isLink_iff heΓ).mpr hl
        rcases hlΓ with ⟨e₀, x₀, y₀, hl₀, rfl, hxx₀, rfl⟩
        have hx₀_V : x₀ ∈ Γ.V := hl₀.left_mem
        have he₀_E : e₀ ∈ Γ.E := hl₀.edge_mem
        have hx_inter : ιV x₀ ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A) := ⟨⟨x₀, hx₀_V, rfl⟩, hxx₀.symm ▸ hxA⟩
        rw [← hJ.Γ_inter_D A hA] at hx_inter
        rcases hx_inter with ⟨x₁, hx₁, hxx₁⟩
        rw [ιV.injective hxx₁] at hx₁
        have hx₀_D : x₀ ∈ D A :=
          ((mem_interSet_V_iff (hJ.disc_D A hA).1.isCompact.isClosed).mp hx₁).2
        have he₀_not_D : ¬ (e₀ ⊆ D A) := by
          intro he₀D
          have he₀_inter : e₀ ∈ (Γ.interSet (D A)).E :=
            GM11.mem_interSet_E_iff.mpr ⟨he₀_E, he₀D⟩
          have he_inter : ιE e₀ ∈ E((Γ.interSet (D A)).toEmbeddedGraph ιV ιE) :=
            ⟨e₀, he₀_inter, rfl⟩
          rw [hJ.Γ_inter_D A hA] at he_inter
          exact heA ((inf_le_right (a := Γ.toEmbeddedGraph ιV ιE)).edgeSet_mono he_inter)
        have he₀_pre : IsPreconnected e₀ :=
          (GM11.PaintingOrDrawing.edge_props (Γ := PaintingOrDrawing.drawing Γ) he₀_E).1
        have hNorm : Γ.IsNormal (subBd (D A)) := (hJ.disc_D A hA).2.1
        have he₀_disj_fr : Disjoint e₀ (frontier (D A)) := by
          rw [← GM11.subBd_eq_frontier]
          exact disjoint_left.mpr fun z hze hzbd =>
            (he₀_E.2.1 hze).2 (hNorm ⟨hzbd, (he₀_E.2.1 hze).1⟩)
        have he₀_sub_compl : e₀ ⊆ Set.univ \ D A := by
          intro z hze
          refine ⟨mem_univ z, fun hzD => he₀_not_D ?_⟩
          exact GM12.subset_of_disjoint_frontier he₀_pre
            (hJ.disc_D A hA).1.isCompact.isClosed he₀_disj_fr hze hzD
        have hx₀_cl_e₀ : x₀ ∈ closure e₀ :=
          ((by rw [hl₀.2.2.2]; exact Set.mem_insert x₀ {y₀} : x₀ ∈ closure e₀ ∩ Γ.V)).1
        have hx₀_bd : x₀ ∈ subBd (D A) :=
          ⟨subset_closure hx₀_D, closure_mono he₀_sub_compl hx₀_cl_e₀⟩
        have hx₀_G : ιV x₀ ∈ V(R_G.G.toGraph) := hxx₀ ▸ hA_le.vertexSet_mono hxA
        have hx₀_π : x₀ ∈ Set.range (πS A) := by
          rw [hJ.π_bar_eq_bd_inter A hA]
          exact ⟨hx₀_bd, hx₀_G⟩
        exact Or.inl ⟨x₀, hx₀_π, hxx₀⟩
      · obtain ⟨A', hA', heA'⟩ := mem_iUnion₂.mp heU
        have hne : A ≠ A' := fun h => heA (h ▸ heA')
        have hlA' : A'.IsLink e x y := ((hJ.le_of_mem_𝒜 A' hA').isLink_iff heA').mpr hl
        have hx_inter : x ∈ V(A) ∩ V(A') := ⟨hxA, hlA'.left_mem⟩
        rw [hJ.vertex_inter_𝒜 A hA A' hA' hne] at hx_inter
        rcases hx_inter with ⟨hxπ, _⟩ | hxW
        · exact Or.inl hxπ
        · exact Or.inr hxW
    · have hlK : K.IsLink e x y := (hJ.sep_NK.1.2.1.isLink_iff heK).mpr hl
      have hx_inter : x ∈ V(A ⊓ K) := ⟨hxA, hlK.left_mem⟩
      rw [hAK, Graph.vertexSet_noEdge] at hx_inter
      exact Or.inr hx_inter
  let B₀ := (G.deleteEdges E(A)).deleteVerts (V(A) \ S_A)
  let B := graphUnion B₀ (Graph.noEdge S_A β)
  have hB₀_le : B₀ ≤ G := Graph.deleteVerts_le.trans Graph.deleteEdges_le
  have hno_le : Graph.noEdge S_A β ≤ G := Graph.noEdge_le_iff.mpr hSA_sub_G
  have hB_le : B ≤ G := graphUnion_le hB₀_le hno_le
  have hVB : V(B) = (V(G) \ (V(A) \ S_A)) ∪ S_A := by
    rw [vertexSet_graphUnion, Graph.vertexSet_deleteVerts, Graph.vertexSet_deleteEdges,
      Graph.vertexSet_noEdge]
  have hEB : E(B) = E(G) \ E(A) := by
    ext e
    rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
    constructor
    · intro heB₀
      obtain ⟨x, y, hlB₀⟩ := B₀.exists_isLink_of_mem_edgeSet heB₀
      rw [Graph.deleteVerts_isLink, Graph.deleteEdges_isLink] at hlB₀
      exact ⟨hlB₀.1.1.edge_mem, hlB₀.1.2⟩
    · rintro ⟨heG, heA⟩
      obtain ⟨x, y, hlG⟩ := G.exists_isLink_of_mem_edgeSet heG
      have hlB₀ : B₀.IsLink e x y := by
        rw [Graph.deleteVerts_isLink, Graph.deleteEdges_isLink]
        exact ⟨⟨hlG, heA⟩, fun hx => hx.2 (hlink_not_int hlG heA hx.1),
          fun hy => hy.2 (hlink_not_int hlG.symm heA hy.1)⟩
      exact hlB₀.edge_mem
  refine ⟨B, hB_le, ?_, ?_, ?_, ?_⟩
  · refine ⟨hA_le, hB_le, ?_, ?_, ?_⟩
    · ext x
      rw [mem_union, hVB, mem_union, mem_sdiff, mem_sdiff]
      have hx_imp : x ∈ V(A) → x ∈ V(G) := fun h => hA_le.vertexSet_mono h
      have hS_imp : x ∈ S_A → x ∈ V(G) := fun h => hSA_sub_G h
      tauto
    · ext e
      rw [mem_union, hEB, mem_sdiff]
      have he_imp : e ∈ E(A) → e ∈ E(G) := fun h => hA_le.edgeSet_mono h
      tauto
    · rw [hEB]
      exact disjoint_sdiff_self_right
  · ext x
    rw [mem_inter_iff, hVB, mem_union, mem_sdiff, mem_sdiff]
    exact ⟨fun ⟨hxA, h⟩ => h.elim (fun ⟨_, hnot⟩ => by_contra fun hn => hnot ⟨hxA, hn⟩) id,
      fun hxS => ⟨hSA_sub_A hxS, Or.inr hxS⟩⟩
  · rw [(Compatible.of_le_le hJ.sep_NK.1.2.1 hB_le).le_iff]
    refine ⟨?_, ?_⟩
    · intro x hxK
      rw [hVB]
      by_cases hxA : x ∈ V(A)
      · have hx_AK : x ∈ V(A ⊓ K) := ⟨hxA, hxK⟩
        rw [hAK, Graph.vertexSet_noEdge] at hx_AK
        exact Or.inr (Or.inr hx_AK)
      · exact Or.inl ⟨hJ.sep_NK.1.2.1.vertexSet_mono hxK, fun h => hxA h.1⟩
    · intro e heK
      rw [hEB]
      refine ⟨hJ.sep_NK.1.2.1.edgeSet_mono heK, fun heA => ?_⟩
      obtain ⟨x, y, hlA⟩ := A.exists_isLink_of_mem_edgeSet heA
      have hlG : G.IsLink e x y := hlA.mono hA_le
      have hlK : K.IsLink e x y := (hJ.sep_NK.1.2.1.isLink_iff heK).mpr hlG
      have hlAK : (A ⊓ K).IsLink e x y := ⟨hlA, hlK⟩
      rw [hAK, Graph.noEdge_isLink] at hlAK
      exact hlAK
  · intro A' hA' hne
    have hA'_le : A' ≤ G := hJ.le_of_mem_𝒜 A' hA'
    rw [(Compatible.of_le_le hA'_le hB_le).le_iff]
    refine ⟨?_, ?_⟩
    · intro x hxA'
      rw [hVB]
      by_cases hxA : x ∈ V(A)
      · have hx_inter : x ∈ V(A) ∩ V(A') := ⟨hxA, hxA'⟩
        rw [hJ.vertex_inter_𝒜 A hA A' hA' (Ne.symm hne)] at hx_inter
        rcases hx_inter with ⟨hxπ, _⟩ | hxW
        · exact Or.inr (Or.inl hxπ)
        · exact Or.inr (Or.inr hxW)
      · exact Or.inl ⟨hA'_le.vertexSet_mono hxA', fun h => hxA h.1⟩
    · intro e heA'
      rw [hEB]
      exact ⟨hA'_le.edgeSet_mono heA',
        Set.disjoint_right.mp (hJ.edge_disjoint_𝒜 A hA A' hA' (Ne.symm hne)) heA'⟩

/-! ## 4. Realizing the Effect of $L \cap A$ on $\bar{\pi}(A) \cup W$ when $A$ is Good -/

/-- If `P` is a path in `GA` with ends `u, v` and no internal vertex in `πBar`, and
`Disjoint V(GA) W`, then `V(P) ∩ (πBar ∪ W) ⊆ {u, v}`. -/
private theorem path_vertexSet_inter_subset_ends
    {GA P : Graph α β} {u v : α} {πBar W : Set α}
    (hP : IsGraphPathWithEnds GA P u v)
    (hInt : Disjoint (pathInternalVerts GA P) πBar)
    (hDisjW : Disjoint V(GA) W) :
    V(P) ∩ (πBar ∪ W) ⊆ {u, v} := by
  rintro x ⟨hxP, hxπ | hxW⟩
  · by_cases hxe : x ∈ pathEnds GA P
    · exact IsGraphPathWithEnds.pathEnds_subset_pair hP hxe
    · exact False.elim (Set.disjoint_left.mp hInt ⟨hxP, hxe⟩ hxπ)
  · exact False.elim (Set.disjoint_left.mp hDisjW (hP.1.vertexSet_mono hxP) hxW)

/-- Under `(J1)`–`(J6)`, if $A \in \mathcal{A}$ is a good member and $M \le A$ is a subgraph such
that no edge of $M$ is incident with a vertex in $W$, then there is a subgraph
$L' \le (\Gamma \cap A) \cup N_W$ such that $L' \le \Gamma \cup M$, $E(L') \subseteq E(\Gamma \cap A)$,
and `effectOn L' (πBar ∪ W) = effectOn M (πBar ∪ W)`. -/
theorem exists_subgraph_same_effect_of_isGoodMember {q : ℕ}
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
    {M : Graph α β} (hMA : M ≤ A)
    (hM_no_W : ∀ e ∈ E(M), ∀ w ∈ W, ¬ M.Inc e w) :
    let GA := (Γ.toEmbeddedGraph ιV ιE) ⊓ A
    let πBar := ιV '' Set.range (πS A)
    ∃ L' ≤ graphUnion GA (Graph.noEdge W β),
      L' ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE) M ∧
      E(L') ⊆ E(GA) ∧
      effectOn L' (πBar ∪ W) = effectOn M (πBar ∪ W) := by
  intro GA πBar
  let S_A := πBar ∪ W
  let V₀ := V(M) ∩ S_A
  have hΓ_le_G : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph :=
    hJ.Γ_le.trans Graph.deleteVerts_le
  have hA_le_G : A ≤ R_G.G.toGraph := hJ.le_of_mem_𝒜 A hA
  have hGA_le_G : GA ≤ R_G.G.toGraph := inf_le_left.trans hΓ_le_G
  have hGA_disj_W : Disjoint V(GA) W := by
    rw [Set.disjoint_left]
    rintro x ⟨hxΓ, _⟩ hxW
    have hx_del := hJ.Γ_le.vertexSet_mono hxΓ
    rw [Graph.vertexSet_deleteVerts] at hx_del
    exact hx_del.2 hxW
  have hπ_sub_VGA : πBar ⊆ V(GA) := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨⟨s, hGood.1 hs, rfl⟩, (hJ.image_range_πS_subset hA ⟨s, hs, rfl⟩).1⟩
  have hV₀_sub_GAW : V₀ ⊆ V(graphUnion GA (Graph.noEdge W β)) := by
    rintro x ⟨_, hxπ | hxW⟩
    · exact Or.inl (hπ_sub_VGA hxπ)
    · exact Or.inr hxW
  have hV₀_sub_ΓM : V₀ ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) M) :=
    fun _ hx => Or.inr hx.1
  -- In `M`, no vertex in `W` is connected to any other vertex.
  have hM_conn_W : ∀ {x y}, AreConnectedIn M x y → (x ∈ W ∨ y ∈ W) → x = y ∧ x ∈ V(M) := by
    intro x y hconn hxyW
    have hstep : ∀ {a b} (P : GraphWalk M a b), a ∈ W → a = b := by
      intro a b P haW
      cases P with
      | nil _ => rfl
      | @cons _ m _ e hl _ =>
        exact False.elim (hM_no_W e hl.edge_mem a haW ⟨m, hl⟩)
    rcases hxyW with hxW | hyW
    · rw [areConnectedIn_iff_walk] at hconn
      rcases hconn with ⟨hxM, _, ⟨P⟩⟩
      exact ⟨hstep P hxW, hxM⟩
    · have hsymm := hconn.symm
      rw [areConnectedIn_iff_walk] at hsymm
      rcases hsymm with ⟨hyM, hxM, ⟨P⟩⟩
      have heq := hstep P hyW
      exact ⟨heq.symm, hxM⟩
  -- Split into three cases according to the `M`-connectivity relation on `πBar ∩ V(M)`.
  by_cases hPair : ∃ u ∈ πBar, ∃ v ∈ πBar, u ≠ v ∧ AreConnectedIn M u v
  · rcases hPair with ⟨u₀, hu₀_π, v₀, hv₀_π, huv₀, hconn_uv₀⟩
    have hu₀_V₀ : u₀ ∈ V₀ := ⟨hconn_uv₀.left_mem, Or.inl hu₀_π⟩
    have hv₀_V₀ : v₀ ∈ V₀ := ⟨hconn_uv₀.right_mem, Or.inl hv₀_π⟩
    by_cases hThird : ∃ w ∈ πBar ∩ V(M), ¬ AreConnectedIn M u₀ w
    · -- Case 3: `πBar = {u₀, v₀, w₀}` and only `{u₀, v₀}` are `M`-connected.
      rcases hThird with ⟨w₀, ⟨hw₀_π, hw₀_M⟩, hnot_uw₀⟩
      have hnot_vw₀ : ¬ AreConnectedIn M v₀ w₀ :=
        fun hvw => hnot_uw₀ (hconn_uv₀.trans hvw)
      have hcard_π : πBar.ncard ≤ 3 := by
        rw [(hJ.range_πS_subset_D_and_ncard hA).2.2.2]
        exact (hJ.π_valid A hA).2.1
      have huw₀ : u₀ ≠ w₀ := fun h => hnot_uw₀ (h ▸ areConnectedIn_self_iff.mpr hu₀_V₀.1)
      have hvw₀ : v₀ ≠ w₀ := fun h => hnot_vw₀ (h ▸ areConnectedIn_self_iff.mpr hv₀_V₀.1)
      have htriple_sub : ({u₀, v₀, w₀} : Set α) ⊆ πBar := by
        rintro x (rfl | rfl | rfl)
        · exact hu₀_π
        · exact hv₀_π
        · exact hw₀_π
      have htriple_card : ({u₀, v₀, w₀} : Set α).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hvw₀]
        simp [huv₀, huw₀]
      have hπ_eq_triple : πBar = {u₀, v₀, w₀} :=
        (Set.eq_of_subset_of_ncard_le htriple_sub (by omega)
          ((Set.finite_range (πS A)).image ιV)).symm
      obtain ⟨P, hP_path, hP_int⟩ := hGood.2 u₀ hu₀_π v₀ hv₀_π
      let L' := graphUnion P (Graph.noEdge V₀ β)
      have hP_le_GA : P ≤ GA := hP_path.1
      have hP_le_G : P ≤ R_G.G.toGraph := hP_le_GA.trans hGA_le_G
      have hno_le_G : Graph.noEdge V₀ β ≤ R_G.G.toGraph :=
        Graph.noEdge_le_iff.mpr (inter_subset_left.trans (hMA.trans hA_le_G).vertexSet_mono)
      have hL'_le_G : L' ≤ R_G.G.toGraph := graphUnion_le hP_le_G hno_le_G
      have hP_SA : V(P) ∩ S_A ⊆ {u₀, v₀} :=
        path_vertexSet_inter_subset_ends hP_path hP_int hGA_disj_W
      have hVL'_SA : V(L') ∩ S_A = V₀ := by
        ext x
        rw [vertexSet_graphUnion, Graph.vertexSet_noEdge, union_inter_distrib_right]
        constructor
        · rintro (hxP | ⟨hxV₀, _⟩)
          · rcases hP_SA hxP with rfl | rfl
            · exact hu₀_V₀
            · exact hv₀_V₀
          · exact hxV₀
        · intro hxV₀
          exact Or.inr ⟨hxV₀, hxV₀.2⟩
      refine ⟨L', ?_, ?_, ?_, ?_⟩
      · rw [(Compatible.of_le_le hL'_le_G
          (graphUnion_le hGA_le_G
            (Graph.noEdge_le_iff.mpr (hJ.sep_NK.2.trans
              (inter_subset_left.trans hJ.sep_NK.1.1.vertexSet_mono))))).le_iff]
        refine ⟨union_subset (hP_le_GA.vertexSet_mono.trans subset_union_left) hV₀_sub_GAW, ?_⟩
        rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty, edgeSet_graphUnion,
          Graph.edgeSet_noEdge, union_empty]
        exact hP_le_GA.edgeSet_mono
      · rw [(Compatible.of_le_le hL'_le_G
          (graphUnion_le hΓ_le_G (hMA.trans hA_le_G))).le_iff]
        refine ⟨union_subset ((hP_le_GA.trans inf_le_left).vertexSet_mono.trans subset_union_left)
          hV₀_sub_ΓM, ?_⟩
        rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty, edgeSet_graphUnion]
        exact (hP_le_GA.trans inf_le_left).edgeSet_mono.trans subset_union_left
      · rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
        exact hP_le_GA.edgeSet_mono
      · rw [effectOn_eq_iff_areConnectedIn]
        intro x hxSA y hySA
        constructor
        · intro hconnL'
          have hxV₀ : x ∈ V₀ := hVL'_SA ▸ ⟨hconnL'.left_mem, hxSA⟩
          have hyV₀ : y ∈ V₀ := hVL'_SA ▸ ⟨hconnL'.right_mem, hySA⟩
          by_cases hxy : x = y
          · subst hxy
            exact areConnectedIn_self_iff.mpr hxV₀.1
          · rw [areConnectedIn_iff_walk] at hconnL'
            rcases hconnL' with ⟨_, _, ⟨W_L'⟩⟩
            cases W_L' with
            | nil _ => exact (hxy rfl).elim
            | @cons _ m _ e hl rest =>
              have hlP : P.IsLink e x m := by
                rcases hl with hlP | ⟨_, hlno⟩
                · exact hlP
                · simp at hlno
              have hxP : x ∈ V(P) ∩ S_A := ⟨hlP.left_mem, hxSA⟩
              have hyP : y ∈ V(P) ∩ S_A := by
                have hy_end : ∀ {a b} (Q : GraphWalk L' a b), a ∈ V(P) → b ∈ V(P) := by
                  intro a b Q
                  induction Q with
                  | nil _ => exact id
                  | @cons _ m' _ f hlf rest' ih =>
                    intro _
                    apply ih
                    rcases hlf with hlfP | ⟨_, hlfno⟩
                    · exact hlfP.right_mem
                    · simp at hlfno
                exact ⟨hy_end rest hlP.right_mem, hySA⟩
              rcases hP_SA hxP with rfl | rfl <;> rcases hP_SA hyP with rfl | rfl
              · exact (hxy rfl).elim
              · exact hconn_uv₀
              · exact hconn_uv₀.symm
              · exact (hxy rfl).elim
        · intro hconnM
          have hxV₀ : x ∈ V₀ := ⟨hconnM.left_mem, hxSA⟩
          have hyV₀ : y ∈ V₀ := ⟨hconnM.right_mem, hySA⟩
          by_cases hxy : x = y
          · subst hxy
            exact areConnectedIn_self_iff.mpr (Or.inr hxV₀)
          · have hx_not_W : x ∉ W := fun hxW => hxy (hM_conn_W hconnM (Or.inl hxW)).1
            have hy_not_W : y ∉ W := fun hyW => hxy (hM_conn_W hconnM (Or.inr hyW)).1
            have hx_π : x ∈ πBar := hxSA.resolve_right hx_not_W
            have hy_π : y ∈ πBar := hySA.resolve_right hy_not_W
            rw [hπ_eq_triple] at hx_π hy_π
            have hP_conn : AreConnectedIn L' u₀ v₀ := by
              obtain ⟨_, W_P, _, hVP, _⟩ := hP_path
              have hu₀P : u₀ ∈ V(P) := hVP ▸ W_P.start_mem_support
              have hv₀P : v₀ ∈ V(P) := hVP ▸ W_P.end_mem_support
              have hconnP : AreConnectedIn P u₀ v₀ :=
                areConnectedIn_iff_walk.mpr ⟨hu₀P, hv₀P, ⟨W_P⟩⟩
              exact hconnP.mono (le_graphUnion_left P _)
            rcases hx_π with rfl | rfl | rfl <;> rcases hy_π with rfl | rfl | rfl
            · exact (hxy rfl).elim
            · exact hP_conn
            · exact False.elim (hnot_uw₀ hconnM)
            · exact hP_conn.symm
            · exact (hxy rfl).elim
            · exact False.elim (hnot_vw₀ hconnM)
            · exact False.elim (hnot_uw₀ hconnM.symm)
            · exact False.elim (hnot_vw₀ hconnM.symm)
            · exact (hxy rfl).elim
    · -- Case 2: Every vertex in `πBar ∩ V(M)` is `M`-connected to `u₀`.
      push Not at hThird
      have hchoose_P : ∀ v ∈ πBar ∩ V(M),
          ∃ P : Graph α β, IsGraphPathWithEnds GA P u₀ v ∧
            Disjoint (pathInternalVerts GA P) πBar :=
        fun v hv => hGood.2 u₀ hu₀_π v hv.1
      choose P_of hP_of using hchoose_P
      let P_set : Set (Graph α β) :=
        {Q | ∃ (v : α) (hv : v ∈ πBar ∩ V(M)), Q = P_of v hv}
      have hP_set_le_GA : ∀ Q ∈ P_set, Q ≤ GA := by
        rintro _ ⟨v, hv, rfl⟩
        exact (hP_of v hv).1.1
      have hP_set_le_G : ∀ Q ∈ P_set, Q ≤ R_G.G.toGraph :=
        fun Q hQ => (hP_set_le_GA Q hQ).trans hGA_le_G
      let L'_paths := subgraphSUnion R_G.G.toGraph P_set
      let L' := graphUnion L'_paths (Graph.noEdge V₀ β)
      have hno_le_G : Graph.noEdge V₀ β ≤ R_G.G.toGraph :=
        Graph.noEdge_le_iff.mpr (inter_subset_left.trans (hMA.trans hA_le_G).vertexSet_mono)
      have hL'_le_G : L' ≤ R_G.G.toGraph :=
        graphUnion_le (subgraphSUnion_le hP_set_le_G) hno_le_G
      have hVL'_SA : V(L') ∩ S_A = V₀ := by
        ext x
        rw [vertexSet_graphUnion, vertexSet_subgraphSUnion, Graph.vertexSet_noEdge,
          union_inter_distrib_right]
        constructor
        · rintro (⟨hx_un, hxSA⟩ | ⟨hxV₀, _⟩)
          · obtain ⟨_, ⟨v, hv, rfl⟩, hxP⟩ := mem_iUnion₂.mp hx_un
            have hsub := path_vertexSet_inter_subset_ends (hP_of v hv).1 (hP_of v hv).2 hGA_disj_W
            rcases hsub ⟨hxP, hxSA⟩ with rfl | rfl
            · exact hu₀_V₀
            · exact ⟨hv.2, Or.inl hv.1⟩
          · exact hxV₀
        · intro hxV₀
          exact Or.inr ⟨hxV₀, hxV₀.2⟩
      refine ⟨L', ?_, ?_, ?_, ?_⟩
      · rw [(Compatible.of_le_le hL'_le_G
          (graphUnion_le hGA_le_G
            (Graph.noEdge_le_iff.mpr (hJ.sep_NK.2.trans
              (inter_subset_left.trans hJ.sep_NK.1.1.vertexSet_mono))))).le_iff]
        refine ⟨union_subset ?_ hV₀_sub_GAW, ?_⟩
        · rw [vertexSet_subgraphSUnion]
          exact iUnion₂_subset fun Q hQ => (hP_set_le_GA Q hQ).vertexSet_mono.trans subset_union_left
        · rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
            edgeSet_subgraphSUnion hP_set_le_G, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
          exact iUnion₂_subset fun Q hQ => (hP_set_le_GA Q hQ).edgeSet_mono
      · rw [(Compatible.of_le_le hL'_le_G
          (graphUnion_le hΓ_le_G (hMA.trans hA_le_G))).le_iff]
        refine ⟨union_subset ?_ hV₀_sub_ΓM, ?_⟩
        · rw [vertexSet_subgraphSUnion]
          exact iUnion₂_subset fun Q hQ =>
            ((hP_set_le_GA Q hQ).trans inf_le_left).vertexSet_mono.trans subset_union_left
        · rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
            edgeSet_subgraphSUnion hP_set_le_G, edgeSet_graphUnion]
          exact iUnion₂_subset fun Q hQ =>
            ((hP_set_le_GA Q hQ).trans inf_le_left).edgeSet_mono.trans subset_union_left
      · rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
          edgeSet_subgraphSUnion hP_set_le_G]
        exact iUnion₂_subset fun Q hQ => (hP_set_le_GA Q hQ).edgeSet_mono
      · rw [effectOn_eq_iff_areConnectedIn]
        intro x hxSA y hySA
        constructor
        · intro hconnL'
          have hxV₀ : x ∈ V₀ := hVL'_SA ▸ ⟨hconnL'.left_mem, hxSA⟩
          have hyV₀ : y ∈ V₀ := hVL'_SA ▸ ⟨hconnL'.right_mem, hySA⟩
          by_cases hxy : x = y
          · subst hxy
            exact areConnectedIn_self_iff.mpr hxV₀.1
          · -- Any non-trivial walk in `L'` starts with an edge in `L'_paths`, so `x, y ∈ V(L'_paths) ∩ S_A ⊆ πBar ∩ V(M)`.
            rw [areConnectedIn_iff_walk] at hconnL'
            rcases hconnL' with ⟨_, _, ⟨W_L'⟩⟩
            cases W_L' with
            | nil _ => exact (hxy rfl).elim
            | @cons _ m _ e hl rest =>
              have hl_paths : L'_paths.IsLink e x m := by
                rcases hl with hlp | ⟨_, hlno⟩
                · exact hlp
                · simp at hlno
              have hx_paths : x ∈ V(L'_paths) := hl_paths.left_mem
              have hy_paths : y ∈ V(L'_paths) := by
                have hy_end : ∀ {a b} (Q : GraphWalk L' a b), a ∈ V(L'_paths) → b ∈ V(L'_paths) := by
                  intro a b Q
                  induction Q with
                  | nil _ => exact id
                  | @cons _ m' _ f hlf rest' ih =>
                    intro _
                    apply ih
                    rcases hlf with hlfP | ⟨_, hlfno⟩
                    · exact hlfP.right_mem
                    · simp at hlfno
                exact hy_end rest hl_paths.right_mem
              have hpaths_sub_GA : V(L'_paths) ⊆ V(GA) := by
                rw [vertexSet_subgraphSUnion]
                exact iUnion₂_subset fun Q hQ => (hP_set_le_GA Q hQ).vertexSet_mono
              have hx_not_W : x ∉ W := Set.disjoint_left.mp hGA_disj_W (hpaths_sub_GA hx_paths)
              have hy_not_W : y ∉ W := Set.disjoint_left.mp hGA_disj_W (hpaths_sub_GA hy_paths)
              have hx_πM : x ∈ πBar ∩ V(M) := ⟨hxSA.resolve_right hx_not_W, hxV₀.1⟩
              have hy_πM : y ∈ πBar ∩ V(M) := ⟨hySA.resolve_right hy_not_W, hyV₀.1⟩
              exact (hThird x hx_πM).symm.trans (hThird y hy_πM)
        · intro hconnM
          have hxV₀ : x ∈ V₀ := ⟨hconnM.left_mem, hxSA⟩
          have hyV₀ : y ∈ V₀ := ⟨hconnM.right_mem, hySA⟩
          by_cases hxy : x = y
          · subst hxy
            exact areConnectedIn_self_iff.mpr (Or.inr hxV₀)
          · have hx_not_W : x ∉ W := fun hxW => hxy (hM_conn_W hconnM (Or.inl hxW)).1
            have hy_not_W : y ∉ W := fun hyW => hxy (hM_conn_W hconnM (Or.inr hyW)).1
            have hx_πM : x ∈ πBar ∩ V(M) := ⟨hxSA.resolve_right hx_not_W, hxV₀.1⟩
            have hy_πM : y ∈ πBar ∩ V(M) := ⟨hySA.resolve_right hy_not_W, hyV₀.1⟩
            have hconn_u₀ : ∀ v (hv : v ∈ πBar ∩ V(M)), AreConnectedIn L' u₀ v := by
              intro v hv
              obtain ⟨_, W_P, _, hVP, _⟩ := (hP_of v hv).1
              have hu₀P : u₀ ∈ V(P_of v hv) := hVP ▸ W_P.start_mem_support
              have hvP : v ∈ V(P_of v hv) := hVP ▸ W_P.end_mem_support
              have hconnP : AreConnectedIn (P_of v hv) u₀ v :=
                areConnectedIn_iff_walk.mpr ⟨hu₀P, hvP, ⟨W_P⟩⟩
              exact (hconnP.mono (le_subgraphSUnion hP_set_le_G ⟨v, hv, rfl⟩)).mono
                (le_graphUnion_left L'_paths _)
            exact (hconn_u₀ x hx_πM).symm.trans (hconn_u₀ y hy_πM)
  · -- Case 1: No two distinct vertices of `πBar` are `M`-connected.
    push Not at hPair
    let L' := Graph.noEdge V₀ β
    have hno_le_G : L' ≤ R_G.G.toGraph :=
      Graph.noEdge_le_iff.mpr (inter_subset_left.trans (hMA.trans hA_le_G).vertexSet_mono)
    refine ⟨L', ?_, ?_, ?_, ?_⟩
    · exact Graph.noEdge_le_iff.mpr hV₀_sub_GAW
    · exact Graph.noEdge_le_iff.mpr hV₀_sub_ΓM
    · simp [L']
    · rw [effectOn_eq_iff_areConnectedIn]
      intro x hxSA y hySA
      constructor
      · intro hconnL'
        rw [areConnectedIn_iff_walk] at hconnL'
        rcases hconnL' with ⟨hxV₀, _, ⟨W_L'⟩⟩
        cases W_L' with
        | nil _ => exact areConnectedIn_self_iff.mpr hxV₀.1
        | cons hl _ => simp [L'] at hl
      · intro hconnM
        have hxV₀ : x ∈ V₀ := ⟨hconnM.left_mem, hxSA⟩
        by_cases hxy : x = y
        · subst hxy
          exact areConnectedIn_self_iff.mpr hxV₀
        · have hx_not_W : x ∉ W := fun hxW => hxy (hM_conn_W hconnM (Or.inl hxW)).1
          have hy_not_W : y ∉ W := fun hyW => hxy (hM_conn_W hconnM (Or.inr hyW)).1
          have hx_π : x ∈ πBar := hxSA.resolve_right hx_not_W
          have hy_π : y ∈ πBar := hySA.resolve_right hy_not_W
          exact False.elim (hPair x hx_π y hy_π hxy hconnM)

/-! ## 5. Proofs of Claim (7) and Claim (8) (pages 554–555) -/

/-- **Graph Minors XXII, (7.4) Claim (7)** (pages 554–555):
"(7) *If $A \in \mathcal{A} \setminus \mathcal{B}$, then $L \cap A \subseteq \Gamma \cup N_W$.*"
Note: The paper's subproof begins with "Since $A \notin \mathcal{B}$, it follows that
$d(D(A), \Sigma \setminus \Delta) < \theta$." Accordingly, we state Claim (7) with the condition
$d(D(A), \Sigma \setminus \Delta) < \theta$ (which holds for all $A \in \mathcal{A} \setminus \mathcal{B}^*$
where $\mathcal{B}^* = \mathcal{B} \cup \{A \in \mathcal{A} : d(D(A), \Sigma \setminus \Delta) \ge \theta\}$).
The subproof prints "$L' \subseteq (\Gamma \cap A) \cup N_w$", a misprint for $N_W$, which the Lean
uses (see the correction to the proof of (7.4) in `corrections/GM22.md`). -/
theorem lemma_7_4_claim_7
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal)
    {A : Graph α β} (hA : A ∈ 𝒜) (hA_not_ℬ : A ∉ ℬ)
    (hdist : subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ) :
    c.L ⊓ A ≤ graphUnion c.Γ_emb (Graph.noEdge W β) := by
  let G := R_G.G.toGraph
  let πBar := c.ιV '' Set.range (πS A)
  -- Step 1: By Claim (4), `A` is good.
  have hGood : IsGoodMember c.ιV c.ιE c.Γ πLen πS A :=
    lemma_7_4_claim_4 c hc_ext hA hdist
  -- Step 2: No edge of `c.L ⊓ A` is incident with a vertex in `W` (since `A ∉ ℬ`).
  have hφ_le_G : ∀ P ∈ c.φV '' V(R_H.G.toGraph), P ≤ G := by
    rintro _ ⟨v, hv, rfl⟩
    exact c.hJ.isModel.subgraph_of_mem v hv
  have hL_le_G : c.L ≤ G := subgraphSUnion_le hφ_le_G
  have hA_le_G : A ≤ G := c.hJ.le_of_mem_𝒜 A hA
  have hLA_no_W : ∀ e ∈ E(c.L ⊓ A), ∀ w ∈ W, ¬ (c.L ⊓ A).Inc e w := by
    rintro e _ w hwW ⟨y, hlL, hlA⟩
    have heL : e ∈ E(c.L) := hlL.edge_mem
    rw [ValidConfig74.L, edgeSet_subgraphSUnion hφ_le_G, mem_iUnion₂] at heL
    rcases heL with ⟨_, ⟨v, hv, rfl⟩, he_φv⟩
    have hlG : G.IsLink e w y := hlA.mono hA_le_G
    have hl_φv : (c.φV v).IsLink e w y := ((c.hJ.isModel.subgraph_of_mem v hv).isLink_iff he_φv).mpr hlG
    have hl_inter : (A ⊓ c.φV v).IsLink e w y := ⟨hlA, hl_φv⟩
    exact hA_not_ℬ (c.hSuff.mem_of_edge_inc_W v hv A hA ⟨e, hl_inter.edge_mem, w, hwW, y, hl_inter⟩)
  -- Step 3: Obtain `L' ≤ (Γ ⊓ A) ∪ N_W` with the same effect on `πBar ∪ W` as `c.L ⊓ A`.
  obtain ⟨L', hL'_le_GAW, hL'_le_ΓLA, hEL'_sub, heff_L'⟩ :=
    exists_subgraph_same_effect_of_isGoodMember c.hJ hA hGood (inf_le_right (a := c.L)) hLA_no_W
  -- Step 4: Obtain the separation `(A, B)` of `G`.
  have hAK : A ⊓ K = Graph.noEdge W β := by
    by_contra hne
    exact not_le_of_gt hdist (c.hJ.dist_D_of_inter_K A hA hne)
  obtain ⟨B, hB_le_G, hsep_AB, hV_AB, hK_le_B, hA'_le_B⟩ :=
    exists_separation_of_mem_𝒜 c.hJ hA hAK
  -- Step 5: Let `Z = V(K ∪ ⋃_{A' ∈ ℬ} A')`. Then `Z` is a basis for `c.φ` and `Z ⊆ V(B)`.
  let K_ℬ := graphUnion K (subgraphSUnion G ℬ)
  let Z := V(K_ℬ)
  have hBasis : IsModelBasis R_G R_H c.φV c.φE Z := c.hSuff.isModelBasis c.hJ
  have hZ_sub_VB : Z ⊆ V(B) := by
    rintro x (hxK | hxU)
    · exact hK_le_B.vertexSet_mono hxK
    · rw [vertexSet_subgraphSUnion] at hxU
      obtain ⟨A', hA'_ℬ, hxA'⟩ := mem_iUnion₂.mp hxU
      have hne : A' ≠ A := fun h => hA_not_ℬ (h ▸ hA'_ℬ)
      exact (hA'_le_B A' (c.hSuff.subset hA'_ℬ) hne).vertexSet_mono hxA'
  -- Step 6: Apply 2.6 with `Z' = Z ∪ (πBar ∪ W)` to `L_new = L' ∪ (c.L ⊓ B)`.
  let Z' := Z ∪ (πBar ∪ W)
  have hZ'_sub_G : Z' ⊆ V(G) :=
    union_subset (hZ_sub_VB.trans hB_le_G.vertexSet_mono)
      ((hV_AB.symm ▸ inter_subset_left).trans hA_le_G.vertexSet_mono)
  have hAB_sub_Z' : V(A) ∩ V(B) ⊆ Z' := by
    rw [hV_AB]
    exact subset_union_right
  have hZ'_inter_VA : Z' ∩ V(A) = πBar ∪ W := by
    ext x
    constructor
    · rintro ⟨hxZ | hxπW, hxA⟩
      · rw [← hV_AB]
        exact ⟨hxA, hZ_sub_VB hxZ⟩
      · exact hxπW
    · intro hxπW
      have hxAB : x ∈ V(A) ∩ V(B) := by rwa [hV_AB]
      exact ⟨Or.inr hxπW, hxAB.1⟩
  have hΓ_le_G : c.Γ_emb ≤ G := c.hJ.Γ_le.trans Graph.deleteVerts_le
  have hL'_le_G : L' ≤ G :=
    hL'_le_ΓLA.trans (graphUnion_le hΓ_le_G (inf_le_left.trans hL_le_G))
  have hL'_le_A : L' ≤ A := by
    rw [(Compatible.of_le_le hL'_le_G hA_le_G).le_iff]
    refine ⟨?_, hEL'_sub.trans (inf_le_right (a := c.Γ_emb)).edgeSet_mono⟩
    intro x hxL'
    rcases hL'_le_GAW.vertexSet_mono hxL' with ⟨_, hxA⟩ | hxW
    · exact hxA
    · exact c.hJ.W_subset_V A hA hxW
  have hLA_eq : subgraphInter G c.L A = c.L ⊓ A :=
    Graph.ext rfl (fun _ _ _ => subgraphInter_isLink hL_le_G hA_le_G)
  have hLB_eq : subgraphInter G c.L B = c.L ⊓ B :=
    Graph.ext rfl (fun _ _ _ => subgraphInter_isLink hL_le_G hB_le_G)
  have heff_Z' : effectOn L' (Z' ∩ V(A)) = effectOn (subgraphInter G c.L A) (Z' ∩ V(A)) := by
    rw [hZ'_inter_VA, hLA_eq]
    exact heff_L'
  have heff_union_Z' :=
    theorem_2_6_proof hL_le_G hsep_AB hZ'_sub_G hAB_sub_Z' hL'_le_A heff_Z'
  let L_new := subgraphUnion G L' (subgraphInter G c.L B)
  have heff_union_Z : effectOn L_new Z = effectOn c.L Z := by
    rw [effectOn_eq_iff_areConnectedIn] at heff_union_Z' ⊢
    exact fun u hu v hv => heff_union_Z' u (Or.inl hu) v (Or.inl hv)
  -- Step 7: Check `L_new ≤ c.L ∪ c.Γ_emb` and `Disjoint (c.φE '' E(H)) E(L_new)`, then apply Claim (5).
  have hL_new_le_G : L_new ≤ G :=
    subgraphUnion_le hL'_le_G (subgraphInter_le hL_le_G)
  have hL_new_le_LΓ : L_new ≤ graphUnion c.L c.Γ_emb := by
    rw [(Compatible.of_le_le hL_new_le_G (graphUnion_le hL_le_G hΓ_le_G)).le_iff]
    refine ⟨?_, ?_⟩
    · rw [vertexSet_subgraphUnion]
      refine union_subset ?_ ((subgraphInter_le_left hL_le_G hB_le_G).vertexSet_mono.trans subset_union_left)
      intro x hxL'
      rcases hL'_le_ΓLA.vertexSet_mono hxL' with hxΓ | ⟨hxL, _⟩
      · exact Or.inr hxΓ
      · exact Or.inl hxL
    · rw [edgeSet_subgraphUnion hL'_le_G (subgraphInter_le hL_le_G)]
      refine union_subset ?_ ((subgraphInter_le_left hL_le_G hB_le_G).edgeSet_mono.trans subset_union_left)
      exact (hEL'_sub.trans (inf_le_left (b := A)).edgeSet_mono).trans subset_union_right
  have hL_new_disj : Disjoint (c.φE '' E(R_H.G.toGraph)) E(L_new) := by
    rw [Set.disjoint_left]
    rintro _ ⟨eH, heH, rfl⟩ he_new
    rw [edgeSet_subgraphUnion hL'_le_G (subgraphInter_le hL_le_G)] at he_new
    rcases he_new with heL' | heLB
    · have he_Γ : c.φE eH ∈ E(c.Γ_emb) :=
        (hEL'_sub.trans (inf_le_left (b := A)).edgeSet_mono) heL'
      have he_A : c.φE eH ∈ E(A) :=
        (hEL'_sub.trans (inf_le_right (a := c.Γ_emb)).edgeSet_mono) heL'
      rcases c.hSuff.φE_mem eH heH with heK | heU
      · have he_N : c.φE eH ∈ E(N) := by
          rw [congr_arg Graph.edgeSet c.hJ.N_eq, edgeSet_graphUnion, edgeSet_graphUnion]
          exact Or.inl (Or.inl he_Γ)
        exact Set.disjoint_left.mp c.hJ.sep_NK.1.2.2.2.2 he_N heK
      · obtain ⟨A', hA'_ℬ, heA'⟩ := mem_iUnion₂.mp heU
        have hne : A ≠ A' := fun h => hA_not_ℬ (h ▸ hA'_ℬ)
        exact Set.disjoint_left.mp (c.hJ.edge_disjoint_𝒜 A hA A' (c.hSuff.subset hA'_ℬ) hne)
          he_A heA'
    · have heL : c.φE eH ∈ E(c.L) := (subgraphInter_le_left hL_le_G hB_le_G).edgeSet_mono heLB
      rw [ValidConfig74.L, edgeSet_subgraphSUnion hφ_le_G, mem_iUnion₂] at heL
      rcases heL with ⟨_, ⟨v, hv, rfl⟩, he_φv⟩
      exact c.hJ.isModel.edge_not_mem_φV eH heH v hv he_φv
  have hClaim5 := (lemma_7_4_claim_5 c hc_ext hBasis Subset.rfl hL_new_le_LΓ hL_new_disj
    heff_union_Z).1
  -- Step 8: Deduce `c.L ⊓ A ≤ c.Γ_emb ∪ N_W`.
  have hNW_le_G : Graph.noEdge W β ≤ G :=
    Graph.noEdge_le_iff.mpr (c.hJ.sep_NK.2.trans (inter_subset_left.trans c.hJ.sep_NK.1.1.vertexSet_mono))
  rw [(Compatible.of_le_le (inf_le_left.trans hL_le_G) (graphUnion_le hΓ_le_G hNW_le_G)).le_iff]
  have hπ_sub_Γ : πBar ⊆ V(c.Γ_emb) := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hGood.1 hs, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro x ⟨hxL, hxA⟩
    have hx_un : x ∈ V(graphUnion L_new c.Γ_emb) := by
      rw [hClaim5]
      exact Or.inl hxL
    rw [vertexSet_graphUnion, vertexSet_subgraphUnion] at hx_un
    rcases hx_un with (hxL' | ⟨_, hxB⟩) | hxΓ
    · rcases hL'_le_GAW.vertexSet_mono hxL' with ⟨hxΓ, _⟩ | hxW
      · exact Or.inl hxΓ
      · exact Or.inr hxW
    · have hx_AB : x ∈ V(A) ∩ V(B) := ⟨hxA, hxB⟩
      rw [hV_AB] at hx_AB
      rcases hx_AB with hxπ | hxW
      · exact Or.inl (hπ_sub_Γ hxπ)
      · exact Or.inr hxW
    · exact Or.inl hxΓ
  · intro e heLA
    have heL : e ∈ E(c.L) := (inf_le_left (b := A)).edgeSet_mono heLA
    have heA : e ∈ E(A) := (inf_le_right (a := c.L)).edgeSet_mono heLA
    have he_un : e ∈ E(graphUnion L_new c.Γ_emb) := by
      rw [hClaim5]
      exact Or.inl heL
    rw [edgeSet_graphUnion, edgeSet_subgraphUnion hL'_le_G (subgraphInter_le hL_le_G)] at he_un
    rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
    rcases he_un with (heL' | heLB) | heΓ
    · exact (hEL'_sub.trans (inf_le_left (b := A)).edgeSet_mono) heL'
    · have heB : e ∈ E(B) := (subgraphInter_le_right hL_le_G hB_le_G).edgeSet_mono heLB
      exact False.elim (Set.disjoint_left.mp hsep_AB.2.2.2.2 heA heB)
    · exact heΓ

/-- **Graph Minors XXII, (7.4) Claim (8)** (page 555):
"(8) *$\mathcal{B}$ is adequate for $\phi$.*"
Here we prove adequacy for $\mathcal{B}^* = \mathcal{B} \cup \{A \in \mathcal{A} : d(D(A), \Sigma \setminus \Delta) \ge \theta\}$
(and hence for $\mathcal{B}$ itself whenever $\{A \in \mathcal{A} : d(D(A), \Sigma \setminus \Delta) \ge \theta\} \subseteq \mathcal{B}$). -/
theorem lemma_7_4_claim_8
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal) :
    let ℬ_star := ℬ ∪ {A ∈ 𝒜 | θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ)}
    IsAdequateFor c.ιV c.ιE W 𝒜 ℬ_star c.Γ K R_H c.φV c.φE := by
  intro ℬ_star
  have hSuff_star : IsSufficientFor W 𝒜 ℬ_star K R_H c.φV c.φE :=
    c.hSuff.mono subset_union_left (union_subset c.hSuff.subset (fun _ h => h.1))
  refine ⟨hSuff_star.subset, ?_, hSuff_star.φV_meets, hSuff_star.φE_mem,
    hSuff_star.mem_of_inter_K_ne_NW⟩
  intro v hv A hA hnot_le
  by_contra hA_not_star
  have hA_not_ℬ : A ∉ ℬ := fun h => hA_not_star (Or.inl h)
  have hdist_lt : subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ := by
    by_contra! hge
    exact hA_not_star (Or.inr ⟨hA, hge⟩)
  have h7 := lemma_7_4_claim_7 c hc_ext hA hA_not_ℬ hdist_lt
  have hφ_le_G : ∀ P ∈ c.φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.hJ.isModel.subgraph_of_mem u hu
  have hφv_le_L : c.φV v ≤ c.L := le_subgraphSUnion hφ_le_G ⟨v, hv, rfl⟩
  have hle : A ⊓ c.φV v ≤ c.L ⊓ A := by
    refine ⟨fun x hx => ⟨hφv_le_L.vertexSet_mono hx.2, hx.1⟩, ?_⟩
    intro e x y ⟨hlA, hlφ⟩
    exact ⟨hlφ.mono hφv_le_L, hlA⟩
  exact hnot_le (hle.trans h7)

end GraphMinor.GM22
