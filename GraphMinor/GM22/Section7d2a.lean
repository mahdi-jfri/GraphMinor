module

public import GraphMinor.GM22.Section7d1
public import GraphMinor.GM10.TangleLemmas
public import GraphMinor.GM12.Section2Zero
public import GraphMinor.GM14.Section5
public import GraphMinor.GM14.Section7a

/-!
# Graph Minors XXII – Section 7.4 (Part 2a): Isolated Disc Clusters and Claim (3)

This file formalizes the isolated disc cluster separation argument (`no_isolated_disc_cluster`)
and **Claim (3)** (`lemma_7_4_claim_3`, pages 553–554) of the proof of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## Helper Lemmas on Tangles and Region Distances -/

/-- For any tangle $\mathcal{T}$ of order $\theta$ in a hypergraph $G$, the trivial separation
$(\bot, G)$ belongs to $\mathcal{T}$. -/
theorem isTangle_bot_mem {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    (⊥, G) ∈ 𝒯 := by
  have hsep : G.IsSeparation ⊥ G := by
    rw [GM10.isSeparation_iff_of_le bot_le le_rfl]
    simp
  have hord : Hypergraph.separationOrder (⊥ : Hypergraph α β) G < θ := by
    have h0 : Hypergraph.separationOrder (⊥ : Hypergraph α β) G = 0 := by
      simp [Hypergraph.separationOrder]
    have h1 := h𝒯.one_le
    omega
  rcases h𝒯.axiom1 hsep hord with h1 | h2
  · exact h1
  · exact (h𝒯.axiom3 h2 rfl).elim

omit [T2Space S] in
/-- If $r \in \Gamma.R$ is a region of $\Gamma$ and $X \subseteq r$ is nonempty, then the only atom
of $\Gamma$ meeting $X$ is $r$. -/
theorem atom_inter_nonempty_iff_eq_region {Γ : Drawing S} {r X a : Set S}
    (hr : r ∈ Γ.R) (hXr : X ⊆ r) (hXne : X.Nonempty) (ha : a ∈ Γ.A) :
    (a ∩ X).Nonempty ↔ a = r := by
  constructor
  · intro hne
    exact GM12.atom_eq_region_of_meets ha hr (hne.mono (inter_subset_inter_right a hXr))
  · rintro rfl
    rwa [inter_eq_right.mpr hXr]

omit [T2Space S] in
/-- Two nonempty subsets $X_1, X_2$ of the same region $r \in \Gamma.R$ have the same tangle
distance to any set $Y \subseteq S$. -/
theorem subsetTangleDist_eq_of_subset_region {Γ : Drawing S} {ord : ℕ} {d : Set S → Set S → ℕ}
    {r X₁ X₂ : Set S} (hr : r ∈ Γ.R)
    (hX₁ : X₁ ⊆ r) (hX₁_ne : X₁.Nonempty)
    (hX₂ : X₂ ⊆ r) (hX₂_ne : X₂.Nonempty) (Y : Set S) :
    subsetTangleDist Γ ord d X₁ Y = subsetTangleDist Γ ord d X₂ Y := by
  have hiff : ∀ a ∈ Γ.A, (a ∩ X₁).Nonempty ↔ (a ∩ X₂).Nonempty := by
    intro a ha
    rw [atom_inter_nonempty_iff_eq_region hr hX₁ hX₁_ne ha,
      atom_inter_nonempty_iff_eq_region hr hX₂ hX₂_ne ha]
  unfold subsetTangleDist
  have hex : (∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X₁).Nonempty ∧ (b ∩ Y).Nonempty) ↔
      (∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X₂).Nonempty ∧ (b ∩ Y).Nonempty) := by
    refine exists_congr fun a => and_congr_right fun ha => exists_congr fun b =>
      and_congr_right fun _ => and_congr_left fun _ => hiff a ha
  have hset : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X₁).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k} =
      {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X₂).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k} := by
    ext k
    refine exists_congr fun a => and_congr_right fun ha => exists_congr fun b =>
      and_congr_right fun _ => and_congr_left fun _ => hiff a ha
  by_cases h : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X₁).Nonempty ∧ (b ∩ Y).Nonempty
  · simp [h, hex.mp h, hset]
  · simp [h, mt hex.mpr h]

omit [T2Space S] in
/-- A preconnected set disjoint from the frontier of a closed set `D` that meets `D` is contained
in `D`. -/
theorem isPreconnected_subset_of_disjoint_frontier' {X D : Set S} (hX : IsPreconnected X)
    (hD : IsClosed D) (hdisj : Disjoint X (frontier D)) {x : S} (hxX : x ∈ X) (hxD : x ∈ D) :
    X ⊆ D := by
  intro z hzX
  by_contra hzD
  obtain ⟨w, _, hw1, hw2⟩ := hX (interior D) Dᶜ isOpen_interior hD.isOpen_compl
    (fun y hyX => by
      by_cases hyD : y ∈ D
      · refine Or.inl (by_contra fun hy_int => ?_)
        exact Set.disjoint_left.mp hdisj hyX ⟨subset_closure hyD, hy_int⟩
      · exact Or.inr hyD)
    ⟨x, hxX, by_contra fun hx_int =>
      Set.disjoint_left.mp hdisj hxX ⟨subset_closure hxD, hx_int⟩⟩
    ⟨z, hzX, hzD⟩
  exact hw2 (interior_subset hw1)

/-! ## No Isolated Disc Cluster under `(J1)`–`(J7)` -/

set_option maxHeartbeats 400000 in
/-- Under `(J1)`–`(J7)`, there is no subset $\mathcal{C} \subseteq \mathcal{A}$ containing some
$A_0 \in \mathcal{C}$ with $d(D(A_0), \Sigma \setminus \Delta) < \theta$ such that all discs
$D(A')$ for $A' \in \mathcal{C}$ lie in a single region $r \in \Gamma.R$ and are disjoint from
$D(A'')$ for all $A'' \in \mathcal{A} \setminus \mathcal{C}$. -/
theorem no_isolated_disc_cluster {q : ℕ}
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
    (hJ7 : ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T)
    {𝒞 : Set (Graph α β)} (h𝒞_sub : 𝒞 ⊆ 𝒜)
    {A₀ : Graph α β} (hA₀ : A₀ ∈ 𝒞)
    (hA₀_dist : subsetTangleDist Γ ord d (D A₀) (Set.univ \ Δ) < θ)
    {r : Set S} (hr : r ∈ Γ.R) (h𝒞_r : ∀ A' ∈ 𝒞, D A' ⊆ r)
    (h𝒞_disj : ∀ A' ∈ 𝒞, ∀ A'' ∈ 𝒜 \ 𝒞, Disjoint (D A') (D A'')) :
    False := by
  have hA₀_𝒜 : A₀ ∈ 𝒜 := h𝒞_sub hA₀
  have hDA₀_ne : (D A₀).Nonempty := GM14.IsClosedDisc.nonempty (hJ.disc_D A₀ hA₀_𝒜).1
  -- Step 1: Every `A' ∈ 𝒞` has `subsetTangleDist Γ ord d (D A') (Set.univ \ Δ) < θ`,
  -- hence `A' ⊓ K = Graph.noEdge W β`.
  have h𝒞_inter_K : ∀ A' ∈ 𝒞, A' ⊓ K = Graph.noEdge W β := by
    intro A' hA'
    have hA'_𝒜 : A' ∈ 𝒜 := h𝒞_sub hA'
    have hDA'_ne : (D A').Nonempty := GM14.IsClosedDisc.nonempty (hJ.disc_D A' hA'_𝒜).1
    have hdist_eq : subsetTangleDist Γ ord d (D A') (Set.univ \ Δ) =
        subsetTangleDist Γ ord d (D A₀) (Set.univ \ Δ) :=
      subsetTangleDist_eq_of_subset_region hr (h𝒞_r A' hA') hDA'_ne (h𝒞_r A₀ hA₀) hDA₀_ne _
    have hdist_lt : subsetTangleDist Γ ord d (D A') (Set.univ \ Δ) < θ :=
      hdist_eq.trans_lt hA₀_dist
    by_contra hne
    exact not_le_of_gt hdist_lt (hJ.dist_D_of_inter_K A' hA'_𝒜 hne)
  -- Step 2: Every `A' ∈ 𝒞` has `V(A') ∩ V(K) ⊆ W`, `Disjoint V(A') (ιV '' Γ.V)`, and
  -- `V(A') ∩ V(A'') ⊆ W` for all `A'' ∈ 𝒜 \ 𝒞`.
  have h𝒞_V_K : ∀ A' ∈ 𝒞, V(A') ∩ V(K) ⊆ W := by
    intro A' hA' x hx
    have hx_inter : x ∈ V(A' ⊓ K) := hx
    rw [h𝒞_inter_K A' hA'] at hx_inter
    exact hx_inter
  have h𝒞_V_Γ : ∀ A' ∈ 𝒞, Disjoint V(A') (ιV '' Γ.V) := by
    intro A' hA'
    rw [Set.disjoint_left]
    rintro x hxA' ⟨s, hsΓ, rfl⟩
    have hA'_𝒜 : A' ∈ 𝒜 := h𝒞_sub hA'
    have hx_inter : ιV s ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A') := ⟨⟨s, hsΓ, rfl⟩, hxA'⟩
    rw [← hJ.Γ_inter_D A' hA'_𝒜] at hx_inter
    rcases hx_inter with ⟨s', hs'_inter, hs'_eq⟩
    have hs_eq : s' = s := ιV.injective hs'_eq
    subst hs_eq
    have hs_D : s' ∈ D A' :=
      ((mem_interSet_V_iff (hJ.disc_D A' hA'_𝒜).1.isCompact.isClosed).mp hs'_inter).2
    have hs_r : s' ∈ r := h𝒞_r A' hA' hs_D
    exact region_subset hr hs_r (Γ.V_subset_U hsΓ)
  have h𝒞_V_other : ∀ A' ∈ 𝒞, ∀ A'' ∈ 𝒜 \ 𝒞, V(A') ∩ V(A'') ⊆ W := by
    intro A' hA' A'' hA''
    have hne : A' ≠ A'' := fun heq => hA''.2 (heq ▸ hA')
    rw [hJ.vertex_inter_𝒜 A' (h𝒞_sub hA') A'' hA''.1 hne]
    refine union_subset ?_ Subset.rfl
    rintro x ⟨⟨s₁, hs₁, rfl⟩, ⟨s₂, hs₂, hs_eq⟩⟩
    have hs₁₂ : s₁ = s₂ := ιV.injective hs_eq.symm
    subst hs₁₂
    have hs_inter : s₁ ∈ Set.range (πS A') ∩ Set.range (πS A'') := ⟨hs₁, hs₂⟩
    rw [← hJ.D_inter_eq A' (h𝒞_sub hA') A'' hA''.1 hne] at hs_inter
    exact (Set.disjoint_left.mp (h𝒞_disj A' hA' A'' hA'') hs_inter.1 hs_inter.2).elim
  -- Step 3: Define the separation `(C, D_G)` of `G \ W`.
  let G_del := R_G.G.toGraph.deleteVerts W
  let C := (subgraphSUnion R_G.G.toGraph 𝒞).deleteVerts W
  let D_G := G_del.deleteVerts V(C)
  have h𝒞_le : ∀ B ∈ 𝒞, B ≤ R_G.G.toGraph := fun B hB => hJ.le_of_mem_𝒜 B (h𝒞_sub hB)
  have hC_le : C ≤ G_del := by
    have hle : subgraphSUnion R_G.G.toGraph 𝒞 ≤ R_G.G.toGraph :=
      subgraphSUnion_le h𝒞_le
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts] at hx ⊢
      exact ⟨hle.vertexSet_mono hx.1, hx.2⟩
    · intro e x y hLink
      rw [deleteVerts_isLink] at hLink ⊢
      exact ⟨hLink.1.mono hle, hLink.2⟩
  have hD_le : D_G ≤ G_del := Graph.deleteVerts_le
  -- Every vertex `v ∈ V(C)` belongs to `V(A') \ W` for some `A' ∈ 𝒞`.
  have hVC_iff : ∀ v, v ∈ V(C) ↔ ∃ A' ∈ 𝒞, v ∈ V(A') ∧ v ∉ W := by
    intro v
    rw [vertexSet_deleteVerts, vertexSet_subgraphSUnion]
    simp only [mem_sdiff, mem_iUnion, exists_prop]
    tauto
  -- No link of `G_del` outside `E(C)` has an endpoint in `V(C)`.
  have hLink_in_C_or_D : ∀ {e x y}, G_del.IsLink e x y →
      C.IsLink e x y ∨ D_G.IsLink e x y := by
    intro e x y hL
    have hL_iff := hL
    rw [deleteVerts_isLink] at hL_iff
    rcases hL_iff with ⟨hLG, hxW, hyW⟩
    have heG : e ∈ E(R_G.G.toGraph) := hLG.edge_mem
    have hsepNK := hJ.sep_NK.1
    have heNK : e ∈ E(N) ∪ E(K) := hsepNK.2.2.2.1.symm ▸ heG
    have hnot_VC_of_K : ∀ z, z ∈ V(K) → z ∉ W → z ∉ V(C) := by
      intro z hzK hzW hzC
      obtain ⟨A', hA', hzA', _⟩ := (hVC_iff z).mp hzC
      exact hzW (h𝒞_V_K A' hA' ⟨hzA', hzK⟩)
    have hnot_VC_of_Γ : ∀ z, z ∈ V(Γ.toEmbeddedGraph ιV ιE) → z ∉ V(C) := by
      intro z hzΓ hzC
      obtain ⟨A', hA', hzA', _⟩ := (hVC_iff z).mp hzC
      exact Set.disjoint_left.mp (h𝒞_V_Γ A' hA') hzA' hzΓ
    have hnot_VC_of_other : ∀ A'' ∈ 𝒜 \ 𝒞, ∀ z ∈ V(A''), z ∉ W → z ∉ V(C) := by
      intro A'' hA'' z hzA'' hzW hzC
      obtain ⟨A', hA', hzA', _⟩ := (hVC_iff z).mp hzC
      exact hzW (h𝒞_V_other A' hA' A'' hA'' ⟨hzA', hzA''⟩)
    rcases heNK with heN | heK
    · rw [hJ.N_eq] at heN
      change e ∈ (E(Γ.toEmbeddedGraph ιV ιE) ∪ E(Graph.noEdge W β)) ∪
        E(subgraphSUnion R_G.G.toGraph 𝒜) at heN
      rcases heN with (heΓ | heNW) | he𝒜
      · right
        obtain ⟨u, v, hLΓ⟩ := (Γ.toEmbeddedGraph ιV ιE).exists_isLink_of_mem_edgeSet heΓ
        have hLG' : R_G.G.toGraph.IsLink e u v :=
          hLΓ.mono (hJ.Γ_le.trans Graph.deleteVerts_le)
        have hxΓ : x ∈ V(Γ.toEmbeddedGraph ιV ιE) := by
          rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hLΓ.left_mem
          · exact hLΓ.right_mem
        have hyΓ : y ∈ V(Γ.toEmbeddedGraph ιV ιE) := by
          rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hLΓ.right_mem
          · exact hLΓ.left_mem
        rw [deleteVerts_isLink]
        exact ⟨hL, hnot_VC_of_Γ x hxΓ, hnot_VC_of_Γ y hyΓ⟩
      · exact False.elim heNW
      · rw [edgeSet_subgraphSUnion hJ.le_of_mem_𝒜, mem_iUnion₂] at he𝒜
        rcases he𝒜 with ⟨A₁, hA₁, heA₁⟩
        by_cases hA₁_𝒞 : A₁ ∈ 𝒞
        · left
          obtain ⟨u, v, hLA₁⟩ := A₁.exists_isLink_of_mem_edgeSet heA₁
          have hLG' : R_G.G.toGraph.IsLink e u v := hLA₁.mono (hJ.le_of_mem_𝒜 A₁ hA₁)
          have hLA₁_xy : A₁.IsLink e x y := by
            rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hLA₁
            · exact hLA₁.symm
          have hL_su : (subgraphSUnion R_G.G.toGraph 𝒞).IsLink e x y :=
            hLA₁_xy.mono (le_subgraphSUnion h𝒞_le hA₁_𝒞)
          rw [deleteVerts_isLink]
          exact ⟨hL_su, hxW, hyW⟩
        · right
          obtain ⟨u, v, hLA₁⟩ := A₁.exists_isLink_of_mem_edgeSet heA₁
          have hLG' : R_G.G.toGraph.IsLink e u v := hLA₁.mono (hJ.le_of_mem_𝒜 A₁ hA₁)
          have hxA₁ : x ∈ V(A₁) := by
            rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hLA₁.left_mem
            · exact hLA₁.right_mem
          have hyA₁ : y ∈ V(A₁) := by
            rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hLA₁.right_mem
            · exact hLA₁.left_mem
          rw [deleteVerts_isLink]
          exact ⟨hL, hnot_VC_of_other A₁ ⟨hA₁, hA₁_𝒞⟩ x hxA₁ hxW,
            hnot_VC_of_other A₁ ⟨hA₁, hA₁_𝒞⟩ y hyA₁ hyW⟩
    · right
      obtain ⟨u, v, hLK⟩ := K.exists_isLink_of_mem_edgeSet heK
      have hLG' : R_G.G.toGraph.IsLink e u v := hLK.mono hsepNK.2.1
      have hxK : x ∈ V(K) := by
        rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hLK.left_mem
        · exact hLK.right_mem
      have hyK : y ∈ V(K) := by
        rcases hLG.eq_and_eq_or_eq_and_eq hLG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hLK.right_mem
        · exact hLK.left_mem
      rw [deleteVerts_isLink]
      exact ⟨hL, hnot_VC_of_K x hxK hxW, hnot_VC_of_K y hyK hyW⟩
  have hsep_CD : IsGraphSeparation G_del C D_G := by
    refine ⟨hC_le, hD_le, ?_, ?_, ?_⟩
    · ext v
      rw [mem_union, vertexSet_deleteVerts G_del V(C), mem_sdiff]
      have := @hC_le.vertexSet_mono v
      tauto
    · ext e
      constructor
      · rintro (heC | heD)
        · exact hC_le.edgeSet_mono heC
        · exact hD_le.edgeSet_mono heD
      · intro he
        obtain ⟨x, y, hL⟩ := G_del.exists_isLink_of_mem_edgeSet he
        rcases hLink_in_C_or_D hL with hLC | hLD
        · exact Or.inl hLC.edge_mem
        · exact Or.inr hLD.edge_mem
    · rw [Set.disjoint_left]
      intro e heC heD
      obtain ⟨x, y, hLC⟩ := C.exists_isLink_of_mem_edgeSet heC
      obtain ⟨u, v, hLD⟩ := D_G.exists_isLink_of_mem_edgeSet heD
      have hL1 : G_del.IsLink e x y := hLC.mono hC_le
      have hL2 : G_del.IsLink e u v := hLD.mono hD_le
      have hxC : x ∈ V(C) := hLC.left_mem
      have hLD_iff := hLD
      rw [deleteVerts_isLink] at hLD_iff
      have hu_not_C : u ∉ V(C) := hLD_iff.2.1
      have hv_not_C : v ∉ V(C) := hLD_iff.2.2
      rcases hL1.eq_and_eq_or_eq_and_eq hL2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu_not_C hxC
      · exact hv_not_C hxC
  have hCD_inter_empty : V(C) ∩ V(D_G) = ∅ := by
    ext v
    rw [mem_inter_iff, vertexSet_deleteVerts G_del V(C), mem_sdiff, mem_empty_iff_false]
    tauto
  have hord_lt : (V(C) ∩ V(D_G)).ncard < πLen A₀ := by
    rw [hCD_inter_empty, Set.ncard_empty]
    exact (hJ.π_valid A₀ hA₀_𝒜).1
  have hA₀_le_C : A₀.deleteVerts W ≤ C := by
    have hle : A₀ ≤ subgraphSUnion R_G.G.toGraph 𝒞 :=
      le_subgraphSUnion h𝒞_le hA₀
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts] at hx ⊢
      exact ⟨hle.vertexSet_mono hx.1, hx.2⟩
    · intro e x y hL
      rw [deleteVerts_isLink] at hL ⊢
      exact ⟨hL.1.mono hle, hL.2⟩
  -- Check the restrictions of `C` and `D_G` to `Γ`:
  have hC_Γ_V : ιV ⁻¹' V(C) ∩ Γ.V = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    intro hsC hsΓ
    obtain ⟨A', hA', hsA', _⟩ := (hVC_iff (ιV s)).mp hsC
    exact Set.disjoint_left.mp (h𝒞_V_Γ A' hA') hsA' ⟨s, hsΓ, rfl⟩
  have hC_Γ_E : ιE ⁻¹' E(C) ∩ Γ.E = ∅ := by
    ext e
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    intro heC heΓ
    obtain ⟨x, y, hLC⟩ := C.exists_isLink_of_mem_edgeSet heC
    obtain ⟨u, v, hLΓ⟩ := (Γ.toEmbeddedGraph ιV ιE).exists_isLink_of_mem_edgeSet ⟨e, heΓ, rfl⟩
    have hL1 : G_del.IsLink (ιE e) x y := hLC.mono hC_le
    have hL2 : G_del.IsLink (ιE e) u v := hLΓ.mono hJ.Γ_le
    have hxC : x ∈ V(C) := hLC.left_mem
    have hxΓ : x ∈ V(Γ.toEmbeddedGraph ιV ιE) := by
      rcases hL1.eq_and_eq_or_eq_and_eq hL2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hLΓ.left_mem
      · exact hLΓ.right_mem
    rcases hxΓ with ⟨s, hsΓ, rfl⟩
    have hs_inter : s ∈ ιV ⁻¹' V(C) ∩ Γ.V := ⟨hxC, hsΓ⟩
    rw [hC_Γ_V] at hs_inter
    exact hs_inter
  have hD_Γ_V : ιV ⁻¹' V(D_G) ∩ Γ.V = Γ.toHypergraph.vertexSet := by
    ext s
    rw [mem_inter_iff, mem_preimage, vertexSet_deleteVerts G_del V(C), mem_sdiff]
    change (ιV s ∈ V(G_del) ∧ ιV s ∉ V(C)) ∧ s ∈ Γ.V ↔ s ∈ Γ.V
    constructor
    · exact fun h => h.2
    · intro hsΓ
      have hsG_del : ιV s ∈ V(G_del) := hJ.Γ_le.vertexSet_mono ⟨s, hsΓ, rfl⟩
      have hs_not_C : ιV s ∉ V(C) := fun hsC => by
        have : s ∈ ιV ⁻¹' V(C) ∩ Γ.V := ⟨hsC, hsΓ⟩
        rw [hC_Γ_V] at this
        exact this
      exact ⟨⟨hsG_del, hs_not_C⟩, hsΓ⟩
  have hD_Γ_E : ιE ⁻¹' E(D_G) ∩ Γ.E = Γ.toHypergraph.edgeSet := by
    ext e
    change ιE e ∈ E(D_G) ∧ e ∈ Γ.E ↔ e ∈ Γ.E
    constructor
    · exact fun h => h.2
    · intro heΓ
      have heG_del : ιE e ∈ E(G_del) := hJ.Γ_le.edgeSet_mono ⟨e, heΓ, rfl⟩
      have he_not_C : ιE e ∉ E(C) := fun heC => by
        have : e ∈ ιE ⁻¹' E(C) ∩ Γ.E := ⟨heC, heΓ⟩
        rw [hC_Γ_E] at this
        exact this
      have heCD : ιE e ∈ E(C) ∪ E(D_G) := hsep_CD.2.2.2.1.symm ▸ heG_del
      exact ⟨heCD.resolve_left he_not_C, heΓ⟩
  have hbot_mem : ((⊥ : Hypergraph S (Set S)), Γ.toHypergraph) ∈ T :=
    isTangle_bot_mem hJ.hasMetric.1.2.1
  exact hJ7.no_small_sep A₀ hA₀_𝒜
    ⟨C, D_G, ⊥, Γ.toHypergraph, hsep_CD, hord_lt, hA₀_le_C,
      hC_Γ_V.symm, hC_Γ_E.symm, hD_Γ_V.symm, hD_Γ_E.symm, hbot_mem⟩

/-! ## Claim (3) of Theorem 7.4 (pages 553–554) -/

/-- **Graph Minors XXII, (7.4) Claim (3)** (pages 553–554):
(3) *If $F \subseteq \Sigma$ is an $O$-arc with $F \cap U(\Gamma) = \emptyset$ and $F \cap D(A) = \emptyset$ for each $A \in \mathcal{A}$, then $ins(F) \cap U(\Gamma) = \emptyset$ and $ins(F) \cap D(A) = \emptyset$ for all $A \in \mathcal{A}$ with $d(D(A), \Sigma \setminus \Delta) < \theta$.* -/
theorem lemma_7_4_claim_3 {q : ℕ}
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
    (hJ7 : ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T)
    {A : Graph α β} (hA : A ∈ 𝒜)
    (hdist : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ) :
    ¬ ∃ F : Set S, IsOArc F ∧ Disjoint F Γ.U ∧ D A ⊆ ins F ∧
      ∀ A' ∈ 𝒜, Disjoint (D A') F := by
  rintro ⟨F, hFO, hFU, hDA_sub, hDF_disj⟩
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  -- Since `F` is an O-arc disjoint from `Γ.U`, `F ⊆ r` for some region `r ∈ Γ.R`.
  obtain ⟨x₀, hx₀F⟩ := GM14.IsOArc.nonempty hFO
  have hx₀_compl : x₀ ∈ Set.univ \ Γ.U := ⟨trivial, Set.disjoint_left.mp hFU hx₀F⟩
  let r := connectedComponentIn (Set.univ \ Γ.U) x₀
  have hr : r ∈ Γ.R := (mem_R_iff Γ).mpr ⟨x₀, hx₀_compl.2, rfl⟩
  have hF_sub_compl : F ⊆ Set.univ \ Γ.U :=
    fun x hx => ⟨trivial, Set.disjoint_left.mp hFU hx⟩
  have hFr : F ⊆ r :=
    (GM14.IsOArc.isPreconnected hFO).subset_connectedComponentIn hx₀F hF_sub_compl
  -- `F` is `Γ`-normal of order `0 < ord`, so `IsTangleIns Γ T F (ins F)` holds.
  have hF_norm : Γ.IsNormal F :=
    fun x hx => (Set.disjoint_left.mp hFU hx.1 hx.2).elim
  have hFV_empty : F ∩ Γ.V = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxF hxV
    exact Set.disjoint_left.mp hFU hxF (Γ.V_subset_U hxV)
  have hF_ord : (F ∩ Γ.V).ncard < ord := by
    rw [hFV_empty, Set.ncard_empty]
    have := hJ.four_le_θ
    have := hJ.θ_le_ord
    omega
  obtain ⟨hins_disc, hins_bd, hins_T⟩ := hJ.ins_spec F hFO hF_norm hF_ord
  have hr_cell : IsOpenDisc r := hJ.isTwoCell.2 r hr
  have hins_sub_r : ins F ⊆ r :=
    GM12.selected_disc_subset_region hS hJ.hasMetric.1.2.1 hr hr_cell hFO hFr
      hins_disc hins_bd hins_T
  -- Apply `no_isolated_disc_cluster` to `𝒞 := {A' ∈ 𝒜 | D A' ⊆ ins F}`.
  let 𝒞 : Set (Graph α β) := {A' ∈ 𝒜 | D A' ⊆ ins F}
  have h𝒞_sub : 𝒞 ⊆ 𝒜 := fun _ h => h.1
  have hA_𝒞 : A ∈ 𝒞 := ⟨hA, hDA_sub⟩
  have h𝒞_r : ∀ A' ∈ 𝒞, D A' ⊆ r := fun A' hA' => hA'.2.trans hins_sub_r
  have h𝒞_disj : ∀ A' ∈ 𝒞, ∀ A'' ∈ 𝒜 \ 𝒞, Disjoint (D A') (D A'') := by
    intro A' hA' A'' hA''
    rw [Set.disjoint_left]
    intro x hxA' hxA''
    apply hA''.2
    refine ⟨hA''.1, ?_⟩
    have hdisj_fr : Disjoint (D A'') (frontier (ins F)) := by
      rw [← subBd_eq_frontier, hins_bd]
      exact hDF_disj A'' hA''.1
    exact isPreconnected_subset_of_disjoint_frontier'
      (GM14.IsClosedDisc.isPreconnected (hJ.disc_D A'' hA''.1).1)
      hins_disc.isCompact.isClosed hdisj_fr hxA'' (hA'.2 hxA')
  exact no_isolated_disc_cluster hJ hJ7 h𝒞_sub hA_𝒞 hdist hr h𝒞_r h𝒞_disj

end GraphMinor.GM22
