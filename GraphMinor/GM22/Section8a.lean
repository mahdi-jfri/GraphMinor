module

public import GraphMinor.GM22.Section8Parallel
public import GraphMinor.GM22.Section2Forest
public import GraphMinor.GM22.Section7c1
public import GraphMinor.GM22.Section7d2b
public import GraphMinor.Surface.SphereDisc
public import GraphMinor.GM14.Section3
public import GraphMinor.GM12.Section4PathExists
import GraphMinor.GM12.Section79

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 8 (Part 1): Proofs of 8.1 and 8.2

This file formalizes **8.1** (`theorem_8_1`, pages 556–557) and **8.2** (`theorem_8_2`,
pages 557–559, with `lemma_8_2_claim_1` through `lemma_8_2_claim_4`) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Helper Lemmas and Proof of 8.1 (pages 556–557) -/

/-- Under `(J1)`–`(J6)`, the set
$Z_0 = (V(K) \cup \bigcup_{A \in \mathcal{A}} V(A)) \cap \bigcup_{v \in V(H)} V(\phi(v))$
is a basis for $\phi$. -/
theorem SystemJ1ToJ6.isModelBasis_inter_L₀ {q : ℕ}
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
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE) :
    let L₀ := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
    let K_star := V(K) ∪ ⋃ A ∈ 𝒜, V(A)
    IsModelBasis R_G R_H φV φE (K_star ∩ V(L₀)) := by
  intro L₀ K_star
  have hP_le : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩
    exact hJ.isModel.subgraph_of_mem v hv
  have hL₀_le : L₀ ≤ R_G.G.toGraph := subgraphSUnion_le hP_le
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hmem_L₀ : ∀ {v : αH}, v ∈ V(R_H.G.toGraph) → V(φV v) ⊆ V(L₀) := by
    intro v hv
    exact (le_subgraphSUnion hP_le ⟨v, hv, rfl⟩).vertexSet_mono
  have he_ends_in_K_star : ∀ e ∈ E(R_H.G.toGraph),
      R_G.G.head (φE e) ∈ K_star ∧ R_G.G.tail (φE e) ∈ K_star := by
    intro e he
    have hlink_G : R_G.G.toGraph.IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) :=
      R_G.G.isLink_of_mem (φE e) (hJ.isModel.edge_mem e he)
    rcases hJ.φE_mem e he with heK | heA
    · have hlink_K : K.IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) :=
        (hK_le.isLink_iff heK).mpr hlink_G
      exact ⟨Or.inl hlink_K.right_mem, Or.inl hlink_K.left_mem⟩
    · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heA
      have hlink_A : A.IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) :=
        ((hJ.le_of_mem_𝒜 A hA).isLink_iff heA).mpr hlink_G
      exact ⟨Or.inr (mem_iUnion₂.mpr ⟨A, hA, hlink_A.right_mem⟩),
        Or.inr (mem_iUnion₂.mpr ⟨A, hA, hlink_A.left_mem⟩)⟩
  refine ⟨inter_subset_right.trans hL₀_le.vertexSet_mono, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi_W : R_G.roots i ∈ W := hJ.W_eq ▸ ⟨i, rfl⟩
    have hi_K : R_G.roots i ∈ V(K) := (hJ.sep_NK.2 hi_W).2
    have hi_L₀ : R_G.roots i ∈ V(L₀) :=
      hmem_L₀ (R_H.roots_mem i) (hJ.isModel.root_mem i)
    exact ⟨Or.inl hi_K, hi_L₀⟩
  · intro e he
    have hh_V : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).right_mem
    exact ⟨(he_ends_in_K_star e he).1, hmem_L₀ hh_V (hJ.isModel.head_mem e he)⟩
  · intro e he
    have ht_V : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).left_mem
    exact ⟨(he_ends_in_K_star e he).2, hmem_L₀ ht_V (hJ.isModel.tail_mem e he)⟩
  · intro v hv
    obtain ⟨x, hxφ, hxK⟩ := hJ.φV_meets v hv
    exact ⟨x, ⟨hxK, hmem_L₀ hv hxφ⟩, hxφ⟩

/-- Given a model $\phi$ of $(H, \chi)$ in $(G, \omega)$ with finite $V(G), E(G)$ and a basis
$Z \subseteq V(L_0)$ where $L_0 = \bigcup_{v \in V(H)} \phi(v)$, there exists a model $\phi'$ of
$(H, \chi)$ in $(G, \omega)$ with $\phi'_E = \phi_E$, $V(\phi'(v)) \cap Z = V(\phi(v)) \cap Z$ for
all $v \in V(H)$, and $L = \bigcup_{v \in V(H)} \phi'(v) \le L_0$ such that $L$ is a forest,
$Z \subseteq V(L)$, and every vertex of $L$ of degree $\le 1$ belongs to $Z$. -/
theorem exists_minimal_forest_model {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    (hfinV : V(R_G.G.toGraph).Finite) (hfinE : E(R_G.G.toGraph).Finite)
    (hMod : IsRootedDigraphModel R_G R_H φV φE)
    (hBasis : IsModelBasis R_G R_H φV φE Z)
    (hZ_L₀ : Z ⊆ V(subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))) :
    ∃ φV' : αH → Graph α β,
      let L := subgraphSUnion R_G.G.toGraph (φV' '' V(R_H.G.toGraph))
      IsRootedDigraphModel R_G R_H φV' φE ∧
      (∀ v ∈ V(R_H.G.toGraph), V(φV' v) ∩ Z = V(φV v) ∩ Z) ∧
      L ≤ subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)) ∧
      Z ⊆ V(L) ∧
      IsGraphForest L ∧
      {v ∈ V(L) | vertexValency L v ≤ 1} ⊆ Z := by
  let L₀ := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
  let Valid (φV' : αH → Graph α β) : Prop :=
    IsRootedDigraphModel R_G R_H φV' φE ∧
    (∀ v ∈ V(R_H.G.toGraph), V(φV' v) ∩ Z = V(φV v) ∩ Z) ∧
    subgraphSUnion R_G.G.toGraph (φV' '' V(R_H.G.toGraph)) ≤ L₀
  let L_of (φV' : αH → Graph α β) : Graph α β :=
    subgraphSUnion R_G.G.toGraph (φV' '' V(R_H.G.toGraph))
  let meas (φV' : αH → Graph α β) : ℕ :=
    V(L_of φV').ncard + E(L_of φV').ncard
  have hValid₀ : Valid φV := ⟨hMod, fun _ _ => rfl, le_rfl⟩
  have hne : {m : ℕ | ∃ φV', Valid φV' ∧ meas φV' = m}.Nonempty :=
    ⟨meas φV, φV, hValid₀, rfl⟩
  obtain ⟨m₀, ⟨φV', hValid', hm₀⟩, hmin⟩ := wellFounded_lt.has_min _ hne
  obtain ⟨hMod', hZ_eq, hL_le_L₀⟩ := hValid'
  let L := L_of φV'
  have hP'_le : ∀ P ∈ φV' '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩
    exact hMod'.subgraph_of_mem v hv
  have hL_le_G : L ≤ R_G.G.toGraph := subgraphSUnion_le hP'_le
  have hZ_sub_L : Z ⊆ V(L) := by
    intro z hz
    have hzL₀ := hZ_L₀ hz
    rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hzL₀ ⊢
    rcases hzL₀ with ⟨_, ⟨v, hv, rfl⟩, hzv⟩
    have hz_inter : z ∈ V(φV v) ∩ Z := ⟨hzv, hz⟩
    rw [← hZ_eq v hv] at hz_inter
    exact ⟨φV' v, ⟨v, hv, rfl⟩, hz_inter.1⟩
  have hBasis' : IsModelBasis R_G R_H φV' φE Z :=
    { hBasis with
      inter_φV_nonempty := fun v hv => by
        rw [Set.inter_comm, hZ_eq v hv, Set.inter_comm]
        exact hBasis.inter_φV_nonempty v hv }
  have hL_le_del : L ≤ R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph)) := by
    refine ⟨by rw [Graph.vertexSet_deleteEdges]; exact hL_le_G.vertexSet_mono, fun e x y hl => ?_⟩
    rw [Graph.deleteEdges_isLink]
    refine ⟨hl.mono hL_le_G, ?_⟩
    rintro ⟨eH, heH, rfl⟩
    have heL : φE eH ∈ E(L) := hl.edge_mem
    rw [edgeSet_subgraphSUnion hP'_le, mem_iUnion₂] at heL
    rcases heL with ⟨_, ⟨v, hv, rfl⟩, he_φv⟩
    exact hMod'.edge_not_mem_φV eH heH v hv he_φv
  -- Show `IsVitalFor L L Z`.
  have hVital : IsVitalFor L L Z := by
    refine ⟨le_rfl, hZ_sub_L, fun L' hL'L heff => ?_⟩
    have hL'_le_del : L' ≤ R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph)) :=
      hL'L.trans hL_le_del
    obtain ⟨φV'', hφV''_spec, hMod''⟩ :=
      gm22_theorem_6_2 R_G R_H φV' φE Z L L' hMod' hBasis' rfl hL'_le_del heff
    have hP''_le : ∀ P ∈ φV'' '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
      rintro _ ⟨v, hv, rfl⟩
      exact hMod''.subgraph_of_mem v hv
    let L'' := L_of φV''
    have hL''_le_L' : L'' ≤ L' := by
      refine subgraphSUnion_le_of_forall_le hP''_le (hL'L.trans hL_le_G) ?_
      rintro _ ⟨v, hv, rfl⟩
      exact (hφV''_spec v hv).1.1
    have hL''_le_L : L'' ≤ L := hL''_le_L'.trans hL'L
    have hValid'' : Valid φV'' :=
      ⟨hMod'', fun v hv => (hφV''_spec v hv).2.trans (hZ_eq v hv),
        hL''_le_L.trans hL_le_L₀⟩
    have hm_le : meas φV' ≤ meas φV'' := by
      rw [hm₀]
      exact not_lt.mp (hmin (meas φV'') ⟨φV'', hValid'', rfl⟩)
    have hfinVL : V(L).Finite := hfinV.subset hL_le_G.vertexSet_mono
    have hfinEL : E(L).Finite := hfinE.subset hL_le_G.edgeSet_mono
    have hV_le₁ : V(L'').ncard ≤ V(L').ncard :=
      Set.ncard_le_ncard hL''_le_L'.vertexSet_mono (hfinVL.subset hL'L.vertexSet_mono)
    have hV_le₂ : V(L').ncard ≤ V(L).ncard :=
      Set.ncard_le_ncard hL'L.vertexSet_mono hfinVL
    have hE_le₁ : E(L'').ncard ≤ E(L').ncard :=
      Set.ncard_le_ncard hL''_le_L'.edgeSet_mono (hfinEL.subset hL'L.edgeSet_mono)
    have hE_le₂ : E(L').ncard ≤ E(L).ncard :=
      Set.ncard_le_ncard hL'L.edgeSet_mono hfinEL
    have hm_le' : V(L).ncard + E(L).ncard ≤ V(L'').ncard + E(L'').ncard := hm_le
    have hV_eq : V(L').ncard = V(L).ncard := by omega
    have hE_eq : E(L').ncard = E(L).ncard := by omega
    exact (Compatible.of_le_le hL'L le_rfl).ext
      (Set.eq_of_subset_of_ncard_le hL'L.vertexSet_mono hV_eq.ge hfinVL)
      (Set.eq_of_subset_of_ncard_le hL'L.edgeSet_mono hE_eq.ge hfinEL)
  have h22 := theorem_2_2_proof (hfinE.subset hL_le_G.edgeSet_mono) hZ_sub_L hVital
  refine ⟨φV', hMod', hZ_eq, hL_le_L₀, hZ_sub_L, h22.1, ?_⟩
  rintro v ⟨hvL, hval⟩
  have hval' : vertexValency L v ≤ 1 := hval
  by_contra hvZ
  have hge2 := h22.2.2 v ⟨hvL, hvZ⟩
  omega

/-- **Graph Minors XXII, (8.1)** (Section 8, page 556):
*Let (J1)–(J6) hold. Then there exists $$\mathcal{A}' \subseteq \mathcal{A}$$, sufficient for some
model of $$(H, \chi)$$ in $$(G, \omega)$$, such that there are at most $$3q + 5\delta$$ members
$$A$$ of $$\mathcal{A}'$$ with $$d(D(A), \Sigma \setminus \Delta) < \theta$$.* -/
theorem theorem_8_1_proof {q : ℕ}
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
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE) :
    ∃ (𝒜' : Set (Graph α β)) (φV' : αH → Graph α β) (φE' : βH → β),
      IsRootedDigraphModel R_G R_H φV' φE' ∧
      IsSufficientFor W 𝒜 𝒜' K R_H φV' φE' ∧
      {A ∈ 𝒜' | subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ}.ncard ≤ 3 * q + 5 * δ := by
  let L₀ := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
  let K_star := V(K) ∪ ⋃ A ∈ 𝒜, V(A)
  -- Step 1: Choose a basis `Z ⊆ K_star ∩ V(L₀)` for `φ` with `|Z| ≤ q + 3δ` using 6.1.
  have hBasis₀ := hJ.isModelBasis_inter_L₀
  obtain ⟨Z, hZ_sub, hBasis_Z, hZ_card⟩ :=
    gm22_theorem_6_1 R_G R_H φV φE (K_star ∩ V(L₀)) hJ.detail_H hJ.isModel hBasis₀
  have hZ_K_star : Z ⊆ K_star := hZ_sub.trans inter_subset_left
  have hZ_L₀ : Z ⊆ V(L₀) := hZ_sub.trans inter_subset_right
  -- Step 2: Choose a minimal model `(φV', φE)` with `L = ⋃(φ'(v) : v ∈ V(H)) ≤ L₀`.
  obtain ⟨φV', hMod', hZ_eq, _, hZ_L, hForest_L, hLeaves_Z⟩ :=
    exists_minimal_forest_model hJ.finite_V hJ.finite_E hJ.isModel hBasis_Z hZ_L₀
  let L := subgraphSUnion R_G.G.toGraph (φV' '' V(R_H.G.toGraph))
  have hP'_le : ∀ P ∈ φV' '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩
    exact hMod'.subgraph_of_mem v hv
  have hL_le_G : L ≤ R_G.G.toGraph := subgraphSUnion_le hP'_le
  have hfinVL : V(L).Finite := hJ.finite_V.subset hL_le_G.vertexSet_mono
  have hfinEL : E(L).Finite := hJ.finite_E.subset hL_le_G.edgeSet_mono
  have hfinZ : Z.Finite := hJ.finite_V.subset hBasis_Z.subset_V
  -- Step 3: Bound `∑_{y ∈ W} d_L(y) ≤ 2|W| + |Z| ≤ 3q + 3δ` by 2.3.
  have hW_sub_Z : W ⊆ Z := by
    rw [hJ.W_eq]
    rintro _ ⟨i, rfl⟩
    exact hBasis_Z.roots_mem i
  have hW_sub_L : W ⊆ V(L) := hW_sub_Z.trans hZ_L
  have hW_card : W.ncard = q := by
    rw [hJ.W_eq, Set.ncard_range_of_injective hJ.inj_roots, Nat.card_fin]
  have hLeaves_card : {v ∈ V(L) | vertexValency L v ≤ 1}.ncard ≤ q + 3 * δ :=
    (Set.ncard_le_ncard hLeaves_Z hfinZ).trans hZ_card
  have hSum_W : (∑ᶠ y ∈ W, vertexValency L y) ≤ 3 * q + 3 * δ := by
    have h23 := theorem_2_3_proof hfinVL hfinEL hForest_L hLeaves_card hW_sub_L
    rw [hW_card] at h23
    omega
  -- Step 4: Define `𝒜₁` and prove `|𝒜₁| ≤ 3q + 3δ`.
  let 𝒜₁ : Set (Graph α β) :=
    {A ∈ 𝒜 | ∃ e ∈ E(A ⊓ L), ∃ w ∈ W, (A ⊓ L).Inc e w}
  have h𝒜₁_sub : 𝒜₁ ⊆ 𝒜 := fun _ h => h.1
  let E_inc_W : Set β := ⋃ y ∈ W, {e ∈ E(L) | L.Inc e y}
  have hfinW : W.Finite := hfinZ.subset hW_sub_Z
  have hE_inc_W_card : E_inc_W.ncard ≤ 3 * q + 3 * δ := by
    have h1 : E_inc_W = ⋃ y ∈ hfinW.toFinset, {e ∈ E(L) | L.Inc e y} := by
      ext e
      simp [E_inc_W]
    rw [h1]
    have h2 : ∀ s : Finset α, (⋃ y ∈ s, {e ∈ E(L) | L.Inc e y}).ncard ≤
        ∑ y ∈ s, {e ∈ E(L) | L.Inc e y}.ncard := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
        exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
    have h2' := h2 hfinW.toFinset
    have h3 : (∑ y ∈ hfinW.toFinset, {e ∈ E(L) | L.Inc e y}.ncard) =
        ∑ᶠ y ∈ W, vertexValency L y := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfinW]
      refine Finset.sum_congr rfl fun y _ => ?_
      exact (vertexValency_eq_ncard_inc_of_isGraphForest hForest_L y).symm
    omega
  have h𝒜₁_fin_card : 𝒜₁.Finite ∧ 𝒜₁.ncard ≤ 3 * q + 3 * δ := by
    have hex_e : ∀ A : 𝒜₁, ∃ e ∈ E_inc_W, e ∈ E(A.1) := by
      rintro ⟨A, hA, e, he, w, hwW, hInc⟩
      have hAL_le_A : A ⊓ L ≤ A := inf_le_left
      have hAL_le_L : A ⊓ L ≤ L := inf_le_right
      rcases hInc with ⟨z, hlink⟩
      have hlink_L : L.IsLink e w z := hlink.mono hAL_le_L
      exact ⟨e, mem_iUnion₂.mpr ⟨w, hwW, hlink_L.edge_mem, z, hlink_L⟩,
        hAL_le_A.edgeSet_mono he⟩
    let f₁ : 𝒜₁ → β := fun A => Classical.choose (hex_e A)
    have hf₁_spec : ∀ A : 𝒜₁, f₁ A ∈ E_inc_W ∧ f₁ A ∈ E(A.1) :=
      fun A => Classical.choose_spec (hex_e A)
    have hf₁_inj : Function.Injective f₁ := by
      intro A₁ A₂ heq
      by_contra hne
      have hne_val : A₁.1 ≠ A₂.1 := fun h => hne (Subtype.ext h)
      have he₁ : f₁ A₁ ∈ E(A₁.1) := (hf₁_spec A₁).2
      have he₂ : f₁ A₁ ∈ E(A₂.1) := heq ▸ (hf₁_spec A₂).2
      exact Set.disjoint_left.mp (hJ.edge_disjoint_𝒜 A₁.1 A₁.2.1 A₂.1 A₂.2.1 hne_val) he₁ he₂
    have hfin_EW : E_inc_W.Finite := hfinEL.subset fun e he => by
      rcases mem_iUnion₂.mp he with ⟨_, _, heL, _⟩
      exact heL
    have hfin_range : (Set.range f₁).Finite :=
      hfin_EW.subset (by rintro _ ⟨A, rfl⟩; exact (hf₁_spec A).1)
    have hfin_𝒜₁ : 𝒜₁.Finite := by
      have : Finite (Set.range f₁) := hfin_range.to_subtype
      have : Finite 𝒜₁ := Finite.of_injective (Set.rangeFactorization f₁)
        (fun A₁ A₂ h => hf₁_inj (congrArg Subtype.val h))
      exact Set.toFinite 𝒜₁
    have hcard_le : (Set.range f₁).ncard ≤ E_inc_W.ncard :=
      Set.ncard_le_ncard (by rintro _ ⟨A, rfl⟩; exact (hf₁_spec A).1) hfin_EW
    have hrange_eq : (Set.range f₁).ncard = 𝒜₁.ncard := by
      rw [Set.ncard_range_of_injective hf₁_inj, Nat.card_coe_set_eq]
    exact ⟨hfin_𝒜₁, by omega⟩
  -- Step 5: Define `𝒜₂ ⊆ 𝒜` with `|𝒜₂| ≤ δ`.
  let V_need : Set αH :=
    {v ∈ V(R_H.G.toGraph) \ Set.range R_H.roots | ¬ (V(φV' v) ∩ V(K)).Nonempty}
  have hex_A₂ : ∀ v : V_need, ∃ A ∈ 𝒜, (V(φV' v.1) ∩ V(A)).Nonempty := by
    rintro ⟨v, ⟨hvV, _⟩, hnotK⟩
    obtain ⟨z, hzZ, hzφ⟩ := hBasis_Z.inter_φV_nonempty v hvV
    have hzφ' : z ∈ V(φV' v) := by
      have : z ∈ V(φV v) ∩ Z := ⟨hzφ, hzZ⟩
      rw [← hZ_eq v hvV] at this
      exact this.1
    rcases hZ_K_star hzZ with hzK | hzA
    · exact False.elim (hnotK ⟨z, hzφ', hzK⟩)
    · obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.mp hzA
      exact ⟨A, hA, z, hzφ', hzA⟩
  let pickA₂ : V_need → Graph α β := fun v => Classical.choose (hex_A₂ v)
  have hpickA₂_spec : ∀ v : V_need, pickA₂ v ∈ 𝒜 ∧ (V(φV' v.1) ∩ V(pickA₂ v)).Nonempty :=
    fun v => Classical.choose_spec (hex_A₂ v)
  let 𝒜₂ : Set (Graph α β) := Set.range pickA₂
  have h𝒜₂_sub : 𝒜₂ ⊆ 𝒜 := by
    rintro _ ⟨v, rfl⟩
    exact (hpickA₂_spec v).1
  have h𝒜₂_fin_card : 𝒜₂.Finite ∧ 𝒜₂.ncard ≤ δ := by
    have hfin_Vdiff : (V(R_H.G.toGraph) \ Set.range R_H.roots).Finite := hJ.detail_H.1.sdiff
    have hfin_Vneed : V_need.Finite := hfin_Vdiff.subset fun _ h => h.1
    have : Finite V_need := hfin_Vneed.to_subtype
    have hfin_𝒜₂ : 𝒜₂.Finite := Set.finite_range pickA₂
    have h1 : (pickA₂ '' Set.univ).ncard ≤ (Set.univ : Set V_need).ncard :=
      Set.ncard_image_le Set.finite_univ
    rw [Set.image_univ, Set.ncard_univ, Nat.card_coe_set_eq] at h1
    have h2 : V_need.ncard ≤ (V(R_H.G.toGraph) \ Set.range R_H.roots).ncard :=
      Set.ncard_le_ncard (fun _ h => h.1) hfin_Vdiff
    exact ⟨hfin_𝒜₂, h1.trans (h2.trans hJ.detail_H.2.2.2)⟩
  have hφV'_meets_𝒜₂ : ∀ v ∈ V(R_H.G.toGraph),
      (V(φV' v) ∩ (V(K) ∪ ⋃ A ∈ 𝒜₂, V(A))).Nonempty := by
    intro v hv
    by_cases hK_ne : (V(φV' v) ∩ V(K)).Nonempty
    · obtain ⟨x, hxφ, hxK⟩ := hK_ne
      exact ⟨x, hxφ, Or.inl hxK⟩
    · by_cases hroot : v ∈ Set.range R_H.roots
      · rcases hroot with ⟨i, rfl⟩
        have hi_φ' : R_G.roots i ∈ V(φV' (R_H.roots i)) := hMod'.root_mem i
        have hi_W : R_G.roots i ∈ W := hJ.W_eq ▸ ⟨i, rfl⟩
        have hi_K : R_G.roots i ∈ V(K) := (hJ.sep_NK.2 hi_W).2
        exact ⟨R_G.roots i, hi_φ', Or.inl hi_K⟩
      · let v' : V_need := ⟨v, ⟨hv, hroot⟩, hK_ne⟩
        obtain ⟨x, hxφ, hxA⟩ := (hpickA₂_spec v').2
        exact ⟨x, hxφ, Or.inr (mem_iUnion₂.mpr ⟨pickA₂ v', ⟨v', rfl⟩, hxA⟩)⟩
  -- Step 6: Define `𝒜₃ = {A ∈ 𝒜 | (E(A) ∩ φ'(E(H))).Nonempty}` and prove `|𝒜₃| ≤ δ`.
  let 𝒜₃ : Set (Graph α β) :=
    {A ∈ 𝒜 | (E(A) ∩ (φE '' E(R_H.G.toGraph))).Nonempty}
  have h𝒜₃_sub : 𝒜₃ ⊆ 𝒜 := fun _ h => h.1
  have h𝒜₃_fin_card : 𝒜₃.Finite ∧ 𝒜₃.ncard ≤ δ := by
    have hex_e₃ : ∀ A : 𝒜₃, ∃ e ∈ φE '' E(R_H.G.toGraph), e ∈ E(A.1) := by
      rintro ⟨A, _, x, hxA, hxE⟩
      exact ⟨x, hxE, hxA⟩
    let f₃ : 𝒜₃ → β := fun A => Classical.choose (hex_e₃ A)
    have hf₃_spec : ∀ A : 𝒜₃, f₃ A ∈ φE '' E(R_H.G.toGraph) ∧ f₃ A ∈ E(A.1) :=
      fun A => Classical.choose_spec (hex_e₃ A)
    have hf₃_inj : Function.Injective f₃ := by
      intro A₁ A₂ heq
      by_contra hne
      have hne_val : A₁.1 ≠ A₂.1 := fun h => hne (Subtype.ext h)
      exact Set.disjoint_left.mp (hJ.edge_disjoint_𝒜 A₁.1 A₁.2.1 A₂.1 A₂.2.1 hne_val)
        (hf₃_spec A₁).2 (heq ▸ (hf₃_spec A₂).2)
    have hfin_φE : (φE '' E(R_H.G.toGraph)).Finite := hJ.detail_H.2.1.image φE
    have hfin_range : (Set.range f₃).Finite :=
      hfin_φE.subset (by rintro _ ⟨A, rfl⟩; exact (hf₃_spec A).1)
    have hfin_𝒜₃ : 𝒜₃.Finite := by
      have : Finite (Set.range f₃) := hfin_range.to_subtype
      have : Finite 𝒜₃ := Finite.of_injective (Set.rangeFactorization f₃)
        (fun A₁ A₂ h => hf₃_inj (congrArg Subtype.val h))
      exact Set.toFinite 𝒜₃
    have hcard_le : (Set.range f₃).ncard ≤ (φE '' E(R_H.G.toGraph)).ncard :=
      Set.ncard_le_ncard (by rintro _ ⟨A, rfl⟩; exact (hf₃_spec A).1) hfin_φE
    have hrange_eq : (Set.range f₃).ncard = 𝒜₃.ncard := by
      rw [Set.ncard_range_of_injective hf₃_inj, Nat.card_coe_set_eq]
    have hφE_le : (φE '' E(R_H.G.toGraph)).ncard ≤ δ :=
      (Set.ncard_image_le hJ.detail_H.2.1).trans hJ.detail_H.2.2.1
    exact ⟨hfin_𝒜₃, by omega⟩
  -- Step 7: Define `𝒜₄` and `𝒜' = 𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃ ∪ 𝒜₄`.
  let 𝒜₄ : Set (Graph α β) :=
    {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
  have h𝒜₄_sub : 𝒜₄ ⊆ 𝒜 := fun _ h => h.1
  let 𝒜' : Set (Graph α β) := 𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃ ∪ 𝒜₄
  have h𝒜'_sub : 𝒜' ⊆ 𝒜 :=
    union_subset (union_subset (union_subset h𝒜₁_sub h𝒜₂_sub) h𝒜₃_sub) h𝒜₄_sub
  refine ⟨𝒜', φV', φE, hMod', ?_, ?_⟩
  · -- Verify `IsSufficientFor W 𝒜 𝒜' K R_H φV' φE`.
    refine ⟨h𝒜'_sub, ?_, ?_, ?_, ?_⟩
    · intro v hv A hA ⟨e, he, w, hwW, hInc⟩
      have hφ_le_L : φV' v ≤ L := le_subgraphSUnion hP'_le ⟨v, hv, rfl⟩
      have hinf_le : A ⊓ φV' v ≤ A ⊓ L := inf_le_inf_left A hφ_le_L
      rcases hInc with ⟨z, hlink⟩
      have hlink_AL : (A ⊓ L).IsLink e w z := hlink.mono hinf_le
      have hA_𝒜₁ : A ∈ 𝒜₁ := ⟨hA, e, hlink_AL.edge_mem, w, hwW, z, hlink_AL⟩
      exact Or.inl (Or.inl (Or.inl hA_𝒜₁))
    · intro v hv
      obtain ⟨x, hxφ, hxK | hxA₂⟩ := hφV'_meets_𝒜₂ v hv
      · exact ⟨x, hxφ, Or.inl hxK⟩
      · obtain ⟨A, hA₂, hxA⟩ := mem_iUnion₂.mp hxA₂
        exact ⟨x, hxφ, Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl (Or.inl (Or.inr hA₂)), hxA⟩)⟩
    · intro e he
      rcases hJ.φE_mem e he with heK | heA
      · exact Or.inl heK
      · obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heA
        have hA_𝒜₃ : A ∈ 𝒜₃ := ⟨hA, φE e, heA, e, he, rfl⟩
        exact Or.inr (mem_iUnion₂.mpr ⟨A, Or.inl (Or.inr hA_𝒜₃), heA⟩)
    · intro A hA hne
      have hA_𝒜₄ : A ∈ 𝒜₄ := ⟨hA, hJ.dist_D_of_inter_K A hA hne⟩
      exact Or.inr hA_𝒜₄
  · -- Bound `{A ∈ 𝒜' | d(D(A), Σ \ Δ) < θ}.ncard ≤ 3q + 5δ`.
    have hsub_123 : {A ∈ 𝒜' | subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ} ⊆
        𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃ := by
      rintro A ⟨hA' | hA₄, hlt⟩
      · exact hA'
      · exact False.elim (not_le_of_gt hlt hA₄.2)
    have hfin_123 : (𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃).Finite :=
      (h𝒜₁_fin_card.1.union h𝒜₂_fin_card.1).union h𝒜₃_fin_card.1
    have hle1 : {A ∈ 𝒜' | subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ}.ncard ≤
        (𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃).ncard :=
      Set.ncard_le_ncard hsub_123 hfin_123
    have hle2 : (𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃).ncard ≤ (𝒜₁ ∪ 𝒜₂).ncard + 𝒜₃.ncard :=
      Set.ncard_union_le (𝒜₁ ∪ 𝒜₂) 𝒜₃
    have hle3 : (𝒜₁ ∪ 𝒜₂).ncard ≤ 𝒜₁.ncard + 𝒜₂.ncard :=
      Set.ncard_union_le 𝒜₁ 𝒜₂
    have hcard₁ := h𝒜₁_fin_card.2
    have hcard₂ := h𝒜₂_fin_card.2
    have hcard₃ := h𝒜₃_fin_card.2
    omega

/-! ## 2. Helper Lemmas and Proof of 8.2 (pages 557–559) -/

/-- Under `HasTangleMetric Γ ord T d` on a connected closed surface, if two vertices
$u, v \in V(\Gamma)$ are linked by an edge of $\Gamma$, then $d(\{u\}, \{v\}) \le 2$. -/
theorem HasTangleMetric.dist_le_two_of_isLink (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {e : Set S} {u v : S}
    (hl : Γ.toGraph.IsLink e u v) :
    d {u} {v} ≤ 2 := by
  have he : e ∈ Γ.E := hl.1
  have hu : u ∈ Γ.V := hl.2.1
  have hv : v ∈ Γ.V := hl.2.2.1
  have hu_cl : u ∈ closure e := by
    have : u ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inl rfl
    exact this.1
  have hv_cl : v ∈ closure e := by
    have : v ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inr rfl
    exact this.1
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hue : ({u} : Set S) ≠ e := by
    intro h
    obtain ⟨p, hp⟩ := he.1
    have hp_u : p = u := by
      have : p ∈ ({u} : Set S) := h ▸ hp
      exact mem_singleton_iff.mp this
    exact (he.2.1 hp).2 (hp_u ▸ hu)
  obtain ⟨hResp, K, ins, hK, hd, hdeq⟩ := hM
  rw [hdeq {u} huA {v} hvA]
  have h1 := GM14.tangleMetric_le_of_vertex_mem_closure_edge hS hK hd huA he hv hv_cl hue
  have h2 := GM11.tangleMetric_vertex_edge_le hS hResp hK hd he hu hu_cl
  exact h1.trans h2

/-- For $u, v \in V(\Gamma)$, `subsetTangleDist Γ ord d {u} {v} = d {u} {v}`. -/
theorem subsetTangleDist_singletons_eq {Γ : Drawing S} {ord : ℕ} {d : Set S → Set S → ℕ}
    {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) :
    subsetTangleDist Γ ord d {u} {v} = d {u} {v} := by
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  refine le_antisymm (subsetTangleDist_le_of_mem huA hvA ⟨u, rfl, rfl⟩ ⟨v, rfl, rfl⟩) ?_
  have hex : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ {u}).Nonempty ∧ (b ∩ {v}).Nonempty :=
    ⟨{u}, huA, {v}, hvA, ⟨u, rfl, rfl⟩, ⟨v, rfl, rfl⟩⟩
  simp only [subsetTangleDist, hex, ↓reduceIte]
  have hne : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
      (a ∩ {u}).Nonempty ∧ (b ∩ {v}).Nonempty ∧ d a b = k}.Nonempty :=
    ⟨d {u} {v}, {u}, huA, {v}, hvA, ⟨u, rfl, rfl⟩, ⟨v, rfl, rfl⟩, rfl⟩
  rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, hau, hbv, hdab⟩
  have ha_eq : a = {u} := GM12.atom_eq_of_inter_nonempty ha huA hau
  have hb_eq : b = {v} := GM12.atom_eq_of_inter_nonempty hb hvA hbv
  rw [← hdab, ha_eq, hb_eq]

omit [T2Space S] in
/-- If $k \le \operatorname{ord}$ and $k \le d(a, b)$ for all $a, b \in A(\Gamma)$ with
$a \cap X \ne \emptyset$ and $b \cap Y \ne \emptyset$, then
$k \le \operatorname{subsetTangleDist} \Gamma\ \operatorname{ord}\ d\ X\ Y$. -/
theorem le_subsetTangleDist_of_forall {Γ : Drawing S} {ord : ℕ} {d : Set S → Set S → ℕ}
    {X Y : Set S} {k : ℕ} (hk_ord : k ≤ ord)
    (h : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, (a ∩ X).Nonempty → (b ∩ Y).Nonempty → k ≤ d a b) :
    k ≤ subsetTangleDist Γ ord d X Y := by
  unfold subsetTangleDist
  split_ifs with hex
  · have hne : {m : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
        (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = m}.Nonempty := by
      rcases hex with ⟨a, ha, b, hb, haX, hbY⟩
      exact ⟨d a b, a, ha, b, hb, haX, hbY, rfl⟩
    rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, haX, hbY, hdab⟩
    rw [← hdab]
    exact h a ha b hb haX hbY
  · exact hk_ord

/-- For $u, v \in V(\Gamma)$ and $Y \subseteq \Sigma$,
$d(\{u\}, Y) \le d(\{u\}, \{v\}) + d(\{v\}, Y)$. -/
theorem subsetTangleDist_singleton_triangle (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) (Y : Set S) :
    subsetTangleDist Γ ord d {u} Y ≤ d {u} {v} + subsetTangleDist Γ ord d {v} Y := by
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  by_cases hex : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ {v}).Nonempty ∧ (b ∩ Y).Nonempty
  · have hne : {m : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
        (a ∩ {v}).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = m}.Nonempty := by
      rcases hex with ⟨a, ha, b, hb, hav, hbY⟩
      exact ⟨d a b, a, ha, b, hb, hav, hbY, rfl⟩
    have heq : subsetTangleDist Γ ord d {v} Y =
        sInf {m : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ {v}).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = m} := by
      simp only [subsetTangleDist, hex, ↓reduceIte]
    rw [heq]
    rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, hav, hbY, hdab⟩
    have ha_eq : a = {v} := GM12.atom_eq_of_inter_nonempty ha hvA hav
    rw [← hdab, ha_eq]
    exact (subsetTangleDist_le_of_mem (X := {u}) huA hb ⟨u, rfl, rfl⟩ hbY).trans
      (HasTangleMetric.triangle hS hM huA hvA hb)
  · have heq_v : subsetTangleDist Γ ord d {v} Y = ord := by
      simp only [subsetTangleDist, hex, ↓reduceIte]
    have hex_u : ¬ ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ {u}).Nonempty ∧ (b ∩ Y).Nonempty := by
      rintro ⟨_, _, b, hb, _, hbY⟩
      exact hex ⟨{v}, hvA, b, hb, ⟨v, rfl, rfl⟩, hbY⟩
    have heq_u : subsetTangleDist Γ ord d {u} Y = ord := by
      simp only [subsetTangleDist, hex_u, ↓reduceIte]
    rw [heq_u, heq_v]
    omega

/-- If $u \in V(\Gamma)$, $d(\{u\}, Y) \le k$, and $k < \operatorname{ord}$, then there exists
$z \in A(\Gamma)$ with $z \cap Y \ne \emptyset$ and $d(\{u\}, z) \le k$. -/
theorem exists_atom_of_subsetTangleDist_singleton_le {Γ : Drawing S} {ord : ℕ}
    {d : Set S → Set S → ℕ} {u : S} (hu : u ∈ Γ.V) {Y : Set S} {k : ℕ}
    (hle : subsetTangleDist Γ ord d {u} Y ≤ k) (hlt : k < ord) :
    ∃ z ∈ Γ.A, (z ∩ Y).Nonempty ∧ d {u} z ≤ k := by
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hex : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ {u}).Nonempty ∧ (b ∩ Y).Nonempty := by
    by_contra hno
    simp only [subsetTangleDist, hno, ↓reduceIte] at hle
    omega
  have hne : {m : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
      (a ∩ {u}).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = m}.Nonempty := by
    rcases hex with ⟨a, ha, b, hb, hau, hbY⟩
    exact ⟨d a b, a, ha, b, hb, hau, hbY, rfl⟩
  have hsInf_le : sInf {m : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
      (a ∩ {u}).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = m} ≤ k := by
    simpa only [subsetTangleDist, hex, ↓reduceIte] using hle
  rcases Nat.sInf_mem hne with ⟨a, ha, z, hz, hau, hzY, hdaz⟩
  have ha_eq : a = {u} := GM12.atom_eq_of_inter_nonempty ha huA hau
  exact ⟨z, hz, hzY, by rw [← ha_eq, hdaz]; exact hsInf_le⟩

omit [T2Space S] in
/-- In a sphere $\Sigma$, the complement of the interior of a closed disc $\Delta'$ is a closed
disc $\Delta_c = (\Sigma \setminus \Delta') \cup \operatorname{bd}(\Delta')$ with
$\operatorname{bd}(\Delta_c) = \operatorname{bd}(\Delta')$ and
$\Delta_c \setminus \operatorname{bd}(\Delta_c) = \Sigma \setminus \Delta'$. -/
theorem exists_complementary_closedDisc_in_sphere (hSph : IsSphere S) {Δ' : Set S}
    (hΔ' : IsClosedDisc Δ') :
    ∃ Δ_c : Set S,
      IsClosedDisc Δ_c ∧
      subBd Δ_c = subBd Δ' ∧
      Δ_c = (Set.univ \ Δ') ∪ subBd Δ' ∧
      Δ_c \ subBd Δ_c = Set.univ \ Δ' := by
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hSph
  have hbd_eq : subBd Δ' = discBd Δ' := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hΔ']
  have hOArc : IsOArc (discBd Δ') := hΔ'.isOArc_discBd
  obtain ⟨Δ₁, Δ₂, hne, hD₁, hD₂, hbd₁, hbd₂, hcup, hcap, -, huniq⟩ :=
    sphere_disc S hSph (discBd Δ') hOArc
  rcases huniq Δ' hΔ' rfl with h_eq₁ | h_eq₂
  · subst h_eq₁
    refine ⟨Δ₂, hD₂, ?_, ?_, ?_⟩
    · rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hD₂, hbd₂, hbd_eq]
    · ext x
      simp only [mem_union, mem_sdiff, mem_univ, true_and, hbd_eq]
      constructor
      · intro hx₂
        by_cases hx₁ : x ∈ Δ'
        · exact Or.inr (hcap ▸ ⟨hx₁, hx₂⟩)
        · exact Or.inl hx₁
      · rintro (hx₁ | hxbd)
        · rcases (hcup ▸ mem_univ x : x ∈ Δ' ∪ Δ₂) with h | h
          · exact False.elim (hx₁ h)
          · exact h
        · exact Surface.discBd_subset Δ₂ (hbd₂.symm ▸ hxbd)
    · ext x
      have hbd₂' : subBd Δ₂ = discBd Δ' := by
        rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hD₂, hbd₂]
      simp only [mem_sdiff, mem_univ, true_and, hbd₂']
      constructor
      · rintro ⟨hx₂, hxbd⟩ hx₁
        exact hxbd (hcap ▸ ⟨hx₁, hx₂⟩)
      · intro hx₁
        rcases (hcup ▸ mem_univ x : x ∈ Δ' ∪ Δ₂) with h | h
        · exact False.elim (hx₁ h)
        · exact ⟨h, fun hxbd => hx₁ (Surface.discBd_subset Δ' hxbd)⟩
  · subst h_eq₂
    refine ⟨Δ₁, hD₁, ?_, ?_, ?_⟩
    · rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hD₁, hbd₁, hbd_eq]
    · ext x
      simp only [mem_union, mem_sdiff, mem_univ, true_and, hbd_eq]
      constructor
      · intro hx₁
        by_cases hx₂ : x ∈ Δ'
        · exact Or.inr (hcap ▸ ⟨hx₁, hx₂⟩)
        · exact Or.inl hx₂
      · rintro (hx₂ | hxbd)
        · rcases (hcup ▸ mem_univ x : x ∈ Δ₁ ∪ Δ') with h | h
          · exact h
          · exact False.elim (hx₂ h)
        · exact Surface.discBd_subset Δ₁ (hbd₁.symm ▸ hxbd)
    · ext x
      have hbd₁' : subBd Δ₁ = discBd Δ' := by
        rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hD₁, hbd₁]
      simp only [mem_sdiff, mem_univ, true_and, hbd₁']
      constructor
      · rintro ⟨hx₁, hxbd⟩ hx₂
        exact hxbd (hcap ▸ ⟨hx₁, hx₂⟩)
      · intro hx₂
        rcases (hcup ▸ mem_univ x : x ∈ Δ₁ ∪ Δ') with h | h
        · exact ⟨h, fun hxbd => hx₂ (Surface.discBd_subset Δ' hxbd)⟩
        · exact False.elim (hx₂ h)

/-- **Graph Minors XXII, 8.2 Claim (1)** (Section 8, page 557):
"(1) For $3 \le n \le \theta - 3$, there is a closed disc $\Delta_n \subseteq \Sigma$ such that
$v^* \notin \Delta_n$, $\Delta \subseteq \Delta_n$, $bd(\Delta_n) \subseteq U(\Gamma)$,
$d(v^*, \Delta_n) \ge n$, and $d(v^*, x) \le n + 2$ for every $x \in A(\Gamma)$ with
$x \not\subseteq \Delta_n \setminus bd(\Delta_n)$." -/
theorem lemma_8_2_claim_1 {q : ℕ}
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
    (hdist_v_star : θ ≤ subsetTangleDist Γ ord d {v_star} Δ)
    {n : ℕ} (hn3 : 3 ≤ n) (hnθ : n + 3 ≤ θ) :
    ∃ Δ_n : Set S,
      IsClosedDisc Δ_n ∧
      v_star ∉ Δ_n ∧
      Δ ⊆ Δ_n ∧
      subBd Δ_n ⊆ Γ.U ∧
      n ≤ subsetTangleDist Γ ord d {v_star} Δ_n ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ_n \ subBd Δ_n) → d {v_star} x ≤ n + 2) := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hJ.v_star_mem.1, rfl⟩)
  have hn_ord : n + 3 ≤ ord := hnθ.trans hJ.θ_le_ord
  obtain ⟨Δ', hΔ'_disc, hΔ'_bd, hΔ'_le, hΔ'_ge, hv_star_in⟩ :=
    gm22_theorem_5_1 Γ ord n T d {v_star} hS hJ.hasMetric hv_star_A (by omega) hn_ord
  obtain ⟨Δ_n, hΔn_disc, hΔn_bd_eq, hΔn_eq, hΔn_int_eq⟩ :=
    exists_complementary_closedDisc_in_sphere hJ.isSphere hΔ'_disc
  refine ⟨Δ_n, hΔn_disc, ?_, ?_, hΔn_bd_eq ▸ hΔ'_bd, ?_, ?_⟩
  · -- `v_star ∉ Δ_n` because `v_star ∈ Δ' \ subBd Δ' = univ \ Δ_n`.
    have hv_in : v_star ∈ Δ' \ subBd Δ' := hv_star_in rfl
    intro hv_Δn
    rcases hΔn_eq ▸ hv_Δn with ⟨_, hv_not_Δ'⟩ | hv_bd
    · exact hv_not_Δ' hv_in.1
    · exact hv_in.2 hv_bd
  · -- `Δ ⊆ Δ_n`: if `p ∈ Δ ∩ (Δ' \ subBd Δ')`, the atom `a` of `p` meets both `Δ` and `Δ'`,
    -- giving `n + 3 ≤ θ ≤ d(v^*, a) ≤ n + 2`, a contradiction.
    intro p hpΔ
    rw [hΔn_eq]
    by_cases hp_in : p ∈ Δ' \ subBd Δ'
    · obtain ⟨a, ha, hpa⟩ := GM11.exists_atom Γ p
      have hd_le : d {v_star} a ≤ n + 2 := hΔ'_le a ha ⟨p, hpa, hp_in.1⟩
      have hd_ge : θ ≤ d {v_star} a :=
        hdist_v_star.trans (subsetTangleDist_le_of_mem hv_star_A ha ⟨v_star, rfl, rfl⟩ ⟨p, hpa, hpΔ⟩)
      omega
    · by_cases hp_Δ' : p ∈ Δ'
      · exact Or.inr (by_contra fun h => hp_in ⟨hp_Δ', h⟩)
      · exact Or.inl ⟨mem_univ p, hp_Δ'⟩
  · -- `n ≤ subsetTangleDist Γ ord d {v_star} Δ_n`.
    refine le_subsetTangleDist_of_forall (by omega) fun a ha b hb hav hbΔn => ?_
    have ha_eq : a = {v_star} := GM12.atom_eq_of_inter_nonempty ha hv_star_A hav
    subst ha_eq
    refine hΔ'_ge b hb ?_
    intro hb_sub
    rcases hbΔn with ⟨p, hpb, hpΔn⟩
    have hp_in : p ∈ Δ' \ subBd Δ' := hb_sub hpb
    rcases hΔn_eq ▸ hpΔn with ⟨_, hp_not⟩ | hp_bd
    · exact hp_not hp_in.1
    · exact hp_in.2 hp_bd
  · -- For `x ∈ Γ.A` with `¬ (x ⊆ Δ_n \ subBd Δ_n)`, `d {v_star} x ≤ n + 2`.
    intro x hx hx_not
    rw [hΔn_int_eq] at hx_not
    obtain ⟨p, hpx, hp_not_sdiff⟩ := not_subset.mp hx_not
    have hp_Δ' : p ∈ Δ' := by_contra fun h => hp_not_sdiff ⟨mem_univ p, h⟩
    exact hΔ'_le x hx ⟨p, hpx, hp_Δ'⟩

/-- **Graph Minors XXII, 8.2 Claim (2)** (Section 8, page 557):
"(2) There is a closed disc $\Delta' \subseteq \Sigma$ such that $v^* \notin \Delta'$,
$\Delta \subseteq \Delta'$, $bd(\Delta') \subseteq U(\Gamma)$,
$d(v^*, \Delta') \ge (\theta' + 2\eta + 7)(\tau + 1)$, and for each $A \in \mathcal{B}$, either
$D(A) \cap \Delta' = \emptyset$ or $d(D(A), \Sigma \setminus \Delta') \ge \theta'$." -/
theorem lemma_8_2_claim_2 {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ θ' η τ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hℬ_sub : ℬ ⊆ 𝒜)
    (hθ'_ge : 4 ≤ θ')
    (hθ_eq : θ = 2 * (τ + 1) * (θ' + 2 * η + 7) + 3)
    (h𝒜'_card : {A ∈ ℬ | subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ}.ncard ≤ τ)
    (hdist_v_star : θ ≤ subsetTangleDist Γ ord d {v_star} Δ) :
    ∃ Δ' : Set S,
      IsClosedDisc Δ' ∧
      v_star ∉ Δ' ∧
      Δ ⊆ Δ' ∧
      subBd Δ' ⊆ Γ.U ∧
      (θ' + 2 * η + 7) * (τ + 1) ≤ subsetTangleDist Γ ord d {v_star} Δ' ∧
      {A ∈ ℬ | Disjoint (D A) Δ'}.ncard ≤ τ ∧
      (∀ A ∈ ℬ, Disjoint (D A) Δ' ∨
        θ' ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ')) := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hJ.v_star_mem.1, rfl⟩)
  let step := θ' + 2 * η + 7
  let n : ℕ → ℕ := fun i => (τ + i + 1) * step
  have hn_bounds : ∀ i ≤ τ + 1, 3 ≤ n i ∧ n i + 3 ≤ θ := by
    intro i hi
    dsimp only [n, step]
    have : 11 ≤ θ' + 2 * η + 7 := by omega
    have hle : (τ + i + 1) * (θ' + 2 * η + 7) ≤ 2 * (τ + 1) * (θ' + 2 * η + 7) :=
      Nat.mul_le_mul_right _ (by omega)
    have hge : 1 * 11 ≤ (τ + i + 1) * (θ' + 2 * η + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  -- Choose `Δ_seq i` for `i ≤ τ + 1` using Claim (1).
  have hex_Δ : ∀ i : Fin (τ + 2), ∃ Δ_i : Set S,
      IsClosedDisc Δ_i ∧
      v_star ∉ Δ_i ∧
      Δ ⊆ Δ_i ∧
      subBd Δ_i ⊆ Γ.U ∧
      n i.1 ≤ subsetTangleDist Γ ord d {v_star} Δ_i ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ_i \ subBd Δ_i) → d {v_star} x ≤ n i.1 + 2) := by
    intro i
    have hb := hn_bounds i.1 (by omega)
    exact lemma_8_2_claim_1 hJ hdist_v_star hb.1 hb.2
  let Δ_seq : Fin (τ + 2) → Set S := fun i => Classical.choose (hex_Δ i)
  have hΔ_spec : ∀ i : Fin (τ + 2),
      IsClosedDisc (Δ_seq i) ∧
      v_star ∉ Δ_seq i ∧
      Δ ⊆ Δ_seq i ∧
      subBd (Δ_seq i) ⊆ Γ.U ∧
      n i.1 ≤ subsetTangleDist Γ ord d {v_star} (Δ_seq i) ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ_seq i \ subBd (Δ_seq i)) → d {v_star} x ≤ n i.1 + 2) :=
    fun i => Classical.choose_spec (hex_Δ i)
  let 𝒜_seq : Fin (τ + 2) → Set (Graph α β) :=
    fun i => {A ∈ ℬ | Disjoint (D A) (Δ_seq i)}
  let 𝒜' : Set (Graph α β) := {A ∈ ℬ | subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ}
  have hfin_ℬ : ℬ.Finite := hJ.finite_𝒜.subset hℬ_sub
  -- Any `A ∈ ℬ` with `Disjoint (D A) Δ` lies in `𝒜'`.
  have h𝒜_seq_sub_𝒜' : ∀ i : Fin (τ + 2), 𝒜_seq i ⊆ 𝒜' := by
    rintro i A ⟨hAℬ, hdis⟩
    refine ⟨hAℬ, ?_⟩
    have hA : A ∈ 𝒜 := hℬ_sub hAℬ
    have hD_sub : D A ⊆ Set.univ \ Δ := by
      intro p hpD
      exact ⟨mem_univ p, fun hpΔ => Set.disjoint_left.mp hdis hpD ((hΔ_spec i).2.2.1 hpΔ)⟩
    obtain ⟨hDisc_A, _, _⟩ := hJ.disc_D A hA
    obtain ⟨h, g, c⟩ := hDisc_A.exists_isChart
    have hp₀_mem : g 0 ∈ D A := c.gm (Metric.mem_closedBall_self zero_le_one)
    obtain ⟨a₀, ha₀, hpa₀⟩ := GM11.exists_atom Γ (g 0)
    have hd0 : d a₀ a₀ = 0 := HasTangleMetric.self_eq_zero hJ.hasMetric ha₀
    have hle0 : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) ≤ 0 := by
      rw [← hd0]
      exact subsetTangleDist_le_of_mem ha₀ ha₀ ⟨g 0, hpa₀, hp₀_mem⟩
        ⟨g 0, hpa₀, hD_sub hp₀_mem⟩
    have := hJ.four_le_θ
    omega
  -- Show `Δ_seq j ⊆ Δ_seq i` whenever `i < j`.
  have hΔ_anti : ∀ i j : Fin (τ + 2), i < j → Δ_seq j ⊆ Δ_seq i := by
    intro i j hij p hpj
    by_contra hpi
    have hp_not_int : ¬ (({p} : Set S) ⊆ Δ_seq i \ subBd (Δ_seq i)) :=
      fun h => hpi (h rfl).1
    obtain ⟨a, ha, hpa⟩ := GM11.exists_atom Γ p
    have ha_not_int : ¬ (a ⊆ Δ_seq i \ subBd (Δ_seq i)) :=
      fun h => hpi (h hpa).1
    have hd_le : d {v_star} a ≤ n i.1 + 2 := (hΔ_spec i).2.2.2.2.2 a ha ha_not_int
    have hd_ge : n j.1 ≤ d {v_star} a :=
      ((hΔ_spec j).2.2.2.2.1).trans
        (subsetTangleDist_le_of_mem hv_star_A ha ⟨v_star, rfl, rfl⟩ ⟨p, hpa, hpj⟩)
    have hstep_ge : 11 ≤ step := by dsimp [step]; omega
    have hnij : n i.1 + 11 ≤ n j.1 := by
      dsimp only [n]
      have : (τ + i.1 + 1 + 1) * step ≤ (τ + j.1 + 1) * step :=
        Nat.mul_le_mul_right step (by omega)
      linarith
    omega
  have h𝒜_mono : ∀ i j : Fin (τ + 2), i < j → 𝒜_seq i ⊆ 𝒜_seq j := by
    rintro i j hij A ⟨hAℬ, hdis⟩
    exact ⟨hAℬ, hdis.mono_right (hΔ_anti i j hij)⟩
  -- At `i = τ + 1`, `|𝒜_seq (τ + 1)| ≤ |𝒜'| ≤ τ < τ + 1`.
  let i_last : Fin (τ + 2) := ⟨τ + 1, by omega⟩
  have hlast_lt : (𝒜_seq i_last).ncard < i_last.1 := by
    have hle : (𝒜_seq i_last).ncard ≤ 𝒜'.ncard :=
      Set.ncard_le_ncard (h𝒜_seq_sub_𝒜' i_last) (hfin_ℬ.subset fun _ h => h.1)
    have h𝒜'_le : 𝒜'.ncard ≤ τ := h𝒜'_card
    have hi_last : i_last.1 = τ + 1 := rfl
    omega
  have hex_i : ∃ k : ℕ, ∃ hk : k < τ + 2, (𝒜_seq ⟨k, hk⟩).ncard < k :=
    ⟨τ + 1, by omega, hlast_lt⟩
  let i₀ := Nat.find hex_i
  obtain ⟨hi₀_lt, hi₀_card⟩ := Nat.find_spec hex_i
  have hi₀_pos : 1 ≤ i₀ := by
    by_contra h0
    have hi₀_eq : i₀ = 0 := by omega
    omega
  let idx : Fin (τ + 2) := ⟨i₀, hi₀_lt⟩
  let idx_prev : Fin (τ + 2) := ⟨i₀ - 1, by omega⟩
  have hprev_ge : i₀ - 1 ≤ (𝒜_seq idx_prev).ncard := by
    by_contra hlt
    exact Nat.find_min hex_i (by omega : i₀ - 1 < i₀) ⟨by omega, not_le.mp hlt⟩
  have hsub_prev : 𝒜_seq idx_prev ⊆ 𝒜_seq idx :=
    h𝒜_mono idx_prev idx (by change i₀ - 1 < i₀; omega)
  have hcard_eq : (𝒜_seq idx).ncard = (𝒜_seq idx_prev).ncard := by
    have hle := Set.ncard_le_ncard hsub_prev (hfin_ℬ.subset fun _ h => h.1)
    have hi₀_card' : (𝒜_seq idx).ncard < i₀ := hi₀_card
    omega
  have h𝒜_eq : 𝒜_seq idx_prev = 𝒜_seq idx :=
    Set.eq_of_subset_of_ncard_le hsub_prev hcard_eq.le (hfin_ℬ.subset fun _ h => h.1)
  let Δ' := Δ_seq idx_prev
  refine ⟨Δ', (hΔ_spec idx_prev).1, (hΔ_spec idx_prev).2.1, (hΔ_spec idx_prev).2.2.1,
    (hΔ_spec idx_prev).2.2.2.1, ?_, ?_, ?_⟩
  · -- `(θ' + 2η + 7)(τ + 1) ≤ n(i₀ - 1) ≤ subsetTangleDist Γ ord d {v_star} Δ'`.
    have h1 : (θ' + 2 * η + 7) * (τ + 1) ≤ n idx_prev.1 := by
      dsimp only [n, step, idx_prev]
      rw [Nat.mul_comm (θ' + 2 * η + 7) (τ + 1)]
      exact Nat.mul_le_mul_right _ (by omega)
    exact h1.trans (hΔ_spec idx_prev).2.2.2.2.1
  · -- `{A ∈ ℬ | Disjoint (D A) Δ'}.ncard ≤ τ`.
    change (𝒜_seq idx_prev).ncard ≤ τ
    rw [h𝒜_eq]
    have hi₀_card' : (𝒜_seq idx).ncard < i₀ := hi₀_card
    have : i₀ < τ + 2 := hi₀_lt
    omega
  · -- For `A ∈ ℬ`, either `Disjoint (D A) Δ'` or `θ' ≤ subsetTangleDist Γ ord d (D A) (univ \ Δ')`.
    intro A hAℬ
    by_cases hA_mem : A ∈ 𝒜_seq idx
    · rw [← h𝒜_eq] at hA_mem
      exact Or.inl hA_mem.2
    · right
      have hnot_dis : ¬ Disjoint (D A) (Δ_seq idx) := fun h => hA_mem ⟨hAℬ, h⟩
      obtain ⟨p₀, hp₀D, hp₀Δ⟩ := Set.not_disjoint_iff.mp hnot_dis
      obtain ⟨a₀, ha₀, hpa₀⟩ := GM11.exists_atom Γ p₀
      have hd_a₀ : n idx.1 ≤ d {v_star} a₀ :=
        ((hΔ_spec idx).2.2.2.2.1).trans
          (subsetTangleDist_le_of_mem hv_star_A ha₀ ⟨v_star, rfl, rfl⟩ ⟨p₀, hpa₀, hp₀Δ⟩)
      have hθ'_ord : θ' ≤ ord := by
        have := hJ.θ_le_ord
        have : θ' ≤ θ := by
          rw [hθ_eq]
          have : 1 * θ' ≤ 2 * (τ + 1) * (θ' + 2 * η + 7) :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
        omega
      refine le_subsetTangleDist_of_forall hθ'_ord fun y hy z hz hyD hzOut => ?_
      have hd_ya₀ : d a₀ y ≤ 3 :=
        hJ.dist_le_three_of_meets_D (hℬ_sub hAℬ) ha₀ hy ⟨p₀, hpa₀, hp₀D⟩ hyD
      have hz_not_int : ¬ (z ⊆ Δ' \ subBd Δ') := by
        rcases hzOut with ⟨q, hqz, _, hq_not_Δ'⟩
        exact fun h => hq_not_Δ' (h hqz).1
      have hd_z : d {v_star} z ≤ n idx_prev.1 + 2 :=
        (hΔ_spec idx_prev).2.2.2.2.2 z hz hz_not_int
      have htri₁ : d {v_star} a₀ ≤ d {v_star} y + d y a₀ :=
        HasTangleMetric.triangle hS hJ.hasMetric hv_star_A hy ha₀
      have hcomm₁ : d y a₀ = d a₀ y := HasTangleMetric.comm hJ.hasMetric hy ha₀
      have htri₂ : d {v_star} y ≤ d {v_star} z + d z y :=
        HasTangleMetric.triangle hS hJ.hasMetric hv_star_A hz hy
      have hcomm₂ : d z y = d y z := HasTangleMetric.comm hJ.hasMetric hz hy
      have hn_diff : n idx.1 = n idx_prev.1 + (θ' + 2 * η + 7) := by
        dsimp only [n, step, idx, idx_prev]
        have : τ + i₀ + 1 = (τ + (i₀ - 1) + 1) + 1 := by omega
        rw [this, Nat.succ_mul]
      omega

/-- Every $O$-arc $F \subseteq U(\Gamma)$ meets $V(\Gamma)$. -/
theorem nonempty_inter_V_of_isOArc_subset_U {Γ : Drawing S} {F : Set S}
    (hF : IsOArc F) (hFU : F ⊆ Γ.U) :
    (F ∩ Γ.V).Nonempty := by
  obtain ⟨φ⟩ := id hF
  let p : S := (φ 1).1
  have hpF : p ∈ F := (φ 1).2
  by_cases hpV : p ∈ Γ.V
  · exact ⟨p, hpF, hpV⟩
  · obtain ⟨e, he, hpe⟩ := Γ.exists_edge_of_mem (hFU hpF) hpV
    have hnot_dis : ¬ Disjoint e F := Set.not_disjoint_iff.mpr ⟨p, hpe, hpF⟩
    have heF : e ⊆ F := (GM14.edge_subset_or_disjoint_of_isOArc hF hFU he).resolve_right hnot_dis
    have hclF : closure e ⊆ F := (GM14.IsOArc.isClosed hF).closure_subset_iff.mpr heF
    rcases Γ.edge_cond e he with ⟨x, _, _, hcap, _⟩ | ⟨x, hcap, _⟩
    · have hx : x ∈ closure e ∩ Γ.V := by rw [hcap]; exact Or.inl rfl
      exact ⟨x, hclF hx.1, hx.2⟩
    · have hx : x ∈ closure e ∩ Γ.V := by rw [hcap]; rfl
      exact ⟨x, hclF hx.1, hx.2⟩

/-- Along any walk $P$ of $\Gamma$ from $a$ to $b$, if $d(v^*, a) < K$ and $K \le d(v^*, b)$, then
there is a vertex $w \in V(\Gamma)$ with $K \le d(v^*, w) \le K + 1$. -/
theorem exists_vertex_on_walk_dist_between (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {v_star : S} (hv_star : v_star ∈ Γ.V)
    {a b : S} (P : GraphWalk Γ.toGraph a b) {K : ℕ}
    (ha_lt : d {v_star} {a} < K) (hb_ge : K ≤ d {v_star} {b}) :
    ∃ w ∈ Γ.V, K ≤ d {v_star} {w} ∧ d {v_star} {w} ≤ K + 1 := by
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hv_star, rfl⟩)
  induction P with
  | nil hx => omega
  | @cons x y z e hl r ih =>
    have hx : x ∈ Γ.V := hl.2.1
    have hy : y ∈ Γ.V := hl.2.2.1
    have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hx, rfl⟩)
    have hyA : ({y} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨y, hy, rfl⟩)
    by_cases hy_ge : K ≤ d {v_star} {y}
    · have hd_xy : d {x} {y} ≤ 2 := HasTangleMetric.dist_le_two_of_isLink hS hM hl
      have htri : d {v_star} {y} ≤ d {v_star} {x} + d {x} {y} :=
        HasTangleMetric.triangle hS hM hv_star_A hxA hyA
      exact ⟨y, hy, hy_ge, by omega⟩
    · exact ih (not_le.mp hy_ge) hb_ge

/-- **Graph Minors XXII, 8.2 Claim (3)** (Section 8, page 558):
"(3) There are vertices $v_1, \dots, v_{\tau}$ of $\Gamma$ such that
(i) for $1 \le i \le \tau$, $d(v^*, v_i) \ge \theta' + \eta + 3$,
(ii) for $1 \le i \le \tau$, $d(v_i, \Delta') \ge \eta + 4$, and
(iii) for $1 \le i < j \le \tau$, $d(v_i, v_j) \ge \theta' + 2\eta + 6$." -/
theorem lemma_8_2_claim_3 {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ θ' η τ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ Δ' : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hΔ'_disc : IsClosedDisc Δ') (hΔ'_bd : subBd Δ' ⊆ Γ.U)
    (hΔ'_dist : (θ' + 2 * η + 7) * (τ + 1) ≤ subsetTangleDist Γ ord d {v_star} Δ') :
    ∃ v_seq : Fin τ → S,
      (∀ i : Fin τ, v_seq i ∈ Γ.V) ∧
      (∀ i : Fin τ, θ' + η + 3 ≤ subsetTangleDist Γ ord d {v_star} {v_seq i}) ∧
      (∀ i : Fin τ, η + 4 ≤ subsetTangleDist Γ ord d {v_seq i} Δ') ∧
      (∀ i j : Fin τ, i < j → θ' + 2 * η + 6 ≤ subsetTangleDist Γ ord d {v_seq i} {v_seq j}) := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hv_star : v_star ∈ Γ.V := hJ.v_star_mem.1
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hv_star, rfl⟩)
  -- `subBd Δ'` is an O-arc in `Γ.U`, so it contains a vertex `u ∈ subBd Δ' ∩ Γ.V`.
  have hOArc_bd : IsOArc (subBd Δ') := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hΔ'_disc]
    exact hΔ'_disc.isOArc_discBd
  obtain ⟨u, hu_bd, huV⟩ := nonempty_inter_V_of_isOArc_subset_U hOArc_bd hΔ'_bd
  have hu_Δ' : u ∈ Δ' := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hΔ'_disc] at hu_bd
    exact Surface.discBd_subset Δ' hu_bd
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, huV, rfl⟩)
  have hd_u : (θ' + 2 * η + 7) * (τ + 1) ≤ d {v_star} {u} :=
    hΔ'_dist.trans (subsetTangleDist_le_of_mem hv_star_A huA ⟨v_star, rfl, rfl⟩ ⟨u, rfl, hu_Δ'⟩)
  obtain ⟨P⟩ := GM12.exists_walk_of_open_disc_regions hS hJ.isTwoCell.2 hv_star huV
  have hd_self : d {v_star} {v_star} = 0 := HasTangleMetric.self_eq_zero hJ.hasMetric hv_star_A
  let step := θ' + 2 * η + 7
  have hex_vi : ∀ i : Fin τ, ∃ w ∈ Γ.V,
      step * (i.1 + 1) ≤ d {v_star} {w} ∧ d {v_star} {w} ≤ step * (i.1 + 1) + 1 := by
    intro i
    have hK_pos : d {v_star} {v_star} < step * (i.1 + 1) := by
      rw [hd_self]
      dsimp only [step]
      exact Nat.mul_pos (by omega) (by omega)
    have hK_le_u : step * (i.1 + 1) ≤ d {v_star} {u} := by
      have : step * (i.1 + 1) ≤ step * (τ + 1) := Nat.mul_le_mul_left step (by omega)
      exact this.trans hd_u
    exact exists_vertex_on_walk_dist_between hS hJ.hasMetric hv_star P hK_pos hK_le_u
  let v_seq : Fin τ → S := fun i => Classical.choose (hex_vi i)
  have hv_spec : ∀ i : Fin τ, v_seq i ∈ Γ.V ∧
      step * (i.1 + 1) ≤ d {v_star} {v_seq i} ∧
      d {v_star} {v_seq i} ≤ step * (i.1 + 1) + 1 :=
    fun i => Classical.choose_spec (hex_vi i)
  refine ⟨v_seq, fun i => (hv_spec i).1, ?_, ?_, ?_⟩
  · -- (i) `θ' + η + 3 ≤ d(v^*, v_i)`.
    intro i
    rw [subsetTangleDist_singletons_eq hv_star (hv_spec i).1]
    have h1 := (hv_spec i).2.1
    have h2 : step * 1 ≤ step * (i.1 + 1) := Nat.mul_le_mul_left step (by omega)
    dsimp only [step] at h1 h2
    omega
  · -- (ii) `η + 4 ≤ d(v_i, Δ')`.
    intro i
    have htri := subsetTangleDist_singleton_triangle hS hJ.hasMetric hv_star (hv_spec i).1 Δ'
    have h1 := (hv_spec i).2.2
    have h2 : step * (i.1 + 1) + step ≤ step * (τ + 1) := by
      have : i.1 + 1 + 1 ≤ τ + 1 := by omega
      calc step * (i.1 + 1) + step = step * (i.1 + 1 + 1) := by ring
        _ ≤ step * (τ + 1) := Nat.mul_le_mul_left step this
    dsimp only [step] at h1 h2
    omega
  · -- (iii) `θ' + 2η + 6 ≤ d(v_i, v_j)` for `i < j`.
    intro i j hij
    have hvi : v_seq i ∈ Γ.V := (hv_spec i).1
    have hvj : v_seq j ∈ Γ.V := (hv_spec j).1
    have hviA : ({v_seq i} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_seq i, hvi, rfl⟩)
    have hvjA : ({v_seq j} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_seq j, hvj, rfl⟩)
    rw [subsetTangleDist_singletons_eq hvi hvj]
    have htri : d {v_star} {v_seq j} ≤ d {v_star} {v_seq i} + d {v_seq i} {v_seq j} :=
      HasTangleMetric.triangle hS hJ.hasMetric hv_star_A hviA hvjA
    have h1 := (hv_spec i).2.2
    have h2 := (hv_spec j).2.1
    have h3 : step * (i.1 + 1) + step ≤ step * (j.1 + 1) := by
      have : i.1 + 1 + 1 ≤ j.1 + 1 := by omega
      calc step * (i.1 + 1) + step = step * (i.1 + 1 + 1) := by ring
        _ ≤ step * (j.1 + 1) := Nat.mul_le_mul_left step this
    dsimp only [step] at h1 h2 h3
    omega

/-- **Graph Minors XXII, 8.2 Claim (4)** (Section 8, page 558):
"(4) The following hold:
(i) For $1 \le i \le t$, $d(v^*, D(A'_i)) \ge \theta'$.
(ii) For $1 \le i \le t$, $D(A'_i) \cap \Delta = \emptyset$.
(iii) For $1 \le i < j \le t$, $d(D(A'_i), D(A'_j)) \ge \theta'$."
We also record $$D(A'_i) \cap \Delta' = \emptyset$$, which the paper's subproof of (4)(ii) on page 558
actually establishes (using $$\eta + 4 \le d(v_i, \Delta')$$) and which page 559 uses when applying
7.4 with $$\Delta$$ replaced by $$\Delta'$$. -/
theorem lemma_8_2_claim_4 {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ θ' η τ t ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ Δ' : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hθ_ord : θ' + 2 * η + 7 ≤ ord)
    (hΔ_sub : Δ ⊆ Δ')
    (ht_le : t ≤ τ)
    {v_seq : Fin τ → S}
    (hv_V : ∀ i : Fin τ, v_seq i ∈ Γ.V)
    (hv_i : ∀ i : Fin τ, θ' + η + 3 ≤ subsetTangleDist Γ ord d {v_star} {v_seq i})
    (hv_ii : ∀ i : Fin τ, η + 4 ≤ subsetTangleDist Γ ord d {v_seq i} Δ')
    (hv_iii : ∀ i j : Fin τ, i < j → θ' + 2 * η + 6 ≤ subsetTangleDist Γ ord d {v_seq i} {v_seq j})
    {A_fam' : Fin t → Graph α β}
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hA'_dist : ∀ i : Fin t,
      subsetTangleDist Γ ord d {v_seq ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩} (D (A_fam' i)) ≤ η) :
    (∀ i : Fin t, θ' ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i))) ∧
    (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ' ∧ Disjoint (D (A_fam' i)) Δ) ∧
    (∀ i j : Fin t, i < j → θ' ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j))) := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hv_star : v_star ∈ Γ.V := hJ.v_star_mem.1
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hv_star, rfl⟩)
  let castIdx (i : Fin t) : Fin τ := ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩
  have hex_zi : ∀ i : Fin t, ∃ z_i ∈ Γ.A,
      (z_i ∩ D (A_fam' i)).Nonempty ∧ d {v_seq (castIdx i)} z_i ≤ η := by
    intro i
    exact exists_atom_of_subsetTangleDist_singleton_le (hv_V (castIdx i)) (hA'_dist i) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · -- (i) For `1 ≤ i ≤ t`, `θ' ≤ d(v^*, D(A'_i))`.
    intro i
    obtain ⟨z_i, hz_i, hz_i_D, hd_vi_zi⟩ := hex_zi i
    have hvi : v_seq (castIdx i) ∈ Γ.V := hv_V (castIdx i)
    have hviA : ({v_seq (castIdx i)} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨_, hvi, rfl⟩)
    refine le_subsetTangleDist_of_forall (by omega) fun a ha z hz hav hzD => ?_
    have ha_eq : a = {v_star} := GM12.atom_eq_of_inter_nonempty ha hv_star_A hav
    subst ha_eq
    have hd_z_zi : d z z_i ≤ 3 :=
      hJ.dist_le_three_of_meets_D (hA'_mem i) hz hz_i hzD hz_i_D
    have hd_v_vi : θ' + η + 3 ≤ d {v_star} {v_seq (castIdx i)} := by
      have := hv_i (castIdx i)
      rwa [subsetTangleDist_singletons_eq hv_star hvi] at this
    have htri₁ : d {v_star} {v_seq (castIdx i)} ≤ d {v_star} z + d z {v_seq (castIdx i)} :=
      HasTangleMetric.triangle hS hJ.hasMetric hv_star_A hz hviA
    have htri₂ : d z {v_seq (castIdx i)} ≤ d z z_i + d z_i {v_seq (castIdx i)} :=
      HasTangleMetric.triangle hS hJ.hasMetric hz hz_i hviA
    have hcomm : d z_i {v_seq (castIdx i)} = d {v_seq (castIdx i)} z_i :=
      HasTangleMetric.comm hJ.hasMetric hz_i hviA
    omega
  · -- (ii) For `1 ≤ i ≤ t`, `Disjoint (D (A'_i)) Δ'` and `Disjoint (D (A'_i)) Δ`.
    intro i
    have hdis_Δ' : Disjoint (D (A_fam' i)) Δ' := by
      rw [Set.disjoint_iff_inter_eq_empty]
      by_contra hne
      obtain ⟨p, hpD, hpΔ'⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨z, hz, hpz⟩ := GM11.exists_atom Γ p
      obtain ⟨z_i, hz_i, hz_i_D, hd_vi_zi⟩ := hex_zi i
      have hvi : v_seq (castIdx i) ∈ Γ.V := hv_V (castIdx i)
      have hviA : ({v_seq (castIdx i)} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨_, hvi, rfl⟩)
      have hd_zi_z : d z_i z ≤ 3 :=
        hJ.dist_le_three_of_meets_D (hA'_mem i) hz_i hz hz_i_D ⟨p, hpz, hpD⟩
      have hd_vi_z : η + 4 ≤ d {v_seq (castIdx i)} z :=
        (hv_ii (castIdx i)).trans
          (subsetTangleDist_le_of_mem hviA hz ⟨_, rfl, rfl⟩ ⟨p, hpz, hpΔ'⟩)
      have htri : d {v_seq (castIdx i)} z ≤ d {v_seq (castIdx i)} z_i + d z_i z :=
        HasTangleMetric.triangle hS hJ.hasMetric hviA hz_i hz
      omega
    exact ⟨hdis_Δ', hdis_Δ'.mono_right hΔ_sub⟩
  · -- (iii) For `1 ≤ i < j ≤ t`, `θ' ≤ d(D(A'_i), D(A'_j))`.
    intro i j hij
    obtain ⟨z_i, hz_i, hz_i_D, hd_vi_zi⟩ := hex_zi i
    obtain ⟨z_j, hz_j, hz_j_D, hd_vj_zj⟩ := hex_zi j
    have hvi : v_seq (castIdx i) ∈ Γ.V := hv_V (castIdx i)
    have hvj : v_seq (castIdx j) ∈ Γ.V := hv_V (castIdx j)
    have hviA : ({v_seq (castIdx i)} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨_, hvi, rfl⟩)
    have hvjA : ({v_seq (castIdx j)} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨_, hvj, rfl⟩)
    have hij_cast : castIdx i < castIdx j := hij
    have hd_vivj : θ' + 2 * η + 6 ≤ d {v_seq (castIdx i)} {v_seq (castIdx j)} := by
      have := hv_iii (castIdx i) (castIdx j) hij_cast
      rwa [subsetTangleDist_singletons_eq hvi hvj] at this
    refine le_subsetTangleDist_of_forall (by omega) fun y hy z hz hyD hzD => ?_
    have hd_zi_y : d z_i y ≤ 3 :=
      hJ.dist_le_three_of_meets_D (hA'_mem i) hz_i hy hz_i_D hyD
    have hd_z_zj : d z z_j ≤ 3 :=
      hJ.dist_le_three_of_meets_D (hA'_mem j) hz hz_j hzD hz_j_D
    have htri₁ : d {v_seq (castIdx i)} {v_seq (castIdx j)} ≤
        d {v_seq (castIdx i)} z_i + d z_i {v_seq (castIdx j)} :=
      HasTangleMetric.triangle hS hJ.hasMetric hviA hz_i hvjA
    have htri₂ : d z_i {v_seq (castIdx j)} ≤ d z_i y + d y {v_seq (castIdx j)} :=
      HasTangleMetric.triangle hS hJ.hasMetric hz_i hy hvjA
    have htri₃ : d y {v_seq (castIdx j)} ≤ d y z + d z {v_seq (castIdx j)} :=
      HasTangleMetric.triangle hS hJ.hasMetric hy hz hvjA
    have htri₄ : d z {v_seq (castIdx j)} ≤ d z z_j + d z_j {v_seq (castIdx j)} :=
      HasTangleMetric.triangle hS hJ.hasMetric hz hz_j hvjA
    have hcomm : d z_j {v_seq (castIdx j)} = d {v_seq (castIdx j)} z_j :=
      HasTangleMetric.comm hJ.hasMetric hz_j hvjA
    omega

/-- **Graph Minors XXII, (8.2)** (Section 8, page 557):
*For all integers $$q, \delta, \eta \ge 0$$ there exists $$\theta \ge 4$$ with the following
property. Let (J1)–(J7) hold, and suppose that for every $$A \in \mathcal{A}$$ with
$$D(A) \cap \Delta = \emptyset$$ and every $$v \in V(\Gamma)$$ with $$v \notin \Delta$$, there
exists $$A' \in \mathcal{A}$$ with $$d(v, D(A')) \le \eta$$ such that
$$(A', \pi(A') + \omega)$$ has the same $$\delta$$-folio as $$(A, \pi(A) + \omega)$$. Suppose also
that $$d(v^*, \Delta) \ge \theta$$. Then there is a model of $$(H, \chi)$$ in
$$(G \setminus \{v^*\}, \omega)$$.* -/
theorem theorem_8_2_proof  (q δ η : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV : αH → Graph α β) (φE : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T →
        (∀ A ∈ 𝒜, Disjoint (D A) Δ → ∀ v ∈ Γ.V, v ∉ Δ →
          ∃ A' ∈ 𝒜, subsetTangleDist Γ ord d {v} (D A') ≤ η ∧
            ∃ hlen : πLen A' = πLen A,
              ∀ (hA : A ≤ R_G.G.toGraph) (hA' : A' ≤ R_G.G.toGraph)
                (hπ : ∀ k : Fin (πLen A + q),
                  seqConcat (ιV ∘ πS A) R_G.roots k ∈ V(A))
                (hπ' : ∀ k : Fin (πLen A + q),
                  seqConcat (fun k : Fin (πLen A) =>
                    ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots k ∈ V(A')),
                HasSameDeltaFolio
                  (subRootedDigraph R_G.G A' hA'
                    (seqConcat (fun k : Fin (πLen A) =>
                      ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots) hπ')
                  (subRootedDigraph R_G.G A hA
                    (seqConcat (ιV ∘ πS A) R_G.roots) hπ) δ) →
        θ ≤ subsetTangleDist Γ ord d {v_star} Δ →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H := by
  let τ := 3 * q + 5 * δ
  obtain ⟨θ', hθ'4, hθ'_spec⟩ := theorem_7_4_parallel.{w, u, v, u₁, v₁} q δ τ
  let θ := 2 * (τ + 1) * (θ' + 2 * η + 7) + 3
  have hθ4 : 4 ≤ θ := by
    dsimp only [θ]
    have : 1 * 4 ≤ 2 * (τ + 1) * (θ' + 2 * η + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  refine ⟨θ, hθ4, ?_⟩
  intro S _ _ α β αH βH ιV ιE R_G W 𝒜 πLen πS Γ orient ord T ins d D N K Δ v_star R_H φV φE
    hJ hJ7 hHom hdist_v_star
  -- By 8.1, replace `φ` by `(φV₁, φE₁)` and obtain `ℬ ⊆ 𝒜` sufficient for `(φV₁, φE₁)` with
  -- `{A ∈ ℬ | d(D(A), Σ \ Δ) < θ}.ncard ≤ τ`.
  obtain ⟨ℬ, φV₁, φE₁, hMod₁, hSuff, hℬ_card⟩ := theorem_8_1_proof hJ
  have hJ₁ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV₁ φE₁ :=
    { hJ with
      isModel := hMod₁
      φV_meets := fun v hv => by
        obtain ⟨x, hxφ, hxK | hxA⟩ := hSuff.φV_meets v hv
        · exact ⟨x, hxφ, Or.inl hxK⟩
        · obtain ⟨A, hAℬ, hxA⟩ := mem_iUnion₂.mp hxA
          exact ⟨x, hxφ, Or.inr (mem_iUnion₂.mpr ⟨A, hSuff.subset hAℬ, hxA⟩)⟩
      φE_mem := fun e he => by
        rcases hSuff.φE_mem e he with heK | heA
        · exact Or.inl heK
        · obtain ⟨A, hAℬ, heA⟩ := mem_iUnion₂.mp heA
          exact Or.inr (mem_iUnion₂.mpr ⟨A, hSuff.subset hAℬ, heA⟩) }
  -- Apply Claim (2) to get `Δ'`.
  obtain ⟨Δ', hΔ'_disc, hv_star_not_Δ', hΔ_sub_Δ', hΔ'_bd, hΔ'_dist, hℬ_Δ'_card, hℬ_or⟩ :=
    lemma_8_2_claim_2 hJ₁ hSuff.subset hθ'4 rfl hℬ_card hdist_v_star
  -- Apply Claim (3) to get `v_1, ..., v_τ`.
  obtain ⟨v_seq, hv_V, hv_i, hv_ii, hv_iii⟩ :=
    lemma_8_2_claim_3 hJ₁ hΔ'_disc hΔ'_bd hΔ'_dist
  -- Enumerate `ℬ₀ = {A ∈ ℬ | Disjoint (D A) Δ'}` as `A_1, ..., A_t` with `t ≤ τ`.
  let ℬ₀ : Set (Graph α β) := {A ∈ ℬ | Disjoint (D A) Δ'}
  have hfin_ℬ₀ : ℬ₀.Finite := (hJ.finite_𝒜.subset hSuff.subset).subset (fun _ h => h.1)
  let _ : Fintype ℬ₀ := hfin_ℬ₀.fintype
  let t := ℬ₀.ncard
  have ht_eq : Fintype.card ℬ₀ = t := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have ht_le : t ≤ τ := hℬ_Δ'_card
  let e_enum : Fin t ≃ ℬ₀ := (Fintype.equivFinOfCardEq ht_eq).symm
  let A_fam : Fin t → Graph α β := fun i => (e_enum i).1
  have hA_fam_mem : ∀ i : Fin t, A_fam i ∈ ℬ₀ := fun i => (e_enum i).2
  have hA_fam_range : Set.range A_fam = ℬ₀ := by
    ext A
    constructor
    · rintro ⟨i, rfl⟩
      exact hA_fam_mem i
    · intro hA
      exact ⟨e_enum.symm ⟨A, hA⟩, by simp [A_fam]⟩
  -- For each `1 ≤ i ≤ t`, `v_seq i ∉ Δ'` (since `d(v_i, Δ') ≥ η + 4 ≥ 4 > 0`), so `v_seq i ∉ Δ`.
  have hv_not_Δ : ∀ i : Fin t, v_seq ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩ ∉ Δ := by
    intro i hv_in_Δ
    let i' : Fin τ := ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩
    have hv_in_Δ' : v_seq i' ∈ Δ' := hΔ_sub_Δ' hv_in_Δ
    have hvi_A : ({v_seq i'} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_seq i', hv_V i', rfl⟩)
    have hd0 : d {v_seq i'} {v_seq i'} = 0 := HasTangleMetric.self_eq_zero hJ.hasMetric hvi_A
    have hle0 : subsetTangleDist Γ ord d {v_seq i'} Δ' ≤ 0 := by
      rw [← hd0]
      exact subsetTangleDist_le_of_mem hvi_A hvi_A ⟨v_seq i', rfl, rfl⟩ ⟨v_seq i', rfl, hv_in_Δ'⟩
    have := hv_ii i'
    omega
  -- Choose `A'_i ∈ 𝒜` for each `i : Fin t` using the homogeneity hypothesis `hHom`.
  have hex_A' : ∀ i : Fin t,
      ∃ A' ∈ 𝒜, subsetTangleDist Γ ord d {v_seq ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩} (D A') ≤ η ∧
        ∃ hlen : πLen A' = πLen (A_fam i),
          ∀ (hA : A_fam i ≤ R_G.G.toGraph) (hA' : A' ≤ R_G.G.toGraph)
            (hπ : ∀ k : Fin (πLen (A_fam i) + q),
              seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
            (hπ' : ∀ k : Fin (πLen (A_fam i) + q),
              seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots k ∈ V(A')),
            HasSameDeltaFolio
              (subRootedDigraph R_G.G A' hA'
                (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                  ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots) hπ')
              (subRootedDigraph R_G.G (A_fam i) hA
                (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπ) δ := by
    intro i
    have hAi_ℬ : A_fam i ∈ ℬ := (hA_fam_mem i).1
    have hAi_dis : Disjoint (D (A_fam i)) Δ := (hA_fam_mem i).2.mono_right hΔ_sub_Δ'
    exact hHom (A_fam i) (hSuff.subset hAi_ℬ) hAi_dis
      (v_seq ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩)
      (hv_V ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩) (hv_not_Δ i)
  let A_fam' : Fin t → Graph α β := fun i => Classical.choose (hex_A' i)
  have hA'_spec : ∀ i : Fin t,
      A_fam' i ∈ 𝒜 ∧
      subsetTangleDist Γ ord d {v_seq ⟨i.1, lt_of_lt_of_le i.2 ht_le⟩} (D (A_fam' i)) ≤ η ∧
      ∃ hlen : πLen (A_fam' i) = πLen (A_fam i),
        ∀ (hA : A_fam i ≤ R_G.G.toGraph) (hA' : A_fam' i ≤ R_G.G.toGraph)
          (hπ : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
          (hπ' : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV (πS (A_fam' i) (Fin.cast hlen.symm k))) R_G.roots k ∈ V(A_fam' i)),
          HasSameDeltaFolio
            (subRootedDigraph R_G.G (A_fam' i) hA'
              (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV (πS (A_fam' i) (Fin.cast hlen.symm k))) R_G.roots) hπ')
            (subRootedDigraph R_G.G (A_fam i) hA
              (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπ) δ :=
    fun i => Classical.choose_spec (hex_A' i)
  -- Apply Claim (4).
  have hθ'_le_θ : θ' + 2 * η + 7 ≤ θ := by
    dsimp only [θ]
    have : 1 * (θ' + 2 * η + 7) ≤ 2 * (τ + 1) * (θ' + 2 * η + 7) :=
      Nat.mul_le_mul (by omega) le_rfl
    omega
  have hθ_ord : θ' + 2 * η + 7 ≤ ord := hθ'_le_θ.trans hJ.θ_le_ord
  obtain ⟨hc4_i, hc4_ii, hc4_iii⟩ :=
    lemma_8_2_claim_4 hJ₁ hθ_ord hΔ_sub_Δ' ht_le hv_V hv_i hv_ii hv_iii
      (fun i => (hA'_spec i).1) (fun i => (hA'_spec i).2.1)
  -- Verify `SystemJ1ToJ6` with `Δ, θ` replaced by `Δ', θ'`.
  have hle_ord_atom : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, d a b ≤ ord :=
    fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb
  have hcompl_sub : Set.univ \ Δ' ⊆ Set.univ \ Δ :=
    Set.sdiff_subset_sdiff Subset.rfl hΔ_sub_Δ'
  have hJ' : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ' ord T ins d D N K Δ' v_star δ R_H φV₁ φE₁ :=
    { hJ₁ with
      four_le_θ := hθ'4
      θ_le_ord := by omega
      disc_Δ := ⟨hΔ'_disc, hΔ'_bd⟩
      dist_Γ_inter_K := fun v hv hvK => by
        have h1 : θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ) := hJ.dist_Γ_inter_K v hv hvK
        have h2 : subsetTangleDist Γ ord d {v} (Set.univ \ Δ) ≤
            subsetTangleDist Γ ord d {v} (Set.univ \ Δ') :=
          subsetTangleDist_anti hle_ord_atom Subset.rfl hcompl_sub
        omega
      dist_D_of_inter_K := fun A hA hne => by
        have h1 : θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) := hJ.dist_D_of_inter_K A hA hne
        have h2 : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) ≤
            subsetTangleDist Γ ord d (D A) (Set.univ \ Δ') :=
          subsetTangleDist_anti hle_ord_atom Subset.rfl hcompl_sub
        omega
      v_star_mem := ⟨hJ.v_star_mem.1, hv_star_not_Δ'⟩ }
  let hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i) :=
    fun i => Classical.choose (hA'_spec i).2.2
  have hfolio : ∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
      (hπi : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
      (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (fun k : Fin (πLen (A_fam i)) =>
          ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
      HasSameDeltaFolio
        (subRootedDigraph R_G.G (A_fam' i) hA'i
          (seqConcat (fun k : Fin (πLen (A_fam i)) =>
            ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
        (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ :=
    fun i => Classical.choose_spec (hA'_spec i).2.2
  exact hθ'_spec ιV ιE R_G W 𝒜 ℬ πLen πS Γ orient ord T ins d D N K Δ' v_star R_H φV₁ φE₁
    hJ' hJ7 hSuff t A_fam A_fam' ht_le
    (fun i => (hA_fam_mem i).1)
    (fun i => (hA'_spec i).1)
    (fun A ⟨hAℬ, hA_not_range⟩ => by
      rcases hℬ_or A hAℬ with hdis | hge
      · exact False.elim (hA_not_range (hA_fam_range.symm ▸ ⟨hAℬ, hdis⟩))
      · exact hge)
    hlen hfolio
    (fun i => (hA_fam_mem i).2)
    hc4_i
    (fun i => (hc4_ii i).1)
    hc4_iii

end GraphMinor.GM22
