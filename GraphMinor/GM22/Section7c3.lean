module

public import GraphMinor.GM22.Section7c2

/-!
# Graph Minors XXII, Section 7 (Part 3c): Claims (8)–(9) of Theorem 7.3

This file formalizes the construction of $Z_0$, $Z'$, $Z$, $\alpha$, $\mu$, and proves
Claims (8) and (9) of the proof of **7.3** (`theorem_7_3`, pages 549–550) from
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM16

universe u v w u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## Construction of $Z_0$ (page 549) -/

/-- Construction of $Z_0 = Y_1 \cup Y_2 \cup W$ on page 549:
- $Z_0 \subseteq V(K_1)$ and $Z_0 \subseteq V(L_{\text{model}})$, where
  $L_{\text{model}} = \bigcup_{v \in V(H)} \phi(v)$,
- $W \subseteq Z_0$ and $|Z_0| \le q + 3\delta$,
- for every $e \in E(H)$ with $\phi(e) \in E(K_1)$, both ends of $\phi(e)$ belong to $Z_0$,
- for every $v \in V(H)$, $V(\phi(v)) \cap (Z_0 \cup V(A_1 \cup \dots \cup A_t)) \ne \emptyset$. -/
theorem exists_Z0_7_3 {q t : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hAdeq : IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE)
    {A_fam : Fin t → Graph α β}
    (hA_mem_ℬ : ∀ i : Fin t, A_fam i ∈ ℬ)
    (hdist_other : ∀ A ∈ ℬ \ Set.range A_fam,
      θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let L_model := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
    let A_union := subgraphSUnion R_G.G.toGraph (Set.range A_fam)
    ∃ Z₀ : Set α,
      Z₀ ⊆ V(K₁) ∧
      Z₀ ⊆ V(L_model) ∧
      W ⊆ Z₀ ∧
      Z₀.ncard ≤ q + 3 * δ ∧
      (∀ e ∈ E(R_H.G.toGraph), φE e ∈ E(K₁) →
        R_G.G.head (φE e) ∈ Z₀ ∧ R_G.G.tail (φE e) ∈ Z₀) ∧
      (∀ v ∈ V(R_H.G.toGraph), (V(φV v) ∩ (Z₀ ∪ V(A_union))).Nonempty) := by
  classical
  intro 𝒜_far K₁ L_model A_union
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hA_le : ∀ M ∈ Set.range A_fam, M ≤ R_G.G.toGraph := by
    rintro _ ⟨i, rfl⟩
    exact hJ.le_of_mem_𝒜 (A_fam i) (hAdeq.subset (hA_mem_ℬ i))
  -- `V(K) ∪ ⋃ B ∈ ℬ, V(B) ⊆ V(K₁) ∪ V(A_union)`
  have hV_Kℬ_sub : V(K) ∪ (⋃ B ∈ ℬ, V(B)) ⊆ V(K₁) ∪ V(A_union) := by
    rintro u (huK | huℬ)
    · exact Or.inl (Or.inl huK)
    · obtain ⟨B, hB, huB⟩ := mem_iUnion₂.mp huℬ
      by_cases hBr : B ∈ Set.range A_fam
      · exact Or.inr ((le_subgraphSUnion hA_le hBr).vertexSet_mono huB)
      · have hB_far : B ∈ 𝒜_far := ⟨hAdeq.subset hB, hdist_other B ⟨hB, hBr⟩⟩
        exact Or.inl (Or.inr ((le_subgraphSUnion hfar_le hB_far).vertexSet_mono huB))
  -- Define `V_miss := {v ∈ V(H) | Disjoint V(φV v) (W ∪ V(A_union))}`
  let V_miss : Set αH := {v ∈ V(R_H.G.toGraph) | Disjoint V(φV v) (W ∪ V(A_union))}
  have hV_miss_sub : V_miss ⊆ V(R_H.G.toGraph) \ Set.range R_H.roots := by
    rintro v ⟨hv, hdisj⟩
    refine ⟨hv, ?_⟩
    rintro ⟨j, rfl⟩
    have hr_φ : R_G.roots j ∈ V(φV (R_H.roots j)) := hJ.isModel.root_mem j
    have hr_W : R_G.roots j ∈ W := hJ.W_eq ▸ ⟨j, rfl⟩
    exact disjoint_left.mp hdisj hr_φ (Or.inl hr_W)
  have hV_miss_meets_K₁ : ∀ v : V_miss, (V(K₁) ∩ V(φV v.1)).Nonempty := by
    rintro ⟨v, hv, hdisj⟩
    obtain ⟨u, huφ, huKℬ⟩ := hAdeq.φV_meets v hv
    rcases hV_Kℬ_sub huKℬ with huK₁ | huAu
    · exact ⟨u, huK₁, huφ⟩
    · exact (disjoint_left.mp hdisj huφ (Or.inr huAu)).elim
  let pickY₁ : V_miss → α := fun v => Classical.choose (hV_miss_meets_K₁ v)
  have hpickY₁_spec : ∀ v : V_miss, pickY₁ v ∈ V(K₁) ∧ pickY₁ v ∈ V(φV v.1) :=
    fun v => Classical.choose_spec (hV_miss_meets_K₁ v)
  let Y₁ : Set α := Set.range pickY₁
  let E_K₁ : Set βH := {e ∈ E(R_H.G.toGraph) | φE e ∈ E(K₁)}
  let Y₂h : Set α := (fun e => R_G.G.head (φE e)) '' E_K₁
  let Y₂t : Set α := (fun e => R_G.G.tail (φE e)) '' E_K₁
  let Y₂ : Set α := Y₂h ∪ Y₂t
  let Z₀ : Set α := Y₁ ∪ Y₂ ∪ W
  -- 1. `Z₀ ⊆ V(K₁)`:
  have hY₁_K₁ : Y₁ ⊆ V(K₁) := by
    rintro _ ⟨v, rfl⟩
    exact (hpickY₁_spec v).1
  have hY₂h_K₁ : Y₂h ⊆ V(K₁) := by
    rintro _ ⟨e, ⟨_, heK₁⟩, rfl⟩
    have hlink_G := R_G.G.isLink_of_mem (φE e) (hK₁_le.edgeSet_mono heK₁)
    exact ((hK₁_le.isLink_iff heK₁).mpr hlink_G).right_mem
  have hY₂t_K₁ : Y₂t ⊆ V(K₁) := by
    rintro _ ⟨e, ⟨_, heK₁⟩, rfl⟩
    have hlink_G := R_G.G.isLink_of_mem (φE e) (hK₁_le.edgeSet_mono heK₁)
    exact ((hK₁_le.isLink_iff heK₁).mpr hlink_G).left_mem
  have hW_K₁ : W ⊆ V(K₁) := fun w hw => Or.inl (hJ.sep_NK.2 hw).2
  have hZ₀_K₁ : Z₀ ⊆ V(K₁) :=
    union_subset (union_subset hY₁_K₁ (union_subset hY₂h_K₁ hY₂t_K₁)) hW_K₁
  -- 2. `Z₀ ⊆ V(L_model)`:
  have hφ_le_L : ∀ v ∈ V(R_H.G.toGraph), φV v ≤ L_model := by
    intro v hv
    exact le_subgraphSUnion (by rintro _ ⟨w, hw, rfl⟩; exact hJ.isModel.subgraph_of_mem w hw)
      ⟨v, hv, rfl⟩
  have hY₁_L : Y₁ ⊆ V(L_model) := by
    rintro _ ⟨v, rfl⟩
    exact (hφ_le_L v.1 v.2.1).vertexSet_mono (hpickY₁_spec v).2
  have hY₂h_L : Y₂h ⊆ V(L_model) := by
    rintro _ ⟨e, ⟨heH, _⟩, rfl⟩
    have hhV : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e heH).right_mem
    exact (hφ_le_L _ hhV).vertexSet_mono (hJ.isModel.head_mem e heH)
  have hY₂t_L : Y₂t ⊆ V(L_model) := by
    rintro _ ⟨e, ⟨heH, _⟩, rfl⟩
    have htV : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e heH).left_mem
    exact (hφ_le_L _ htV).vertexSet_mono (hJ.isModel.tail_mem e heH)
  have hW_L : W ⊆ V(L_model) := by
    rw [hJ.W_eq]
    rintro _ ⟨j, rfl⟩
    exact (hφ_le_L (R_H.roots j) (R_H.roots_mem j)).vertexSet_mono (hJ.isModel.root_mem j)
  have hZ₀_L : Z₀ ⊆ V(L_model) :=
    union_subset (union_subset hY₁_L (union_subset hY₂h_L hY₂t_L)) hW_L
  -- 3. `W ⊆ Z₀`:
  have hW_Z₀ : W ⊆ Z₀ := subset_union_right
  -- 4. `Z₀.ncard ≤ q + 3 * δ`:
  have hfin_Vdiff : (V(R_H.G.toGraph) \ Set.range R_H.roots).Finite := hJ.detail_H.1.sdiff
  have hfin_miss : V_miss.Finite := hfin_Vdiff.subset hV_miss_sub
  have : Finite V_miss := hfin_miss.to_subtype
  have hcY₁ : Y₁.ncard ≤ δ := by
    have h1 : (pickY₁ '' Set.univ).ncard ≤ (Set.univ : Set V_miss).ncard :=
      Set.ncard_image_le Set.finite_univ
    have h2 : (Set.univ : Set V_miss).ncard = V_miss.ncard := by
      rw [Set.ncard_univ, Nat.card_coe_set_eq]
    have h3 : Y₁.ncard ≤ V_miss.ncard := by simpa [Y₁, Set.image_univ, h2] using h1
    exact h3.trans ((ncard_le_ncard hV_miss_sub hfin_Vdiff).trans hJ.detail_H.2.2.2)
  have hfin_EH : E(R_H.G.toGraph).Finite := hJ.detail_H.2.1
  have hfin_EK₁ : E_K₁.Finite := hfin_EH.subset (fun _ h => h.1)
  have hc_EK₁ : E_K₁.ncard ≤ δ :=
    (ncard_le_ncard (fun _ h => h.1) hfin_EH).trans hJ.detail_H.2.2.1
  have hcY₂h : Y₂h.ncard ≤ δ := (ncard_image_le hfin_EK₁).trans hc_EK₁
  have hcY₂t : Y₂t.ncard ≤ δ := (ncard_image_le hfin_EK₁).trans hc_EK₁
  have hcW : W.ncard ≤ q := by
    rw [hJ.W_eq]
    have h : (R_G.roots '' Set.univ).ncard ≤ (Set.univ : Set (Fin q)).ncard :=
      Set.ncard_image_le Set.finite_univ
    simpa [Set.image_univ, Set.ncard_univ, Nat.card_fin] using h
  have hcZ₀ : Z₀.ncard ≤ q + 3 * δ := by
    calc Z₀.ncard
      _ ≤ (Y₁ ∪ Y₂).ncard + W.ncard := ncard_union_le (Y₁ ∪ Y₂) W
      _ ≤ Y₁.ncard + Y₂.ncard + W.ncard :=
          Nat.add_le_add_right (ncard_union_le Y₁ Y₂) _
      _ ≤ Y₁.ncard + (Y₂h.ncard + Y₂t.ncard) + W.ncard :=
          Nat.add_le_add_right (Nat.add_le_add_left (ncard_union_le Y₂h Y₂t) _) _
      _ ≤ q + 3 * δ := by omega
  -- 5. Ends of `φE e ∈ E(K₁)`:
  have hends : ∀ e ∈ E(R_H.G.toGraph), φE e ∈ E(K₁) →
      R_G.G.head (φE e) ∈ Z₀ ∧ R_G.G.tail (φE e) ∈ Z₀ := by
    intro e heH heK₁
    have he_mem : e ∈ E_K₁ := ⟨heH, heK₁⟩
    exact ⟨Or.inl (Or.inr (Or.inl ⟨e, he_mem, rfl⟩)),
      Or.inl (Or.inr (Or.inr ⟨e, he_mem, rfl⟩))⟩
  -- 6. Every `φV v` meets `Z₀ ∪ V(A_union)`:
  have hmeets : ∀ v ∈ V(R_H.G.toGraph), (V(φV v) ∩ (Z₀ ∪ V(A_union))).Nonempty := by
    intro v hv
    by_cases hdisj : Disjoint V(φV v) (W ∪ V(A_union))
    · let v' : V_miss := ⟨v, hv, hdisj⟩
      exact ⟨pickY₁ v', (hpickY₁_spec v').2, Or.inl (Or.inl (Or.inl ⟨v', rfl⟩))⟩
    · rw [Set.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨u, huφ, huW | huAu⟩
      · exact ⟨u, huφ, Or.inl (Or.inr huW)⟩
      · exact ⟨u, huφ, Or.inr huAu⟩
  exact ⟨Z₀, hZ₀_K₁, hZ₀_L, hW_Z₀, hcZ₀, hends, hmeets⟩

/-! ## Proof of Claim (8) of 7.3 (pages 549–550) -/

omit [T2Space S] in
/-- Monotonicity of `Drawing.toEmbeddedGraph` with respect to `Drawing.IsSubdrawing`. -/
theorem toEmbeddedGraph_le_of_isSubdrawing {D₁ D₂ : Drawing S} (h : D₁.IsSubdrawing D₂)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    D₁.toEmbeddedGraph ιV ιE ≤ D₂.toEmbeddedGraph ιV ιE :=
  ⟨image_mono h.1, fun _ _ _ ⟨e₀, x₀, y₀, hl, he, hx, hy⟩ =>
    ⟨e₀, x₀, y₀, (h.isLink_iff hl.1).mp hl, he, hx, hy⟩⟩

/-- **Graph Minors XXII, (7.3) Claim (8)** (page 549):
(8) *There is a subgraph $L_0'$ of $(\Gamma \cap \Sigma') \cup K_1$ with the same effect on $Z'$ as
$L_2 \cup (L \cap K_1)$ and with $E(L_0') \cap \phi(E(H)) \subseteq E(A_1 \cup \dots \cup A_t)$.* -/
theorem lemma_7_3_claim_8 {q t τ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ θ' ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hCleanV : ιV ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A))
    (hCleanE : ιE ⁻¹' E(R_G.G.toGraph) ⊆ Γ.E)
    (hAdeq : IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE)
    {A_fam A_fam' : Fin t → Graph α β}
    (hA_mem_ℬ : ∀ i : Fin t, A_fam i ∈ ℬ)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hdist_other : ∀ A ∈ ℬ \ Set.range A_fam,
      θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ))
    (ht_le : t ≤ τ)
    (h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ)
    (h_iii : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ)
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    (hθ_le : θ' + 2 ≤ θ)
    (h53_spec : ∀ (Γ' : Drawing S) (K₁ L' : Graph α β) (Z' : Set α) (F : Fin t → Set S),
      IsClosedSurface S →
      V(K₁).Finite → E(K₁).Finite →
      (Γ.toEmbeddedGraph ιV ιE).Compatible K₁ →
      Γ.IsTwoCell →
      θ' ≤ ord →
      HasTangleMetric Γ ord T d →
      (∀ F₀ : Set S, IsOArc F₀ → Γ.IsNormal F₀ → (F₀ ∩ Γ.V).ncard < ord →
        IsTangleIns Γ T F₀ (ins F₀)) →
      Z' ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁) →
      Z'.ncard ≤ q + 3 * δ + 3 * τ →
      (∀ i : Fin t, IsOArc (F i) ∧ Γ.IsNormal (F i)) →
      ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ⊆ Z' →
      Z' ⊆ ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ∪ V(K₁) →
      Pairwise (fun i j : Fin t => Disjoint (ins (F i)) (ins (F j))) →
      (∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
        (F₀ ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard ∧ ins (F i) ⊆ ins F₀) →
      (∀ i j : Fin t, i ≠ j → θ' ≤ subsetTangleDist Γ ord d (ins (F i)) (ins (F j))) →
      (∀ i : Fin t, ∀ v ∈ Γ.V, ιV v ∈ V(K₁) →
        θ' ≤ subsetTangleDist Γ ord d (ins (F i)) {v}) →
      let R := ⋃ z ∈ {z ∈ Γ.A | ∀ v ∈ Γ.V, ιV v ∈ V(K₁) → θ' ≤ d z {v}}, z
      let S' := Set.univ \ ⋃ i : Fin t, (ins (F i) \ F i)
      IsVariant Γ Γ' (R ∩ S') →
      (Γ'.toEmbeddedGraph ιV ιE).Compatible K₁ →
      (Γ'.toEmbeddedGraph ιV ιE) ⊓ K₁ = (Γ.toEmbeddedGraph ιV ιE) ⊓ K₁ →
      (∀ i : Fin t, Γ.interSet (ins (F i)) = Γ'.interSet (ins (F i))) →
      L' ≤ graphUnion ((Γ'.interSet S').toEmbeddedGraph ιV ιE) K₁ →
      ∃ L ≤ graphUnion ((Γ.interSet S').toEmbeddedGraph ιV ιE) K₁,
        effectOn L Z' = effectOn L' Z' ∧ L ⊓ K₁ ≤ L')
    {D_in : Fin t → Set S}
    {β_homeo : S ≃ₜ S}
    (hβ_fix : ∀ z ∈ Δ, β_homeo z = z)
    {M_fam : Fin t → Drawing S}
    (hM_U_sub : ∀ i : Fin t, (M_fam i).U ⊆ D (A_fam i))
    (hM_E : ∀ i : Fin t, ∀ e ∈ (M_fam i).E, e ⊆ (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i)
    {M_union Γ₀ Γ₁ Γ₃ : Drawing S}
    (hMU_V : M_union.V = ⋃ i : Fin t, (M_fam i).V)
    (hMU_E : M_union.E = ⋃ i : Fin t, (M_fam i).E)
    (hΓ₀_eq : Γ₀ = Γ.interSet (Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i)))))
    (hΓ₁_V : Γ₁.V = Γ₀.V ∪ M_union.V)
    (hΓ₁_E : Γ₁.E = Γ₀.E ∪ M_union.E)
    (hΓ₂_inter_DA' : ∀ i : Fin t,
      (mapDrawingHomeo β_homeo Γ₁).U ∩ D (A_fam' i) = Set.range (πS (A_fam' i)))
    (hΓ₂_V_DA' : ∀ i : Fin t,
      Set.range (πS (A_fam' i)) ⊆ (mapDrawingHomeo β_homeo Γ₁).V)
    (hΓ₃_V : Γ₃.V = (mapDrawingHomeo β_homeo Γ₁).V ∪
      ⋃ i : Fin t, (Γ.interSet (ins (subBd (D (A_fam' i))))).V)
    (hΓ₃_E : Γ₃.E = (mapDrawingHomeo β_homeo Γ₁).E ∪
      ⋃ i : Fin t, (Γ.interSet (ins (subBd (D (A_fam' i))))).E)
    {Z₀ : Set α}
    (hZ₀_K₁ : Z₀ ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hZ₀_card : Z₀.ncard ≤ q + 3 * δ) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let L := graphUnion (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β)
      (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))
    let L₀ := L ⊓ (Γ₀.toEmbeddedGraph ιV ιE)
    let L₁ := graphUnion L₀ (M_union.toEmbeddedGraph ιV ιE)
    let L₂ := mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo) L₁
    let Z' := Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))
    let F_fam : Fin t → Set S := fun i => subBd (D (A_fam' i))
    let S_prime := Set.univ \ ⋃ i : Fin t, (ins (F_fam i) \ F_fam i)
    ∃ L'₀ ≤ graphUnion ((Γ.interSet S_prime).toEmbeddedGraph ιV ιE) K₁,
      effectOn L'₀ Z' = effectOn (graphUnion L₂ (L ⊓ K₁)) Z' ∧
      L'₀ ⊓ K₁ ≤ graphUnion L₂ (L ⊓ K₁) ∧
      E(L'₀) ∩ (φE '' E(R_H.G.toGraph)) ⊆ E(subgraphSUnion R_G.G.toGraph (Set.range A_fam)) := by
  classical
  intro 𝒜_far K₁ L L₀ L₁ L₂ Z' F_fam S_prime
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hθ'_le_θ : θ' ≤ θ := by omega
  have hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜 := fun i => hAdeq.subset (hA_mem_ℬ i)
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph := hJ.Γ_le.trans deleteVerts_le
  -- Claims (1), (2), (3), (6), (7)
  have h1 := lemma_7_3_claim_1 hJ hAdeq hA_mem_ℬ hdist_other
  have h2 := lemma_7_3_claim_2 hJ hCleanV
  have h3 : ∀ i : Fin t, F_fam i ∩ Γ.V = Set.range (πS (A_fam' i)) :=
    fun i => lemma_7_3_claim_3 hJ hA'_mem h_v i
  have h6 := lemma_7_3_claim_6 hJ hA_mem hA'_mem h_ii h_v hβ_fix
    hM_U_sub hM_E hMU_V hMU_E (hΓ₀_eq ▸ hΓ₁_V) (hΓ₀_eq ▸ hΓ₁_E)
    hΓ₂_inter_DA' hΓ₂_V_DA' hΓ₃_V hΓ₃_E hθ_le
  obtain ⟨hV_diff_Δ, hE_sub_Δ, -, -, -, hΓ_inter_ins, hΓ₃_inter_S_prime, -, hVar_RS_prime⟩ := h6
  have h7 := lemma_7_3_claim_7 hJ hCleanV hCleanE hβ_fix hV_diff_Δ hE_sub_Δ
  obtain ⟨hCompat_Γ₃_K₁, hInter_Γ₃_K₁, _⟩ := h7
  -- Check hypotheses of 5.3 for `Z'` and `F_fam`
  have hins_eq : ∀ i : Fin t, ins (F_fam i) = D (A_fam' i) :=
    fun i => (hJ.disc_D (A_fam' i) (hA'_mem i)).2.2.symm
  have hF_oarc_norm : ∀ i : Fin t, IsOArc (F_fam i) ∧ Γ.IsNormal (F_fam i) := by
    intro i
    have hdisc := hJ.disc_D (A_fam' i) (hA'_mem i)
    refine ⟨?_, hdisc.2.1⟩
    change IsOArc (subBd (D (A_fam' i)))
    rw [IsClosedDisc.subBd_eq_discBd hS hdisc.1]
    exact hdisc.1.isOArc_discBd
  have hF_union_V : (⋃ i : Fin t, F_fam i) ∩ Γ.V = ⋃ i : Fin t, Set.range (πS (A_fam' i)) := by
    rw [iUnion_inter]
    exact iUnion_congr h3
  have hF_img_V : ιV '' ((⋃ i : Fin t, F_fam i) ∩ Γ.V) =
      ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i)) := by
    rw [hF_union_V, image_iUnion]
  have hZ'_sub_ΓK₁ : Z' ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁) := by
    rw [vertexSet_graphUnion]
    rintro u (huZ₀ | huπ)
    · exact Or.inr (hZ₀_K₁ huZ₀)
    · obtain ⟨i, x, hx_range, rfl⟩ := mem_iUnion.mp huπ
      rw [← h3 i] at hx_range
      exact Or.inl ⟨x, hx_range.2, rfl⟩
  have hZ'_card : Z'.ncard ≤ q + 3 * δ + 3 * τ := by
    have hc_each : ∀ i : Fin t, (ιV '' Set.range (πS (A_fam' i))).ncard ≤ 3 := by
      intro i
      rw [(hJ.range_πS_subset_D_and_ncard (hA'_mem i)).2.2.2]
      exact (hJ.π_valid (A_fam' i) (hA'_mem i)).2.1
    have hc_union : (⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))).ncard ≤ 3 * t := by
      have hbi : ∀ (s : Finset (Fin t)),
          (⋃ i ∈ s, ιV '' Set.range (πS (A_fam' i))).ncard ≤ 3 * s.card := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          rw [Finset.set_biUnion_insert, Finset.card_insert_of_notMem ha, Nat.mul_add, Nat.mul_one,
            Nat.add_comm (3 * s.card)]
          exact (Set.ncard_union_le _ _).trans (Nat.add_le_add (hc_each a) ih)
      simpa using hbi Finset.univ
    calc Z'.ncard
      _ ≤ Z₀.ncard + (⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))).ncard :=
          ncard_union_le _ _
      _ ≤ (q + 3 * δ) + 3 * t := Nat.add_le_add hZ₀_card hc_union
      _ ≤ q + 3 * δ + 3 * τ := by omega
  have hF_sub_Z' : ιV '' ((⋃ i : Fin t, F_fam i) ∩ Γ.V) ⊆ Z' := by
    rw [hF_img_V]
    exact subset_union_right
  have hZ'_sub_FK₁ : Z' ⊆ ιV '' ((⋃ i : Fin t, F_fam i) ∩ Γ.V) ∪ V(K₁) := by
    rw [hF_img_V, Set.union_comm]
    exact union_subset_union_left _ hZ₀_K₁
  have hDA'_disj : Pairwise (fun i j : Fin t => Disjoint (ins (F_fam i)) (ins (F_fam j))) := by
    intro i j hij
    rw [hins_eq i, hins_eq j]
    have h4 := hJ.four_le_θ
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd := h_iv i j hlt
      exact disjoint_of_one_le_subsetTangleDist hJ.hasMetric (by omega)
    · have hd := h_iv j i hgt
      exact (disjoint_of_one_le_subsetTangleDist hJ.hasMetric (by omega)).symm
  have h53_i : ∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
      (F₀ ∩ Γ.V).ncard < (F_fam i ∩ Γ.V).ncard ∧ ins (F_fam i) ⊆ ins F₀ := by
    intro i
    rw [h3 i, hins_eq i]
    exact h_v i
  have h53_ii : ∀ i j : Fin t, i ≠ j →
      θ' ≤ subsetTangleDist Γ ord d (ins (F_fam i)) (ins (F_fam j)) := by
    intro i j hij
    rw [hins_eq i, hins_eq j]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hθ'_le_θ.trans (h_iv i j hlt)
    · rw [subsetTangleDist_comm hJ.hasMetric]
      exact hθ'_le_θ.trans (h_iv j i hgt)
  have h53_iii : ∀ i : Fin t, ∀ v ∈ Γ.V, ιV v ∈ V(K₁) →
      θ' ≤ subsetTangleDist Γ ord d (ins (F_fam i)) {v} := by
    intro i v _ hvK₁
    rw [hins_eq i, subsetTangleDist_comm hJ.hasMetric]
    have hDA'_sub : D (A_fam' i) ⊆ Set.univ \ Δ := by
      intro x hx
      exact ⟨trivial, disjoint_left.mp (h_iii i) hx⟩
    exact hθ'_le_θ.trans ((h2.1 v hvK₁).trans (subsetTangleDist_anti
      (fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb) Subset.rfl hDA'_sub))
  -- Show `L₂ ≤ (Γ₃.interSet S_prime).toEmbeddedGraph ιV ιE`
  have hL₁_le_Γ₁ : L₁ ≤ Γ₁.toEmbeddedGraph ιV ιE := by
    have hΓ₀_le_Γ₁ : Γ₀.toEmbeddedGraph ιV ιE ≤ Γ₁.toEmbeddedGraph ιV ιE :=
      toEmbeddedGraph_le_of_isSubdrawing
        ⟨hΓ₁_V.symm ▸ subset_union_left, hΓ₁_E.symm ▸ subset_union_left⟩ ιV ιE
    have hMU_le_Γ₁ : M_union.toEmbeddedGraph ιV ιE ≤ Γ₁.toEmbeddedGraph ιV ιE :=
      toEmbeddedGraph_le_of_isSubdrawing
        ⟨hΓ₁_V.symm ▸ subset_union_right, hΓ₁_E.symm ▸ subset_union_right⟩ ιV ιE
    exact graphUnion_le ((inf_le_right : L₀ ≤ _).trans hΓ₀_le_Γ₁) hMU_le_Γ₁
  have hL₂_le_Γ₂ : L₂ ≤ (Γ₃.interSet S_prime).toEmbeddedGraph ιV ιE := by
    rw [hΓ₃_inter_S_prime, ← mapGraphEquiv_toEmbeddedGraph ιV ιE β_homeo Γ₁]
    exact mapGraphEquiv_mono _ _ hL₁_le_Γ₁
  have hL'_le : graphUnion L₂ (L ⊓ K₁) ≤
      graphUnion ((Γ₃.interSet S_prime).toEmbeddedGraph ιV ιE) K₁ := by
    refine graphUnion_le ?_ ?_
    · exact hL₂_le_Γ₂.trans (le_graphUnion_left _ _)
    · have hComp_Γ₃S_K₁ : ((Γ₃.interSet S_prime).toEmbeddedGraph ιV ιE).Compatible K₁ :=
        Compatible.of_le_le
          ((toEmbeddedGraph_le_of_isSubdrawing interSet_isSub ιV ιE).trans (le_graphUnion_left _ _))
          (le_graphUnion_right hCompat_Γ₃_K₁)
      exact (inf_le_right : L ⊓ K₁ ≤ K₁).trans (le_graphUnion_right hComp_Γ₃S_K₁)
  -- Apply 5.3!
  obtain ⟨L'₀, hL'₀_le, heff, hL'₀_inter_K₁⟩ :=
    h53_spec Γ₃ K₁ (graphUnion L₂ (L ⊓ K₁)) Z' F_fam
      hS
      (hJ.finite_V.subset hK₁_le.vertexSet_mono)
      (hJ.finite_E.subset hK₁_le.edgeSet_mono)
      (Compatible.of_le_le hΓ_le hK₁_le)
      hJ.isTwoCell
      (hθ'_le_θ.trans hJ.θ_le_ord)
      hJ.hasMetric
      hJ.ins_spec
      hZ'_sub_ΓK₁
      hZ'_card
      hF_oarc_norm
      hF_sub_Z'
      hZ'_sub_FK₁
      hDA'_disj
      h53_i
      h53_ii
      h53_iii
      hVar_RS_prime
      hCompat_Γ₃_K₁
      hInter_Γ₃_K₁
      hΓ_inter_ins
      hL'_le
  refine ⟨L'₀, hL'₀_le, heff, hL'₀_inter_K₁, ?_⟩
  -- Finally, show `E(L'₀) ∩ φE '' E(H) ⊆ E(A_union)`:
  rintro f ⟨hf_L'₀, eH, heH, rfl⟩
  have hf_K₁A : φE eH ∈ E(graphUnion K₁ (subgraphSUnion R_G.G.toGraph (Set.range A_fam))) :=
    h1.2 ⟨eH, heH, rfl⟩
  rw [edgeSet_graphUnion] at hf_K₁A
  rcases hf_K₁A with hf_K₁ | hf_Au
  · exfalso
    have hΓS_le : (Γ.interSet S_prime).toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph :=
      (toEmbeddedGraph_le_of_isSubdrawing interSet_isSub ιV ιE).trans hΓ_le
    have hL'₀_le_G : L'₀ ≤ R_G.G.toGraph := hL'₀_le.trans (graphUnion_le hΓS_le hK₁_le)
    have hComp_L'₀_K₁ : L'₀.Compatible K₁ := Compatible.of_le_le hL'₀_le_G hK₁_le
    obtain ⟨u, v, huv_K₁⟩ := K₁.exists_isLink_of_mem_edgeSet hf_K₁
    have huv_L'₀ : L'₀.IsLink (φE eH) u v :=
      (hComp_L'₀_K₁.isLink_congr hf_L'₀ hf_K₁).mpr huv_K₁
    have hf_inter : φE eH ∈ E(L'₀ ⊓ K₁) :=
      ((L'₀ ⊓ K₁).edge_mem_iff_exists_isLink (φE eH)).mpr ⟨u, v, huv_L'₀, huv_K₁⟩
    have hf_L₂_or_LK₁ : φE eH ∈ E(graphUnion L₂ (L ⊓ K₁)) :=
      hL'₀_inter_K₁.edgeSet_mono hf_inter
    have hf_not_L : φE eH ∉ E(L) := by
      have hφ_le_G : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
        rintro _ ⟨w, hw, rfl⟩
        exact hJ.isModel.subgraph_of_mem w hw
      change φE eH ∉ E(graphUnion (Graph.noEdge _ β) (subgraphSUnion R_G.G.toGraph _))
      rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, empty_union,
        edgeSet_subgraphSUnion hφ_le_G, mem_iUnion₂]
      rintro ⟨_, ⟨w, hw, rfl⟩, hmem⟩
      exact hJ.isModel.edge_not_mem_φV eH heH w hw hmem
    rw [edgeSet_graphUnion] at hf_L₂_or_LK₁
    rcases hf_L₂_or_LK₁ with hf_L₂ | hf_LK₁
    · have hfix_e : (homeoEdgeEquiv ιE β_homeo).symm (φE eH) = φE eH := by
        by_cases hrange : φE eH ∈ Set.range ιE
        · rcases hrange with ⟨e₀, he₀_eq⟩
          rw [← he₀_eq, homeoEdgeEquiv_symm, homeoEdgeEquiv_apply_ιE]
          congr 1
          have he₀_G : e₀ ∈ ιE ⁻¹' E(R_G.G.toGraph) := by
            change ιE e₀ ∈ E(R_G.G.toGraph)
            rw [he₀_eq]
            exact hK₁_le.edgeSet_mono hf_K₁
          have he₀_Γ : e₀ ∈ Γ.E := hCleanE he₀_G
          have huv_G : R_G.G.toGraph.IsLink (ιE e₀) u v :=
            he₀_eq.symm ▸ huv_K₁.mono hK₁_le
          have huv_Γ : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e₀) u v :=
            ((Compatible.of_le_le hΓ_le le_rfl).isLink_congr
              (mem_image_of_mem ιE he₀_Γ) huv_G.edge_mem).mpr huv_G
          rcases huv_Γ with ⟨e₁, x, y, ⟨he₁, hxΓ, _, hcl⟩, he₁_eq, rfl, rfl⟩
          have he₁_eq' : e₁ = e₀ := ιE.injective he₁_eq
          subst he₁_eq'
          have hx_K₁ : x ∈ ιV ⁻¹' V(K₁) := huv_K₁.left_mem
          have hx_cl : x ∈ closure e₁ := by
            have : x ∈ closure e₁ ∩ Γ.V := by rw [hcl]; exact Set.mem_insert x {y}
            exact this.1
          have he₁_sub_Δ : e₁ ⊆ Δ := by
            by_contra hnot
            obtain ⟨z, hze, hz_not_Δ⟩ := not_subset.mp hnot
            have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hxΓ, rfl⟩)
            have heA : e₁ ∈ Γ.A := Or.inl (Or.inr he₁)
            have hd_xe : d {x} e₁ ≤ 2 :=
              GM16.vertex_atom_dist_le_two hS hJ.hasMetric x hxΓ e₁ heA hx_cl
            have hθ_dist : θ ≤ subsetTangleDist Γ ord d {x} (Set.univ \ Δ) := h2.1 x hx_K₁
            have hle : subsetTangleDist Γ ord d {x} (Set.univ \ Δ) ≤ d {x} e₁ :=
              subsetTangleDist_le_of_mem hxA heA ⟨x, rfl, rfl⟩ ⟨z, hze, trivial, hz_not_Δ⟩
            have h4 := hJ.four_le_θ
            omega
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            have hw_Δ : w ∈ Δ := he₁_sub_Δ hw
            have hsymm_w : β_homeo.symm w = w :=
              β_homeo.injective (by rw [β_homeo.apply_symm_apply, hβ_fix w hw_Δ])
            rwa [hsymm_w]
          · intro hz
            have hz_Δ : z ∈ Δ := he₁_sub_Δ hz
            exact ⟨z, hz, β_homeo.injective (by rw [β_homeo.apply_symm_apply, hβ_fix z hz_Δ])⟩
        · rw [homeoEdgeEquiv_symm]
          exact homeoEdgeEquiv_apply_of_not_mem ιE β_homeo.symm hrange
      rcases hf_L₂ with ⟨e', he'_L₁, he'_eq⟩
      have he'_eq' : e' = φE eH := by
        rw [← hfix_e, ← he'_eq, Equiv.symm_apply_apply]
      subst he'_eq'
      rw [edgeSet_graphUnion] at he'_L₁
      rcases he'_L₁ with hf_L₀ | hf_MU
      · exact hf_not_L ((inf_le_left : L₀ ≤ L).edgeSet_mono hf_L₀)
      · rcases hf_MU with ⟨e₀, he₀_MU, he₀_eq⟩
        rw [hMU_E, mem_iUnion] at he₀_MU
        rcases he₀_MU with ⟨i, he₀_Mi⟩
        have he₀_sub : e₀ ⊆ D (A_fam i) :=
          ((hM_E i e₀ he₀_Mi).trans sdiff_subset).trans sdiff_subset
        obtain ⟨z₀, hz₀⟩ := he₀_Mi.1
        have hz₀_DA : z₀ ∈ D (A_fam i) := he₀_sub hz₀
        have huv_G : R_G.G.toGraph.IsLink (ιE e₀) u v :=
          he₀_eq.symm ▸ huv_K₁.mono hK₁_le
        have he₀_Γ : e₀ ∈ Γ.E := hCleanE huv_G.edge_mem
        have huv_Γ : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e₀) u v :=
          ((Compatible.of_le_le hΓ_le le_rfl).isLink_congr
            (mem_image_of_mem ιE he₀_Γ) huv_G.edge_mem).mpr huv_G
        rcases huv_Γ with ⟨e₁, x, y, ⟨he₁, hxΓ, _, hcl⟩, he₁_eq, rfl, rfl⟩
        have he₁_eq' : e₁ = e₀ := ιE.injective he₁_eq
        subst he₁_eq'
        have hx_K₁ : x ∈ ιV ⁻¹' V(K₁) := huv_K₁.left_mem
        have hx_cl : x ∈ closure e₁ := by
          have : x ∈ closure e₁ ∩ Γ.V := by rw [hcl]; exact Set.mem_insert x {y}
          exact this.1
        have hz₀_Δ : z₀ ∈ Δ := by
          by_contra hz_not_Δ
          have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hxΓ, rfl⟩)
          have heA : e₁ ∈ Γ.A := Or.inl (Or.inr he₁)
          have hd_xe : d {x} e₁ ≤ 2 :=
            GM16.vertex_atom_dist_le_two hS hJ.hasMetric x hxΓ e₁ heA hx_cl
          have hθ_dist : θ ≤ subsetTangleDist Γ ord d {x} (Set.univ \ Δ) := h2.1 x hx_K₁
          have hle : subsetTangleDist Γ ord d {x} (Set.univ \ Δ) ≤ d {x} e₁ :=
            subsetTangleDist_le_of_mem hxA heA ⟨x, rfl, rfl⟩ ⟨z₀, hz₀, trivial, hz_not_Δ⟩
          have h4 := hJ.four_le_θ
          omega
        exact disjoint_left.mp (h_ii i) hz₀_DA hz₀_Δ
    · exact hf_not_L ((inf_le_left : L ⊓ K₁ ≤ L).edgeSet_mono hf_LK₁)
  · exact hf_Au

/-! ## Proof of Claim (9) of 7.3 (page 550) -/

/-- If `ρ : α → α` retracts `G₁` onto `G₀` in the sense that every vertex of `G₁` maps into `V(G₀)`
and every link `G₁.IsLink e a b` satisfies either `G₀.IsLink e (ρ a) (ρ b)` or `ρ a = ρ b`, then
`AreConnectedIn G₁ u v` implies `AreConnectedIn G₀ (ρ u) (ρ v)`. -/
theorem areConnectedIn_of_retract {G₀ G₁ : Graph α β} {ρ : α → α}
    (hρ_V : ∀ x ∈ V(G₁), ρ x ∈ V(G₀))
    (hρ_link : ∀ {e : β} {a b : α}, G₁.IsLink e a b →
      G₀.IsLink e (ρ a) (ρ b) ∨ ρ a = ρ b)
    {u v : α} (hconn : AreConnectedIn G₁ u v) :
    AreConnectedIn G₀ (ρ u) (ρ v) := by
  rw [areConnectedIn_iff_walk] at hconn
  rcases hconn with ⟨_, _, ⟨W⟩⟩
  have hwalk : ∀ {a b : α}, GraphWalk G₁ a b → AreConnectedIn G₀ (ρ a) (ρ b) := by
    intro a b W₀
    induction W₀ with
    | nil ha => exact areConnectedIn_self_iff.mpr (hρ_V _ ha)
    | @cons a₁ m₁ b₁ e hlink _ ih =>
      rcases hρ_link hlink with hlink₀ | heq
      · have hstep : AreConnectedIn G₀ (ρ a₁) (ρ m₁) :=
          areConnectedIn_iff_walk.mpr
            ⟨hlink₀.left_mem, hlink₀.right_mem, ⟨GraphWalk.cons hlink₀ (GraphWalk.nil hlink₀.right_mem)⟩⟩
        exact hstep.trans ih
      · rw [heq]
        exact ih
  exact hwalk W

/-- Definition of $\alpha \colon \alpha \to \alpha$ on page 550: maps the $j$-th term of
$\pi(A'_i)$ to the $j$-th term of $\pi(A_i)$, and fixes all other vertices (in particular $Z_0$). -/
noncomputable def alphaMap73 {t : ℕ} (ιV : S ↪ α)
    {πLen : Graph α β → ℕ} (πS : ∀ A : Graph α β, Fin (πLen A) → S)
    (A_fam A_fam' : Fin t → Graph α β)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)) (u : α) : α :=
  open Classical in
  if h : ∃ (i : Fin t) (j : Fin (πLen (A_fam' i))), u = ιV (πS (A_fam' i) j) then
    let i := Classical.choose h
    let j := Classical.choose (Classical.choose_spec h)
    ιV (πS (A_fam i) (Fin.cast (hlen i) j))
  else u

/-- Under pairwise disjointness of $D(A'_i)$ and injectivity of $\pi(A'_i)$, `alphaMap73` maps the
$j$-th term of $\pi(A'_i)$ to the $j$-th term of $\pi(A_i)$. -/
theorem alphaMap73_apply_πS {q t : ℕ}
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
    {A_fam A_fam' : Fin t → Graph α β}
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    (i : Fin t) (j : Fin (πLen (A_fam' i))) :
    alphaMap73 ιV πS A_fam A_fam' hlen (ιV (πS (A_fam' i) j)) =
      ιV (πS (A_fam i) (Fin.cast (hlen i) j)) := by
  classical
  have huniq : ∀ (i₀ : Fin t) (j₀ : Fin (πLen (A_fam' i₀))),
      ιV (πS (A_fam' i) j) = ιV (πS (A_fam' i₀) j₀) →
      ιV (πS (A_fam i₀) (Fin.cast (hlen i₀) j₀)) =
        ιV (πS (A_fam i) (Fin.cast (hlen i) j)) := by
    intro i₀ j₀ heq
    have heq_S : πS (A_fam' i) j = πS (A_fam' i₀) j₀ := ιV.injective heq
    have hi_eq : i₀ = i := by
      by_contra hne
      have hx_i : πS (A_fam' i) j ∈ D (A_fam' i) :=
        (hJ.range_πS_subset_D_and_ncard (hA'_mem i)).2.1 ⟨j, rfl⟩
      have hx_i₀ : πS (A_fam' i) j ∈ D (A_fam' i₀) :=
        heq_S ▸ (hJ.range_πS_subset_D_and_ncard (hA'_mem i₀)).2.1 ⟨j₀, rfl⟩
      have h1_le_θ : 1 ≤ θ := le_trans (by decide : 1 ≤ 4) hJ.four_le_θ
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hdisj := disjoint_of_one_le_subsetTangleDist hJ.hasMetric
          (h1_le_θ.trans (h_iv i₀ i hlt))
        exact disjoint_left.mp hdisj hx_i₀ hx_i
      · have hdisj := disjoint_of_one_le_subsetTangleDist hJ.hasMetric
          (h1_le_θ.trans (h_iv i i₀ hgt))
        exact disjoint_left.mp hdisj hx_i hx_i₀
    subst hi_eq
    have hj_eq : j₀ = j := (hJ.π_valid (A_fam' i₀) (hA'_mem i₀)).2.2.1 heq_S.symm
    subst hj_eq
    rfl
  unfold alphaMap73
  split_ifs with hex
  · exact huniq (Classical.choose hex) (Classical.choose (Classical.choose_spec hex))
      (Classical.choose_spec (Classical.choose_spec hex))
  · exact False.elim (hex ⟨i, j, rfl⟩)

/-- `alphaMap73` fixes every vertex $u \in V(K_1)$ (and hence every $u \in Z_0$). -/
theorem alphaMap73_apply_of_mem_K₁ {q t : ℕ}
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
    (hCleanV : ιV ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A))
    {A_fam A_fam' : Fin t → Graph α β}
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    (h_iii : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ)
    {u : α}
    (hu : u ∈ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}))) :
    alphaMap73 ιV πS A_fam A_fam' hlen u = u := by
  classical
  have h2 := lemma_7_3_claim_2 hJ hCleanV
  unfold alphaMap73
  split_ifs with hex
  · exfalso
    rcases hex with ⟨i, j, rfl⟩
    have hx_Δ : πS (A_fam' i) j ∈ Δ := h2.2.2 hu
    have hx_DA' : πS (A_fam' i) j ∈ D (A_fam' i) :=
      (hJ.range_πS_subset_D_and_ncard (hA'_mem i)).2.1 ⟨j, rfl⟩
    exact disjoint_left.mp (h_iii i) hx_DA' hx_Δ
  · rfl

/-- **Graph Minors XXII, (7.3) Claim (9)** (page 550):
(9) *$u, v \in Z'$ are $L'_0$-connected if and only if $\alpha(u), \alpha(v)$ are
$L_0 \cup (L \cap K_1)$-connected.* -/
theorem lemma_7_3_claim_9 {q t : ℕ}
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
    (hCleanV : ιV ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A))
    (hCleanE : ιE ⁻¹' E(R_G.G.toGraph) ⊆ Γ.E)
    {A_fam A_fam' : Fin t → Graph α β}
    (hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    (h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ)
    (h_iii : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ)
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    {D_in : Fin t → Set S}
    (hD_in : ∀ i : Fin t, IsClosedDisc (D_in i) ∧ D_in i ⊆ D (A_fam i) \ subBd (D (A_fam i)))
    {β_homeo : S ≃ₜ S}
    (hβ_fix : ∀ z ∈ Δ, β_homeo z = z)
    (hβ_img : ∀ i : Fin t, β_homeo '' D_in i = D (A_fam' i))
    {M_fam : Fin t → Drawing S}
    {L_arc : ∀ i : Fin t, Fin (πLen (A_fam i)) → Set S}
    (hM_spec : ∀ i : Fin t,
      let π_in : Fin (πLen (A_fam i)) → S :=
        fun j => β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))
      (M_fam i).U = (⋃ j : Fin (πLen (A_fam i)), L_arc i j) ∧
      (M_fam i).V = Set.range π_in ∪ Set.range (πS (A_fam i)) ∧
      (M_fam i).E = Set.range (fun j : Fin (πLen (A_fam i)) =>
        L_arc i j \ {π_in j, πS (A_fam i) j}) ∧
      (∀ j : Fin (πLen (A_fam i)),
        IsLineWithEnds (L_arc i j) (π_in j) (πS (A_fam i) j)) ∧
      (∀ j : Fin (πLen (A_fam i)), π_in j ≠ πS (A_fam i) j) ∧
      Pairwise (fun j₁ j₂ : Fin (πLen (A_fam i)) => Disjoint (L_arc i j₁) (L_arc i j₂)))
    (hM_E : ∀ i : Fin t, ∀ e ∈ (M_fam i).E, e ⊆ (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i)
    {M_union Γ₀ : Drawing S}
    (hMU_V : M_union.V = ⋃ i : Fin t, (M_fam i).V)
    (hMU_E : M_union.E = ⋃ i : Fin t, (M_fam i).E)
    (hΓ₀_eq : Γ₀ = Γ.interSet (Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i)))))
    {Z₀ : Set α}
    (hZ₀_K₁ : Z₀ ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hZ₀_L : Z₀ ⊆ V(subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))))
    {L'₀ : Graph α β}
    (heff : effectOn L'₀ (Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))) =
      effectOn (graphUnion
        (mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo)
          (graphUnion
            ((graphUnion (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β)
              (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))) ⊓
              (Γ₀.toEmbeddedGraph ιV ιE))
            (M_union.toEmbeddedGraph ιV ιE)))
        ((graphUnion (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β)
          (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))) ⊓
          (graphUnion K (subgraphSUnion R_G.G.toGraph
            {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}))))
        (Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i)))) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let π_bar_union := ⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))
    let L := graphUnion (Graph.noEdge π_bar_union β)
      (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))
    let L₀_ext := graphUnion (L ⊓ (Γ₀.toEmbeddedGraph ιV ιE)) (Graph.noEdge π_bar_union β)
    let Z' := Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))
    let α_map := alphaMap73 ιV πS A_fam A_fam' hlen
    ∀ u ∈ Z', ∀ v ∈ Z',
      AreConnectedIn L'₀ u v ↔ AreConnectedIn (graphUnion L₀_ext (L ⊓ K₁)) (α_map u) (α_map v) := by
  classical
  intro 𝒜_far K₁ π_bar_union L L₀_ext Z' α_map u huZ' v hvZ'
  let L₀ := L ⊓ (Γ₀.toEmbeddedGraph ιV ιE)
  let L₁ := graphUnion L₀ (M_union.toEmbeddedGraph ιV ιE)
  let L₂ := mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo) L₁
  let G₀ := graphUnion L₀_ext (L ⊓ K₁)
  let G₁ := graphUnion L₁ (L ⊓ K₁)
  let G₂ := graphUnion L₂ (L ⊓ K₁)
  let μ_map : α → α := (homeoVertEquiv ιV β_homeo).symm
  let π_in : ∀ i : Fin t, Fin (πLen (A_fam i)) → S :=
    fun i j => β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))
  have h2 := lemma_7_3_claim_2 hJ hCleanV
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph := hJ.Γ_le.trans deleteVerts_le
  -- Check that `π_bar_union ⊆ V(M_union.toEmbeddedGraph ιV ιE)`:
  have hπ_bar_sub_MU : π_bar_union ⊆ V(M_union.toEmbeddedGraph ιV ιE) := by
    rintro _ ⟨_, ⟨i, rfl⟩, x, ⟨j, rfl⟩, rfl⟩
    refine ⟨πS (A_fam i) j, ?_, rfl⟩
    rw [hMU_V, mem_iUnion]
    refine ⟨i, ?_⟩
    rw [(hM_spec i).2.1]
    exact Or.inr ⟨j, rfl⟩
  -- Check that `Disjoint E(G₀) E(M_union.toEmbeddedGraph ιV ιE)`:
  have hdisj_E_G₀_MU : Disjoint E(G₀) E(M_union.toEmbeddedGraph ιV ιE) := by
    rw [Set.disjoint_left]
    rintro e heG₀ ⟨e₀, he₀_MU, rfl⟩
    rw [hMU_E, mem_iUnion] at he₀_MU
    rcases he₀_MU with ⟨i, he₀_Mi⟩
    have he₀_sub : e₀ ⊆ (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i := hM_E i e₀ he₀_Mi
    obtain ⟨z₀, hz₀⟩ := he₀_Mi.1
    have hz₀_int : z₀ ∈ D (A_fam i) \ subBd (D (A_fam i)) := (he₀_sub hz₀).1
    simp only [G₀, L₀_ext, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty] at heG₀
    rcases heG₀ with heL₀ | heLK₁
    · have heΓ₀ : ιE e₀ ∈ E(Γ₀.toEmbeddedGraph ιV ιE) :=
        (inf_le_right : L₀ ≤ Γ₀.toEmbeddedGraph ιV ιE).edgeSet_mono heL₀
      rcases heΓ₀ with ⟨e₁, he₁_Γ₀, he₁_eq⟩
      have he₁_eq' : e₁ = e₀ := ιE.injective he₁_eq
      subst he₁_eq'
      rw [hΓ₀_eq, mem_interSet_E_iff] at he₁_Γ₀
      have hz₀_compl := he₁_Γ₀.2 hz₀
      exact hz₀_compl.2 (mem_iUnion.mpr ⟨i, hz₀_int⟩)
    · have heK₁ : ιE e₀ ∈ E(K₁) := (inf_le_right : L ⊓ K₁ ≤ K₁).edgeSet_mono heLK₁
      obtain ⟨u', v', huv'_K₁⟩ := K₁.exists_isLink_of_mem_edgeSet heK₁
      have huv'_G : R_G.G.toGraph.IsLink (ιE e₀) u' v' := huv'_K₁.mono hK₁_le
      have he₀_Γ : e₀ ∈ Γ.E := hCleanE huv'_G.edge_mem
      have huv'_Γ : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e₀) u' v' :=
        ((Compatible.of_le_le hΓ_le le_rfl).isLink_congr
          (mem_image_of_mem ιE he₀_Γ) huv'_G.edge_mem).mpr huv'_G
      rcases huv'_Γ with ⟨e₁, x, y, ⟨he₁, hxΓ, _, hcl⟩, he₁_eq, rfl, rfl⟩
      have he₁_eq' : e₁ = e₀ := ιE.injective he₁_eq
      subst he₁_eq'
      have hx_K₁ : x ∈ ιV ⁻¹' V(K₁) := huv'_K₁.left_mem
      have hx_cl : x ∈ closure e₁ := by
        have : x ∈ closure e₁ ∩ Γ.V := by rw [hcl]; exact Set.mem_insert x {y}
        exact this.1
      obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
      have hz₀_Δ : z₀ ∈ Δ := by
        by_contra hz_not_Δ
        have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hxΓ, rfl⟩)
        have heA : e₁ ∈ Γ.A := Or.inl (Or.inr he₁)
        have hd_xe : d {x} e₁ ≤ 2 :=
          GM16.vertex_atom_dist_le_two hS hJ.hasMetric x hxΓ e₁ heA hx_cl
        have hθ_dist : θ ≤ subsetTangleDist Γ ord d {x} (Set.univ \ Δ) := h2.1 x hx_K₁
        have hle : subsetTangleDist Γ ord d {x} (Set.univ \ Δ) ≤ d {x} e₁ :=
          subsetTangleDist_le_of_mem hxA heA ⟨x, rfl, rfl⟩ ⟨z₀, hz₀, trivial, hz_not_Δ⟩
        have h4 := hJ.four_le_θ
        omega
      exact disjoint_left.mp (h_ii i) hz₀_int.1 hz₀_Δ
  -- Check that `G₀ ≤ G₁`:
  have hG₀_le_G₁ : G₀ ≤ G₁ := by
    refine ⟨?_, fun e x y hl => ?_⟩
    · intro w hw
      simp only [G₀, G₁, L₁, L₀_ext, vertexSet_graphUnion, Graph.vertexSet_noEdge, mem_union] at hw ⊢
      rcases hw with (hwL₀ | hwπ) | hwLK₁
      · exact Or.inl (Or.inl hwL₀)
      · exact Or.inl (Or.inr (hπ_bar_sub_MU hwπ))
      · exact Or.inr hwLK₁
    · rcases hl with (hlL₀ | ⟨_, hlno⟩) | ⟨he_not_L₀_ext, hlLK₁⟩
      · exact Or.inl (Or.inl hlL₀)
      · exact False.elim hlno
      · refine Or.inr ⟨?_, hlLK₁⟩
        rw [edgeSet_graphUnion, mem_union, not_or]
        refine ⟨fun heL₀ => he_not_L₀_ext (Or.inl heL₀), fun heMU => ?_⟩
        have heG₀ : e ∈ E(G₀) := Or.inr hlLK₁.edge_mem
        exact disjoint_left.mp hdisj_E_G₀_MU heG₀ heMU
  -- Check that every link in `G₁` is either in `G₀` or in `M_union.toEmbeddedGraph ιV ιE`:
  have hG₁_isLink : ∀ {e : β} {a b : α}, G₁.IsLink e a b →
      G₀.IsLink e a b ∨ (M_union.toEmbeddedGraph ιV ιE).IsLink e a b := by
    intro e a b hl
    rcases hl with (hlL₀ | ⟨_, hlMU⟩) | ⟨he_not_L₁, hlLK₁⟩
    · exact Or.inl (Or.inl (Or.inl hlL₀))
    · exact Or.inr hlMU
    · rw [edgeSet_graphUnion, mem_union, not_or] at he_not_L₁
      refine Or.inl (Or.inr ⟨?_, hlLK₁⟩)
      simp only [L₀_ext, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
      exact he_not_L₁.1
  -- Define the retraction `ρ : α → α` from `V(G₁)` onto `V(G₀)`:
  let ρ : α → α := fun w =>
    if h : ∃ (i : Fin t) (j : Fin (πLen (A_fam i))), w = ιV (π_in i j) then
      let i := Classical.choose h
      let j := Classical.choose (Classical.choose_spec h)
      ιV (πS (A_fam i) j)
    else w
  -- 1. Uniqueness of `(i, j)` for `π_in i j`:
  have hπ_in_inj : ∀ (i₁ i₂ : Fin t) (j₁ : Fin (πLen (A_fam i₁))) (j₂ : Fin (πLen (A_fam i₂))),
      π_in i₁ j₁ = π_in i₂ j₂ → i₁ = i₂ ∧ HEq j₁ j₂ := by
    intro i₁ i₂ j₁ j₂ heq
    have heq' : πS (A_fam' i₁) (Fin.cast (hlen i₁).symm j₁) =
        πS (A_fam' i₂) (Fin.cast (hlen i₂).symm j₂) := by
      have := congrArg β_homeo heq
      simpa [π_in] using this
    have hi_eq : i₁ = i₂ := by
      by_contra hne
      have hx₁ : πS (A_fam' i₁) (Fin.cast (hlen i₁).symm j₁) ∈ D (A_fam' i₁) :=
        (hJ.range_πS_subset_D_and_ncard (hA'_mem i₁)).2.1 ⟨_, rfl⟩
      have hx₂ : πS (A_fam' i₁) (Fin.cast (hlen i₁).symm j₁) ∈ D (A_fam' i₂) :=
        heq' ▸ (hJ.range_πS_subset_D_and_ncard (hA'_mem i₂)).2.1 ⟨_, rfl⟩
      have h1_le_θ : 1 ≤ θ := le_trans (by decide : 1 ≤ 4) hJ.four_le_θ
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hdisj := disjoint_of_one_le_subsetTangleDist hJ.hasMetric
          (h1_le_θ.trans (h_iv i₁ i₂ hlt))
        exact disjoint_left.mp hdisj hx₁ hx₂
      · have hdisj := disjoint_of_one_le_subsetTangleDist hJ.hasMetric
          (h1_le_θ.trans (h_iv i₂ i₁ hgt))
        exact disjoint_left.mp hdisj hx₂ hx₁
    subst hi_eq
    have hj_eq' := (hJ.π_valid (A_fam' i₁) (hA'_mem i₁)).2.2.1 heq'
    exact ⟨rfl, heq_of_eq ((Fin.cast_injective (hlen i₁).symm) hj_eq')⟩
  have hρ_π_in : ∀ (i : Fin t) (j : Fin (πLen (A_fam i))),
      ρ (ιV (π_in i j)) = ιV (πS (A_fam i) j) := by
    intro i j
    have huniq : ∀ (i₀ : Fin t) (j₀ : Fin (πLen (A_fam i₀))),
        ιV (π_in i j) = ιV (π_in i₀ j₀) →
        ιV (πS (A_fam i₀) j₀) = ιV (πS (A_fam i) j) := by
      intro i₀ j₀ heq
      obtain ⟨hi, hj⟩ := hπ_in_inj i i₀ j j₀ (ιV.injective heq)
      subst hi
      cases eq_of_heq hj
      rfl
    dsimp only [ρ]
    split_ifs with hex
    · exact huniq (Classical.choose hex) (Classical.choose (Classical.choose_spec hex))
        (Classical.choose_spec (Classical.choose_spec hex))
    · exact False.elim (hex ⟨i, j, rfl⟩)
  -- 2. For `w ∈ V(G₀)`, `ρ w = w`:
  have hπ_in_mem_int : ∀ (i : Fin t) (j : Fin (πLen (A_fam i))),
      π_in i j ∈ D (A_fam i) \ subBd (D (A_fam i)) := by
    intro i j
    have h5 := lemma_7_3_claim_5 hJ hA_mem hA'_mem hlen (fun k => (hD_in k).1) hβ_img i
    have hbd_in : π_in i j ∈ subBd (D_in i) := h5.1 ⟨Fin.cast (hlen i).symm j, rfl⟩
    have hcl_in : subBd (D_in i) ⊆ D_in i := by
      rw [subBd_eq_frontier]
      exact (hD_in i).1.isClosed.frontier_subset
    exact (hD_in i).2 (hcl_in hbd_in)
  have hρ_of_mem_G₀ : ∀ w ∈ V(G₀), ρ w = w := by
    intro w hw
    dsimp only [ρ]
    split_ifs with hex
    · exfalso
      rcases hex with ⟨i, j, rfl⟩
      have hx_int : π_in i j ∈ D (A_fam i) \ subBd (D (A_fam i)) := hπ_in_mem_int i j
      simp only [G₀, L₀_ext, vertexSet_graphUnion, vertexSet_inf, Graph.vertexSet_noEdge,
        mem_union, mem_inter_iff] at hw
      rcases hw with ((⟨_, hwΓ₀⟩ | hwπ) | ⟨_, hwK₁⟩)
      · rcases hwΓ₀ with ⟨x, hxΓ₀, hxeq⟩
        have hxeq' : x = π_in i j := ιV.injective hxeq
        subst hxeq'
        have hxU : π_in i j ∈ Γ₀.U := Γ₀.V_subset_U hxΓ₀
        rw [hΓ₀_eq] at hxU
        have hxS₀ := interSet_U_subset (isClosed_compl_iUnion_discInt _) hxU
        exact hxS₀.2 (mem_iUnion.mpr ⟨i, hx_int⟩)
      · obtain ⟨k, x, ⟨j', rfl⟩, hxeq⟩ := mem_iUnion.mp hwπ
        have hxeq' : πS (A_fam k) j' = π_in i j := ιV.injective hxeq
        by_cases hAk : A_fam k = A_fam i
        · have hx_bd : πS (A_fam k) j' ∈ subBd (D (A_fam k)) :=
            (hJ.range_πS_subset_D_and_ncard (hA_mem k)).1 ⟨j', rfl⟩
          rw [hxeq', hAk] at hx_bd
          exact hx_int.2 hx_bd
        · have hx_Dk : π_in i j ∈ D (A_fam i) ∩ D (A_fam k) :=
            ⟨hx_int.1, hxeq' ▸ (hJ.range_πS_subset_D_and_ncard (hA_mem k)).2.1 ⟨j', rfl⟩⟩
          rw [hJ.D_inter_eq (A_fam i) (hA_mem i) (A_fam k) (hA_mem k) (Ne.symm hAk)] at hx_Dk
          exact hx_int.2 ((hJ.range_πS_subset_D_and_ncard (hA_mem i)).1 hx_Dk.1)
      · have hx_Δ : π_in i j ∈ Δ := h2.2.2 hwK₁
        exact disjoint_left.mp (h_ii i) hx_int.1 hx_Δ
    · rfl
  -- 3. Every `ιV (πS (A_fam i) j) ∈ V(G₀)`:
  have hπS_mem_G₀ : ∀ (i : Fin t) (j : Fin (πLen (A_fam i))),
      ιV (πS (A_fam i) j) ∈ V(G₀) := by
    intro i j
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i, ⟨πS (A_fam i) j, ⟨j, rfl⟩, rfl⟩⟩))
  -- 4. Helper for `closure e₀ ∩ M_union.V = {π_in i j, πS (A_fam i) j}`:
  have hcl_Mi_eq : ∀ (i : Fin t) (j : Fin (πLen (A_fam i))),
      let e₀ := L_arc i j \ {π_in i j, πS (A_fam i) j}
      e₀ ∈ (M_fam i).E ∧ closure e₀ ∩ (M_fam i).V = {π_in i j, πS (A_fam i) j} := by
    intro i j e₀
    have hline : IsLineWithEnds (L_arc i j) (π_in i j) (πS (A_fam i) j) :=
      (hM_spec i).2.2.2.1 j
    have hne : π_in i j ≠ πS (A_fam i) j := (hM_spec i).2.2.2.2.1 j
    have hdisj : Pairwise (fun j₁ j₂ : Fin (πLen (A_fam i)) => Disjoint (L_arc i j₁) (L_arc i j₂)) :=
      (hM_spec i).2.2.2.2.2
    have he₀_Mi : e₀ ∈ (M_fam i).E := by
      rw [(hM_spec i).2.2.1]
      exact ⟨j, rfl⟩
    refine ⟨he₀_Mi, ?_⟩
    have hcl_eq : closure e₀ = L_arc i j := GM11.closure_sdiff_pair hline
    have hends_sub : ∀ k : Fin (πLen (A_fam i)),
        ({π_in i k, πS (A_fam i) k} : Set S) ⊆ L_arc i k :=
      fun k => (GM11.lineDrawing ((hM_spec i).2.2.2.1 k) ((hM_spec i).2.2.2.2.1 k)).V_subset_U
    rw [hcl_eq]
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨hzL, hzV⟩
      rw [(hM_spec i).2.1] at hzV
      rcases hzV with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hzk : π_in i k ∈ L_arc i k := hends_sub k (Or.inl rfl)
        have hjk : j = k := by
          by_contra hjk_ne
          exact disjoint_left.mp (hdisj hjk_ne) hzL hzk
        subst hjk
        exact Or.inl rfl
      · have hzk : πS (A_fam i) k ∈ L_arc i k := hends_sub k (Or.inr rfl)
        have hjk : j = k := by
          by_contra hjk_ne
          exact disjoint_left.mp (hdisj hjk_ne) hzL hzk
        subst hjk
        exact Or.inr rfl
    · rintro z (rfl | rfl)
      · refine ⟨hends_sub j (Or.inl rfl), ?_⟩
        rw [(hM_spec i).2.1]
        exact Or.inl ⟨j, rfl⟩
      · refine ⟨hends_sub j (Or.inr rfl), ?_⟩
        rw [(hM_spec i).2.1]
        exact Or.inr ⟨j, rfl⟩
  have hcl_MU_eq : ∀ (i : Fin t) (j : Fin (πLen (A_fam i))),
      let e₀ := L_arc i j \ {π_in i j, πS (A_fam i) j}
      closure e₀ ∩ M_union.V = {π_in i j, πS (A_fam i) j} := by
    intro i j e₀
    have ⟨he₀_Mi, hcl_Mi⟩ := hcl_Mi_eq i j
    have he₀_MU : e₀ ∈ M_union.E := by
      rw [hMU_E, mem_iUnion]
      exact ⟨i, he₀_Mi⟩
    refine Subset.antisymm ?_ ?_
    · intro z ⟨hz_cl, hz_V⟩
      have hz_not_e₀ : z ∉ e₀ := fun hze₀ => (he₀_MU.2.1 hze₀).2 hz_V
      have hz_Mi_V : z ∈ (M_fam i).V := by
        by_contra hz_not
        have hz_e₀ : z ∈ e₀ := by
          change z ∈ L_arc i j \ {π_in i j, πS (A_fam i) j}
          rw [← (M_fam i).closure_diff_V he₀_Mi]
          exact ⟨hz_cl, hz_not⟩
        exact hz_not_e₀ hz_e₀
      rw [← hcl_Mi]
      exact ⟨hz_cl, hz_Mi_V⟩
    · rw [← hcl_Mi]
      refine inter_subset_inter_right _ ?_
      intro z hz
      rw [hMU_V, mem_iUnion]
      exact ⟨i, hz⟩
  -- 5. Check retraction hypotheses `hρ_V` and `hρ_link`:
  have hρ_V : ∀ w ∈ V(G₁), ρ w ∈ V(G₀) := by
    intro w hw
    simp only [G₁, L₁, vertexSet_graphUnion, mem_union] at hw
    rcases hw with (hwL₀ | hwMU) | hwLK₁
    · have hwG₀ : w ∈ V(G₀) := Or.inl (Or.inl hwL₀)
      rwa [hρ_of_mem_G₀ w hwG₀]
    · rcases hwMU with ⟨x, hxMU, rfl⟩
      rw [hMU_V, mem_iUnion] at hxMU
      rcases hxMU with ⟨i, hxMi⟩
      rw [(hM_spec i).2.1, mem_union] at hxMi
      rcases hxMi with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hρ_π_in i j]
        exact hπS_mem_G₀ i j
      · have hwG₀ : ιV (πS (A_fam i) j) ∈ V(G₀) := hπS_mem_G₀ i j
        rwa [hρ_of_mem_G₀ _ hwG₀]
    · have hwG₀ : w ∈ V(G₀) := Or.inr hwLK₁
      rwa [hρ_of_mem_G₀ w hwG₀]
  have hρ_link : ∀ {e : β} {a b : α}, G₁.IsLink e a b →
      G₀.IsLink e (ρ a) (ρ b) ∨ ρ a = ρ b := by
    intro e a b hl
    rcases hG₁_isLink hl with hlG₀ | hlMU
    · rw [hρ_of_mem_G₀ a hlG₀.left_mem, hρ_of_mem_G₀ b hlG₀.right_mem]
      exact Or.inl hlG₀
    · rcases hlMU with ⟨e₀, x, y, ⟨he₀_MU, _, _, hcl_MU⟩, rfl, rfl, rfl⟩
      rw [hMU_E, mem_iUnion] at he₀_MU
      rcases he₀_MU with ⟨i, he₀_Mi⟩
      rw [(hM_spec i).2.2.1] at he₀_Mi
      rcases he₀_Mi with ⟨j, he₀_eq⟩
      subst he₀_eq
      have hcl_eq : ({x, y} : Set S) = {π_in i j, πS (A_fam i) j} :=
        hcl_MU.symm.trans (hcl_MU_eq i j)
      have hρ_end : ∀ z ∈ ({π_in i j, πS (A_fam i) j} : Set S),
          ρ (ιV z) = ιV (πS (A_fam i) j) := by
        rintro z (rfl | rfl)
        · exact hρ_π_in i j
        · exact hρ_of_mem_G₀ _ (hπS_mem_G₀ i j)
      have hx_mem : x ∈ ({π_in i j, πS (A_fam i) j} : Set S) :=
        hcl_eq ▸ Set.mem_insert x {y}
      have hy_mem : y ∈ ({π_in i j, πS (A_fam i) j} : Set S) :=
        hcl_eq ▸ Set.mem_insert_of_mem x rfl
      exact Or.inr ((hρ_end x hx_mem).trans (hρ_end y hy_mem).symm)
  -- 6. For every `w ∈ Z'`, `α_map w ∈ V(G₀)` and `AreConnectedIn G₁ (α_map w) (μ_map w)`:
  have hZ₀_mem_LK₁ : ∀ w ∈ Z₀, w ∈ V(L ⊓ K₁) := by
    intro w hw
    exact ⟨Or.inr (hZ₀_L hw), hZ₀_K₁ hw⟩
  have hZ'_α_μ : ∀ w ∈ Z', α_map w ∈ V(G₀) ∧ AreConnectedIn G₁ (α_map w) (μ_map w) := by
    rintro w (hwZ₀ | hwπ')
    · have hwK₁ : w ∈ V(K₁) := hZ₀_K₁ hwZ₀
      have hα_w : α_map w = w := alphaMap73_apply_of_mem_K₁ hJ hCleanV hA'_mem hlen h_iii hwK₁
      have hμ_w : μ_map w = w := by
        by_cases hrange : w ∈ Set.range ιV
        · rcases hrange with ⟨x, rfl⟩
          have hx_Δ : x ∈ Δ := h2.2.2 hwK₁
          change (homeoVertEquiv ιV β_homeo).symm (ιV x) = ιV x
          rw [homeoVertEquiv_symm, homeoVertEquiv_apply_ιV]
          congr 1
          exact β_homeo.injective (by rw [β_homeo.apply_symm_apply, hβ_fix x hx_Δ])
        · change (homeoVertEquiv ιV β_homeo).symm w = w
          rw [homeoVertEquiv_symm]
          exact homeoVertEquiv_apply_of_not_mem ιV β_homeo.symm hrange
      have hwG₀ : w ∈ V(G₀) := Or.inr (hZ₀_mem_LK₁ w hwZ₀)
      rw [hα_w, hμ_w]
      exact ⟨hwG₀, areConnectedIn_self_iff.mpr (hG₀_le_G₁.vertexSet_mono hwG₀)⟩
    · obtain ⟨i, x, ⟨j', rfl⟩, rfl⟩ := mem_iUnion.mp hwπ'
      let j : Fin (πLen (A_fam i)) := Fin.cast (hlen i) j'
      have hj'_eq : j' = Fin.cast (hlen i).symm j := by simp [j]
      have hα_w : α_map (ιV (πS (A_fam' i) j')) = ιV (πS (A_fam i) j) :=
        alphaMap73_apply_πS hJ hA'_mem hlen h_iv i j'
      have hμ_w : μ_map (ιV (πS (A_fam' i) j')) = ιV (π_in i j) := by
        change (homeoVertEquiv ιV β_homeo).symm (ιV (πS (A_fam' i) j')) = ιV (π_in i j)
        rw [homeoVertEquiv_symm, homeoVertEquiv_apply_ιV, hj'_eq]
      rw [hα_w, hμ_w]
      refine ⟨hπS_mem_G₀ i j, ?_⟩
      -- Show `G₁.IsLink (ιE e₀) (ιV (πS (A_fam i) j)) (ιV (π_in i j))`:
      let e₀ := L_arc i j \ {π_in i j, πS (A_fam i) j}
      have ⟨he₀_Mi, _⟩ := hcl_Mi_eq i j
      have he₀_MU : e₀ ∈ M_union.E := by
        rw [hMU_E, mem_iUnion]
        exact ⟨i, he₀_Mi⟩
      have hx_MU : πS (A_fam i) j ∈ M_union.V := by
        rw [hMU_V, mem_iUnion]
        refine ⟨i, ?_⟩
        rw [(hM_spec i).2.1]
        exact Or.inr ⟨j, rfl⟩
      have hy_MU : π_in i j ∈ M_union.V := by
        rw [hMU_V, mem_iUnion]
        refine ⟨i, ?_⟩
        rw [(hM_spec i).2.1]
        exact Or.inl ⟨j, rfl⟩
      have hcl_symm : closure e₀ ∩ M_union.V = {πS (A_fam i) j, π_in i j} := by
        rw [hcl_MU_eq i j, Set.pair_comm]
      have hl_MU : (M_union.toEmbeddedGraph ιV ιE).IsLink (ιE e₀)
          (ιV (πS (A_fam i) j)) (ιV (π_in i j)) :=
        ⟨e₀, πS (A_fam i) j, π_in i j, ⟨he₀_MU, hx_MU, hy_MU, hcl_symm⟩, rfl, rfl, rfl⟩
      have he_not_L₀ : ιE e₀ ∉ E(L₀) := by
        intro heL₀
        have heG₀ : ιE e₀ ∈ E(G₀) := Or.inl (Or.inl heL₀)
        exact disjoint_left.mp hdisj_E_G₀_MU heG₀ ⟨e₀, he₀_MU, rfl⟩
      have hl_G₁ : G₁.IsLink (ιE e₀) (ιV (πS (A_fam i) j)) (ιV (π_in i j)) :=
        Or.inl (Or.inr ⟨he_not_L₀, hl_MU⟩)
      exact areConnectedIn_iff_walk.mpr
        ⟨hl_G₁.left_mem, hl_G₁.right_mem, ⟨GraphWalk.cons hl_G₁ (GraphWalk.nil hl_G₁.right_mem)⟩⟩
  -- 7. Equivalence (a) ↔ (b):
  have hαu_G₀ : α_map u ∈ V(G₀) := (hZ'_α_μ u huZ').1
  have hαv_G₀ : α_map v ∈ V(G₀) := (hZ'_α_μ v hvZ').1
  have h_ab : AreConnectedIn G₀ (α_map u) (α_map v) ↔ AreConnectedIn G₁ (α_map u) (α_map v) := by
    constructor
    · exact AreConnectedIn.mono hG₀_le_G₁
    · intro h
      have hret := areConnectedIn_of_retract hρ_V hρ_link h
      rwa [hρ_of_mem_G₀ (α_map u) hαu_G₀, hρ_of_mem_G₀ (α_map v) hαv_G₀] at hret
  -- 8. Equivalence (b) ↔ (c):
  have h_bc : AreConnectedIn G₁ (α_map u) (α_map v) ↔ AreConnectedIn G₁ (μ_map u) (μ_map v) := by
    have hconn_u := (hZ'_α_μ u huZ').2
    have hconn_v := (hZ'_α_μ v hvZ').2
    exact ⟨fun h => (hconn_u.symm.trans h).trans hconn_v,
      fun h => (hconn_u.trans h).trans hconn_v.symm⟩
  -- 9. Equivalence (c) ↔ (d). The map fixes every vertex and every edge of `L ⊓ K₁`, since
  -- these lie in `Δ` (the print's "β fixes U(L_1 ∩ (L ∩ K_1)) pointwise", page 550).
  have hLK₁_map : mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo)
      (L ⊓ K₁) = L ⊓ K₁ := by
    apply mapGraphEquiv_eq_self
    · intro w hw
      have hwK₁ : w ∈ V(K₁) := hw.2
      by_cases hrange : w ∈ Set.range ιV
      · rcases hrange with ⟨x, rfl⟩
        rw [homeoVertEquiv_apply_ιV, hβ_fix x (h2.2.2 hwK₁)]
      · exact homeoVertEquiv_apply_of_not_mem ιV β_homeo hrange
    · intro e he
      have heK₁ : e ∈ E(K₁) := (inf_le_right : L ⊓ K₁ ≤ K₁).edgeSet_mono he
      by_cases hrange : e ∈ Set.range ιE
      · rcases hrange with ⟨e₀, rfl⟩
        rw [homeoEdgeEquiv_apply_ιE]
        congr 1
        obtain ⟨u', v', huv'_K₁⟩ := K₁.exists_isLink_of_mem_edgeSet heK₁
        have huv'_G : R_G.G.toGraph.IsLink (ιE e₀) u' v' := huv'_K₁.mono hK₁_le
        have he₀_Γ : e₀ ∈ Γ.E := hCleanE huv'_G.edge_mem
        have huv'_Γ : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e₀) u' v' :=
          ((Compatible.of_le_le hΓ_le le_rfl).isLink_congr
            (mem_image_of_mem ιE he₀_Γ) huv'_G.edge_mem).mpr huv'_G
        rcases huv'_Γ with ⟨e₁, x, y, ⟨he₁, hxΓ, _, hcl⟩, he₁_eq, rfl, rfl⟩
        have he₁_eq' : e₁ = e₀ := ιE.injective he₁_eq
        subst he₁_eq'
        have hx_K₁ : x ∈ ιV ⁻¹' V(K₁) := huv'_K₁.left_mem
        have hx_cl : x ∈ closure e₁ := by
          have : x ∈ closure e₁ ∩ Γ.V := by rw [hcl]; exact Set.mem_insert x {y}
          exact this.1
        obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
        have he₁_sub_Δ : e₁ ⊆ Δ := by
          by_contra hnot
          obtain ⟨z, hze, hz_not_Δ⟩ := not_subset.mp hnot
          have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hxΓ, rfl⟩)
          have heA : e₁ ∈ Γ.A := Or.inl (Or.inr he₁)
          have hd_xe : d {x} e₁ ≤ 2 :=
            GM16.vertex_atom_dist_le_two hS hJ.hasMetric x hxΓ e₁ heA hx_cl
          have hθ_dist : θ ≤ subsetTangleDist Γ ord d {x} (Set.univ \ Δ) := h2.1 x hx_K₁
          have hle : subsetTangleDist Γ ord d {x} (Set.univ \ Δ) ≤ d {x} e₁ :=
            subsetTangleDist_le_of_mem hxA heA ⟨x, rfl, rfl⟩ ⟨z, hze, trivial, hz_not_Δ⟩
          have h4 := hJ.four_le_θ
          omega
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [hβ_fix w (he₁_sub_Δ hw)]
          exact hw
        · intro hz
          exact ⟨z, hz, hβ_fix z (he₁_sub_Δ hz)⟩
      · exact homeoEdgeEquiv_apply_of_not_mem ιE β_homeo hrange
  have hG₂_eq : G₂ = mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo) G₁ := by
    dsimp only [G₁, G₂]
    rw [mapGraphEquiv_graphUnion, hLK₁_map]
  have h_cd : AreConnectedIn G₁ (μ_map u) (μ_map v) ↔ AreConnectedIn G₂ u v := by
    rw [hG₂_eq, ← areConnectedIn_mapGraphEquiv_iff (homeoVertEquiv ιV β_homeo)
      (homeoEdgeEquiv ιE β_homeo) G₁ (μ_map u) (μ_map v)]
    dsimp only [μ_map]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  -- 10. Equivalence (d) ↔ (e):
  have h_de : AreConnectedIn L'₀ u v ↔ AreConnectedIn G₂ u v :=
    effectOn_eq_iff_areConnectedIn.mp heff u huZ' v hvZ'
  exact h_de.trans (h_cd.symm.trans (h_bc.symm.trans h_ab.symm))

end GraphMinor.GM22
