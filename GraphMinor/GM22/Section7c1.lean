module

public import GraphMinor.GM22.Section7b
public import GraphMinor.Surface.DiscMatch
public import GraphMinor.GM19.FeatureOrient
import GraphMinor.GM11.CitedResults
import GraphMinor.GM11.PlaneFacts
import GraphMinor.GM14.DiscSlope
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.PlaneOrientation

/-!
# Graph Minors XXII, Section 7 (Part 3a): Claims (1)–(5) of Theorem 7.3

This file formalizes Claims (1)–(5) of the proof of **7.3** (pages 547–548) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM09
  GraphMinor.GM11 GraphMinor.GM14

universe u v u₁ v₁ w

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## Basic Helper Lemmas on Disjointness and Tangle Distance -/

/-- Under `HasTangleMetric Γ ord T d`, for any atom `a ∈ Γ.A`, `d a a = 0`. -/
theorem HasTangleMetric.self_eq_zero {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {a : Set S} (ha : a ∈ Γ.A) :
    d a a = 0 := by
  obtain ⟨-, K, ins, -, -, hdeq⟩ := hM
  rw [hdeq a ha a ha]
  simp [tangleMetric]

/-- If `P ≤ H` for all `P ∈ P_set` (with `P ≤ G` and `H ≤ G`), then `subgraphSUnion G P_set ≤ H`. -/
theorem subgraphSUnion_le_of_forall_le {G H : Graph α β} {P_set : Set (Graph α β)}
    (hP : ∀ P ∈ P_set, P ≤ G) (hH : H ≤ G) (hle : ∀ P ∈ P_set, P ≤ H) :
    subgraphSUnion G P_set ≤ H := by
  rw [(Compatible.of_le_le (subgraphSUnion_le hP) hH).le_iff, vertexSet_subgraphSUnion,
    edgeSet_subgraphSUnion hP]
  exact ⟨iUnion₂_subset fun P h => (hle P h).vertexSet_mono,
    iUnion₂_subset fun P h => (hle P h).edgeSet_mono⟩

/-- If `1 ≤ subsetTangleDist Γ ord d X Y` and `Γ` is a drawing on `S` (so `⋃₀ Γ.A = univ`), then
`Disjoint X Y`. -/
theorem disjoint_of_one_le_subsetTangleDist {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {X Y : Set S}
    (h1 : 1 ≤ subsetTangleDist Γ ord d X Y) :
    Disjoint X Y := by
  rw [disjoint_left]
  intro p hpX hpY
  obtain ⟨z, hzA, hpz⟩ := GM11.exists_atom Γ p
  have hle : subsetTangleDist Γ ord d X Y ≤ d z z :=
    subsetTangleDist_le_of_mem hzA hzA ⟨p, hpz, hpX⟩ ⟨p, hpz, hpY⟩
  rw [HasTangleMetric.self_eq_zero hM hzA] at hle
  omega

/-- If `1 ≤ subsetTangleDist Γ ord d X (Set.univ \ Δ)`, then `X ⊆ Δ`. -/
theorem subset_of_one_le_subsetTangleDist_compl {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {X Δ : Set S}
    (h1 : 1 ≤ subsetTangleDist Γ ord d X (Set.univ \ Δ)) :
    X ⊆ Δ := by
  have hdisj := disjoint_of_one_le_subsetTangleDist hM h1
  intro x hx
  by_contra hxΔ
  exact disjoint_left.mp hdisj hx ⟨mem_univ x, hxΔ⟩

/-- For any `A ∈ 𝒜`, `Set.range (πS A) ⊆ D A` and `(Set.range (πS A)).ncard = πLen A`. -/
theorem SystemJ1ToJ6.range_πS_subset_D_and_ncard {q : ℕ}
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
    Set.range (πS A) ⊆ subBd (D A) ∧ Set.range (πS A) ⊆ D A ∧
      (Set.range (πS A)).ncard = πLen A ∧
      (ιV '' Set.range (πS A)).ncard = πLen A := by
  have hbd : Set.range (πS A) ⊆ subBd (D A) := by
    rw [hJ.π_bar_eq_bd_inter A hA]
    exact inter_subset_left
  have hD_cl : IsClosed (D A) := (hJ.disc_D A hA).1.isClosed
  have hsubD : subBd (D A) ⊆ D A := by
    rw [subBd_eq_frontier]
    exact frontier_subset_iff_isClosed.mpr hD_cl
  have hinj := (hJ.π_valid A hA).2.2.1
  have hncard₁ : (Set.range (πS A)).ncard = πLen A := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hncard₂ : (ιV '' Set.range (πS A)).ncard = πLen A := by
    rw [Set.ncard_image_of_injective _ ιV.injective, hncard₁]
  exact ⟨hbd, hbd.trans hsubD, hncard₁, hncard₂⟩

/-- For any `A ∈ 𝒜`, `ιV '' Set.range (πS A) ⊆ V(A) \ W`. -/
theorem SystemJ1ToJ6.image_range_πS_subset {q : ℕ}
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
    ιV '' Set.range (πS A) ⊆ V(A) \ W := by
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact (hJ.π_valid A hA).2.2.2 j

/-! ## Proof of Claim (1) of 7.3 -/

/-- **Graph Minors XXII, (7.3) Claim (1)** (page 548):
(1) *$L \subseteq \Gamma \cup K_1 \cup A_1 \cup \dots \cup A_t$, and
$\phi(E(H)) \subseteq E(K_1 \cup A_1 \cup \dots \cup A_t)$.* -/
theorem lemma_7_3_claim_1 {q t : ℕ}
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
    (hA_mem : ∀ i : Fin t, A_fam i ∈ ℬ)
    (hdist_other : ∀ A ∈ ℬ \ Set.range A_fam,
      θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let L := graphUnion (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β)
      (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))
    let A_union := subgraphSUnion R_G.G.toGraph (Set.range A_fam)
    L ≤ graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁) A_union ∧
      φE '' E(R_H.G.toGraph) ⊆ E(graphUnion K₁ A_union) := by
  intro 𝒜_far K₁ L A_union
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph :=
    hJ.Γ_le.trans deleteVerts_le
  have hΓK₁_le : graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁ ≤ R_G.G.toGraph :=
    graphUnion_le hΓ_le hK₁_le
  have hA_le : ∀ M ∈ Set.range A_fam, M ≤ R_G.G.toGraph := by
    rintro _ ⟨i, rfl⟩
    exact hJ.le_of_mem_𝒜 (A_fam i) (hAdeq.subset (hA_mem i))
  have hAu_le : A_union ≤ R_G.G.toGraph := subgraphSUnion_le hA_le
  have hRHS_le : graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁) A_union ≤ R_G.G.toGraph :=
    graphUnion_le hΓK₁_le hAu_le
  have hℬ_sub : subgraphSUnion R_G.G.toGraph ℬ ≤ graphUnion K₁ A_union := by
    refine subgraphSUnion_le_of_forall_le
      (fun B hB => hJ.le_of_mem_𝒜 B (hAdeq.subset hB)) (graphUnion_le hK₁_le hAu_le) ?_
    intro B hB
    by_cases hBr : B ∈ Set.range A_fam
    · exact (le_subgraphSUnion hA_le hBr).trans
        (le_graphUnion_right (Compatible.of_le_le hK₁_le hAu_le))
    · have hB_far : B ∈ 𝒜_far := ⟨hAdeq.subset hB, hdist_other B ⟨hB, hBr⟩⟩
      exact (le_subgraphSUnion hfar_le hB_far).trans
        ((le_graphUnion_right (Compatible.of_le_le hK_le (subgraphSUnion_le hfar_le))).trans
          (le_graphUnion_left K₁ A_union))
  have hKℬ_le : graphUnion K (subgraphSUnion R_G.G.toGraph ℬ) ≤ graphUnion K₁ A_union := by
    refine graphUnion_le ?_ hℬ_sub
    exact (le_graphUnion_left K (subgraphSUnion R_G.G.toGraph 𝒜_far)).trans
      (le_graphUnion_left K₁ A_union)
  -- Every branch set `φV v` is a subgraph of `Γ ∪ K₁ ∪ A_union`.
  have hφ_le_Kℬ : ∀ v ∈ V(R_H.G.toGraph),
      φV v ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE)
        (graphUnion K (subgraphSUnion R_G.G.toGraph ℬ)) :=
    fun v hv => hAdeq.φV_le_Γ_union_K' hJ hJ.isModel hv
  have hφ_le_RHS : ∀ v ∈ V(R_H.G.toGraph),
      φV v ≤ graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁) A_union := by
    intro v hv
    rw [(Compatible.of_le_le (hJ.isModel.subgraph_of_mem v hv) hRHS_le).le_iff]
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx1 := (hφ_le_Kℬ v hv).vertexSet_mono hx
      rw [vertexSet_graphUnion, vertexSet_graphUnion] at hx1 ⊢
      rcases hx1 with hxΓ | hxKℬ
      · exact Or.inl (Or.inl hxΓ)
      · have hx2 := hKℬ_le.vertexSet_mono hxKℬ
        rw [vertexSet_graphUnion] at hx2
        rcases hx2 with hxK₁ | hxAu
        · exact Or.inl (Or.inr hxK₁)
        · exact Or.inr hxAu
    · intro e he
      have he1 := (hφ_le_Kℬ v hv).edgeSet_mono he
      rw [edgeSet_graphUnion, edgeSet_graphUnion] at he1 ⊢
      rcases he1 with heΓ | heKℬ
      · exact Or.inl (Or.inl heΓ)
      · have he2 := hKℬ_le.edgeSet_mono heKℬ
        rw [edgeSet_graphUnion] at he2
        rcases he2 with heK₁ | heAu
        · exact Or.inl (Or.inr heK₁)
        · exact Or.inr heAu
  constructor
  · refine graphUnion_le ?_ ?_
    · refine ⟨?_, fun e x y hl => by simp at hl⟩
      rintro x ⟨_, ⟨i, rfl⟩, hx⟩
      have hxAi : x ∈ V(A_fam i) :=
        (hJ.image_range_πS_subset (hAdeq.subset (hA_mem i)) hx).1
      have hxAu : x ∈ V(A_union) :=
        (le_subgraphSUnion hA_le ⟨i, rfl⟩).vertexSet_mono hxAi
      rw [vertexSet_graphUnion]
      exact Or.inr hxAu
    · refine subgraphSUnion_le_of_forall_le ?_ hRHS_le ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact hJ.isModel.subgraph_of_mem v hv
      · rintro _ ⟨v, hv, rfl⟩
        exact hφ_le_RHS v hv
  · rintro _ ⟨e, he, rfl⟩
    have he_mem := hAdeq.φE_mem e he
    have hE_Kℬ : E(K) ∪ ⋃ A ∈ ℬ, E(A) = E(graphUnion K (subgraphSUnion R_G.G.toGraph ℬ)) := by
      rw [edgeSet_graphUnion,
        edgeSet_subgraphSUnion (fun B hB => hJ.le_of_mem_𝒜 B (hAdeq.subset hB))]
    rw [hE_Kℬ] at he_mem
    exact hKℬ_le.edgeSet_mono he_mem

/-! ## Proof of Claim (2) of 7.3 -/

/-- **Graph Minors XXII, (7.3) Claim (2)** (page 548):
(2) *We may assume that $d(V(K_1) \cap \Sigma, \Sigma \setminus \Delta) \ge \theta$.* -/
theorem lemma_7_3_claim_2 {q : ℕ}
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
    (hCleanV : ιV ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A)) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    (∀ v ∈ ιV ⁻¹' V(K₁), θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ)) ∧
      θ ≤ subsetTangleDist Γ ord d (ιV ⁻¹' V(K₁)) (Set.univ \ Δ) ∧
      ιV ⁻¹' V(K₁) ⊆ Δ := by
  intro 𝒜_far K₁
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have h71 := theorem_7_1_proof hJ
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hpt : ∀ v ∈ ιV ⁻¹' V(K₁), θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ) := by
    intro v hvK₁
    have hvG : v ∈ ιV ⁻¹' V(R_G.G.toGraph) := hK₁_le.vertexSet_mono hvK₁
    by_cases hvΓ : v ∈ Γ.V
    · exact h71.1.1 v hvΓ hvK₁
    · have hv_union := hCleanV hvG
      rcases hv_union with hvΓ' | hvπ
      · exact (hvΓ hvΓ').elim
      · obtain ⟨A', hA', hv_πA'⟩ := mem_iUnion₂.mp hvπ
        have hv_not_W : ιV v ∉ W :=
          (hJ.image_range_πS_subset hA' ⟨v, hv_πA', rfl⟩).2
        -- Check why `ιV v ∈ V(K₁)` must come from some `A ∈ 𝒜_far` (or `K`, in which case `A'`
        -- meets `K` off `W`).
        rw [mem_preimage, vertexSet_graphUnion, vertexSet_subgraphSUnion] at hvK₁
        have hex_far : ∃ A ∈ 𝒜_far, ιV v ∈ V(A) := by
          rcases hvK₁ with hvK | hv_far
          · refine ⟨A', ⟨hA', ?_⟩, (hJ.image_range_πS_subset hA' ⟨v, hv_πA', rfl⟩).1⟩
            refine hJ.dist_D_of_inter_K A' hA' ?_
            intro heq
            have hv_inter : ιV v ∈ V(A' ⊓ K) :=
              ⟨(hJ.image_range_πS_subset hA' ⟨v, hv_πA', rfl⟩).1, hvK⟩
            rw [heq, Graph.vertexSet_noEdge] at hv_inter
            exact hv_not_W hv_inter
          · obtain ⟨A, hA, hvA⟩ := mem_iUnion₂.mp hv_far
            exact ⟨A, hA, hvA⟩
        obtain ⟨A, hA_far, hvA⟩ := hex_far
        have hv_πA : v ∈ Set.range (πS A) := by
          by_cases hAA' : A = A'
          · exact hAA' ▸ hv_πA'
          · have hv_inter : ιV v ∈ V(A) ∩ V(A') := ⟨hvA, (hJ.image_range_πS_subset hA' ⟨v, hv_πA', rfl⟩).1⟩
            rw [hJ.vertex_inter_𝒜 A hA_far.1 A' hA' hAA'] at hv_inter
            rcases hv_inter with ⟨⟨x, hx, hxv⟩, _⟩ | hvW
            · exact ιV.injective hxv ▸ hx
            · exact (hv_not_W hvW).elim
        have hv_DA : ({v} : Set S) ⊆ D A :=
          singleton_subset_iff.mpr ((hJ.range_πS_subset_D_and_ncard hA_far.1).2.1 hv_πA)
        exact hA_far.2.trans (subsetTangleDist_anti
          (fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb) hv_DA Subset.rfl)
  have hset : θ ≤ subsetTangleDist Γ ord d (ιV ⁻¹' V(K₁)) (Set.univ \ Δ) := by
    classical
    unfold subsetTangleDist
    split_ifs with hex
    · have hne : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ (ιV ⁻¹' V(K₁))).Nonempty ∧
          (b ∩ (Set.univ \ Δ)).Nonempty ∧ d a b = k}.Nonempty := by
        rcases hex with ⟨a, ha, b, hb, haX, hbY⟩
        exact ⟨d a b, a, ha, b, hb, haX, hbY, rfl⟩
      rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, ⟨v, hva, hvK₁⟩, hbY, hdab⟩
      rw [← hdab]
      exact (hpt v hvK₁).trans (subsetTangleDist_le_of_mem ha hb ⟨v, hva, rfl⟩ hbY)
    · exact hJ.θ_le_ord
  have hsubΔ : ιV ⁻¹' V(K₁) ⊆ Δ := by
    have h4 := hJ.four_le_θ
    exact subset_of_one_le_subsetTangleDist_compl hJ.hasMetric (by omega)
  exact ⟨hpt, hset, hsubΔ⟩

/-! ## Proof of Claim (3) of 7.3 -/

/-- **Graph Minors XXII, (7.3) Claim (3)** (page 548):
(3) *For $1 \le i \le t$, $F_i \cap V(\Gamma) = \bar{\pi}(A_i')$.* -/
theorem lemma_7_3_claim_3 {q t : ℕ}
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
    {A_fam' : Fin t → Graph α β}
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    (i : Fin t) :
    subBd (D (A_fam' i)) ∩ Γ.V = Set.range (πS (A_fam' i)) := by
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hAi' := hA'_mem i
  let F_i := subBd (D (A_fam' i))
  have hdisc := hJ.disc_D (A_fam' i) hAi'
  have hOArc : IsOArc F_i := by
    change IsOArc (subBd (D (A_fam' i)))
    rw [IsClosedDisc.subBd_eq_discBd hS hdisc.1]
    exact hdisc.1.isOArc_discBd
  have hsub : F_i ∩ Γ.V ⊆ Set.range (πS (A_fam' i)) := by
    rw [hJ.π_bar_eq_bd_inter (A_fam' i) hAi']
    refine inter_subset_inter_right F_i ?_
    intro x hxΓ
    exact (hJ.Γ_le.trans deleteVerts_le).vertexSet_mono ⟨x, hxΓ, rfl⟩
  have hfin : (Set.range (πS (A_fam' i))).Finite := Set.finite_range _
  have hge : (Set.range (πS (A_fam' i))).ncard ≤ (F_i ∩ Γ.V).ncard := by
    by_contra hlt
    push Not at hlt
    exact h_v i ⟨F_i, hOArc, hdisc.2.1, hlt, hdisc.2.2.subset⟩
  exact Set.eq_of_subset_of_ncard_le hsub hge hfin

/-! ## Proof of Claim (4) and Claim (5) of 7.3 -/

omit [T2Space S] in
/-- Every closed disc `D_set` in a closed surface `S` contains a closed disc `D_in` in its interior
`D_set \ subBd D_set`. -/
theorem exists_inner_disc_of_isClosedDisc (hS : IsClosedSurface S) {D_set : Set S}
    (hD : IsClosedDisc D_set) :
    ∃ D_in : Set S, IsClosedDisc D_in ∧ D_in ⊆ D_set \ subBd D_set := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hsub_ball : closedBall (0 : ℂ) (1 / 2) ⊆ closedBall 0 1 :=
    closedBall_subset_closedBall (by norm_num)
  have hdisc_half : IsClosedDisc (closedBall (0 : ℂ) (1 / 2)) :=
    (isClosedDisc_of_convex (convex_closedBall 0 (1 / 2))
      (by rw [interior_closedBall _ (by norm_num)]; exact ⟨0, by simp⟩)
      isBounded_closedBall isClosed_closedBall).1
  have hD_in : IsClosedDisc (g '' closedBall 0 (1 / 2)) := (c.disc_g hsub_ball hdisc_half).1
  refine ⟨g '' closedBall 0 (1 / 2), hD_in, ?_⟩
  rw [IsClosedDisc.subBd_eq_discBd hS hD, ← c.g_sphere, ← c.g_closedBall,
    ← c.g_sdiff Subset.rfl sphere_subset_closedBall]
  refine image_mono ?_
  intro z hz
  rw [mem_sdiff, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
  have hz' : ‖z‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hz
  exact ⟨by linarith, by linarith⟩

/-- A homeomorphism `e : S ≃ₜ S` of a connected closed surface that fixes a closed disc `Q`
pointwise preserves every surface orientation `ω`. -/
theorem preserved_of_fix_closedDisc [ConnectedSpace S] (hS : IsClosedSurface S)
    (ω : GM19.SurfaceOrientation S) (e : S ≃ₜ S) {Q : Set S}
    (hQ : IsClosedDisc Q) (hfix : ∀ z ∈ Q, e z = z) :
    ω.IsPreservedBy e := by
  have hSurf : IsSurface S := hS.isSurface
  rcases GM19.homeo_orientation hSurf e with h | h
  · exact h ω
  · exfalso
    obtain ⟨ψ⟩ := hQ.isOArc_discBd
    let p : Circle → S := fun w => (ψ w).1
    have hp_mem : ∀ w, p w ∈ discBd Q := fun w => (ψ w).2
    have hp_inj : Function.Injective p := fun a b hab => ψ.injective (Subtype.ext hab)
    have hpi := Real.pi_gt_three
    have h1 : Circle.exp 0 ≠ Circle.exp 1 :=
      Surface.circle_exp_ne (by norm_num) (by rw [abs_lt]; constructor <;> linarith)
    have h2 : Circle.exp 1 ≠ Circle.exp 2 :=
      Surface.circle_exp_ne (by norm_num) (by rw [abs_lt]; constructor <;> linarith)
    have h3 : Circle.exp 0 ≠ Circle.exp 2 :=
      Surface.circle_exp_ne (by norm_num) (by rw [abs_lt]; constructor <;> linarith)
    let a := p (Circle.exp 0)
    let b := p (Circle.exp 1)
    let c := p (Circle.exp 2)
    have ha : a ∈ discBd Q := hp_mem _
    have hb : b ∈ discBd Q := hp_mem _
    have hc : c ∈ discBd Q := hp_mem _
    have hab : a ≠ b := fun heq => h1 (hp_inj heq)
    have hbc : b ≠ c := fun heq => h2 (hp_inj heq)
    have hac : a ≠ c := fun heq => h3 (hp_inj heq)
    have himg : e '' Q = Q := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hfix z hz]
        exact hz
      · intro hx
        exact ⟨x, hx, hfix x hx⟩
    have hrev := h ω Q hQ a b c ha hb hc hab hbc hac
    rw [himg, hfix a (Surface.discBd_subset Q ha), hfix b (Surface.discBd_subset Q hb),
      hfix c (Surface.discBd_subset Q hc)] at hrev
    exact iff_not_self hrev

/-- **Graph Minors XXII, (7.3) Claim (4)** (page 548):
(4) *There is a homeomorphism $\beta : \Sigma \to \Sigma$ fixing $\Delta$ pointwise and mapping
$D_i$ to $D(A_i')$ for $1 \le i \le t$.* -/
theorem lemma_7_3_claim_4 {q t : ℕ}
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
    (hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜)
    (hA_inj : Function.Injective A_fam)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ)
    (h_iii : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ)
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    {D_in : Fin t → Set S}
    (hD_in : ∀ i : Fin t, IsClosedDisc (D_in i) ∧ D_in i ⊆ D (A_fam i) \ subBd (D (A_fam i))) :
    ∃ β : S ≃ₜ S,
      (∀ z ∈ Δ, β z = z) ∧
      (∀ i : Fin t, β '' D_in i = D (A_fam' i)) ∧
      orient.IsPreservedBy β := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hD_in_disj : Pairwise (fun i j : Fin t => Disjoint (D_in i) (D_in j)) := by
    intro i j hij
    rw [disjoint_left]
    intro x hxi hxj
    have hx1 := (hD_in i).2 hxi
    have hx2 := (hD_in j).2 hxj
    have hcap : x ∈ D (A_fam i) ∩ D (A_fam j) := ⟨hx1.1, hx2.1⟩
    rw [hJ.D_inter_eq (A_fam i) (hA_mem i) (A_fam j) (hA_mem j) (hA_inj.ne hij)] at hcap
    exact hx1.2 ((hJ.range_πS_subset_D_and_ncard (hA_mem i)).1 hcap.1)
  have hDA'_disj : Pairwise (fun i j : Fin t => Disjoint (D (A_fam' i)) (D (A_fam' j))) := by
    intro i j hij
    have h4 := hJ.four_le_θ
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd := h_iv i j hlt
      exact disjoint_of_one_le_subsetTangleDist hJ.hasMetric (by omega)
    · have hd := h_iv j i hgt
      exact (disjoint_of_one_le_subsetTangleDist hJ.hasMetric (by omega)).symm
  let Q : Unit → Set S := fun _ => Δ
  have hQ : ∀ k : Unit, IsClosedDisc (Q k) := fun _ => hJ.disc_Δ.1
  have hQQ : Pairwise (fun i j : Unit => Disjoint (Q i) (Q j)) := fun _ _ h => (h rfl).elim
  have hAQ : ∀ (i : Fin t) (k : Unit), Disjoint (D_in i) (Q k) :=
    fun i _ => (h_ii i).mono_left ((hD_in i).2.trans sdiff_subset)
  have hA'Q : ∀ (i : Fin t) (k : Unit), Disjoint (D (A_fam' i)) (Q k) :=
    fun i _ => h_iii i
  obtain ⟨β, hβ_img, hβ_fix⟩ := exists_disc_family_match hS Q hQ hQQ D_in
    (fun i => D (A_fam' i)) (fun i => (hD_in i).1)
    (fun i => (hJ.disc_D (A_fam' i) (hA'_mem i)).1)
    hD_in_disj hDA'_disj hAQ hA'Q
  have hfixΔ : ∀ z ∈ Δ, β z = z := hβ_fix ()
  have hpres : orient.IsPreservedBy β :=
    preserved_of_fix_closedDisc hS orient β hJ.disc_Δ.1 hfixΔ
  exact ⟨β, hfixΔ, hβ_img, hpres⟩

/-- **Graph Minors XXII, (7.3) Claim (5)** (page 548):
(5) *For $1 \le i \le t$, $|\bar{\pi}_i| = |\bar{\pi}(A_i)| = |\bar{\pi}(A_i')|$.* -/
theorem lemma_7_3_claim_5 {q t : ℕ}
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
    (hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    {D_in : Fin t → Set S}
    (_hD_in : ∀ i : Fin t, IsClosedDisc (D_in i))
    {β : S ≃ₜ S}
    (hβ_img : ∀ i : Fin t, β '' D_in i = D (A_fam' i))
    (i : Fin t) :
    let π_in : Fin (πLen (A_fam' i)) → S := fun j => β.symm (πS (A_fam' i) j)
    Set.range π_in ⊆ subBd (D_in i) ∧
      Function.Injective π_in ∧
      (Set.range π_in).ncard = (Set.range (πS (A_fam i))).ncard ∧
      (Set.range (πS (A_fam i))).ncard = (Set.range (πS (A_fam' i))).ncard ∧
      (Set.range (πS (A_fam' i))).ncard = πLen (A_fam i) := by
  intro π_in
  have hAi := hA_mem i
  have hAi' := hA'_mem i
  have hlen_i := hlen i
  have hinj_Ai' : Function.Injective (πS (A_fam' i)) := (hJ.π_valid (A_fam' i) hAi').2.2.1
  have hinj_in : Function.Injective π_in := β.symm.injective.comp hinj_Ai'
  have hbd_in : Set.range π_in ⊆ subBd (D_in i) := by
    rintro _ ⟨j, rfl⟩
    have hj_bd : πS (A_fam' i) j ∈ subBd (D (A_fam' i)) :=
      (hJ.range_πS_subset_D_and_ncard hAi').1 ⟨j, rfl⟩
    have hD_eq : D_in i = β.symm '' D (A_fam' i) := by
      rw [← hβ_img i, ← image_comp, Homeomorph.symm_comp_self, image_id]
    rw [hD_eq, subBd_eq_frontier, ← Homeomorph.image_frontier β.symm, ← subBd_eq_frontier]
    exact mem_image_of_mem β.symm hj_bd
  have hc_in : (Set.range π_in).ncard = πLen (A_fam' i) := by
    rw [Set.ncard_range_of_injective hinj_in, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hc_Ai : (Set.range (πS (A_fam i))).ncard = πLen (A_fam i) :=
    (hJ.range_πS_subset_D_and_ncard hAi).2.2.1
  have hc_Ai' : (Set.range (πS (A_fam' i))).ncard = πLen (A_fam' i) :=
    (hJ.range_πS_subset_D_and_ncard hAi').2.2.1
  refine ⟨hbd_in, hinj_in, ?_, ?_, ?_⟩ <;> omega

end GraphMinor.GM22
