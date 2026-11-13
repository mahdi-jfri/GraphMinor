module

public import GraphMinor.GM22.Section7c4
import GraphMinor.GM22.ParallelProofs

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 7 (Part 3e): Claim (13) and Proof of Theorem 7.3

This file formalizes Claim (13) (`lemma_7_3_claim_13`, page 552) and completes the proof of
**7.3** (`theorem_7_3`, pages 547–552) of N. Robertson and P. D. Seymour,
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

/-! ## Monotonicity of `SystemJ1ToJ6` in `θ` -/

/-- `SystemJ1ToJ6` is downward monotone in `θ` as long as `4 ≤ θ'`. -/
theorem SystemJ1ToJ6.mono_θ {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ θ' ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (h4 : 4 ≤ θ') (hle : θ' ≤ θ) :
    SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ' ord T ins d D N K Δ v_star δ R_H φV φE :=
  { hJ with
    four_le_θ := h4
    θ_le_ord := hle.trans hJ.θ_le_ord
    dist_Γ_inter_K := fun v hv hvK => hle.trans (hJ.dist_Γ_inter_K v hv hvK)
    dist_D_of_inter_K := fun A hA hne => hle.trans (hJ.dist_D_of_inter_K A hA hne) }

/-! ## Claim (13) of Theorem 7.3 (page 552) -/

/-- **Graph Minors XXII, (7.3) Claim (13)** (page 552):
Let $\mathcal{A}' = \{A \in \mathcal{A} \colon d(v^*, D(A)) \ge \theta'\}$.
(13) *$\mathcal{A}'$ is adequate for $\phi'$.* -/
theorem lemma_7_3_claim_13 {q t : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ θ' ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hθ_eq : θ = θ' + 3)
    {A_fam' : Fin t → Graph α β}
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (h_iii_dist : ∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i)))
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    {Z₀ : Set α}
    (hZ₀_K₁ : Z₀ ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    {φ'V : αH → Graph α β} {φ'E : βH → β}
    (hφ'V_le : ∀ v ∈ V(R_H.G.toGraph), φ'V v ≤
      graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE)
        (graphUnion K (subgraphSUnion R_G.G.toGraph
          {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
        (subgraphSUnion R_G.G.toGraph (Set.range A_fam')))
    (hφ'E_sub : φ'E '' E(R_H.G.toGraph) ⊆
      ((φE '' E(R_H.G.toGraph)) ∩ E(graphUnion K (subgraphSUnion R_G.G.toGraph
        {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}))) ∪
      ⋃ i : Fin t, E(A_fam' i))
    (hφ'V_meets : ∀ v ∈ V(R_H.G.toGraph),
      (V(φ'V v) ∩ (Z₀ ∪ ⋃ i : Fin t, V(A_fam' i))).Nonempty) :
    let 𝒜' := {A ∈ 𝒜 | θ' ≤ subsetTangleDist Γ ord d {v_star} (D A)}
    IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φ'V φ'E := by
  intro 𝒜'
  let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
  let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
  have h71 := theorem_7_1_proof hJ
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph := hJ.Γ_le.trans deleteVerts_le
  have hNW_le : Graph.noEdge W β ≤ R_G.G.toGraph := by
    rw [Graph.noEdge_le_iff]
    exact hJ.sep_NK.2.trans (inter_subset_left.trans hJ.sep_NK.1.1.vertexSet_mono)
  have hA'_range_le : ∀ M ∈ Set.range A_fam', M ≤ R_G.G.toGraph := by
    rintro _ ⟨i, rfl⟩
    exact hJ.le_of_mem_𝒜 (A_fam' i) (hA'_mem i)
  have hA'_mem_𝒜' : ∀ i : Fin t, A_fam' i ∈ 𝒜' :=
    fun i => ⟨hA'_mem i, (by omega : θ' ≤ θ).trans (h_iii_dist i)⟩
  have hfar_sub_𝒜' : 𝒜_far ⊆ 𝒜' := by
    rintro A ⟨hA, hdist⟩
    refine ⟨hA, ?_⟩
    have hv_sub : ({v_star} : Set S) ⊆ Set.univ \ Δ :=
      singleton_subset_iff.mpr ⟨mem_univ v_star, hJ.v_star_mem.2⟩
    have hle : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) ≤
        subsetTangleDist Γ ord d {v_star} (D A) := by
      rw [subsetTangleDist_comm hJ.hasMetric {v_star} (D A)]
      exact subsetTangleDist_anti
        (fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb) Subset.rfl hv_sub
    omega
  refine ⟨fun _ h => h.1, ?_, ?_, ?_, ?_⟩
  · -- Condition (i): if `A ∈ 𝒜 \ 𝒜'`, then `A ⊓ φ'V v ≤ Γ ∪ N_W`.
    intro v hv A hA hnot_le
    by_contra hA_not_𝒜'
    apply hnot_le
    have hdist_lt : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ - 3 := by
      have hnot_θ' : ¬ (θ' ≤ subsetTangleDist Γ ord d {v_star} (D A)) :=
        fun h => hA_not_𝒜' ⟨hA, h⟩
      have hv_sub : ({v_star} : Set S) ⊆ Set.univ \ Δ :=
        singleton_subset_iff.mpr ⟨mem_univ v_star, hJ.v_star_mem.2⟩
      have hle : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) ≤
          subsetTangleDist Γ ord d {v_star} (D A) := by
        rw [subsetTangleDist_comm hJ.hasMetric {v_star} (D A)]
        exact subsetTangleDist_anti
          (fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb) Subset.rfl hv_sub
      omega
    have hA_le_G : A ≤ R_G.G.toGraph := hJ.le_of_mem_𝒜 A hA
    have hA_K₁ : A ⊓ K₁ = Graph.noEdge W β := h71.2.2 A hA hdist_lt
    have hA_V_K₁ : V(A) ∩ V(K₁) = W := by
      have := congrArg Graph.vertexSet hA_K₁
      simpa using this
    have hA_E_K₁ : E(A) ∩ E(K₁) = ∅ := by
      rw [← (Compatible.of_le_le hA_le_G hK₁_le).edgeSet_inf, hA_K₁, Graph.edgeSet_noEdge]
    have hA_ne_A' : ∀ i : Fin t, A ≠ A_fam' i := by
      intro i hEq
      exact hA_not_𝒜' (hEq ▸ hA'_mem_𝒜' i)
    have hΓNW_le_G : graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β) ≤ R_G.G.toGraph :=
      graphUnion_le hΓ_le hNW_le
    rw [(Compatible.of_le_le (inf_le_left.trans hA_le_G) hΓNW_le_G).le_iff]
    have hφ_le := hφ'V_le v hv
    constructor
    · rintro x ⟨hxA, hxφ⟩
      have hx_un : x ∈ V(graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁)
          (subgraphSUnion R_G.G.toGraph (Set.range A_fam'))) :=
        hφ_le.vertexSet_mono hxφ
      rw [vertexSet_graphUnion, vertexSet_graphUnion, vertexSet_subgraphSUnion] at hx_un
      rw [vertexSet_graphUnion, Graph.vertexSet_noEdge]
      rcases hx_un with (hxΓ | hxK₁) | hxA'_un
      · exact Or.inl hxΓ
      · have hxW : x ∈ W := by
          rw [← hA_V_K₁]
          exact ⟨hxA, hxK₁⟩
        exact Or.inr hxW
      · obtain ⟨_, ⟨i, rfl⟩, hxA'⟩ := mem_iUnion₂.mp hxA'_un
        have hx_inter : x ∈ V(A) ∩ V(A_fam' i) := ⟨hxA, hxA'⟩
        rw [hJ.vertex_inter_𝒜 A hA (A_fam' i) (hA'_mem i) (hA_ne_A' i)] at hx_inter
        rcases hx_inter with ⟨_, hx_π'⟩ | hxW
        · left
          have h3 := lemma_7_3_claim_3 hJ hA'_mem h_v i
          rw [← h3] at hx_π'
          rcases hx_π' with ⟨p, hp, rfl⟩
          exact ⟨p, hp.2, rfl⟩
        · exact Or.inr hxW
    · rintro e he
      have heA : e ∈ E(A) := (inf_le_left (b := φ'V v)).edgeSet_mono he
      have heφ : e ∈ E(φ'V v) := (inf_le_right (a := A)).edgeSet_mono he
      have he_un := hφ_le.edgeSet_mono heφ
      rw [edgeSet_graphUnion, edgeSet_graphUnion, edgeSet_subgraphSUnion hA'_range_le] at he_un
      rw [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
      rcases he_un with (heΓ | heK₁) | heA'
      · exact heΓ
      · exfalso
        have : e ∈ E(A) ∩ E(K₁) := ⟨heA, heK₁⟩
        rw [hA_E_K₁] at this
        exact this
      · exfalso
        obtain ⟨_, ⟨i, rfl⟩, heA'i⟩ := mem_iUnion₂.mp heA'
        exact disjoint_left.mp (hJ.edge_disjoint_𝒜 A hA (A_fam' i) (hA'_mem i) (hA_ne_A' i))
          heA heA'i
  · -- Condition (ii): `(V(φ'V v) ∩ (V(K) ∪ ⋃ A ∈ 𝒜', V(A))).Nonempty`
    intro v hv
    obtain ⟨x, hxφ, hx_un⟩ := hφ'V_meets v hv
    refine ⟨x, hxφ, ?_⟩
    rcases hx_un with hxZ₀ | hxA'
    · have hxK₁ := hZ₀_K₁ hxZ₀
      rw [vertexSet_graphUnion, vertexSet_subgraphSUnion] at hxK₁
      rcases hxK₁ with hxK | hx_far
      · exact Or.inl hxK
      · obtain ⟨A, hA_far, hxA⟩ := mem_iUnion₂.mp hx_far
        exact Or.inr (mem_iUnion₂.mpr ⟨A, hfar_sub_𝒜' hA_far, hxA⟩)
    · obtain ⟨i, hxA'i⟩ := mem_iUnion.mp hxA'
      exact Or.inr (mem_iUnion₂.mpr ⟨A_fam' i, hA'_mem_𝒜' i, hxA'i⟩)
  · -- Condition (iii): `φ'E e ∈ E(K) ∪ ⋃ A ∈ 𝒜', E(A)`
    intro e he
    have he_mem := hφ'E_sub ⟨e, he, rfl⟩
    rcases he_mem with ⟨_, heK₁⟩ | heA'
    · rw [edgeSet_graphUnion, edgeSet_subgraphSUnion hfar_le] at heK₁
      rcases heK₁ with heK | he_far
      · exact Or.inl heK
      · obtain ⟨A, hA_far, heA⟩ := mem_iUnion₂.mp he_far
        exact Or.inr (mem_iUnion₂.mpr ⟨A, hfar_sub_𝒜' hA_far, heA⟩)
    · obtain ⟨i, heA'i⟩ := mem_iUnion.mp heA'
      exact Or.inr (mem_iUnion₂.mpr ⟨A_fam' i, hA'_mem_𝒜' i, heA'i⟩)
  · -- Condition (iv): if `A ∈ 𝒜` and `A ⊓ K ≠ N_W`, then `A ∈ 𝒜'`.
    intro A hA hne
    exact hfar_sub_𝒜' ⟨hA, hJ.dist_D_of_inter_K A hA hne⟩

/-! ## Clean Embedding and Injective Subfamily Reductions for Theorem 7.3 -/

/-- Hilbert's hotel lemma: in an infinite type `X`, given finite disjoint sets `S₀, F ⊆ X`, there is
an embedding `f : X ↪ X` that fixes `S₀` pointwise and avoids `F`. -/
theorem exists_embedding_avoid_finite {X : Type*} [Infinite X] {S₀ F : Set X}
    (hS₀ : S₀.Finite) (hF : F.Finite) (hDisj : Disjoint S₀ F) :
    ∃ f : X ↪ X, (∀ x ∈ S₀, f x = x) ∧ ∀ x : X, f x ∉ F := by
  classical
  let U : Set X := Set.univ \ (S₀ ∪ F)
  have hCompl_inf : U.Infinite :=
    Set.infinite_univ.sdiff (hS₀.union hF)
  let e_nat : ℕ ↪ U := hCompl_inf.natEmbedding
  have : Finite F := hF.to_subtype
  let e_F : F ≃ Fin (Nat.card F) := Finite.equivFin F
  let g : X → X := fun x =>
    if hxF : x ∈ F then
      (e_nat (2 * (e_F ⟨x, hxF⟩).1)).1
    else if hxN : ∃ n : ℕ, (e_nat n).1 = x then
      (e_nat (2 * Classical.choose hxN + 1)).1
    else
      x
  have he_nat_not_S₀ : ∀ n : ℕ, (e_nat n).1 ∉ S₀ :=
    fun n h => (e_nat n).2.2 (Or.inl h)
  have he_nat_not_F : ∀ n : ℕ, (e_nat n).1 ∉ F :=
    fun n h => (e_nat n).2.2 (Or.inr h)
  have he_nat_inj : ∀ m n : ℕ, (e_nat m).1 = (e_nat n).1 → m = n :=
    fun m n h => e_nat.injective (Subtype.ext h)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    dsimp only [g] at hxy
    by_cases hxF : x ∈ F <;> by_cases hyF : y ∈ F
    · simp only [hxF, hyF, ↓reduceDIte] at hxy
      have h2 := he_nat_inj _ _ hxy
      have hFin : e_F ⟨x, hxF⟩ = e_F ⟨y, hyF⟩ := Fin.ext (by omega)
      exact congrArg Subtype.val (e_F.injective hFin)
    · simp only [hxF, hyF, ↓reduceDIte] at hxy
      by_cases hyN : ∃ n : ℕ, (e_nat n).1 = y
      · simp only [hyN, ↓reduceDIte] at hxy
        have h2 := he_nat_inj _ _ hxy
        omega
      · simp only [hyN, ↓reduceDIte] at hxy
        exact (hyN ⟨2 * (e_F ⟨x, hxF⟩).1, hxy⟩).elim
    · simp only [hxF, hyF, ↓reduceDIte] at hxy
      by_cases hxN : ∃ n : ℕ, (e_nat n).1 = x
      · simp only [hxN, ↓reduceDIte] at hxy
        have h2 := he_nat_inj _ _ hxy
        omega
      · simp only [hxN, ↓reduceDIte] at hxy
        exact (hxN ⟨2 * (e_F ⟨y, hyF⟩).1, hxy.symm⟩).elim
    · simp only [hxF, hyF, ↓reduceDIte] at hxy
      by_cases hxN : ∃ n : ℕ, (e_nat n).1 = x <;> by_cases hyN : ∃ n : ℕ, (e_nat n).1 = y
      · simp only [hxN, hyN, ↓reduceDIte] at hxy
        have h2 := he_nat_inj _ _ hxy
        have hn : Classical.choose hxN = Classical.choose hyN := by omega
        rw [← Classical.choose_spec hxN, ← Classical.choose_spec hyN, hn]
      · simp only [hxN, hyN, ↓reduceDIte] at hxy
        exact (hyN ⟨2 * Classical.choose hxN + 1, hxy⟩).elim
      · simp only [hxN, hyN, ↓reduceDIte] at hxy
        exact (hxN ⟨2 * Classical.choose hyN + 1, hxy.symm⟩).elim
      · simpa only [hxN, hyN, ↓reduceDIte] using hxy
  refine ⟨⟨g, hg_inj⟩, ?_, ?_⟩
  · intro x hxS₀
    have hxF : x ∉ F := disjoint_left.mp hDisj hxS₀
    have hxN : ¬ ∃ n : ℕ, (e_nat n).1 = x := by
      rintro ⟨n, rfl⟩
      exact he_nat_not_S₀ n hxS₀
    change g x = x
    dsimp only [g]
    simp only [hxF, hxN, ↓reduceDIte]
  · intro x
    change g x ∉ F
    dsimp only [g]
    split_ifs with hxF hxN
    · exact he_nat_not_F _
    · exact he_nat_not_F _
    · exact hxF

omit [T2Space S] in
/-- Any space `S` containing a closed disc `Δ` is infinite (`Infinite S`). -/
theorem infinite_of_isClosedDisc {Δ : Set S} (hΔ : IsClosedDisc Δ) : Infinite S := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  let f : ℕ → ℂ := fun n => (1 : ℂ) / (n + 2 : ℂ)
  have hf_mem : ∀ n : ℕ, f n ∈ closedBall (0 : ℂ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff]
    have hge : (1 : ℝ) ≤ ‖(n : ℂ) + 2‖ := by
      have : (n : ℂ) + 2 = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ n + 2)
    simpa [f] using inv_le_one_of_one_le₀ hge
  refine Infinite.of_injective (fun n : ℕ => g (f n)) (fun m n hmn => ?_)
  have hfm : h (g (f m)) = f m := c.hg (hf_mem m)
  have hfn : h (g (f n)) = f n := c.hg (hf_mem n)
  have heq : f m = f n := hfm.symm.trans ((congrArg h hmn).trans hfn)
  have hm_ne : (m : ℂ) + 2 ≠ 0 := by
    have : (m : ℂ) + 2 = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hn_ne : (n : ℂ) + 2 ≠ 0 := by
    have : (n : ℂ) + 2 = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact Nat.cast_ne_zero.mpr (by omega)
  have heq2 : (m : ℂ) + 2 = (n : ℂ) + 2 := by
    simpa [f] using (div_eq_div_iff hm_ne hn_ne).mp heq |>.symm
  have heq3 : ((m + 2 : ℕ) : ℂ) = ((n + 2 : ℕ) : ℂ) := by
    calc ((m + 2 : ℕ) : ℂ) = (m : ℂ) + 2 := by push_cast; ring
    _ = (n : ℂ) + 2 := heq2
    _ = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  have := Nat.cast_injective heq3
  omega

omit [T2Space S] in
/-- When `ιV' : S ↪ α` agrees with `ιV` on `Γ₀.V` and `ιE' : Set S ↪ β` agrees with `ιE` on
`Γ₀.E`, the embedded graphs `Γ₀.toEmbeddedGraph ιV' ιE'` and `Γ₀.toEmbeddedGraph ιV ιE` are
equal. -/
theorem toEmbeddedGraph_congr {Γ₀ : Drawing S} {ιV ιV' : S ↪ α} {ιE ιE' : Set S ↪ β}
    (hV : ∀ x ∈ Γ₀.V, ιV' x = ιV x) (hE : ∀ e ∈ Γ₀.E, ιE' e = ιE e) :
    Γ₀.toEmbeddedGraph ιV' ιE' = Γ₀.toEmbeddedGraph ιV ιE := by
  ext x y e
  · constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, (hV p hp).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, hV p hp⟩
  · constructor
    · rintro ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
      exact ⟨e₀, x₀, y₀, hl, (hE e₀ hl.edge_mem).symm,
        (hV x₀ hl.left_mem).symm, (hV y₀ hl.right_mem).symm⟩
    · rintro ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
      exact ⟨e₀, x₀, y₀, hl, hE e₀ hl.edge_mem,
        hV x₀ hl.left_mem, hV y₀ hl.right_mem⟩

/-- Clean embedding reduction for `(J1)`–`(J6)`: we can replace `ιV` and `ιE` by `ιV'` and `ιE'`
that agree with `ιV` on `Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A)` and with `ιE` on `Γ.E`, such that
`ιV' ⁻¹' V(G) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A)` and `ιE' ⁻¹' E(G) ⊆ Γ.E`. -/
theorem SystemJ1ToJ6.exists_clean_embeddings {q : ℕ}
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
    ∃ (ιV' : S ↪ α) (ιE' : Set S ↪ β),
      (∀ x ∈ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A), ιV' x = ιV x) ∧
      (∀ e ∈ Γ.E, ιE' e = ιE e) ∧
      ιV' ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ (⋃ A ∈ 𝒜, Set.range (πS A)) ∧
      ιE' ⁻¹' E(R_G.G.toGraph) ⊆ Γ.E ∧
      SystemJ1ToJ6 ιV' ιE' R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE := by
  have : Infinite S := infinite_of_isClosedDisc hJ.disc_Δ.1
  have : Infinite (Set S) :=
    Infinite.of_injective (fun x : S => ({x} : Set S)) (fun x y h => singleton_injective h)
  let S₀ : Set S := Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A)
  have hVG_pre_fin : (ιV ⁻¹' V(R_G.G.toGraph)).Finite :=
    hJ.finite_V.preimage ιV.injective.injOn
  have hEG_pre_fin : (ιE ⁻¹' E(R_G.G.toGraph)).Finite :=
    hJ.finite_E.preimage ιE.injective.injOn
  have hS₀_sub : S₀ ⊆ ιV ⁻¹' V(R_G.G.toGraph) := by
    rintro x (hxΓ | hxπ)
    · exact (hJ.Γ_le.trans deleteVerts_le).vertexSet_mono ⟨x, hxΓ, rfl⟩
    · obtain ⟨A, hA, i, rfl⟩ := mem_iUnion₂.mp hxπ
      exact (hJ.le_of_mem_𝒜 A hA).vertexSet_mono ((hJ.π_valid A hA).2.2.2 i).1
  have hS₀_fin : S₀.Finite := hVG_pre_fin.subset hS₀_sub
  have hFV_fin : ((ιV ⁻¹' V(R_G.G.toGraph)) \ S₀).Finite := hVG_pre_fin.sdiff
  obtain ⟨fV, hfV_id, hfV_avoid⟩ :=
    exists_embedding_avoid_finite hS₀_fin hFV_fin disjoint_sdiff_self_right
  have hΓE_sub : Γ.E ⊆ ιE ⁻¹' E(R_G.G.toGraph) :=
    fun e he => (hJ.Γ_le.trans deleteVerts_le).edgeSet_mono ⟨e, he, rfl⟩
  have hΓE_fin : Γ.E.Finite := hEG_pre_fin.subset hΓE_sub
  have hFE_fin : ((ιE ⁻¹' E(R_G.G.toGraph)) \ Γ.E).Finite := hEG_pre_fin.sdiff
  obtain ⟨fE, hfE_id, hfE_avoid⟩ :=
    exists_embedding_avoid_finite hΓE_fin hFE_fin disjoint_sdiff_self_right
  let ιV' : S ↪ α := fV.trans ιV
  let ιE' : Set S ↪ β := fE.trans ιE
  have hιV'_eq : ∀ x ∈ S₀, ιV' x = ιV x :=
    fun x hx => congrArg ιV (hfV_id x hx)
  have hιE'_eq : ∀ e ∈ Γ.E, ιE' e = ιE e :=
    fun e he => congrArg ιE (hfE_id e he)
  have hCleanV' : ιV' ⁻¹' V(R_G.G.toGraph) ⊆ S₀ := by
    intro x hx
    by_contra hxS₀
    have hfx_S₀ : fV x ∉ S₀ := by
      intro hmem
      have hfx_eq := hfV_id (fV x) hmem
      exact hxS₀ (fV.injective hfx_eq ▸ hmem)
    exact hfV_avoid x ⟨hx, hfx_S₀⟩
  have hCleanE' : ιE' ⁻¹' E(R_G.G.toGraph) ⊆ Γ.E := by
    intro e he
    by_contra heΓ
    have hfe_Γ : fE e ∉ Γ.E := by
      intro hmem
      have hfe_eq := hfE_id (fE e) hmem
      exact heΓ (fE.injective hfe_eq ▸ hmem)
    exact hfE_avoid e ⟨he, hfe_Γ⟩
  have hΓ_emb_eq : Γ.toEmbeddedGraph ιV' ιE' = Γ.toEmbeddedGraph ιV ιE :=
    toEmbeddedGraph_congr (fun x hx => hιV'_eq x (Or.inl hx)) hιE'_eq
  have hπ_img_eq : ∀ A ∈ 𝒜, ιV' '' Set.range (πS A) = ιV '' Set.range (πS A) := by
    intro A hA
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hιV'_eq x (Or.inr (mem_iUnion₂.mpr ⟨A, hA, hx⟩))).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hιV'_eq x (Or.inr (mem_iUnion₂.mpr ⟨A, hA, hx⟩))⟩
  refine ⟨ιV', ιE', hιV'_eq, hιE'_eq, hCleanV', hCleanE',
    { hJ with
      π_valid := fun A hA => by
        refine ⟨(hJ.π_valid A hA).1, (hJ.π_valid A hA).2.1, (hJ.π_valid A hA).2.2.1, fun i => ?_⟩
        rw [hιV'_eq (πS A i) (Or.inr (mem_iUnion₂.mpr ⟨A, hA, i, rfl⟩))]
        exact (hJ.π_valid A hA).2.2.2 i
      vertex_inter_𝒜 := fun A hA A' hA' hne => by
        rw [hπ_img_eq A hA, hπ_img_eq A' hA']
        exact hJ.vertex_inter_𝒜 A hA A' hA' hne
      Γ_le := hΓ_emb_eq ▸ hJ.Γ_le
      Γ_inter_D := fun A hA => by
        have hsub : (Γ.interSet (D A)).IsSubdrawing Γ := interSet_isSub
        rw [toEmbeddedGraph_congr (fun x hx => hιV'_eq x (Or.inl (hsub.1 hx)))
          (fun e he => hιE'_eq e (hsub.2 he)), hΓ_emb_eq]
        exact hJ.Γ_inter_D A hA
      π_bar_eq_bd_inter := fun A hA => by
        rw [hJ.π_bar_eq_bd_inter A hA]
        ext x
        constructor
        · intro hx
          have hxπ : x ∈ Set.range (πS A) := by
            rw [hJ.π_bar_eq_bd_inter A hA]
            exact hx
          refine ⟨hx.1, ?_⟩
          change ιV' x ∈ V(R_G.G.toGraph)
          rw [hιV'_eq x (Or.inr (mem_iUnion₂.mpr ⟨A, hA, hxπ⟩))]
          exact hx.2
        · rintro ⟨hxbd, hxV⟩
          refine ⟨hxbd, ?_⟩
          have hxS₀ : x ∈ S₀ := hCleanV' hxV
          change ιV x ∈ V(R_G.G.toGraph)
          rw [← hιV'_eq x hxS₀]
          exact hxV
      N_eq := hΓ_emb_eq ▸ hJ.N_eq
      dist_Γ_inter_K := fun v hv hvK => by
        rw [hιV'_eq v (Or.inl hv)] at hvK
        exact hJ.dist_Γ_inter_K v hv hvK }⟩

/-- Every finite family `A_fam : Fin t → Graph α β` admits a strictly monotone reindexing
`emb : Fin t' → Fin t` with `t' ≤ t` such that `A_fam ∘ emb` is injective and has the same range as
`A_fam`. -/
theorem exists_injective_subfamily {t : ℕ} (A_fam : Fin t → Graph α β) :
    ∃ (t' : ℕ) (emb : Fin t' → Fin t),
      t' ≤ t ∧
      StrictMono emb ∧
      Function.Injective (A_fam ∘ emb) ∧
      Set.range (A_fam ∘ emb) = Set.range A_fam := by
  classical
  let s : Finset (Fin t) := Finset.univ.filter (fun i : Fin t => ∀ j : Fin t, A_fam j = A_fam i → i ≤ j)
  let t' := s.card
  let e : Fin t' ≃o s := s.orderIsoOfFin rfl
  let emb : Fin t' → Fin t := fun k => (e k).1
  have hlt : t' ≤ t := by
    simpa [t'] using s.card_le_univ
  have hStrict : StrictMono emb :=
    fun a b hab => e.strictMono hab
  have hinj : Function.Injective (A_fam ∘ emb) := by
    intro a b hab
    have ha : emb a ∈ s := (e a).2
    have hb : emb b ∈ s := (e b).2
    rw [Finset.mem_filter] at ha hb
    have h1 : emb a ≤ emb b := ha.2 (emb b) hab.symm
    have h2 : emb b ≤ emb a := hb.2 (emb a) hab
    exact hStrict.injective (le_antisymm h1 h2)
  have hrange : Set.range (A_fam ∘ emb) = Set.range A_fam := by
    ext M
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨emb k, rfl⟩
    · rintro ⟨i, rfl⟩
      let fib : Finset (Fin t) := Finset.univ.filter (fun j : Fin t => A_fam j = A_fam i)
      have hfib_ne : fib.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
      let i₀ := fib.min' hfib_ne
      have hi₀_fib : i₀ ∈ fib := Finset.min'_mem fib hfib_ne
      have hi₀_eq : A_fam i₀ = A_fam i := (Finset.mem_filter.mp hi₀_fib).2
      have hi₀_s : i₀ ∈ s := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ i₀, fun j hj => ?_⟩
        exact Finset.min'_le fib j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.trans hi₀_eq⟩)
      obtain ⟨k, hk⟩ := e.surjective ⟨i₀, hi₀_s⟩
      refine ⟨k, ?_⟩
      change A_fam (e k).1 = A_fam i
      rw [hk]
      exact hi₀_eq
  exact ⟨t', emb, hlt, hStrict, hinj, hrange⟩

/-! ## Proof of Theorem 7.3 (pages 547–552) -/

set_option maxHeartbeats 400000 in
/-- **Graph Minors XXII, (7.3)** (pages 547–548):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 5$ with the following property.
Let (J1)–(J6) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be adequate for $\phi$. Let
$A_1, \dots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \dots, A_t\}$. Let $A_1', \dots, A_t' \in \mathcal{A}$, and
suppose that
(i) for $1 \le i \le t$, $(A_i', \pi(A_i') + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A_i')) \ge \theta$ and $D(A_i') \cap \Delta = \emptyset$,"
"(iv) for $1 \le i < j \le t$, $d(D(A_i'), D(A_j')) \ge \theta$,
(v) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |\bar{\pi}(A_i')|$ and with $D(A_i') \subseteq ins(F)$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_3_proof
    (q δ τ : ℕ) :
    ∃ θ : ℕ, 5 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV : αH → Graph α β) (φE : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE →
        ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
        t ≤ τ →
        (∀ i : Fin t, A_fam i ∈ ℬ) →
        (∀ i : Fin t, A_fam' i ∈ 𝒜) →
        (∀ A ∈ ℬ \ Set.range A_fam,
          θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) →
        ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
        (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
          (hπi : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
          (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
          HasSameDeltaFolio
            (subRootedDigraph R_G.G (A_fam' i) hA'i
              (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
            (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
        (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
        (∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i))) →
        (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
        (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j))) →
        (∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
          (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H := by
  classical
  let p := q + 3 * δ + 3 * τ
  obtain ⟨θ_72, hθ72_four, h72_spec⟩ := theorem_7_2_proof.{w, u, v, u₁, v₁} q δ
  obtain ⟨θ_53, hp_lt_θ53, h53_spec⟩ := theorem_5_3_parallel.{w, u, v} p
  let θ' := max θ_72 (max θ_53 (max p 4))
  let θ := θ' + 3
  refine ⟨θ, by omega, ?_⟩
  intro S _ _ α β αH βH ιV ιE R_G W 𝒜 ℬ πLen πS Γ orient ord T ins d D N K Δ v_star R_H
    φV φE hJ hAdeq t₀ A_fam₀ A_fam'₀ ht₀_le hA₀_mem_ℬ hA'₀_mem hdist_other₀ hlen₀ h_i₀
    h_ii₀ h_iii_dist₀ h_iii_disj₀ h_iv₀ h_v₀
  -- Step 1: Pass to an injective subfamily `A_fam = A_fam₀ ∘ emb` with the same range.
  obtain ⟨t, emb, ht_le_t₀, hStrict, hA_inj, hrange_eq⟩ := exists_injective_subfamily A_fam₀
  let A_fam : Fin t → Graph α β := A_fam₀ ∘ emb
  let A_fam' : Fin t → Graph α β := A_fam'₀ ∘ emb
  have ht_le : t ≤ τ := ht_le_t₀.trans ht₀_le
  have hA_mem_ℬ : ∀ i : Fin t, A_fam i ∈ ℬ := fun i => hA₀_mem_ℬ (emb i)
  have hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜 := fun i => hAdeq.subset (hA_mem_ℬ i)
  have hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜 := fun i => hA'₀_mem (emb i)
  have hdist_other : ∀ A ∈ ℬ \ Set.range A_fam,
      θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) := by
    rw [hrange_eq]
    exact hdist_other₀
  have hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i) := fun i => hlen₀ (emb i)
  have h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ := fun i => h_ii₀ (emb i)
  have h_iii_dist : ∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i)) :=
    fun i => h_iii_dist₀ (emb i)
  have h_iii_disj : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ := fun i => h_iii_disj₀ (emb i)
  have h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)) :=
    fun i j hij => h_iv₀ (emb i) (emb j) (hStrict hij)
  have h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F :=
    fun i => h_v₀ (emb i)
  -- Step 2: Replace `ιV, ιE` by clean embeddings `ιV', ιE'`.
  obtain ⟨ιV', ιE', hιV'_eq, hιE'_eq, hCleanV', hCleanE', hJ'⟩ := hJ.exists_clean_embeddings
  have hΓ_emb_eq : Γ.toEmbeddedGraph ιV' ιE' = Γ.toEmbeddedGraph ιV ιE :=
    toEmbeddedGraph_congr (fun x hx => hιV'_eq x (Or.inl hx)) hιE'_eq
  have hAdeq' : IsAdequateFor ιV' ιE' W 𝒜 ℬ Γ K R_H φV φE :=
    { hAdeq with
      mem_of_not_le_Γ_union_NW := fun v hv A hA => by
        rw [hΓ_emb_eq]
        exact hAdeq.mem_of_not_le_Γ_union_NW v hv A hA }
  have h_i' : ∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
      (hπi : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (ιV' ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
      (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (fun k : Fin (πLen (A_fam i)) =>
          ιV' (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
      HasSameDeltaFolio
        (subRootedDigraph R_G.G (A_fam' i) hA'i
          (seqConcat (fun k : Fin (πLen (A_fam i)) =>
            ιV' (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
        (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV' ∘ πS (A_fam i)) R_G.roots) hπi) δ := by
    intro i hAi hA'i hπi hπ'i
    have hseq1 : (ιV' ∘ πS (A_fam i)) = (ιV ∘ πS (A_fam i)) := by
      ext k
      exact hιV'_eq (πS (A_fam i) k) (Or.inr (mem_iUnion₂.mpr ⟨A_fam i, hA_mem i, k, rfl⟩))
    have hseq2 : (fun k : Fin (πLen (A_fam i)) =>
        ιV' (πS (A_fam' i) (Fin.cast (hlen i).symm k))) =
        (fun k : Fin (πLen (A_fam i)) =>
          ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) := by
      ext k
      exact hιV'_eq _ (Or.inr (mem_iUnion₂.mpr ⟨A_fam' i, hA'_mem i, _, rfl⟩))
    revert hπi hπ'i
    rw [hseq1, hseq2]
    intro hπi hπ'i αH' βH' R_H' hDet'
    exact h_i₀ (emb i) hAi hA'i hπi hπ'i R_H' hDet'
  -- Step 3: Choose inner closed discs `D_in i ⊆ D(A_i) \ bd(D(A_i))` and Claim (4) homeomorphism `β`.
  obtain ⟨hS_closed, hConn⟩ := GM11.IsSphere.isClosedSurface hJ'.isSphere
  have h_exists_Din : ∀ i : Fin t,
      ∃ D_i : Set S, IsClosedDisc D_i ∧ D_i ⊆ D (A_fam i) \ subBd (D (A_fam i)) :=
    fun i => exists_inner_disc_of_isClosedDisc hS_closed (hJ'.disc_D (A_fam i) (hA_mem i)).1
  choose D_in hD_in using h_exists_Din
  obtain ⟨β_homeo, hβ_fix, hβ_img, hβ_orient⟩ :=
    lemma_7_3_claim_4 hJ' hA_mem hA_inj hA'_mem h_ii h_iii_disj h_iv hD_in
  -- Step 4: Construct annulus routing drawings `M_fam`, `M_union`, `Γ₁`, `Γ₃`.
  obtain ⟨M_fam, L_arc, hML⟩ :=
    exists_annulus_family_7_3 hJ' hA_mem hA'_mem hlen h_ii hD_in hβ_img hβ_orient
  have hM_V : ∀ i : Fin t, (M_fam i).V =
      Set.range (fun j : Fin (πLen (A_fam i)) =>
        β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))) ∪
      Set.range (πS (A_fam i)) := fun i => (hML i).2.1
  have hM_U_sub : ∀ i : Fin t, (M_fam i).U ⊆ D (A_fam i) := fun i => (hML i).2.2.2.1
  have hM_U_in : ∀ i : Fin t, (M_fam i).U ∩ D_in i =
      Set.range (fun j : Fin (πLen (A_fam i)) =>
        β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))) := fun i => (hML i).2.2.2.2.1
  have hM_E : ∀ i : Fin t, ∀ e ∈ (M_fam i).E, e ⊆ (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i := by
    intro i e he
    rw [(hML i).2.2.1] at he
    rcases he with ⟨j, rfl⟩
    exact (hML i).2.2.2.2.2.2.2.2.2.1 j
  have hM_spec : ∀ i : Fin t,
      let π_in : Fin (πLen (A_fam i)) → S :=
        fun j => β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))
      (M_fam i).U = (⋃ j : Fin (πLen (A_fam i)), L_arc i j) ∧
      (M_fam i).V = Set.range π_in ∪ Set.range (πS (A_fam i)) ∧
      (M_fam i).E = Set.range (fun j : Fin (πLen (A_fam i)) =>
        L_arc i j \ {π_in j, πS (A_fam i) j}) ∧
      (∀ j : Fin (πLen (A_fam i)),
        IsLineWithEnds (L_arc i j) (π_in j) (πS (A_fam i) j)) ∧
      (∀ j : Fin (πLen (A_fam i)), π_in j ≠ πS (A_fam i) j) ∧
      Pairwise (fun j₁ j₂ : Fin (πLen (A_fam i)) => Disjoint (L_arc i j₁) (L_arc i j₂)) := by
    intro i
    have hi := hML i
    exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨M_union, Γ₁, Γ₃, hMU_U, hMU_V, hMU_E, hΓ₁_U, hΓ₁_V, hΓ₁_E,
      hΓ₂_inter_DA', hΓ₂_V_DA', hΓ₃_U, hΓ₃_V, hΓ₃_E⟩ :=
    exists_drawings_7_3 hJ' hA_mem hA_inj hA'_mem hlen h_iv h_v hD_in hβ_img hM_V hM_U_sub hM_U_in
  -- Step 5: Construct `Z₀` (`exists_Z0_7_3`) and apply Claims (8), (9), (12), and (13).
  obtain ⟨Z₀, hZ₀_K₁, hZ₀_L, hW_Z₀, hZ₀_card, hZ₀_ends, hZ₀_meets⟩ :=
    exists_Z0_7_3 hJ' hAdeq' hA_mem_ℬ hdist_other
  obtain ⟨L'₀, hL'₀_le, heff, hL'₀_K₁, hL'₀_edges⟩ :=
    lemma_7_3_claim_8 (τ := τ) (θ' := θ_53) hJ' hCleanV' hCleanE' hAdeq' hA_mem_ℬ hA'_mem
      hdist_other ht_le h_ii h_iii_disj h_iv h_v (by omega)
      (fun Γ' K₁ L' Z' F => @h53_spec S _ _ hConn α β ιV' ιE' Γ Γ' K₁ L' ord T ins d Z' t F)
      hβ_fix hM_U_sub hM_E hMU_V hMU_E rfl hΓ₁_V hΓ₁_E hΓ₂_inter_DA' hΓ₂_V_DA' hΓ₃_V hΓ₃_E
      hZ₀_K₁ hZ₀_card
  have h9 :=
    lemma_7_3_claim_9 hJ' hCleanV' hCleanE' hA_mem hA'_mem hlen h_ii h_iii_disj h_iv
      hD_in hβ_fix hβ_img hM_spec hM_E hMU_V hMU_E rfl hZ₀_K₁ hZ₀_L heff
  obtain ⟨φ'V, φ'E, hMod', hφ'V_le, hφ'E_sub, hφ'V_meets⟩ :=
    lemma_7_3_claim_12 hJ' hCleanV' hAdeq' hA_mem_ℬ hA_inj hA'_mem hdist_other hlen h_i'
      h_ii h_iii_disj h_iv h_v hZ₀_K₁ hZ₀_L hW_Z₀ hZ₀_ends hZ₀_meets hL'₀_le hL'₀_edges h9
  have hAdeq_𝒜' :=
    lemma_7_3_claim_13 (θ' := θ') hJ' rfl hA'_mem h_iii_dist h_v hZ₀_K₁ hφ'V_le hφ'E_sub hφ'V_meets
  -- Step 6: Apply Theorem 7.2 at `θ_72 ≤ θ' ≤ θ`.
  have hJ'_72 : SystemJ1ToJ6 ιV' ιE' R_G W 𝒜 πLen πS Γ orient θ_72 ord T ins d D N K Δ v_star δ R_H φV φE :=
    hJ'.mono_θ hθ72_four (by omega)
  have hdist_𝒜' : ∀ A ∈ {A ∈ 𝒜 | θ' ≤ subsetTangleDist Γ ord d {v_star} (D A)},
      θ_72 ≤ subsetTangleDist Γ ord d {v_star} (D A) :=
    fun A hA => (by omega : θ_72 ≤ θ').trans hA.2
  have hRes' :=
    h72_spec ιV' ιE' R_G W 𝒜 {A ∈ 𝒜 | θ' ≤ subsetTangleDist Γ ord d {v_star} (D A)}
      πLen πS Γ orient ord T ins d D N K Δ v_star R_H φV φ'V φE φ'E hJ'_72 hMod' hAdeq_𝒜' hdist_𝒜'
  have hv_star_eq : ιV' v_star = ιV v_star :=
    hιV'_eq v_star (Or.inl hJ.v_star_mem.1)
  simpa only [hv_star_eq] using hRes'

end GraphMinor.GM22
