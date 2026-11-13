module

public import GraphMinor.GM22.Section7c3
import GraphMinor.GM22.ParallelProofs
import GraphMinor.GM12.Section1

/-!
# Graph Minors XXII, Section 7 (Part 3d): Claims (10)–(12) of Theorem 7.3

This file formalizes Claims (10), (11), and (12) of the proof of **7.3** (`theorem_7_3`,
pages 550–551) from N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in
linkage problems*, J. Combin. Theory Ser. B **102** (2012) 530–563.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric
open Graph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM16

universe u v w u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## Subgraph with Prescribed Vertex Set and Edge Set (`subgraphVE`) -/

/-- The subgraph of $G$ with vertex set $V_0$ and edge set $E_0 \subseteq E(G)$, when every edge in
$E_0$ has both ends in $V_0$. Used for $A_{t+1}$ on page 550. -/
def subgraphVE (G : Graph α β) (V₀ : Set α) (E₀ : Set β)
    (hE : E₀ ⊆ E(G))
    (hends : ∀ e ∈ E₀, ∀ x y, G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) : Graph α β where
  vertexSet := V₀
  edgeSet := E₀
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm _ _ := ⟨fun _ _ ⟨he, hl⟩ => ⟨he, hl.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := h₁.2.left_eq_or_eq h₂.2
  edge_mem_iff_exists_isLink _ := ⟨fun he =>
    let ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet (hE he)
    ⟨x, y, he, hl⟩, fun ⟨_, _, he, _⟩ => he⟩
  left_mem_of_isLink _ _ _ h := (hends _ h.1 _ _ h.2).1

@[simp]
theorem vertexSet_subgraphVE (G : Graph α β) (V₀ : Set α) (E₀ : Set β)
    (hE : E₀ ⊆ E(G)) (hends : ∀ e ∈ E₀, ∀ x y, G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) :
    V(subgraphVE G V₀ E₀ hE hends) = V₀ :=
  rfl

@[simp]
theorem edgeSet_subgraphVE (G : Graph α β) (V₀ : Set α) (E₀ : Set β)
    (hE : E₀ ⊆ E(G)) (hends : ∀ e ∈ E₀, ∀ x y, G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) :
    E(subgraphVE G V₀ E₀ hE hends) = E₀ :=
  rfl

@[simp]
theorem subgraphVE_isLink (G : Graph α β) (V₀ : Set α) (E₀ : Set β)
    (hE : E₀ ⊆ E(G)) (hends : ∀ e ∈ E₀, ∀ x y, G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀)
    {e : β} {x y : α} :
    (subgraphVE G V₀ E₀ hE hends).IsLink e x y ↔ e ∈ E₀ ∧ G.IsLink e x y :=
  Iff.rfl

theorem subgraphVE_le {G : Graph α β} {V₀ : Set α} {E₀ : Set β}
    (hV : V₀ ⊆ V(G)) (hE : E₀ ⊆ E(G))
    (hends : ∀ e ∈ E₀, ∀ x y, G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) :
    subgraphVE G V₀ E₀ hE hends ≤ G :=
  ⟨hV, fun _ _ _ h => h.2⟩

theorem subgraphSUnion_eq_of_le {G₁ G₂ : Graph α β} {P_set : Set (Graph α β)}
    (hP : ∀ P ∈ P_set, P ≤ G₁) (hG : G₁ ≤ G₂) :
    subgraphSUnion G₁ P_set = subgraphSUnion G₂ P_set :=
  (Compatible.of_le_le ((subgraphSUnion_le hP).trans hG)
    (subgraphSUnion_le (fun P h => (hP P h).trans hG))).ext rfl
    (by rw [edgeSet_subgraphSUnion hP,
        edgeSet_subgraphSUnion (fun P h => (hP P h).trans hG)])

theorem subRootedDigraph_ofSubgraph {G : Digraph α β} {G₁ H : Graph α β}
    {q r : ℕ} {roots : Fin q → α} {π : Fin r → α}
    (hG₁ : G₁ ≤ G.toGraph) (hroots : ∀ j : Fin q, roots j ∈ V(G₁))
    (hH : H ≤ (subRootedDigraph G G₁ hG₁ roots hroots).G.toGraph)
    (hH' : H ≤ G.toGraph)
    (hπ : ∀ k : Fin r, π k ∈ V(H)) :
    (⟨(subRootedDigraph G G₁ hG₁ roots hroots).G.ofSubgraph H hH, π, hπ⟩ :
      RootedDigraph α β r) =
      subRootedDigraph G H hH' π hπ :=
  rfl

/-! ## Orderings of Finite Sets and Concatenations -/

/-- Every finite set $X$ admits an ordering `π : Fin X.ncard → α`. -/
theorem exists_ordering_of_finite {X : Set α} (hX : X.Finite) :
    ∃ π : Fin X.ncard → α, IsOrderingOf X π := by
  have : Finite X := hX.to_subtype
  have hcard : Nat.card X = X.ncard := Nat.card_coe_set_eq X
  let e : Fin X.ncard ≃ X := hcard ▸ (Finite.equivFin X).symm
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · ext x
    simp only [mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩

/-- If `π` is an ordering of `X`, `ω` is an ordering of `W`, and `Disjoint X W`, then
`seqConcat π ω` is an ordering of `X ∪ W`. -/
theorem isOrderingOf_seqConcat {p q : ℕ} {X W : Set α}
    {π : Fin p → α} {ω : Fin q → α}
    (hπ : IsOrderingOf X π) (hω : IsOrderingOf W ω) (hdisj : Disjoint X W) :
    IsOrderingOf (X ∪ W) (seqConcat π ω) := by
  have hrange : Set.range (seqConcat π ω) = X ∪ W := by
    rw [← hπ.2, ← hω.2]
    ext x
    simp only [mem_range, mem_union]
    constructor
    · rintro ⟨k, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · exact Or.inl ⟨i, by simp [seqConcat]⟩
      · exact Or.inr ⟨j, by simp [seqConcat]⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Fin.castAdd q i, by simp [seqConcat]⟩
      · exact ⟨Fin.natAdd p j, by simp [seqConcat]⟩
  refine ⟨?_, hrange⟩
  intro k₁ k₂
  refine Fin.addCases (fun i₁ => ?_) (fun j₁ => ?_) k₁
  · refine Fin.addCases (fun i₂ => ?_) (fun j₂ => ?_) k₂
    · intro hk
      simp only [seqConcat, Fin.append_left] at hk
      rw [hπ.1 hk]
    · intro hk
      simp only [seqConcat, Fin.append_left, Fin.append_right] at hk
      have hxX : π i₁ ∈ X := hπ.2 ▸ ⟨i₁, rfl⟩
      have hxW : π i₁ ∈ W := by rw [hk, ← hω.2]; exact ⟨j₂, rfl⟩
      exact False.elim (disjoint_left.mp hdisj hxX hxW)
  · refine Fin.addCases (fun i₂ => ?_) (fun j₂ => ?_) k₂
    · intro hk
      simp only [seqConcat, Fin.append_left, Fin.append_right] at hk
      have hxX : π i₂ ∈ X := hπ.2 ▸ ⟨i₂, rfl⟩
      have hxW : π i₂ ∈ W := by rw [← hk, ← hω.2]; exact ⟨j₁, rfl⟩
      exact False.elim (disjoint_left.mp hdisj hxX hxW)
    · intro hk
      simp only [seqConcat, Fin.append_right] at hk
      rw [hω.1 hk]

/-- Reindexing the first component of `seqConcat` along `Fin.cast` preserves `IsOrderingOf`. -/
theorem IsOrderingOf.seqConcat_finCast {p₁ p₂ q : ℕ} {X : Set α}
    {π : Fin p₁ → α} {ω : Fin q → α}
    (h : IsOrderingOf X (seqConcat π ω)) (hp : p₁ = p₂) :
    IsOrderingOf X (seqConcat (fun k : Fin p₂ => π (Fin.cast hp.symm k)) ω) := by
  subst hp
  exact h

/-! ## Helper Lemmas for Claims (10) and (11) -/

/-- Under `(J1)`–`(J6)`, if $A \in \mathcal{A}$ satisfies $D(A) \cap \Delta = \emptyset$, then
$d(D(A), \Sigma \setminus \Delta) = 0 < \theta - 3$, and hence $A \cap K_1 = N_W$ by 7.1(iii). -/
theorem SystemJ1ToJ6.inter_K₁_eq_noEdge_of_disjoint_Δ {q : ℕ}
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
    {A : Graph α β} (hA : A ∈ 𝒜) (hdisj : Disjoint (D A) Δ) :
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph
      {A' ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A') (Set.univ \ Δ)})
    A ⊓ K₁ = Graph.noEdge W β := by
  intro K₁
  have h0_lt : 0 < πLen A := (hJ.π_valid A hA).1
  let p₀ : S := πS A ⟨0, h0_lt⟩
  have hp₀_D : p₀ ∈ D A := (hJ.range_πS_subset_D_and_ncard hA).2.1 ⟨⟨0, h0_lt⟩, rfl⟩
  have hdist0 : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) = 0 := by
    by_contra hne
    have h1 : 1 ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) := Nat.pos_of_ne_zero hne
    have hsub : D A ⊆ Δ := subset_of_one_le_subsetTangleDist_compl hJ.hasMetric h1
    exact disjoint_left.mp hdisj hp₀_D (hsub hp₀_D)
  have h4 := hJ.four_le_θ
  exact (theorem_7_1_proof hJ).2.2 A hA (by omega)

/-- The $(t+2)$-element family $\{A_0, A_{t+1}, A_1, \dots, A_t\}$ indexed by `Fin (t + 1 + 1)`
via nested `Fin.cases`:
- index `0` is `A₀` (definitionally),
- index `(0 : Fin (t + 1)).succ` is `A_t1` (definitionally),
- index `j.succ.succ` (`j : Fin t`) is `F j` (definitionally). -/
def div73Family {t : ℕ} (A₀ : Graph α β) (F : Fin t → Graph α β) (A_t1 : Graph α β) :
    Fin (t + 1 + 1) → Graph α β :=
  Fin.cases A₀ (Fin.cases A_t1 F)

@[simp]
theorem div73Family_zero {t : ℕ} (A₀ : Graph α β) (F : Fin t → Graph α β) (A_t1 : Graph α β) :
    div73Family A₀ F A_t1 0 = A₀ :=
  rfl

@[simp]
theorem div73Family_succ_zero {t : ℕ} (A₀ : Graph α β) (F : Fin t → Graph α β) (A_t1 : Graph α β) :
    div73Family A₀ F A_t1 (0 : Fin (t + 1)).succ = A_t1 :=
  rfl

@[simp]
theorem div73Family_succ_succ {t : ℕ} (A₀ : Graph α β) (F : Fin t → Graph α β)
    (A_t1 : Graph α β) (j : Fin t) :
    div73Family A₀ F A_t1 j.succ.succ = F j :=
  rfl

/-- **Graph Minors XXII, (7.3) Claim (10)** (page 550):
(10) *$\{A_0, A_1, \ldots, A_{t+1}\}$ is a $Z$-division of $\Gamma \cup K_1 \cup A_1 \cup \cdots \cup A_t$,
and $Z \subseteq V(A_0)$, and for $1 \le i \le t+1$, $\pi(A_i) + \omega$ is an ordering of
$Z \cap V(A_i)$.* -/
theorem lemma_7_3_claim_10 {q t r : ℕ}
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
    {F : Fin t → Graph α β}
    (hF_mem : ∀ i : Fin t, F i ∈ 𝒜)
    (hF_inj : Function.Injective F)
    (hF_disj : ∀ i : Fin t, Disjoint (D (F i)) Δ)
    {Z₀ : Set α}
    (hZ₀_K₁ : Z₀ ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hW_Z₀ : W ⊆ Z₀)
    {E_t1 : Set β}
    (hE_t1_eq : E_t1 = (φE '' E(R_H.G.toGraph)) ∩ E(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hE_t1_sub : E_t1 ⊆ E(R_G.G.toGraph))
    (hE_t1_ends : ∀ e ∈ E_t1, ∀ x y, R_G.G.toGraph.IsLink e x y → x ∈ Z₀ ∧ y ∈ Z₀)
    {π_t1 : Fin r → α}
    (hπ_t1 : IsOrderingOf (Z₀ \ W) π_t1) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let S₀ := Set.univ \ ⋃ i : Fin t, (D (F i) \ subBd (D (F i)))
    let Γ₀ := Γ.interSet S₀
    let π_bar_union := ⋃ i : Fin t, ιV '' Set.range (πS (F i))
    let Z := Z₀ ∪ π_bar_union
    let A₀ := (graphUnion (graphUnion (Γ₀.toEmbeddedGraph ιV ιE) (Graph.noEdge π_bar_union β)) K₁).deleteEdges E_t1
    let A_t1 := subgraphVE R_G.G.toGraph Z₀ E_t1 hE_t1_sub hE_t1_ends
    let G_un := graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁)
      (subgraphSUnion R_G.G.toGraph (Set.range F))
    let A_div := div73Family A₀ F A_t1
    IsIndexedZDivision G_un Z A_div ∧
      Z ⊆ V(A₀) ∧
      (∀ j : Fin t, IsOrderingOf (Z ∩ V(F j)) (seqConcat (ιV ∘ πS (F j)) R_G.roots)) ∧
      IsOrderingOf (Z ∩ V(A_t1)) (seqConcat π_t1 R_G.roots) := by
  classical
  intro 𝒜_far K₁ S₀ Γ₀ π_bar_union Z A₀ A_t1 G_un A_div
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph := hJ.Γ_le.trans deleteVerts_le
  have hF_le_G : ∀ i : Fin t, F i ≤ R_G.G.toGraph := fun i => hJ.le_of_mem_𝒜 (F i) (hF_mem i)
  have hF_range_le : ∀ M ∈ Set.range F, M ≤ R_G.G.toGraph := by
    rintro _ ⟨i, rfl⟩
    exact hF_le_G i
  have hFun_le_G : subgraphSUnion R_G.G.toGraph (Set.range F) ≤ R_G.G.toGraph :=
    subgraphSUnion_le hF_range_le
  have hG_un_le : G_un ≤ R_G.G.toGraph :=
    graphUnion_le (graphUnion_le hΓ_le hK₁_le) hFun_le_G
  have hΓ₀_le_Γ : Γ₀.toEmbeddedGraph ιV ιE ≤ Γ.toEmbeddedGraph ιV ιE :=
    toEmbeddedGraph_le_of_isSubdrawing interSet_isSub ιV ιE
  have hπ_sub_Fun : π_bar_union ⊆ V(subgraphSUnion R_G.G.toGraph (Set.range F)) := by
    rintro _ ⟨_, ⟨i, rfl⟩, x, ⟨j, rfl⟩, rfl⟩
    have hx_Fi : ιV (πS (F i) j) ∈ V(F i) := ((hJ.π_valid (F i) (hF_mem i)).2.2.2 j).1
    exact (le_subgraphSUnion hF_range_le ⟨i, rfl⟩).vertexSet_mono hx_Fi
  have hnoEdge_le_Fun : Graph.noEdge π_bar_union β ≤ subgraphSUnion R_G.G.toGraph (Set.range F) :=
    ⟨hπ_sub_Fun, fun _ _ _ h => False.elim h⟩
  -- 1. Check `A₀ ≤ G_un`, `F j ≤ G_un`, `A_t1 ≤ G_un`:
  have hA₀_le_G_un : A₀ ≤ G_un := by
    refine deleteEdges_le.trans (graphUnion_le (graphUnion_le ?_ ?_) ?_)
    · exact hΓ₀_le_Γ.trans ((le_graphUnion_left _ _).trans (le_graphUnion_left _ _))
    · exact hnoEdge_le_Fun.trans (le_graphUnion_right
        (Compatible.of_le_le (graphUnion_le hΓ_le hK₁_le) hFun_le_G))
    · exact (le_graphUnion_right (Compatible.of_le_le hΓ_le hK₁_le)).trans
        (le_graphUnion_left _ _)
  have hF_le_G_un : ∀ j : Fin t, F j ≤ G_un := fun j =>
    (le_subgraphSUnion hF_range_le ⟨j, rfl⟩).trans
      (le_graphUnion_right (Compatible.of_le_le (graphUnion_le hΓ_le hK₁_le) hFun_le_G))
  have hA_t1_le_K₁ : A_t1 ≤ K₁ := by
    refine ⟨hZ₀_K₁, fun e x y ⟨he_t1, hlG⟩ => ?_⟩
    have heK₁ : e ∈ E(K₁) := by rw [hE_t1_eq] at he_t1; exact he_t1.2
    exact (hK₁_le.isLink_iff heK₁).mpr hlG
  have hA_t1_le_G_un : A_t1 ≤ G_un :=
    hA_t1_le_K₁.trans ((le_graphUnion_right (Compatible.of_le_le hΓ_le hK₁_le)).trans
      (le_graphUnion_left _ _))
  have hA_div_le : ∀ i : Fin (t + 1 + 1), A_div i ≤ G_un := by
    intro i
    refine Fin.cases hA₀_le_G_un (fun i' => ?_) i
    refine Fin.cases hA_t1_le_G_un (fun j => hF_le_G_un j) i'
  -- 2. Show `Γ.toEmbeddedGraph ιV ιE ≤ graphUnion (Γ₀.toEmbeddedGraph ιV ιE) (subgraphSUnion R_G.G.toGraph (Set.range F))`:
  have hΓ_V_sub : V(Γ.toEmbeddedGraph ιV ιE) ⊆
      V(Γ₀.toEmbeddedGraph ιV ιE) ∪ V(subgraphSUnion R_G.G.toGraph (Set.range F)) := by
    rintro _ ⟨x, hxΓ, rfl⟩
    by_cases hxS₀ : x ∈ S₀
    · exact Or.inl ⟨x, Or.inl ⟨⟨hxΓ, hxS₀⟩, hxΓ⟩, rfl⟩
    · simp only [S₀, mem_sdiff, mem_univ, true_and, not_not, mem_iUnion] at hxS₀
      rcases hxS₀ with ⟨j, hxj⟩
      have hx_inter : ιV x ∈ V((Γ.interSet (D (F j))).toEmbeddedGraph ιV ιE) :=
        ⟨x, Or.inl ⟨⟨hxΓ, hxj.1⟩, hxΓ⟩, rfl⟩
      rw [hJ.Γ_inter_D (F j) (hF_mem j)] at hx_inter
      exact Or.inr ((le_subgraphSUnion hF_range_le ⟨j, rfl⟩).vertexSet_mono hx_inter.2)
  have hΓ_E_sub : E(Γ.toEmbeddedGraph ιV ιE) ⊆
      E(Γ₀.toEmbeddedGraph ιV ιE) ∪ E(subgraphSUnion R_G.G.toGraph (Set.range F)) := by
    rintro _ ⟨e₀, he₀, rfl⟩
    by_cases heS₀ : e₀ ⊆ S₀
    · refine Or.inl ⟨e₀, ?_, rfl⟩
      rw [mem_interSet_E_iff]
      exact ⟨he₀, heS₀⟩
    · obtain ⟨z, hze₀, hz_not_S₀⟩ := not_subset.mp heS₀
      simp only [S₀, mem_sdiff, mem_univ, true_and, not_not, mem_iUnion] at hz_not_S₀
      rcases hz_not_S₀ with ⟨j, hzj⟩
      have hdisc_j := hJ.disc_D (F j) (hF_mem j)
      have hdisj_bd : Disjoint e₀ (frontier (D (F j))) := by
        rw [← subBd_eq_frontier, disjoint_left]
        intro p hpe₀ hpbd
        exact (he₀.2.1 hpe₀).2 (hdisc_j.2.1 ⟨hpbd, (he₀.2.1 hpe₀).1⟩)
      have he₀_sub_D : e₀ ⊆ D (F j) :=
        GM12.subset_of_disjoint_frontier he₀.2.2.1.isConnected.isPreconnected
          hdisc_j.1.isClosed hdisj_bd hze₀ hzj.1
      have he_inter : ιE e₀ ∈ E((Γ.interSet (D (F j))).toEmbeddedGraph ιV ιE) := by
        refine ⟨e₀, ?_, rfl⟩
        rw [mem_interSet_E_iff]
        exact ⟨he₀, he₀_sub_D⟩
      rw [hJ.Γ_inter_D (F j) (hF_mem j)] at he_inter
      have he_Fj : ιE e₀ ∈ E(F j) :=
        (inf_le_right : (Γ.toEmbeddedGraph ιV ιE) ⊓ F j ≤ F j).edgeSet_mono he_inter
      exact Or.inr ((le_subgraphSUnion hF_range_le ⟨j, rfl⟩).edgeSet_mono he_Fj)
  -- 3. Show `subgraphSUnion G_un (Set.range A_div) = G_un`:
  have hA_div_range_le : ∀ M ∈ Set.range A_div, M ≤ G_un := by
    rintro _ ⟨i, rfl⟩
    exact hA_div_le i
  have hSUnion_eq : subgraphSUnion G_un (Set.range A_div) = G_un := by
    have hle : subgraphSUnion G_un (Set.range A_div) ≤ G_un := subgraphSUnion_le hA_div_range_le
    have hV_eq : V(subgraphSUnion G_un (Set.range A_div)) = V(G_un) := by
      refine Subset.antisymm hle.vertexSet_mono ?_
      rintro u ((huΓ | huK₁) | huF)
      · rcases hΓ_V_sub huΓ with huΓ₀ | huF
        · refine (le_subgraphSUnion hA_div_range_le ⟨0, rfl⟩).vertexSet_mono ?_
          change u ∈ V(A₀)
          rw [vertexSet_deleteEdges]
          exact Or.inl (Or.inl huΓ₀)
        · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at huF
          rcases huF with ⟨_, ⟨j, rfl⟩, huj⟩
          exact (le_subgraphSUnion hA_div_range_le ⟨j.succ.succ, rfl⟩).vertexSet_mono huj
      · refine (le_subgraphSUnion hA_div_range_le ⟨0, rfl⟩).vertexSet_mono ?_
        change u ∈ V(A₀)
        rw [vertexSet_deleteEdges]
        exact Or.inr huK₁
      · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at huF
        rcases huF with ⟨_, ⟨j, rfl⟩, huj⟩
        exact (le_subgraphSUnion hA_div_range_le ⟨j.succ.succ, rfl⟩).vertexSet_mono huj
    have hE_eq : E(subgraphSUnion G_un (Set.range A_div)) = E(G_un) := by
      refine Subset.antisymm hle.edgeSet_mono ?_
      rintro e ((heΓ | heK₁) | heF)
      · rcases hΓ_E_sub heΓ with heΓ₀ | heF
        · by_cases he_t1 : e ∈ E_t1
          · exact (le_subgraphSUnion hA_div_range_le ⟨(0 : Fin (t + 1)).succ, rfl⟩).edgeSet_mono he_t1
          · refine (le_subgraphSUnion hA_div_range_le ⟨0, rfl⟩).edgeSet_mono ?_
            change e ∈ E(A₀)
            rw [edgeSet_deleteEdges]
            exact ⟨Or.inl (Or.inl heΓ₀), he_t1⟩
        · rw [edgeSet_subgraphSUnion hF_range_le, mem_iUnion₂] at heF
          rcases heF with ⟨_, ⟨j, rfl⟩, hej⟩
          exact (le_subgraphSUnion hA_div_range_le ⟨j.succ.succ, rfl⟩).edgeSet_mono hej
      · by_cases he_t1 : e ∈ E_t1
        · exact (le_subgraphSUnion hA_div_range_le ⟨(0 : Fin (t + 1)).succ, rfl⟩).edgeSet_mono he_t1
        · refine (le_subgraphSUnion hA_div_range_le ⟨0, rfl⟩).edgeSet_mono ?_
          change e ∈ E(A₀)
          rw [edgeSet_deleteEdges]
          exact ⟨Or.inr heK₁, he_t1⟩
      · rw [edgeSet_subgraphSUnion hF_range_le, mem_iUnion₂] at heF
        rcases heF with ⟨_, ⟨j, rfl⟩, hej⟩
        exact (le_subgraphSUnion hA_div_range_le ⟨j.succ.succ, rfl⟩).edgeSet_mono hej
    exact (Compatible.of_le_le hle le_rfl).ext hV_eq hE_eq
  -- 4. Intersections `F j ⊓ K₁ = Graph.noEdge W β` and `A₀` vs `F j`:
  have hF_inter_K₁ : ∀ j : Fin t, F j ⊓ K₁ = Graph.noEdge W β :=
    fun j => hJ.inter_K₁_eq_noEdge_of_disjoint_Δ (hF_mem j) (hF_disj j)
  have hF_disj_EK₁ : ∀ j : Fin t, Disjoint E(F j) E(K₁) := by
    intro j
    rw [disjoint_left]
    intro e heF heK₁
    obtain ⟨x, y, hlF⟩ := (F j).exists_isLink_of_mem_edgeSet heF
    have hlG : R_G.G.toGraph.IsLink e x y := hlF.mono (hF_le_G j)
    have hlK₁ : K₁.IsLink e x y := (hK₁_le.isLink_iff heK₁).mpr hlG
    have hl_inter : (F j ⊓ K₁).IsLink e x y := ⟨hlF, hlK₁⟩
    rw [hF_inter_K₁ j] at hl_inter
    exact hl_inter
  have hF_inter_VK₁ : ∀ j : Fin t, V(F j) ∩ V(K₁) = W := by
    intro j
    have := congrArg Graph.vertexSet (hF_inter_K₁ j)
    simpa using this
  have hA₀_F : ∀ j : Fin t, Disjoint E(A₀) E(F j) ∧ V(A₀) ∩ V(F j) ⊆ Z := by
    intro j
    constructor
    · rw [disjoint_left]
      intro e heA₀ heFj
      rw [edgeSet_deleteEdges] at heA₀
      rcases heA₀.1 with (heΓ₀ | heno) | heK₁
      · rcases heΓ₀ with ⟨e₀, he₀_Γ₀, rfl⟩
        rw [mem_interSet_E_iff] at he₀_Γ₀
        have he_inter : ιE e₀ ∈ E((Γ.toEmbeddedGraph ιV ιE) ⊓ F j) := by
          obtain ⟨x, y, hlFj⟩ := (F j).exists_isLink_of_mem_edgeSet heFj
          have hlG : R_G.G.toGraph.IsLink (ιE e₀) x y := hlFj.mono (hF_le_G j)
          have hlΓ : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e₀) x y :=
            (hΓ_le.isLink_iff ⟨e₀, he₀_Γ₀.1, rfl⟩).mpr hlG
          exact IsLink.edge_mem (G := (Γ.toEmbeddedGraph ιV ιE) ⊓ F j) ⟨hlΓ, hlFj⟩
        rw [← hJ.Γ_inter_D (F j) (hF_mem j)] at he_inter
        rcases he_inter with ⟨e₁, he₁_D, he₁_eq⟩
        have he₁_eq' : e₁ = e₀ := ιE.injective he₁_eq
        subst he₁_eq'
        rw [mem_interSet_E_iff] at he₁_D
        obtain ⟨z, hze₀⟩ := he₀_Γ₀.1.1
        have hzD : z ∈ D (F j) := he₁_D.2 hze₀
        have hzS₀ : z ∈ S₀ := he₀_Γ₀.2 hze₀
        have hz_not_int : z ∉ D (F j) \ subBd (D (F j)) :=
          fun hz_int => hzS₀.2 (mem_iUnion.mpr ⟨j, hz_int⟩)
        have hz_bd : z ∈ subBd (D (F j)) := by
          by_contra hnot
          exact hz_not_int ⟨hzD, hnot⟩
        exact (he₀_Γ₀.1.2.1 hze₀).2 ((hJ.disc_D (F j) (hF_mem j)).2.1 ⟨hz_bd, (he₀_Γ₀.1.2.1 hze₀).1⟩)
      · exact heno
      · exact disjoint_left.mp (hF_disj_EK₁ j) heFj heK₁
    · rintro u ⟨huA₀, huFj⟩
      rw [vertexSet_deleteEdges] at huA₀
      rcases huA₀ with (huΓ₀ | huπ) | huK₁
      · rcases huΓ₀ with ⟨x, hxΓ₀, rfl⟩
        have hxΓ : x ∈ Γ.V := interSet_isSub.1 hxΓ₀
        have hx_inter : ιV x ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ F j) := ⟨⟨x, hxΓ, rfl⟩, huFj⟩
        rw [← hJ.Γ_inter_D (F j) (hF_mem j)] at hx_inter
        rcases hx_inter with ⟨x', hx'_D, hx_eq⟩
        have hx_eq' : x' = x := ιV.injective hx_eq
        subst hx_eq'
        have hxD : x' ∈ D (F j) :=
          interSet_U_subset (hJ.disc_D (F j) (hF_mem j)).1.isClosed (Drawing.V_subset_U _ hx'_D)
        have hxS₀ : x' ∈ S₀ :=
          interSet_U_subset (isClosed_compl_iUnion_discInt _) (Drawing.V_subset_U _ hxΓ₀)
        have hx_bd : x' ∈ subBd (D (F j)) := by
          by_contra hnot
          exact hxS₀.2 (mem_iUnion.mpr ⟨j, hxD, hnot⟩)
        have hx_G : x' ∈ ιV ⁻¹' V(R_G.G.toGraph) := (hF_le_G j).vertexSet_mono huFj
        have hx_π : x' ∈ Set.range (πS (F j)) := by
          rw [hJ.π_bar_eq_bd_inter (F j) (hF_mem j)]
          exact ⟨hx_bd, hx_G⟩
        exact Or.inr (mem_iUnion.mpr ⟨j, ⟨x', hx_π, rfl⟩⟩)
      · exact Or.inr huπ
      · have huW : u ∈ W := by
          rw [← hF_inter_VK₁ j]
          exact ⟨huFj, huK₁⟩
        exact Or.inl (hW_Z₀ huW)
  have hF_At1 : ∀ j : Fin t, Disjoint E(F j) E(A_t1) ∧ V(F j) ∩ V(A_t1) ⊆ Z := by
    intro j
    refine ⟨(hF_disj_EK₁ j).mono_right hA_t1_le_K₁.edgeSet_mono, ?_⟩
    intro u ⟨_, huAt1⟩
    exact Or.inl huAt1
  have hA₀_At1 : Disjoint E(A₀) E(A_t1) ∧ V(A₀) ∩ V(A_t1) ⊆ Z := by
    constructor
    · rw [disjoint_left]
      intro e heA₀ heAt1
      rw [edgeSet_deleteEdges] at heA₀
      exact heA₀.2 heAt1
    · intro u ⟨_, huAt1⟩
      exact Or.inl huAt1
  have hF_F : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ →
      Disjoint E(F j₁) E(F j₂) ∧ V(F j₁) ∩ V(F j₂) ⊆ Z := by
    intro j₁ j₂ hne
    have hF_ne : F j₁ ≠ F j₂ := hF_inj.ne hne
    refine ⟨hJ.edge_disjoint_𝒜 (F j₁) (hF_mem j₁) (F j₂) (hF_mem j₂) hF_ne, ?_⟩
    rw [hJ.vertex_inter_𝒜 (F j₁) (hF_mem j₁) (F j₂) (hF_mem j₂) hF_ne]
    rintro u (⟨hu₁, _⟩ | huW)
    · exact Or.inr (mem_iUnion.mpr ⟨j₁, hu₁⟩)
    · exact Or.inl (hW_Z₀ huW)
  -- 5. Assemble `IsIndexedZDivision G_un Z A_div`:
  have hDiv : IsIndexedZDivision G_un Z A_div := by
    refine ⟨hA_div_le, hSUnion_eq, ?_⟩
    have hsymm : ∀ {M₁ M₂ : Graph α β},
        Disjoint E(M₁) E(M₂) ∧ V(M₁) ∩ V(M₂) ⊆ Z →
        Disjoint E(M₂) E(M₁) ∧ V(M₂) ∩ V(M₁) ⊆ Z :=
      fun {M₁ M₂} ⟨hE, hV⟩ => ⟨hE.symm, Set.inter_comm V(M₂) V(M₁) ▸ hV⟩
    intro i₁ i₂
    refine Fin.cases ?_ (fun i₁' => ?_) i₁
    · refine Fin.cases (fun h => False.elim (h rfl)) (fun i₂' => ?_) i₂
      refine Fin.cases (fun _ => hA₀_At1) (fun j₂ _ => hA₀_F j₂) i₂'
    · refine Fin.cases ?_ (fun i₂' => ?_) i₂
      · intro _
        refine Fin.cases (hsymm hA₀_At1) (fun j₁ => hsymm (hA₀_F j₁)) i₁'
      · refine Fin.cases ?_ (fun j₁ => ?_) i₁'
        · refine Fin.cases (fun h => False.elim (h rfl)) (fun j₂ _ => hsymm (hF_At1 j₂)) i₂'
        · refine Fin.cases (fun _ => hF_At1 j₁) (fun j₂ hne => ?_) i₂'
          have hj_ne : j₁ ≠ j₂ := fun h => hne (by rw [h])
          exact hF_F j₁ j₂ hj_ne
  -- 6. Check `Z ⊆ V(A₀)` and the orderings:
  have hZ_sub_A₀ : Z ⊆ V(A₀) := by
    rw [vertexSet_deleteEdges]
    rintro u (huZ₀ | huπ)
    · exact Or.inr (hZ₀_K₁ huZ₀)
    · exact Or.inl (Or.inr huπ)
  have hω_ord : IsOrderingOf W R_G.roots := ⟨hJ.inj_roots, hJ.W_eq.symm⟩
  have hord_F : ∀ j : Fin t,
      IsOrderingOf (Z ∩ V(F j)) (seqConcat (ιV ∘ πS (F j)) R_G.roots) := by
    intro j
    have hZ_inter_Fj : Z ∩ V(F j) = (ιV '' Set.range (πS (F j))) ∪ W := by
      refine Subset.antisymm ?_ ?_
      · rintro u ⟨huZ₀ | huπ, huFj⟩
        · have huW : u ∈ W := by
            rw [← hF_inter_VK₁ j]
            exact ⟨huFj, hZ₀_K₁ huZ₀⟩
          exact Or.inr huW
        · obtain ⟨k, hu_πk⟩ := mem_iUnion.mp huπ
          by_cases hkj : k = j
          · subst hkj
            exact Or.inl hu_πk
          · have hu_Fk : u ∈ V(F k) :=
              ((hJ.image_range_πS_subset (hF_mem k)) hu_πk).1
            have hu_inter : u ∈ V(F k) ∩ V(F j) := ⟨hu_Fk, huFj⟩
            rw [hJ.vertex_inter_𝒜 (F k) (hF_mem k) (F j) (hF_mem j) (hF_inj.ne hkj)] at hu_inter
            rcases hu_inter with ⟨_, hu_πj⟩ | huW
            · exact Or.inl hu_πj
            · exact Or.inr huW
      · rintro u (hu_πj | huW)
        · exact ⟨Or.inr (mem_iUnion.mpr ⟨j, hu_πj⟩),
            ((hJ.image_range_πS_subset (hF_mem j)) hu_πj).1⟩
        · exact ⟨Or.inl (hW_Z₀ huW), hJ.W_subset_V (F j) (hF_mem j) huW⟩
    have hπj_ord : IsOrderingOf (ιV '' Set.range (πS (F j))) (ιV ∘ πS (F j)) :=
      ⟨ιV.injective.comp (hJ.π_valid (F j) (hF_mem j)).2.2.1, Set.range_comp ιV (πS (F j))⟩
    have hdisj_πW : Disjoint (ιV '' Set.range (πS (F j))) W := by
      rw [disjoint_left]
      intro u hu
      exact ((hJ.image_range_πS_subset (hF_mem j)) hu).2
    rw [hZ_inter_Fj]
    exact isOrderingOf_seqConcat hπj_ord hω_ord hdisj_πW
  have hord_At1 : IsOrderingOf (Z ∩ V(A_t1)) (seqConcat π_t1 R_G.roots) := by
    have hZ_inter_At1 : Z ∩ V(A_t1) = (Z₀ \ W) ∪ W := by
      change Z ∩ Z₀ = (Z₀ \ W) ∪ W
      rw [inter_eq_right.mpr subset_union_left, sdiff_union_of_subset hW_Z₀]
    rw [hZ_inter_At1]
    exact isOrderingOf_seqConcat hπ_t1 hω_ord disjoint_sdiff_left
  exact ⟨hDiv, hZ_sub_A₀, hord_F, hord_At1⟩

/-- **Graph Minors XXII, (7.3) Claim (11)** (page 551):
(11) *$\{A'_0, A'_1, \ldots, A'_{t+1}\}$ is a $Z'$-division of $\Gamma \cup K_1 \cup A'_1 \cup \cdots \cup A'_t$,
and for $1 \le i \le t+1$, $\pi(A'_i) + \omega$ is an ordering of $Z' \cap V(A'_i)$.* -/
theorem lemma_7_3_claim_11 {q t r : ℕ}
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
    (h_iii : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ)
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    {Z₀ : Set α}
    (hZ₀_K₁ : Z₀ ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hW_Z₀ : W ⊆ Z₀)
    {E_t1 : Set β}
    (hE_t1_eq : E_t1 = (φE '' E(R_H.G.toGraph)) ∩ E(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hE_t1_sub : E_t1 ⊆ E(R_G.G.toGraph))
    (hE_t1_ends : ∀ e ∈ E_t1, ∀ x y, R_G.G.toGraph.IsLink e x y → x ∈ Z₀ ∧ y ∈ Z₀)
    {π_t1 : Fin r → α}
    (hπ_t1 : IsOrderingOf (Z₀ \ W) π_t1) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let F_fam : Fin t → Set S := fun i => subBd (D (A_fam' i))
    let S_prime := Set.univ \ ⋃ i : Fin t, (ins (F_fam i) \ F_fam i)
    let Z' := Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))
    let A'₀ := (graphUnion ((Γ.interSet S_prime).toEmbeddedGraph ιV ιE) K₁).deleteEdges E_t1
    let A_t1 := subgraphVE R_G.G.toGraph Z₀ E_t1 hE_t1_sub hE_t1_ends
    let G'_un := graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁)
      (subgraphSUnion R_G.G.toGraph (Set.range A_fam'))
    let A'_div := div73Family A'₀ A_fam' A_t1
    IsIndexedZDivision G'_un Z' A'_div ∧
      Z' ⊆ V(A'₀) ∧
      (∀ j : Fin t, IsOrderingOf (Z' ∩ V(A_fam' j)) (seqConcat (ιV ∘ πS (A_fam' j)) R_G.roots)) ∧
      IsOrderingOf (Z' ∩ V(A_t1)) (seqConcat π_t1 R_G.roots) := by
  classical
  intro 𝒜_far K₁ F_fam S_prime Z' A'₀ A_t1 G'_un A'_div
  have h1_le_θ : 1 ≤ θ := le_trans (by decide : 1 ≤ 4) hJ.four_le_θ
  have hDA'_disj : Pairwise (fun i j : Fin t => Disjoint (D (A_fam' i)) (D (A_fam' j))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact disjoint_of_one_le_subsetTangleDist hJ.hasMetric (h1_le_θ.trans (h_iv i j hlt))
    · exact (disjoint_of_one_le_subsetTangleDist hJ.hasMetric (h1_le_θ.trans (h_iv j i hgt))).symm
  have hA'_inj : Function.Injective A_fam' := by
    intro i j hij
    by_contra hne
    have h0_lt : 0 < πLen (A_fam' i) := (hJ.π_valid (A_fam' i) (hA'_mem i)).1
    have hp_i : πS (A_fam' i) ⟨0, h0_lt⟩ ∈ D (A_fam' i) :=
      (hJ.range_πS_subset_D_and_ncard (hA'_mem i)).2.1 ⟨⟨0, h0_lt⟩, rfl⟩
    have hp_j : πS (A_fam' i) ⟨0, h0_lt⟩ ∈ D (A_fam' j) := hij ▸ hp_i
    exact disjoint_left.mp (hDA'_disj hne) hp_i hp_j
  have hS_prime_eq : S_prime = Set.univ \ ⋃ i : Fin t, (D (A_fam' i) \ subBd (D (A_fam' i))) := by
    dsimp only [S_prime, F_fam]
    congr 2
    ext i x
    rw [← (hJ.disc_D (A_fam' i) (hA'_mem i)).2.2]
  have hπ'_sub_ΓS : (⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))) ⊆
      V((Γ.interSet S_prime).toEmbeddedGraph ιV ιE) := by
    rintro _ ⟨_, ⟨i, rfl⟩, x, hx_range, rfl⟩
    have h3 := lemma_7_3_claim_3 hJ hA'_mem h_v i
    rw [← h3] at hx_range
    have hx_S_prime : x ∈ S_prime := by
      rw [hS_prime_eq]
      refine ⟨trivial, ?_⟩
      rw [mem_iUnion]
      rintro ⟨j, hxj⟩
      by_cases hij : i = j
      · subst hij
        exact hxj.2 hx_range.1
      · have hx_Di : x ∈ D (A_fam' i) := by
          have hcl : subBd (D (A_fam' i)) ⊆ D (A_fam' i) := by
            rw [subBd_eq_frontier]
            exact (hJ.disc_D (A_fam' i) (hA'_mem i)).1.isClosed.frontier_subset
          exact hcl hx_range.1
        exact disjoint_left.mp (hDA'_disj hij) hx_Di hxj.1
    exact ⟨x, Or.inl ⟨⟨hx_range.2, hx_S_prime⟩, hx_range.2⟩, rfl⟩
  have hΓS_eq : graphUnion ((Γ.interSet S_prime).toEmbeddedGraph ιV ιE)
      (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))) β) =
      (Γ.interSet S_prime).toEmbeddedGraph ιV ιE := by
    refine Graph.ext (union_eq_self_of_subset_right hπ'_sub_ΓS) fun e x y => ?_
    simp only [graphUnion, Graph.noEdge_isLink, and_false, or_false]
  have h10 := lemma_7_3_claim_10 hJ hA'_mem hA'_inj h_iii hZ₀_K₁ hW_Z₀
    hE_t1_eq hE_t1_sub hE_t1_ends hπ_t1
  dsimp only at h10
  rw [← hS_prime_eq, hΓS_eq] at h10
  exact h10

/-! ## Proof of Claim (12) of 7.3 (page 551) -/

theorem inter_deleteEdges_graphUnion_noEdge_eq {G L M K₁ : Graph α β} {X : Set α} {E_t1 : Set β}
    (hL : L ≤ G) (hM : M ≤ G) (hno : Graph.noEdge X β ≤ G) (hK₁ : K₁ ≤ G)
    (hX_L : X ⊆ V(L)) (hdisj : Disjoint E(L) E_t1) :
    L ⊓ (graphUnion (graphUnion M (Graph.noEdge X β)) K₁).deleteEdges E_t1 =
      graphUnion (graphUnion (L ⊓ M) (Graph.noEdge X β)) (L ⊓ K₁) := by
  have hLHS : L ⊓ (graphUnion (graphUnion M (Graph.noEdge X β)) K₁).deleteEdges E_t1 ≤ G :=
    (inf_le_left : L ⊓ _ ≤ L).trans hL
  have hRHS : graphUnion (graphUnion (L ⊓ M) (Graph.noEdge X β)) (L ⊓ K₁) ≤ G :=
    graphUnion_le (graphUnion_le ((inf_le_left : L ⊓ M ≤ L).trans hL) hno)
      ((inf_le_left : L ⊓ K₁ ≤ L).trans hL)
  refine (Compatible.of_le_le hLHS hRHS).ext ?_ ?_
  · ext u
    simp only [vertexSet_inf, vertexSet_deleteEdges, vertexSet_graphUnion,
      Graph.vertexSet_noEdge, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨huL, (huM | huX) | huK₁⟩
      · exact Or.inl (Or.inl ⟨huL, huM⟩)
      · exact Or.inl (Or.inr huX)
      · exact Or.inr ⟨huL, huK₁⟩
    · rintro ((⟨huL, huM⟩ | huX) | ⟨huL, huK₁⟩)
      · exact ⟨huL, Or.inl (Or.inl huM)⟩
      · exact ⟨hX_L huX, Or.inl (Or.inr huX)⟩
      · exact ⟨huL, Or.inr huK₁⟩
  · ext e
    simp only [edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty]
    constructor
    · intro he
      obtain ⟨x, y, hlL, hlA₀⟩ :=
        (L ⊓ (graphUnion (graphUnion M (Graph.noEdge X β)) K₁).deleteEdges E_t1).exists_isLink_of_mem_edgeSet he
      rw [deleteEdges_isLink] at hlA₀
      rcases hlA₀.1 with (hlM | ⟨_, hlno⟩) | ⟨_, hlK₁⟩
      · exact Or.inl (IsLink.edge_mem (G := L ⊓ M) ⟨hlL, hlM⟩)
      · exact False.elim hlno
      · exact Or.inr (IsLink.edge_mem (G := L ⊓ K₁) ⟨hlL, hlK₁⟩)
    · rintro (heM | heK₁)
      · obtain ⟨x, y, hlL, hlM⟩ := (L ⊓ M).exists_isLink_of_mem_edgeSet heM
        exact IsLink.edge_mem
          (G := L ⊓ (graphUnion (graphUnion M (Graph.noEdge X β)) K₁).deleteEdges E_t1)
          ⟨hlL, ⟨Or.inl (Or.inl hlM), disjoint_left.mp hdisj hlL.edge_mem⟩⟩
      · obtain ⟨x, y, hlL, hlK₁⟩ := (L ⊓ K₁).exists_isLink_of_mem_edgeSet heK₁
        refine IsLink.edge_mem
          (G := L ⊓ (graphUnion (graphUnion M (Graph.noEdge X β)) K₁).deleteEdges E_t1)
          ⟨hlL, ⟨?_, disjoint_left.mp hdisj hlL.edge_mem⟩⟩
        exact (graphUnion_isLink (Compatible.of_le_le (graphUnion_le hM hno) hK₁)).mpr (Or.inr hlK₁)

set_option maxHeartbeats 200000 in
/-- **Graph Minors XXII, (7.3) Claim (12)** (page 551):
(12) *There is a model $\phi'$ of $(H, \chi)$ in $(\Gamma \cup K_1 \cup A'_1 \cup \cdots \cup A'_t, \omega)$
such that $\phi'(E(H)) \subseteq E(A'_1 \cup \cdots \cup A'_{t+1})$ and
$\phi'(v) \cap (A'_1 \cup \cdots \cup A'_{t+1})$ is non-null for each $v \in V(H)$.* -/
theorem lemma_7_3_claim_12 {q t : ℕ}
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
    (hCleanV : ιV ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A))
    (hAdeq : IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE)
    {A_fam A_fam' : Fin t → Graph α β}
    (hA_mem_ℬ : ∀ i : Fin t, A_fam i ∈ ℬ)
    (hA_inj : Function.Injective A_fam)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hdist_other : ∀ A ∈ ℬ \ Set.range A_fam,
      θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ))
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    (h_i : ∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
      (hπi : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
      (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
        seqConcat (fun k : Fin (πLen (A_fam i)) =>
          ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
      HasSameDeltaFolio
        (subRootedDigraph R_G.G (A_fam' i) hA'i
          (seqConcat (fun k : Fin (πLen (A_fam i)) =>
            ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
        (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ)
    (h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ)
    (h_iii : ∀ i : Fin t, Disjoint (D (A_fam' i)) Δ)
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    {Z₀ : Set α}
    (hZ₀_K₁ : Z₀ ⊆ V(graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hZ₀_L : Z₀ ⊆ V(subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))))
    (hW_Z₀ : W ⊆ Z₀)
    (hZ₀_ends : ∀ e ∈ E(R_H.G.toGraph),
      φE e ∈ E(graphUnion K (subgraphSUnion R_G.G.toGraph
        {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})) →
      R_G.G.head (φE e) ∈ Z₀ ∧ R_G.G.tail (φE e) ∈ Z₀)
    (hZ₀_meets : ∀ v ∈ V(R_H.G.toGraph),
      (V(φV v) ∩ (Z₀ ∪ V(subgraphSUnion R_G.G.toGraph (Set.range A_fam)))).Nonempty)
    {L'₀ : Graph α β}
    (hL'₀_le : L'₀ ≤ graphUnion
      ((Γ.interSet (Set.univ \ ⋃ i : Fin t,
        (ins (subBd (D (A_fam' i))) \ subBd (D (A_fam' i))))).toEmbeddedGraph ιV ιE)
      (graphUnion K (subgraphSUnion R_G.G.toGraph
        {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})))
    (hL'₀_edges : E(L'₀) ∩ (φE '' E(R_H.G.toGraph)) ⊆
      E(subgraphSUnion R_G.G.toGraph (Set.range A_fam)))
    (h9 : ∀ u ∈ Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i)),
      ∀ v ∈ Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i)),
      AreConnectedIn L'₀ u v ↔
        AreConnectedIn
          (graphUnion
            (graphUnion
              ((graphUnion (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β)
                (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))) ⊓
                ((Γ.interSet (Set.univ \ ⋃ i : Fin t,
                  (D (A_fam i) \ subBd (D (A_fam i))))).toEmbeddedGraph ιV ιE))
              (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β))
            ((graphUnion (Graph.noEdge (⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))) β)
              (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))) ⊓
              (graphUnion K (subgraphSUnion R_G.G.toGraph
                {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}))))
          (alphaMap73 ιV πS A_fam A_fam' hlen u)
          (alphaMap73 ιV πS A_fam A_fam' hlen v)) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let E_t1 := (φE '' E(R_H.G.toGraph)) ∩ E(K₁)
    let G'_un := graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁)
      (subgraphSUnion R_G.G.toGraph (Set.range A_fam'))
    ∃ (φ'V : αH → Graph α β) (φ'E : βH → β),
      IsRootedDigraphModel R_G R_H φ'V φ'E ∧
      (∀ v ∈ V(R_H.G.toGraph), φ'V v ≤ G'_un) ∧
      φ'E '' E(R_H.G.toGraph) ⊆ E_t1 ∪ ⋃ i : Fin t, E(A_fam' i) ∧
      ∀ v ∈ V(R_H.G.toGraph), (V(φ'V v) ∩ (Z₀ ∪ ⋃ i : Fin t, V(A_fam' i))).Nonempty := by
  classical
  intro 𝒜_far K₁ E_t1 G'_un
  have hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜 := fun i => hAdeq.subset (hA_mem_ℬ i)
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph := hJ.Γ_le.trans deleteVerts_le
  have hA_range_le : ∀ M ∈ Set.range A_fam, M ≤ R_G.G.toGraph := by
    rintro _ ⟨i, rfl⟩
    exact hJ.le_of_mem_𝒜 (A_fam i) (hA_mem i)
  have hA'_range_le : ∀ M ∈ Set.range A_fam', M ≤ R_G.G.toGraph := by
    rintro _ ⟨i, rfl⟩
    exact hJ.le_of_mem_𝒜 (A_fam' i) (hA'_mem i)
  let G_un := graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) K₁)
    (subgraphSUnion R_G.G.toGraph (Set.range A_fam))
  have hG_un_le : G_un ≤ R_G.G.toGraph :=
    graphUnion_le (graphUnion_le hΓ_le hK₁_le) (subgraphSUnion_le hA_range_le)
  have hG'_un_le : G'_un ≤ R_G.G.toGraph :=
    graphUnion_le (graphUnion_le hΓ_le hK₁_le) (subgraphSUnion_le hA'_range_le)
  -- Construct `A_t1` and an ordering `π_t1` of `Z₀ \ W`:
  have hE_t1_sub : E_t1 ⊆ E(R_G.G.toGraph) :=
    fun _ he => hK₁_le.edgeSet_mono he.2
  have hE_t1_ends : ∀ e ∈ E_t1, ∀ x y, R_G.G.toGraph.IsLink e x y → x ∈ Z₀ ∧ y ∈ Z₀ := by
    rintro e ⟨⟨eH, heH, rfl⟩, heK₁⟩ x y hl
    have hl_dir := R_G.G.isLink_of_mem (φE eH) (hK₁_le.edgeSet_mono heK₁)
    obtain ⟨hhZ₀, htZ₀⟩ := hZ₀_ends eH heH heK₁
    rcases hl.left_eq_or_eq hl_dir with rfl | rfl
    · rcases hl.right_eq_or_eq hl_dir with h | h
      · exact ⟨htZ₀, h ▸ htZ₀⟩
      · exact ⟨htZ₀, h ▸ hhZ₀⟩
    · rcases hl.right_eq_or_eq hl_dir with h | h
      · exact ⟨hhZ₀, h ▸ htZ₀⟩
      · exact ⟨hhZ₀, h ▸ hhZ₀⟩
  let A_t1 := subgraphVE R_G.G.toGraph Z₀ E_t1 hE_t1_sub hE_t1_ends
  have hZ₀_fin : (Z₀ \ W).Finite :=
    (hJ.finite_V.subset (hZ₀_K₁.trans hK₁_le.vertexSet_mono)).sdiff
  obtain ⟨π_t1, hπ_t1⟩ := exists_ordering_of_finite hZ₀_fin
  let S₀ := Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i)))
  let Γ₀ := Γ.interSet S₀
  let π_bar_union := ⋃ i : Fin t, ιV '' Set.range (πS (A_fam i))
  let Z := Z₀ ∪ π_bar_union
  let Z' := Z₀ ∪ ⋃ i : Fin t, ιV '' Set.range (πS (A_fam' i))
  let A₀ := (graphUnion (graphUnion (Γ₀.toEmbeddedGraph ιV ιE) (Graph.noEdge π_bar_union β)) K₁).deleteEdges E_t1
  let F_fam : Fin t → Set S := fun i => subBd (D (A_fam' i))
  let S_prime := Set.univ \ ⋃ i : Fin t, (ins (F_fam i) \ F_fam i)
  let A'₀ := (graphUnion ((Γ.interSet S_prime).toEmbeddedGraph ιV ιE) K₁).deleteEdges E_t1
  let A_div := div73Family A₀ A_fam A_t1
  let A'_div := div73Family A'₀ A_fam' A_t1
  -- Apply Claims (10) and (11):
  have h10 :
      IsIndexedZDivision G_un Z A_div ∧
        Z ⊆ V(A₀) ∧
        (∀ j : Fin t, IsOrderingOf (Z ∩ V(A_fam j)) (seqConcat (ιV ∘ πS (A_fam j)) R_G.roots)) ∧
        IsOrderingOf (Z ∩ V(A_t1)) (seqConcat π_t1 R_G.roots) :=
    lemma_7_3_claim_10 hJ hA_mem hA_inj h_ii hZ₀_K₁ hW_Z₀ rfl hE_t1_sub hE_t1_ends hπ_t1
  obtain ⟨hDiv, hZ_sub_A₀, hord_A, hord_At1⟩ := h10
  have h11 :
      IsIndexedZDivision G'_un Z' A'_div ∧
        Z' ⊆ V(A'₀) ∧
        (∀ j : Fin t, IsOrderingOf (Z' ∩ V(A_fam' j)) (seqConcat (ιV ∘ πS (A_fam' j)) R_G.roots)) ∧
        IsOrderingOf (Z' ∩ V(A_t1)) (seqConcat π_t1 R_G.roots) :=
    lemma_7_3_claim_11 hJ hA'_mem h_iii h_iv h_v hZ₀_K₁ hW_Z₀ rfl hE_t1_sub hE_t1_ends hπ_t1
  obtain ⟨hDiv', hZ'_sub_A'₀, hord_A', hord_At1'⟩ := h11
  -- Rooted digraphs `R_G_sub` and `R_G'_sub`:
  have hroots_K₁ : ∀ j : Fin q, R_G.roots j ∈ V(K₁) :=
    fun j => hZ₀_K₁ (hW_Z₀ (hJ.W_eq ▸ ⟨j, rfl⟩))
  have hroots_G_un : ∀ j : Fin q, R_G.roots j ∈ V(G_un) :=
    fun j => Or.inl (Or.inr (hroots_K₁ j))
  have hroots_G'_un : ∀ j : Fin q, R_G.roots j ∈ V(G'_un) :=
    fun j => Or.inl (Or.inr (hroots_K₁ j))
  let R_G_sub := subRootedDigraph R_G.G G_un hG_un_le R_G.roots hroots_G_un
  let R_G'_sub := subRootedDigraph R_G.G G'_un hG'_un_le R_G.roots hroots_G'_un
  -- Indexed sequence lengths `tLen` and sequences `π`, `π'` for `Fin (t + 1)` via `Fin.cases`:
  let tLen : Fin (t + 1) → ℕ :=
    Fin.cases ((Z₀ \ W).ncard + q) (fun i : Fin t => πLen (A_fam i) + q)
  let π_seq : ∀ i : Fin (t + 1), Fin (tLen i) → α :=
    Fin.cases (motive := fun i => Fin (tLen i) → α)
      (seqConcat π_t1 R_G.roots)
      (fun j => seqConcat (ιV ∘ πS (A_fam j)) R_G.roots)
  let π'_seq : ∀ i : Fin (t + 1), Fin (tLen i) → α :=
    Fin.cases (motive := fun i => Fin (tLen i) → α)
      (seqConcat π_t1 R_G.roots)
      (fun j => seqConcat (fun k : Fin (πLen (A_fam j)) =>
        ιV (πS (A_fam' j) (Fin.cast (hlen j).symm k))) R_G.roots)
  -- Check `IsOrderingOf` for `π_seq` and `π'_seq`:
  have hπ_ord : ∀ i : Fin (t + 1), IsOrderingOf (Z ∩ V(A_div i.succ)) (π_seq i) := by
    intro i
    refine Fin.cases hord_At1 (fun j => hord_A j) i
  have hπ'_ord : ∀ i : Fin (t + 1), IsOrderingOf (Z' ∩ V(A'_div i.succ)) (π'_seq i) := by
    intro i
    exact Fin.cases hord_At1' (fun j => (hord_A' j).seqConcat_finCast (hlen j)) i
  -- Check `HasSameDeltaFolio` for `i : Fin (t + 1)`:
  have hfolio : ∀ (i : Fin (t + 1))
      (hA : A_div i.succ ≤ R_G_sub.G.toGraph) (hA' : A'_div i.succ ≤ R_G'_sub.G.toGraph)
      (hπ : ∀ k : Fin (tLen i), π_seq i k ∈ V(A_div i.succ))
      (hπ' : ∀ k : Fin (tLen i), π'_seq i k ∈ V(A'_div i.succ)),
      HasSameDeltaFolio
        ⟨R_G_sub.G.ofSubgraph (A_div i.succ) hA, π_seq i, hπ⟩
        ⟨R_G'_sub.G.ofSubgraph (A'_div i.succ) hA', π'_seq i, hπ'⟩ δ := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hA hA' hπ hπ' αH' βH' R_H' hDet'
      exact Iff.rfl
    · intro hA hA' hπ hπ' αH' βH' R_H' hDet'
      have hAj_G : A_fam j ≤ R_G.G.toGraph := hJ.le_of_mem_𝒜 (A_fam j) (hA_mem j)
      have hA'j_G : A_fam' j ≤ R_G.G.toGraph := hJ.le_of_mem_𝒜 (A_fam' j) (hA'_mem j)
      exact (h_i j hAj_G hA'j_G hπ hπ' R_H' hDet').symm
  -- Check properties of `α_map := alphaMap73 ιV πS A_fam A_fam' hlen`:
  let α_map := alphaMap73 ιV πS A_fam A_fam' hlen
  have hα_Z' : α_map '' Z' = Z := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨w, hwZ₀ | hwπ', rfl⟩
      · change alphaMap73 ιV πS A_fam A_fam' hlen w ∈ Z
        rw [alphaMap73_apply_of_mem_K₁ hJ hCleanV hA'_mem hlen h_iii (hZ₀_K₁ hwZ₀)]
        exact Or.inl hwZ₀
      · obtain ⟨i, x, ⟨j', rfl⟩, rfl⟩ := mem_iUnion.mp hwπ'
        change alphaMap73 ιV πS A_fam A_fam' hlen (ιV (πS (A_fam' i) j')) ∈ Z
        rw [alphaMap73_apply_πS hJ hA'_mem hlen h_iv i j']
        exact Or.inr (mem_iUnion.mpr ⟨i, ⟨_, ⟨Fin.cast (hlen i) j', rfl⟩, rfl⟩⟩)
    · rintro u (huZ₀ | huπ)
      · refine ⟨u, Or.inl huZ₀, ?_⟩
        exact alphaMap73_apply_of_mem_K₁ hJ hCleanV hA'_mem hlen h_iii (hZ₀_K₁ huZ₀)
      · obtain ⟨i, x, ⟨j, rfl⟩, rfl⟩ := mem_iUnion.mp huπ
        let j' : Fin (πLen (A_fam' i)) := Fin.cast (hlen i).symm j
        refine ⟨ιV (πS (A_fam' i) j'), Or.inr (mem_iUnion.mpr ⟨i, ⟨_, ⟨j', rfl⟩, rfl⟩⟩), ?_⟩
        change alphaMap73 ιV πS A_fam A_fam' hlen (ιV (πS (A_fam' i) j')) = ιV (πS (A_fam i) j)
        rw [alphaMap73_apply_πS hJ hA'_mem hlen h_iv i j']
        simp [j']
  have hα_roots : ∀ j : Fin q, α_map (R_G'_sub.roots j) = R_G_sub.roots j :=
    fun j => alphaMap73_apply_of_mem_K₁ hJ hCleanV hA'_mem hlen h_iii (hroots_K₁ j)
  have hα_π : ∀ i : Fin (t + 1), ∀ k : Fin (tLen i), α_map (π'_seq i k) = π_seq i k := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro k
      have hk_Z₀ : seqConcat π_t1 R_G.roots k ∈ Z₀ := by
        have : seqConcat π_t1 R_G.roots k ∈ Z' ∩ V(A_t1) :=
          hord_At1'.2 ▸ ⟨k, rfl⟩
        exact this.2
      exact alphaMap73_apply_of_mem_K₁ hJ hCleanV hA'_mem hlen h_iii (hZ₀_K₁ hk_Z₀)
    · intro k
      change α_map (seqConcat (fun m : Fin (πLen (A_fam j)) =>
        ιV (πS (A_fam' j) (Fin.cast (hlen j).symm m))) R_G.roots k) =
        seqConcat (ιV ∘ πS (A_fam j)) R_G.roots k
      refine Fin.addCases (fun m => ?_) (fun m => ?_) k
      · simp only [seqConcat, Fin.append_left, Function.comp_apply]
        have := alphaMap73_apply_πS hJ hA'_mem hlen h_iv j (Fin.cast (hlen j).symm m)
        simpa using this
      · simp only [seqConcat, Fin.append_right]
        exact alphaMap73_apply_of_mem_K₁ hJ hCleanV hA'_mem hlen h_iii (hroots_K₁ m)
  -- Check `(φV, φE)` is a model in `R_G_sub`, with edges and branch sets meeting `⋃ i, A_div i.succ`:
  have h1 := lemma_7_3_claim_1 hJ hAdeq hA_mem_ℬ hdist_other
  have hφ_le_G_un : ∀ v ∈ V(R_H.G.toGraph), φV v ≤ G_un := by
    intro v hv
    have hP_le : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
      rintro _ ⟨w, hw, rfl⟩
      exact hJ.isModel.subgraph_of_mem w hw
    have hno_le_G : Graph.noEdge π_bar_union β ≤ R_G.G.toGraph := by
      refine ⟨?_, fun _ _ _ h => False.elim h⟩
      rintro _ ⟨_, ⟨i, rfl⟩, x, ⟨j, rfl⟩, rfl⟩
      exact (hJ.le_of_mem_𝒜 (A_fam i) (hA_mem i)).vertexSet_mono
        ((hJ.π_valid (A_fam i) (hA_mem i)).2.2.2 j).1
    have hφ_le_L : φV v ≤ graphUnion (Graph.noEdge π_bar_union β)
        (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) :=
      (le_subgraphSUnion hP_le ⟨v, hv, rfl⟩).trans
        (le_graphUnion_right (Compatible.of_le_le hno_le_G (subgraphSUnion_le hP_le)))
    exact hφ_le_L.trans h1.1
  have hφE_G_un : ∀ e ∈ E(R_H.G.toGraph), φE e ∈ E(G_un) := by
    intro e he
    rcases h1.2 ⟨e, he, rfl⟩ with heK₁ | heAu
    · exact Or.inl (Or.inr heK₁)
    · exact Or.inr heAu
  have hMod_sub : IsRootedDigraphModel R_G_sub R_H φV φE :=
    ⟨hφ_le_G_un, hJ.isModel.connected_of_mem, hJ.isModel.disjoint_V, hJ.isModel.root_mem,
      hφE_G_un, hJ.isModel.injOn_E, hJ.isModel.edge_not_mem_φV,
      hJ.isModel.head_mem, hJ.isModel.tail_mem⟩
  have hφE_in_div : φE '' E(R_H.G.toGraph) ⊆ ⋃ i : Fin (t + 1), E(A_div i.succ) := by
    rintro _ ⟨e, he, rfl⟩
    rcases h1.2 ⟨e, he, rfl⟩ with heK₁ | heAu
    · rw [mem_iUnion]
      exact ⟨0, ⟨⟨e, he, rfl⟩, heK₁⟩⟩
    · rw [edgeSet_subgraphSUnion hA_range_le, mem_iUnion₂] at heAu
      rcases heAu with ⟨_, ⟨j, rfl⟩, hej⟩
      rw [mem_iUnion]
      exact ⟨j.succ, hej⟩
  have hφV_meets_div : ∀ v ∈ V(R_H.G.toGraph),
      (V(φV v) ∩ ⋃ i : Fin (t + 1), V(A_div i.succ)).Nonempty := by
    intro v hv
    obtain ⟨u, huφ, huZ₀ | huAu⟩ := hZ₀_meets v hv
    · exact ⟨u, huφ, mem_iUnion.mpr ⟨0, huZ₀⟩⟩
    · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at huAu
      rcases huAu with ⟨_, ⟨j, rfl⟩, huj⟩
      exact ⟨u, huφ, mem_iUnion.mpr ⟨j.succ, huj⟩⟩
  -- Check `L = graphUnion (Graph.noEdge Z β) L_model` equals `L_c3`:
  let L_model := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
  let L_full := graphUnion (Graph.noEdge Z β) L_model
  let L_c3 := graphUnion (Graph.noEdge π_bar_union β) L_model
  have hL_eq : L_full = L_c3 := by
    refine Graph.ext ?_ fun e x y => ?_
    · change (Z₀ ∪ π_bar_union) ∪ V(L_model) = π_bar_union ∪ V(L_model)
      rw [union_right_comm, union_eq_self_of_subset_left hZ₀_L, Set.union_comm]
    · simp [L_full, L_c3, graphUnion]
  -- Check `L'₀ ≤ A'₀`:
  have hL'₀_disj_Et1 : Disjoint E(L'₀) E_t1 := by
    rw [disjoint_left]
    rintro e heL'₀ ⟨heφ, heK₁⟩
    have heAu : e ∈ E(subgraphSUnion R_G.G.toGraph (Set.range A_fam)) :=
      hL'₀_edges ⟨heL'₀, heφ⟩
    rw [edgeSet_subgraphSUnion hA_range_le, mem_iUnion₂] at heAu
    rcases heAu with ⟨_, ⟨j, rfl⟩, hej⟩
    have hAj_K₁ := hJ.inter_K₁_eq_noEdge_of_disjoint_Δ (hA_mem j) (h_ii j)
    obtain ⟨x, y, hlAj⟩ := (A_fam j).exists_isLink_of_mem_edgeSet hej
    have hlG : R_G.G.toGraph.IsLink e x y := hlAj.mono (hJ.le_of_mem_𝒜 (A_fam j) (hA_mem j))
    have hlK₁ : K₁.IsLink e x y := (hK₁_le.isLink_iff heK₁).mpr hlG
    have hl_inter : (A_fam j ⊓ K₁).IsLink e x y := ⟨hlAj, hlK₁⟩
    rw [hAj_K₁] at hl_inter
    exact hl_inter
  have hL'₀_le_A'₀ : L'₀ ≤ A'_div 0 := by
    change L'₀ ≤ A'₀
    refine ⟨?_, fun e x y hl => ?_⟩
    · rw [vertexSet_deleteEdges]
      exact hL'₀_le.vertexSet_mono
    · rw [deleteEdges_isLink]
      exact ⟨hl.mono hL'₀_le, disjoint_left.mp hL'₀_disj_Et1 hl.edge_mem⟩
  -- Check `L_full ⊓ A_div 0 = graphUnion L₀_ext (L_c3 ⊓ K₁)`:
  have hL_disj_Et1 : Disjoint E(L_c3) E_t1 := by
    rw [disjoint_left]
    rintro e heL ⟨⟨eH, heH, rfl⟩, _⟩
    simp only [L_c3, edgeSet_graphUnion, Graph.edgeSet_noEdge, empty_union] at heL
    have hP_le : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
      rintro _ ⟨w, hw, rfl⟩
      exact hJ.isModel.subgraph_of_mem w hw
    rw [edgeSet_subgraphSUnion hP_le, mem_iUnion₂] at heL
    rcases heL with ⟨_, ⟨v, hv, rfl⟩, he_φv⟩
    exact hJ.isModel.edge_not_mem_φV eH heH v hv he_φv
  have hΓ₀_le_Γ : Γ₀.toEmbeddedGraph ιV ιE ≤ Γ.toEmbeddedGraph ιV ιE :=
    toEmbeddedGraph_le_of_isSubdrawing interSet_isSub ιV ιE
  have hπ_sub_Fun : π_bar_union ⊆ V(subgraphSUnion R_G.G.toGraph (Set.range A_fam)) := by
    rintro _ ⟨_, ⟨i, rfl⟩, x, ⟨j, rfl⟩, rfl⟩
    have hx_Fi : ιV (πS (A_fam i) j) ∈ V(A_fam i) := ((hJ.π_valid (A_fam i) (hA_mem i)).2.2.2 j).1
    exact (le_subgraphSUnion hA_range_le ⟨i, rfl⟩).vertexSet_mono hx_Fi
  have hnoEdge_le_Fun : Graph.noEdge π_bar_union β ≤ subgraphSUnion R_G.G.toGraph (Set.range A_fam) :=
    ⟨hπ_sub_Fun, fun _ _ _ h => False.elim h⟩
  have hL_inter_A₀ : L_full ⊓ A_div 0 =
      graphUnion (graphUnion (L_c3 ⊓ Γ₀.toEmbeddedGraph ιV ιE) (Graph.noEdge π_bar_union β))
        (L_c3 ⊓ K₁) := by
    rw [hL_eq]
    exact inter_deleteEdges_graphUnion_noEdge_eq (h1.1.trans hG_un_le)
      (hΓ₀_le_Γ.trans hΓ_le) (hnoEdge_le_Fun.trans (subgraphSUnion_le hA_range_le)) hK₁_le
      (fun _ hu => Or.inl hu) hL_disj_Et1
  have h9' : ∀ u' ∈ Z', ∀ v' ∈ Z',
      AreConnectedIn L'₀ u' v' ↔ AreConnectedIn (L_full ⊓ A_div 0) (α_map u') (α_map v') := by
    intro u' hu' v' hv'
    rw [hL_inter_A₀]
    exact h9 u' hu' v' hv'
  -- Apply 6.3 (`h63`):
  have hroots_Z : ∀ j : Fin q, R_G_sub.roots j ∈ Z := by
    intro j
    refine Or.inl (hW_Z₀ ?_)
    rw [hJ.W_eq]
    exact ⟨j, rfl⟩
  have hroots_Z' : ∀ j : Fin q, R_G'_sub.roots j ∈ Z' := by
    intro j
    refine Or.inl (hW_Z₀ ?_)
    rw [hJ.W_eq]
    exact ⟨j, rfl⟩
  have hL_full_sub : L_full =
      graphUnion (Graph.noEdge Z β) (subgraphSUnion R_G_sub.G.toGraph (φV '' V(R_H.G.toGraph))) := by
    have hP_sub : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ G_un := by
      rintro _ ⟨w, hw, rfl⟩
      exact hφ_le_G_un w hw
    change graphUnion (Graph.noEdge Z β) (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) =
      graphUnion (Graph.noEdge Z β) (subgraphSUnion G_un (φV '' V(R_H.G.toGraph)))
    rw [subgraphSUnion_eq_of_le hP_sub hG_un_le]
  obtain ⟨φ'V, φ'E, hMod', hφ'E_sub, hφ'V_meets⟩ :=
    theorem_6_3_parallel.{u, v, u₁, v₁, u} R_G_sub R_G'_sub R_H Z A_div tLen π_seq Z' A'_div π'_seq α_map φV φE L_full L'₀
      (hJ.finite_V.subset hG_un_le.vertexSet_mono)
      (hJ.finite_E.subset hG_un_le.edgeSet_mono)
      (hJ.finite_V.subset hG'_un_le.vertexSet_mono)
      (hJ.finite_E.subset hG'_un_le.edgeSet_mono)
      (hZ_sub_A₀.trans (hDiv.1 0).vertexSet_mono)
      hroots_Z
      hDiv
      hZ_sub_A₀
      hπ_ord
      (hZ'_sub_A'₀.trans (hDiv'.1 0).vertexSet_mono)
      hroots_Z'
      hDiv'
      hZ'_sub_A'₀
      hπ'_ord
      hJ.detail_H
      hfolio
      hα_Z'
      hα_roots
      hα_π
      hMod_sub
      hφE_in_div
      hφV_meets_div
      hL_full_sub
      hL'₀_le_A'₀
      h9'
  -- Unpack conclusion of 6.3:
  have hMod'_G : IsRootedDigraphModel R_G R_H φ'V φ'E :=
    ⟨fun v hv => (hMod'.subgraph_of_mem v hv).trans hG'_un_le,
      hMod'.connected_of_mem, hMod'.disjoint_V, hMod'.root_mem,
      fun e he => hG'_un_le.edgeSet_mono (hMod'.edge_mem e he),
      hMod'.injOn_E, hMod'.edge_not_mem_φV, hMod'.head_mem, hMod'.tail_mem⟩
  refine ⟨φ'V, φ'E, hMod'_G, hMod'.subgraph_of_mem, ?_, ?_⟩
  · intro e he
    have he_u := hφ'E_sub he
    rw [mem_iUnion] at he_u
    rcases he_u with ⟨i, hei⟩
    refine Fin.cases (motive := fun i : Fin (t + 1) =>
        e ∈ E(A'_div i.succ) → e ∈ E_t1 ∪ ⋃ j : Fin t, E(A_fam' j))
      (fun h => Or.inl h)
      (fun j h => Or.inr (mem_iUnion.mpr ⟨j, h⟩)) i hei
  · intro v hv
    obtain ⟨u, huφ', hu_u⟩ := hφ'V_meets v hv
    rw [mem_iUnion] at hu_u
    rcases hu_u with ⟨i, hui⟩
    refine ⟨u, huφ', ?_⟩
    refine Fin.cases (motive := fun i : Fin (t + 1) =>
        u ∈ V(A'_div i.succ) → u ∈ Z₀ ∪ ⋃ j : Fin t, V(A_fam' j))
      (fun h => Or.inl h)
      (fun j h => Or.inr (mem_iUnion.mpr ⟨j, h⟩)) i hui

end GraphMinor.GM22
