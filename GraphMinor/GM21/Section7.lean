module

public import GraphMinor.GM21.Section6
public import GraphMinor.GM17.Section4

/-!
# Section 7 of Graph Minors XXI: Presentations and Tree-Width (`(7.1)` and `(7.2)`)

This file formalizes `(7.1)` (`theorem_7_1`) and `(7.2)` (`theorem_7_2`, together with its
subproof Claim `(1)`, `theorem_7_2_claim_1`) from Section 7 (pages 29–31 of the preprint)
of N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*, J. Combin. Theory Ser. B 99 (2009), 583–616.
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Topology Classical
open GraphMinor.Surface
open GraphMinor.Hypergraph
open GraphMinor.GM10
open GraphMinor.GM17
open GraphMinor.GM19 hiding Drawing
open GraphMinor.GM21.Supports

universe u v w

section Section7

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-! ## 1. Graph Minors XXI, `(7.1)`: Characterizations of Small Subgraphs -/

/-- **Graph Minors XXI, (7.1)** (pages 29–30 of the preprint):
"If $\mathcal{T}$ is a tangle in $G$, and $A \subseteq G$, then the following are equivalent:
(i) $A$ is small with respect to $\mathcal{T}$;
(ii) if $X$ denotes the set of vertices of $A$ incident with edges of $G$ not $A$, then
$|X| < ord(\mathcal{T})$, and $(A, B) \in \mathcal{T}$ where
$V(B) = (V(G) \setminus V(A)) \cup X$ and $E(B) = E(G) \setminus E(A)$;
(iii) there is a separation $(A, B)$ of order $< ord(\mathcal{T})$, and $\mathcal{T}$ contains
every such separation."
The first part says (i) and (ii) are equivalent, the second part says (ii) and (iii) are. -/
theorem theorem_7_1_proof
    {G A : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : GM10.IsTangle G θ 𝒯) (hA : A ≤ G) :
    (IsSmallSubgraph 𝒯 A ↔
      ((GM17.attachments G A).ncard < θ ∧ (A, GM17.complSubhypergraph G A) ∈ 𝒯)) ∧
    (((GM17.attachments G A).ncard < θ ∧ (A, GM17.complSubhypergraph G A) ∈ 𝒯) ↔
      ((∃ B : Hypergraph α β, G.IsSeparation A B ∧ Hypergraph.separationOrder A B < θ) ∧
        ∀ B : Hypergraph α β, G.IsSeparation A B →
          Hypergraph.separationOrder A B < θ → (A, B) ∈ 𝒯)) := by
  have hsep_compl : G.IsSeparation A (GM17.complSubhypergraph G A) :=
    GM17.isSeparation_complSubhypergraph hA
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hsmall
    have hSmallWrt : GM17.IsSmallWrt 𝒯 A := hsmall
    have hatt : (GM17.attachments G A).ncard < θ := hSmallWrt.ncard_attachments_lt h𝒯
    have hord : Hypergraph.separationOrder A (GM17.complSubhypergraph G A) < θ := by
      rwa [GM17.separationOrder_complSubhypergraph]
    exact ⟨hatt, GM17.theorem_4_1_i h𝒯 hSmallWrt hsep_compl hord⟩
  · rintro ⟨_, hmem⟩
    exact ⟨GM17.complSubhypergraph G A, hmem⟩
  · rintro ⟨hatt, hmem⟩
    have hord : Hypergraph.separationOrder A (GM17.complSubhypergraph G A) < θ := by
      rwa [GM17.separationOrder_complSubhypergraph]
    have hSmallWrt : GM17.IsSmallWrt 𝒯 A := ⟨GM17.complSubhypergraph G A, hmem⟩
    exact ⟨⟨_, hsep_compl, hord⟩, fun B hsep hordB ↦ GM17.theorem_4_1_i h𝒯 hSmallWrt hsep hordB⟩
  · rintro ⟨⟨B, hsepB, hordB⟩, hall⟩
    have hatt : (GM17.attachments G A).ncard < θ :=
      (GM17.ncard_attachments_le_separationOrder hsepB).trans_lt hordB
    have hord : Hypergraph.separationOrder A (GM17.complSubhypergraph G A) < θ := by
      rwa [GM17.separationOrder_complSubhypergraph]
    exact ⟨hatt, hall _ hsep_compl hord⟩

/-! ## 2. Support & Space Helper Lemmas for Section 7 -/

/-- Every support `F` of `Γ` in `S` is contained in `bd S`. -/
lemma support_subset_bd {Γ : Surface.Drawing S} {F : Set S} (hF : IsSupportOfDrawing Γ F) :
    F ⊆ bd S := by
  rcases hF with ⟨_, _, ⟨_, hv, rfl, _, _⟩ | ⟨hsub, _⟩⟩
  · exact singleton_subset_iff.2 hv.2
  · exact hsub

/-- Two spaces in `drawingSpaces Γ` that share a point are equal. -/
lemma eq_of_mem_drawingSpaces_of_mem {Γ : Surface.Drawing S} {s₁ s₂ : Set S} {x : S}
    (hs₁ : s₁ ∈ drawingSpaces Γ) (hs₂ : s₂ ∈ drawingSpaces Γ)
    (hx₁ : x ∈ s₁) (hx₂ : x ∈ s₂) : s₁ = s₂ := by
  rcases hs₁ with ⟨y₁, _, rfl⟩
  rcases hs₂ with ⟨y₂, _, rfl⟩
  exact (connectedComponentIn_eq hx₁).trans (connectedComponentIn_eq hx₂).symm

/-- The set of spaces `drawingSpaces Γ` of a presentation is finite. -/
theorem IsPresentation.spaces_finite
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    (drawingSpaces Γ).Finite :=
  drawingSpaces_finite h_pres.is_surface h_pres.cuff_vertices_ge_two

/-- The set of spaces `drawingSpaces Γ` of a presentation of depth `≤ d` is finite. -/
theorem PresentationHasDepthLe.spaces_finite
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {d : ℕ}
    (h_depth : PresentationHasDepthLe G Γ Γ_sub ιV ιE r F_star H μ d) :
    (drawingSpaces Γ).Finite :=
  let ⟨_, h_pres, _, _⟩ := h_depth
  h_pres.spaces_finite

/-- `IsPresentation` gives `BijOn ιE Γ.E Γ_sub.edgeSet` and the edge-vertex incidence equivalence. -/
theorem IsPresentation.bijOn_ιE_and_inc_iff
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    BijOn ιE Γ.E Γ_sub.edgeSet ∧
      ∀ e ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE e) (ιV u) ↔ u ∈ closure e :=
  ⟨⟨h_pres.ιE_image ▸ mapsTo_image ιE Γ.E, h_pres.ιE_injOn, h_pres.ιE_image ▸ surjOn_image ιE Γ.E⟩,
    h_pres.inc_iff⟩

/-- Every support `F_star j` of a presentation can be parameterized as `cuffPoint f '' Icc t₀ t₁`
on some cuff `C ∈ cuffs S`. -/
lemma support_param_of_isPresentation
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r) :
    ∃ (C : Set S) (_hC : C ∈ cuffs S) (f : Circle ≃ₜ C) (t₀ t₁ : ℝ),
      t₀ ≤ t₁ ∧ t₁ < t₀ + 2 * Real.pi ∧
      cuffPoint f t₀ ∈ Γ.V ∩ C ∧ cuffPoint f t₁ ∈ Γ.V ∧
      F_star j = cuffPoint f '' Icc t₀ t₁ := by
  have hS := h_pres.is_surface
  rcases h_pres.supports_isSupport j with ⟨endA, endB, hFj_ends⟩
  obtain ⟨C, hC, hFjC⟩ := exists_cuff_of_supportHasEnds hFj_ends
  let f := cuffHomeo hS hC
  have hends_Fj := ends_mem_of_supportHasEnds hFj_ends
  obtain ⟨t₀, _, t₁, ⟨hle, hlt⟩, h_ab_Fj, hFj_eq, _⟩ :=
    support_eq_cuffPoint_Icc hS hC f hFj_ends hFjC
  have ht₀_mem : cuffPoint f t₀ ∈ Γ.V ∩ C := by
    refine ⟨?_, cuffPoint_mem f t₀⟩
    rcases h_ab_Fj with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact hends_Fj.2.2.1.1
    · exact hends_Fj.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases h_ab_Fj with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
    · exact hends_Fj.2.2.2.1.1
    · exact hends_Fj.2.2.1.1
  exact ⟨C, hC, f, t₀, t₁, hle, hlt, ht₀_mem, ht₁V, hFj_eq⟩

/-- Any two distinct spaces `s₁, s₂ ⊆ F_star j` have a vertex `u ∈ Γ.V ∩ F_star j` lying between
them in `F_star j`. -/
lemma exists_liesBetweenInSupport_of_ne
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
    {s₁ s₂ : Set S} (hs₁ : s₁ ∈ drawingSpaces Γ) (hs₂ : s₂ ∈ drawingSpaces Γ)
    (hs₁F : s₁ ⊆ F_star j) (hs₂F : s₂ ⊆ F_star j) (hne : s₁ ≠ s₂) :
    ∃ u ∈ Γ.V ∩ F_star j,
      LiesBetweenInSupport Γ (F_star j) s₁ s₂ u ∨
      LiesBetweenInSupport Γ (F_star j) s₂ s₁ u := by
  obtain ⟨C, hC, f, t₀, t₁, hle, hlt, ht₀, ht₁V, hF_eq⟩ :=
    support_param_of_isPresentation h_pres j
  obtain ⟨α₁, β₁, hα₁, hαβ₁, hβ₁, hα₁V, hβ₁V, _, hs₁_eq, _⟩ :=
    space_in_support_eq_Ioo h_pres.is_surface h_pres.cuff_vertices_ge_two
      hC f hle hlt ht₀ hF_eq hs₁ hs₁F
  obtain ⟨α₂, β₂, hα₂, hαβ₂, hβ₂, hα₂V, hβ₂V, _, hs₂_eq, _⟩ :=
    space_in_support_eq_Ioo h_pres.is_surface h_pres.cuff_vertices_ge_two
      hC f hle hlt ht₀ hF_eq hs₂ hs₂F
  have h_order : β₁ ≤ α₂ ∨ β₂ ≤ α₁ := by
    by_contra hnot
    push Not at hnot
    have hmax_lt_min : max α₁ α₂ < min β₁ β₂ :=
      max_lt (lt_min hαβ₁ hnot.2) (lt_min hnot.1 hαβ₂)
    set m := (max α₁ α₂ + min β₁ β₂) / 2 with hm_def
    have hm₁ : α₁ < m ∧ m < β₁ := by
      constructor <;> linarith [le_max_left α₁ α₂, min_le_left β₁ β₂]
    have hm₂ : α₂ < m ∧ m < β₂ := by
      constructor <;> linarith [le_max_right α₁ α₂, min_le_right β₁ β₂]
    have hm_s₁ : cuffPoint f m ∈ s₁ := by rw [hs₁_eq]; exact ⟨m, hm₁, rfl⟩
    have hm_s₂ : cuffPoint f m ∈ s₂ := by rw [hs₂_eq]; exact ⟨m, hm₂, rfl⟩
    exact hne (eq_of_mem_drawingSpaces_of_mem hs₁ hs₂ hm_s₁ hm_s₂)
  rcases h_order with h12 | h21
  · exact ⟨cuffPoint f β₁, hβ₁V, Or.inl
      (liesBetweenInSupport_of_angles h_pres.is_surface hC f hlt ht₀.1 ht₁V hF_eq
        hs₁ hs₂ hα₁ hαβ₁ le_rfl h12 hαβ₂ hβ₂ hs₁_eq hs₂_eq hβ₁V.1)⟩
  · exact ⟨cuffPoint f β₂, hβ₂V, Or.inr
      (liesBetweenInSupport_of_angles h_pres.is_surface hC f hlt ht₀.1 ht₁V hF_eq
        hs₂ hs₁ hα₂ hαβ₂ le_rfl h21 hαβ₁ hβ₁ hs₂_eq hs₁_eq hβ₂V.1)⟩

/-- Subadditivity of `ncard` over a finite indexed union. -/
lemma ncard_biUnion_le_sum {ι γ : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Set γ)
    (hf : ∀ i ∈ s, (f i).Finite) :
    (⋃ i ∈ s, f i).ncard ≤ ∑ i ∈ s, (f i).ncard := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    have hf_s' : ∀ i ∈ s', (f i).Finite := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (ncard_union_le (f a) (⋃ i ∈ s', f i)).trans (Nat.add_le_add_left (ih hf_s') _)

/-! ## 3. The Subgraph Map `σ(A)` and Claim `(1)` of `(7.2)` -/

/-- Graph Minors XXI, proof of `(7.2)` (page 30 of the preprint):
"$\Gamma^+$ has the same vertex set as $\Gamma$, and its edges are the edges and spaces of $\Gamma$.
Let $S(\Gamma)$ be the set of spaces of $\Gamma$. For any subgraph $A$ of $\Gamma^+$ we define
$\sigma(A)$ to be the union of $A \cap \Gamma$ with all the graphs $\mu(v)$
($v \in V(A) \cap bd(\Sigma)$) and $\mu(s)$ ($s \in E(A) \cap S(\Gamma)$)."

Here `ιV : S → α` and `ιE : Set S → β` identify `Γ.V` and `Γ.E` with `Γ_sub.vertexSet` and
`Γ_sub.edgeSet`, and spaces `s ∈ E(A) ∩ S(Γ)` that lie in one of the supports `F_star j`
contribute `μ (.space s)`. -/
def sigmaSubgraph
    (G : Hypergraph α β) (Γ : Surface.Drawing S) (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S) (μ : BoundaryUnit S → Hypergraph α β)
    (A : Hypergraph S (Set S)) : Hypergraph α β where
  vertexSet := G.vertexSet ∩
    (ιV '' (A.vertexSet ∩ Γ.V) ∪
     (⋃ u ∈ A.vertexSet ∩ (Γ.V ∩ bd S), (μ (.vertex u)).vertexSet) ∪
     (⋃ j : Fin r, ⋃ s ∈ {s ∈ A.edgeSet ∩ drawingSpaces Γ | s ⊆ F_star j},
       (μ (.space s)).vertexSet))
  edgeSet := G.edgeSet ∩
    (ιE '' (A.edgeSet ∩ Γ.E) ∪
     (⋃ u ∈ A.vertexSet ∩ (Γ.V ∩ bd S), (μ (.vertex u)).edgeSet) ∪
     (⋃ j : Fin r, ⋃ s ∈ {s ∈ A.edgeSet ∩ drawingSpaces Γ | s ⊆ F_star j},
       (μ (.space s)).edgeSet))
  Inc e v := G.Inc e v ∧
    v ∈ G.vertexSet ∩
      (ιV '' (A.vertexSet ∩ Γ.V) ∪
       (⋃ u ∈ A.vertexSet ∩ (Γ.V ∩ bd S), (μ (.vertex u)).vertexSet) ∪
       (⋃ j : Fin r, ⋃ s ∈ {s ∈ A.edgeSet ∩ drawingSpaces Γ | s ⊆ F_star j},
         (μ (.space s)).vertexSet)) ∧
    e ∈ G.edgeSet ∩
      (ιE '' (A.edgeSet ∩ Γ.E) ∪
       (⋃ u ∈ A.vertexSet ∩ (Γ.V ∩ bd S), (μ (.vertex u)).edgeSet) ∪
       (⋃ j : Fin r, ⋃ s ∈ {s ∈ A.edgeSet ∩ drawingSpaces Γ | s ⊆ F_star j},
         (μ (.space s)).edgeSet))
  vertex_mem_of_inc _ _ h := h.2.1
  edge_mem_of_inc _ _ h := h.2.2
  vertexSet_finite := G.vertexSet_finite.subset inter_subset_left
  edgeSet_finite := G.edgeSet_finite.subset inter_subset_left

/-- For every `u ∈ Γ.V ∩ bd S`, there is some `j : Fin r` such that `u ∈ Γ.V ∩ F_star j`,
so `μ (.vertex u) ≤ G`, `(μ (.vertex u)).edgeSet = ∅`, and `(μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet = {ιV u}`. -/
lemma mu_vertex_props_of_mem_bd
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    {u : S} (hu : u ∈ Γ.V ∩ bd S) :
    ∃ j : Fin r, u ∈ Γ.V ∩ F_star j ∧
      μ (.vertex u) ≤ G ∧
      (μ (.vertex u)).edgeSet = ∅ ∧
      (μ (.vertex u)).vertexSet.ncard = q j ∧
      (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet = {ιV u} := by
  have huF : u ∈ ⋃ j : Fin r, F_star j := h_pres.bd_vertices_covered hu
  rcases mem_iUnion.1 huF with ⟨j, huj⟩
  have hu_in : u ∈ Γ.V ∩ F_star j := ⟨hu.1, huj⟩
  obtain ⟨hleH, hedge, hcard, hinter⟩ := h_pres.μ_vertex_sub j u hu_in
  exact ⟨j, hu_in, hleH.trans (h_pres.v1_sub j), hedge, hcard, hinter⟩

/-- If `A ≤ drawingPlusHypergraph Γ h_spaces_fin`, then `sigmaSubgraph G Γ ιV ιE r F_star μ A ≤ G`. -/
lemma sigmaSubgraph_le
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_iso : BijOn ιE Γ.E Γ_sub.edgeSet ∧
      ∀ d ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE d) (ιV u) ↔ u ∈ closure d)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    {A : Hypergraph S (Set S)} (hA : A ≤ drawingPlusHypergraph Γ h_spaces_fin) :
    sigmaSubgraph G Γ ιV ιE r F_star μ A ≤ G where
  vertexSet_subset := inter_subset_left
  edgeSet_subset := inter_subset_left
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq]
    dsimp only [sigmaSubgraph]
    refine ⟨fun hinc => ⟨hinc, ?_, he⟩, fun h => h.1⟩
    refine ⟨G.vertex_mem_of_inc hinc, ?_⟩
    rcases he with ⟨_, (he_draw | he_vert) | he_space⟩
    · rcases he_draw with ⟨d, ⟨hdA, hdE⟩, rfl⟩
      have hd_in_sub : ιE d ∈ Γ_sub.edgeSet := h_iso.1.mapsTo hdE
      have hinc_sub : Γ_sub.Inc (ιE d) v :=
        (inc_iff_of_le h_pres.drawing_subgraph hd_in_sub).2 hinc
      have hv_sub : v ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hinc_sub
      rw [← h_pres.ιV_image] at hv_sub
      rcases hv_sub with ⟨u, huV, rfl⟩
      have hu_cl : u ∈ closure d := (h_iso.2 d hdE u huV).1 hinc_sub
      have hinc_plus : (drawingPlusHypergraph Γ h_spaces_fin).Inc d u :=
        ⟨Or.inl hdE, huV, hu_cl⟩
      have hinc_A : A.Inc d u := (inc_iff_of_le hA hdA).2 hinc_plus
      have huA : u ∈ A.vertexSet := A.vertex_mem_of_inc hinc_A
      exact Or.inl (Or.inl ⟨u, ⟨huA, huV⟩, rfl⟩)
    · rw [mem_iUnion₂] at he_vert
      rcases he_vert with ⟨u, ⟨_, hu_bd⟩, he_u⟩
      obtain ⟨_, _, _, hedge_empty, _, _⟩ := mu_vertex_props_of_mem_bd h_pres hu_bd
      rw [hedge_empty] at he_u
      exact False.elim he_u
    · rw [mem_iUnion] at he_space
      rcases he_space with ⟨j, he_j⟩
      rw [mem_iUnion₂] at he_j
      rcases he_j with ⟨s, ⟨⟨hsA, hs_sp⟩, hsF⟩, he_s⟩
      have hs_le : μ (.space s) ≤ G :=
        (h_pres.μ_space_sub j s hs_sp hsF).trans (h_pres.v1_sub j)
      have hinc_s : (μ (.space s)).Inc e v := (inc_iff_of_le hs_le he_s).2 hinc
      have hv_s : v ∈ (μ (.space s)).vertexSet := (μ (.space s)).vertex_mem_of_inc hinc_s
      refine Or.inr ?_
      rw [mem_iUnion]
      refine ⟨j, ?_⟩
      rw [mem_iUnion₂]
      exact ⟨s, ⟨⟨hsA, hs_sp⟩, hsF⟩, hv_s⟩

/-- `sigmaSubgraph` commutes with binary union of subgraphs of `Γ^+`. -/
lemma sigmaSubgraph_union
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_iso : BijOn ιE Γ.E Γ_sub.edgeSet ∧
      ∀ d ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE d) (ιV u) ↔ u ∈ closure d)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    {A₁ A₂ : Hypergraph S (Set S)}
    (hA₁ : A₁ ≤ drawingPlusHypergraph Γ h_spaces_fin)
    (hA₂ : A₂ ≤ drawingPlusHypergraph Γ h_spaces_fin) :
    sigmaSubgraph G Γ ιV ιE r F_star μ (A₁ ∪ A₂) =
      sigmaSubgraph G Γ ιV ιE r F_star μ A₁ ∪ sigmaSubgraph G Γ ιV ιE r F_star μ A₂ := by
  have hle_u : sigmaSubgraph G Γ ιV ιE r F_star μ (A₁ ∪ A₂) ≤ G :=
    sigmaSubgraph_le h_pres h_iso h_spaces_fin (union_le hA₁ hA₂)
  have hle_1 : sigmaSubgraph G Γ ιV ιE r F_star μ A₁ ≤ G :=
    sigmaSubgraph_le h_pres h_iso h_spaces_fin hA₁
  have hle_2 : sigmaSubgraph G Γ ιV ιE r F_star μ A₂ ≤ G :=
    sigmaSubgraph_le h_pres h_iso h_spaces_fin hA₂
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_u (union_le hle_1 hle_2)
  · ext v
    simp only [sigmaSubgraph, union_vertexSet, mem_inter_iff, mem_union, mem_image,
      mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hvG, (⟨u, ⟨hu1 | hu2, huV⟩, rfl⟩ | ⟨u, ⟨hu1 | hu2, hu_bd⟩, hvu⟩) |
        ⟨j, s, ⟨⟨hs1 | hs2, hs_sp⟩, hsF⟩, hvs⟩⟩
      · exact Or.inl ⟨hvG, Or.inl (Or.inl ⟨u, ⟨hu1, huV⟩, rfl⟩)⟩
      · exact Or.inr ⟨hvG, Or.inl (Or.inl ⟨u, ⟨hu2, huV⟩, rfl⟩)⟩
      · exact Or.inl ⟨hvG, Or.inl (Or.inr ⟨u, ⟨hu1, hu_bd⟩, hvu⟩)⟩
      · exact Or.inr ⟨hvG, Or.inl (Or.inr ⟨u, ⟨hu2, hu_bd⟩, hvu⟩)⟩
      · exact Or.inl ⟨hvG, Or.inr ⟨j, s, ⟨⟨hs1, hs_sp⟩, hsF⟩, hvs⟩⟩
      · exact Or.inr ⟨hvG, Or.inr ⟨j, s, ⟨⟨hs2, hs_sp⟩, hsF⟩, hvs⟩⟩
    · rintro (⟨hvG, (⟨u, ⟨hu1, huV⟩, rfl⟩ | ⟨u, ⟨hu1, hu_bd⟩, hvu⟩) |
        ⟨j, s, ⟨⟨hs1, hs_sp⟩, hsF⟩, hvs⟩⟩ |
        ⟨hvG, (⟨u, ⟨hu2, huV⟩, rfl⟩ | ⟨u, ⟨hu2, hu_bd⟩, hvu⟩) |
        ⟨j, s, ⟨⟨hs2, hs_sp⟩, hsF⟩, hvs⟩⟩)
      · exact ⟨hvG, Or.inl (Or.inl ⟨u, ⟨Or.inl hu1, huV⟩, rfl⟩)⟩
      · exact ⟨hvG, Or.inl (Or.inr ⟨u, ⟨Or.inl hu1, hu_bd⟩, hvu⟩)⟩
      · exact ⟨hvG, Or.inr ⟨j, s, ⟨⟨Or.inl hs1, hs_sp⟩, hsF⟩, hvs⟩⟩
      · exact ⟨hvG, Or.inl (Or.inl ⟨u, ⟨Or.inr hu2, huV⟩, rfl⟩)⟩
      · exact ⟨hvG, Or.inl (Or.inr ⟨u, ⟨Or.inr hu2, hu_bd⟩, hvu⟩)⟩
      · exact ⟨hvG, Or.inr ⟨j, s, ⟨⟨Or.inr hs2, hs_sp⟩, hsF⟩, hvs⟩⟩
  · ext e
    simp only [sigmaSubgraph, union_edgeSet, mem_inter_iff, mem_union, mem_image,
      mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨heG, (⟨d, ⟨hd1 | hd2, hdE⟩, rfl⟩ | ⟨u, ⟨hu1 | hu2, hu_bd⟩, heu⟩) |
        ⟨j, s, ⟨⟨hs1 | hs2, hs_sp⟩, hsF⟩, hes⟩⟩
      · exact Or.inl ⟨heG, Or.inl (Or.inl ⟨d, ⟨hd1, hdE⟩, rfl⟩)⟩
      · exact Or.inr ⟨heG, Or.inl (Or.inl ⟨d, ⟨hd2, hdE⟩, rfl⟩)⟩
      · exact Or.inl ⟨heG, Or.inl (Or.inr ⟨u, ⟨hu1, hu_bd⟩, heu⟩)⟩
      · exact Or.inr ⟨heG, Or.inl (Or.inr ⟨u, ⟨hu2, hu_bd⟩, heu⟩)⟩
      · exact Or.inl ⟨heG, Or.inr ⟨j, s, ⟨⟨hs1, hs_sp⟩, hsF⟩, hes⟩⟩
      · exact Or.inr ⟨heG, Or.inr ⟨j, s, ⟨⟨hs2, hs_sp⟩, hsF⟩, hes⟩⟩
    · rintro (⟨heG, (⟨d, ⟨hd1, hdE⟩, rfl⟩ | ⟨u, ⟨hu1, hu_bd⟩, heu⟩) |
        ⟨j, s, ⟨⟨hs1, hs_sp⟩, hsF⟩, hes⟩⟩ |
        ⟨heG, (⟨d, ⟨hd2, hdE⟩, rfl⟩ | ⟨u, ⟨hu2, hu_bd⟩, heu⟩) |
        ⟨j, s, ⟨⟨hs2, hs_sp⟩, hsF⟩, hes⟩⟩)
      · exact ⟨heG, Or.inl (Or.inl ⟨d, ⟨Or.inl hd1, hdE⟩, rfl⟩)⟩
      · exact ⟨heG, Or.inl (Or.inr ⟨u, ⟨Or.inl hu1, hu_bd⟩, heu⟩)⟩
      · exact ⟨heG, Or.inr ⟨j, s, ⟨⟨Or.inl hs1, hs_sp⟩, hsF⟩, hes⟩⟩
      · exact ⟨heG, Or.inl (Or.inl ⟨d, ⟨Or.inr hd2, hdE⟩, rfl⟩)⟩
      · exact ⟨heG, Or.inl (Or.inr ⟨u, ⟨Or.inr hu2, hu_bd⟩, heu⟩)⟩
      · exact ⟨heG, Or.inr ⟨j, s, ⟨⟨Or.inr hs2, hs_sp⟩, hsF⟩, hes⟩⟩

/-- `σ(Γ^+) = G`. -/
lemma sigmaSubgraph_drawingPlusHypergraph
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_iso : BijOn ιE Γ.E Γ_sub.edgeSet ∧
      ∀ d ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE d) (ιV u) ↔ u ∈ closure d)
    (h_spaces_fin : (drawingSpaces Γ).Finite) :
    sigmaSubgraph G Γ ιV ιE r F_star μ (drawingPlusHypergraph Γ h_spaces_fin) = G := by
  have hle : sigmaSubgraph G Γ ιV ιE r F_star μ (drawingPlusHypergraph Γ h_spaces_fin) ≤ G :=
    sigmaSubgraph_le h_pres h_iso h_spaces_fin le_rfl
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl
  · refine Subset.antisymm hle.vertexSet_subset ?_
    intro v hvG
    have hv_union : v ∈ (⋃ j : Fin r, (H j).vertexSet) ∪ Γ_sub.vertexSet :=
      h_pres.v1_union_V ▸ hvG
    refine ⟨hvG, ?_⟩
    rcases hv_union with hvH | hv_sub
    · rw [mem_iUnion] at hvH
      rcases hvH with ⟨j, hvHj⟩
      rw [h_pres.v2_eq j] at hvHj
      rcases hvHj with ⟨_, hv_sp | hv_u⟩
      · rw [mem_iUnion₂] at hv_sp
        rcases hv_sp with ⟨s, ⟨hs_sp, hsF⟩, hvs⟩
        refine Or.inr ?_
        rw [mem_iUnion]
        refine ⟨j, ?_⟩
        rw [mem_iUnion₂]
        exact ⟨s, ⟨⟨Or.inr hs_sp, hs_sp⟩, hsF⟩, hvs⟩
      · rw [mem_iUnion₂] at hv_u
        rcases hv_u with ⟨u, ⟨huV, huF⟩, hvu⟩
        have hu_bd : u ∈ bd S := support_subset_bd (h_pres.supports_isSupport j) huF
        refine Or.inl (Or.inr ?_)
        rw [mem_iUnion₂]
        exact ⟨u, ⟨huV, huV, hu_bd⟩, hvu⟩
    · rw [← h_pres.ιV_image] at hv_sub
      rcases hv_sub with ⟨u, huV, rfl⟩
      exact Or.inl (Or.inl ⟨u, ⟨huV, huV⟩, rfl⟩)
  · refine Subset.antisymm hle.edgeSet_subset ?_
    intro e heG
    have he_union : e ∈ (⋃ j : Fin r, (H j).edgeSet) ∪ Γ_sub.edgeSet :=
      h_pres.v1_union_E ▸ heG
    refine ⟨heG, ?_⟩
    rcases he_union with heH | he_sub
    · rw [mem_iUnion] at heH
      rcases heH with ⟨j, heHj⟩
      rw [h_pres.v2_eq j] at heHj
      rcases heHj with ⟨_, he_sp | he_u⟩
      · rw [mem_iUnion₂] at he_sp
        rcases he_sp with ⟨s, ⟨hs_sp, hsF⟩, hes⟩
        refine Or.inr ?_
        rw [mem_iUnion]
        refine ⟨j, ?_⟩
        rw [mem_iUnion₂]
        exact ⟨s, ⟨⟨Or.inr hs_sp, hs_sp⟩, hsF⟩, hes⟩
      · rw [mem_iUnion₂] at he_u
        rcases he_u with ⟨u, ⟨huV, huF⟩, heu⟩
        have hu_bd : u ∈ bd S := support_subset_bd (h_pres.supports_isSupport j) huF
        refine Or.inl (Or.inr ?_)
        rw [mem_iUnion₂]
        exact ⟨u, ⟨huV, huV, hu_bd⟩, heu⟩
    · rw [← h_iso.1.image_eq] at he_sub
      rcases he_sub with ⟨d, hdE, rfl⟩
      exact Or.inl (Or.inl ⟨d, ⟨Or.inl hdE, hdE⟩, rfl⟩)

/-- For `A ≤ Γ^+`, `V(σ(A)) ∩ V(Γ_sub) = ιV '' V(A)`. -/
lemma sigmaSubgraph_inter_Gamma_sub_vertexSet
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    {A : Hypergraph S (Set S)} (hA : A ≤ drawingPlusHypergraph Γ h_spaces_fin) :
    (sigmaSubgraph G Γ ιV ιE r F_star μ A).vertexSet ∩ Γ_sub.vertexSet = ιV '' A.vertexSet := by
  have hAV : A.vertexSet ⊆ Γ.V := hA.vertexSet_subset
  ext v
  simp only [sigmaSubgraph, mem_inter_iff]
  constructor
  · rintro ⟨⟨_, (hv_draw | hv_vert) | hv_sp⟩, hv_sub⟩
    · rcases hv_draw with ⟨u, ⟨huA, _⟩, rfl⟩
      exact ⟨u, huA, rfl⟩
    · rw [mem_iUnion₂] at hv_vert
      rcases hv_vert with ⟨u, ⟨huA, hu_bd⟩, hvu⟩
      obtain ⟨_, _, _, _, _, hinter⟩ := mu_vertex_props_of_mem_bd h_pres hu_bd
      have hv_eq : v ∈ ({ιV u} : Set α) := hinter ▸ ⟨hvu, hv_sub⟩
      rw [mem_singleton_iff] at hv_eq
      exact ⟨u, huA, hv_eq.symm⟩
    · rw [mem_iUnion] at hv_sp
      rcases hv_sp with ⟨j, hv_j⟩
      rw [mem_iUnion₂] at hv_j
      rcases hv_j with ⟨s, ⟨⟨hsA, hs_sp⟩, hsF⟩, hvs⟩
      obtain ⟨u₁, u₂, hends⟩ :=
        exists_spaceHasEnds_of_mem_drawingSpaces h_pres.is_surface h_pres.cuff_vertices_ge_two hs_sp
      have hinter := (h_pres.v3_space j s hs_sp u₁ u₂ hsF hends).1
      have hv_in_ends : v ∈ ({ιV u₁, ιV u₂} : Set α) := hinter ▸ ⟨hvs, hv_sub⟩
      have hcl : u₁ ∈ closure s ∧ u₂ ∈ closure s := by
        rw [hends.2.2.2.2.2]
        exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
      rcases hv_in_ends with rfl | rfl
      · have hinc_plus : (drawingPlusHypergraph Γ h_spaces_fin).Inc s u₁ :=
          ⟨Or.inr hs_sp, hends.2.1.1, hcl.1⟩
        have hu₁A : u₁ ∈ A.vertexSet := A.vertex_mem_of_inc ((inc_iff_of_le hA hsA).2 hinc_plus)
        exact ⟨u₁, hu₁A, rfl⟩
      · have hinc_plus : (drawingPlusHypergraph Γ h_spaces_fin).Inc s u₂ :=
          ⟨Or.inr hs_sp, hends.2.2.1.1, hcl.2⟩
        have hu₂A : u₂ ∈ A.vertexSet := A.vertex_mem_of_inc ((inc_iff_of_le hA hsA).2 hinc_plus)
        exact ⟨u₂, hu₂A, rfl⟩
  · rintro ⟨u, huA, rfl⟩
    have huV : u ∈ Γ.V := hAV huA
    have hu_sub : ιV u ∈ Γ_sub.vertexSet := by
      rw [← h_pres.ιV_image]
      exact ⟨u, huV, rfl⟩
    have hu_G : ιV u ∈ G.vertexSet := h_pres.drawing_subgraph.vertexSet_subset hu_sub
    exact ⟨⟨hu_G, Or.inl (Or.inl ⟨u, ⟨huA, huV⟩, rfl⟩)⟩, hu_sub⟩

/-- In a separation `(A, B)` of `Γ^+`, if `b_A ≤ a_B` in a support `F_star j = cuffPoint f '' Icc t₀ t₁`
with `cuffPoint f b_A ∈ A.vertexSet` and `cuffPoint f a_B ∈ B.vertexSet`, then there exists an angle
`γ ∈ Icc b_A a_B` such that `cuffPoint f γ ∈ (A ∩ B).vertexSet`. -/
lemma exists_angle_in_inter_of_isSeparation
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    {A B : Hypergraph S (Set S)}
    (hsep : (drawingPlusHypergraph Γ h_spaces_fin).IsSeparation A B)
    (j : Fin r) {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ b_A a_B : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
    (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F_star j = cuffPoint f '' Icc t₀ t₁)
    (hb_A_ge : t₀ ≤ b_A) (hba : b_A ≤ a_B) (ha_B_le : a_B ≤ t₁)
    (hb_A_mem : cuffPoint f b_A ∈ A.vertexSet)
    (ha_B_mem : cuffPoint f a_B ∈ B.vertexSet) :
    ∃ γ ∈ Icc b_A a_B, cuffPoint f γ ∈ (A ∩ B).vertexSet := by
  let T_A : Set ℝ := {τ ∈ Icc b_A a_B | cuffPoint f τ ∈ A.vertexSet}
  have hT_A_fin : T_A.Finite := by
    apply A.vertexSet_finite.of_injOn (f := cuffPoint f)
    · intro τ hτ
      exact hτ.2
    · intro x hx y hy hxy
      exact cuffPoint_injOn_Ico f t₀
        ⟨hb_A_ge.trans hx.1.1, (hx.1.2.trans ha_B_le).trans_lt hlt⟩
        ⟨hb_A_ge.trans hy.1.1, (hy.1.2.trans ha_B_le).trans_lt hlt⟩ hxy
  have hT_A_ne : T_A.Nonempty := ⟨b_A, ⟨le_rfl, hba⟩, hb_A_mem⟩
  let γ := (hT_A_fin.toFinset).max' (hT_A_fin.toFinset_nonempty.2 hT_A_ne)
  have hγ_mem : γ ∈ T_A := (hT_A_fin.mem_toFinset).1 (Finset.max'_mem _ _)
  have hγ_max : ∀ τ ∈ T_A, τ ≤ γ := fun τ hτ =>
    Finset.le_max' _ _ ((hT_A_fin.mem_toFinset).2 hτ)
  refine ⟨γ, hγ_mem.1, hγ_mem.2, ?_⟩
  rcases eq_or_lt_of_le hγ_mem.1.2 with hγ_eq | hγ_lt_aB
  · rw [hγ_eq]
    exact ha_B_mem
  · have hγ_ge_t₀ : t₀ ≤ γ := hb_A_ge.trans hγ_mem.1.1
    have hγ_lt_t₁ : γ < t₁ := hγ_lt_aB.trans_le ha_B_le
    have hγV : cuffPoint f γ ∈ Γ.V := hsep.left_le.vertexSet_subset hγ_mem.2
    obtain ⟨s, hs_sp, β_s, hγ_lt_β, hβ_le_t₁, hsF, hends, hs_eq⟩ :=
      exists_space_starting_at_angle h_pres.is_surface h_pres.cuff_vertices_ge_two
        hC f ht₀ hle hlt hF_eq hγ_ge_t₀ hγ_lt_t₁ hγV ht₁V
    have haB_V : cuffPoint f a_B ∈ Γ.V := hsep.right_le.vertexSet_subset ha_B_mem
    have hβ_le_aB : β_s ≤ a_B := by
      by_contra hgt
      push Not at hgt
      have haB_in_s : cuffPoint f a_B ∈ s := by
        rw [hs_eq]
        exact ⟨a_B, ⟨hγ_lt_aB, hgt⟩, rfl⟩
      exact (subset_bd_diff_of_mem_drawingSpaces hs_sp haB_in_s).2 haB_V
    have hβ_not_A : cuffPoint f β_s ∉ A.vertexSet := by
      intro hβA
      have hβ_in_TA : β_s ∈ T_A := ⟨⟨hγ_mem.1.1.trans hγ_lt_β.le, hβ_le_aB⟩, hβA⟩
      linarith [hγ_max β_s hβ_in_TA]
    have hs_in_plus : s ∈ (drawingPlusHypergraph Γ h_spaces_fin).edgeSet := Or.inr hs_sp
    have hs_AB : s ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union.symm ▸ hs_in_plus
    have hcl_ends : cuffPoint f γ ∈ closure s ∧ cuffPoint f β_s ∈ closure s := by
      rw [hends.2.2.2.2.2]
      exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    rcases hs_AB with hsA | hsB
    · exfalso
      have hinc_plus : (drawingPlusHypergraph Γ h_spaces_fin).Inc s (cuffPoint f β_s) :=
        ⟨hs_in_plus, hends.2.2.1.1, hcl_ends.2⟩
      have hinc_A : A.Inc s (cuffPoint f β_s) := (inc_iff_of_le hsep.left_le hsA).2 hinc_plus
      exact hβ_not_A (A.vertex_mem_of_inc hinc_A)
    · have hinc_plus : (drawingPlusHypergraph Γ h_spaces_fin).Inc s (cuffPoint f γ) :=
        ⟨hs_in_plus, hends.2.1.1, hcl_ends.1⟩
      have hinc_B : B.Inc s (cuffPoint f γ) := (inc_iff_of_le hsep.right_le hsB).2 hinc_plus
      exact B.vertex_mem_of_inc hinc_B

/-- Given a unit `x` in `F_star j = cuffPoint f '' Icc t₀ t₁` arising from a subgraph `A ≤ Γ^+`
(either `x = .vertex u` with `u ∈ A.vertexSet ∩ (Γ.V ∩ F_star j)` or `x = .space s` with
`s ∈ A.edgeSet ∩ drawingSpaces Γ` and `s ⊆ F_star j`), `x` has an angle interval `[a, b] ⊆ [t₀, t₁]`
whose endpoints `cuffPoint f a` and `cuffPoint f b` both belong to `A.vertexSet ∩ Γ.V`. -/
lemma unit_interval_in_support_of_subgraph
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    {A : Hypergraph S (Set S)} (hA : A ≤ drawingPlusHypergraph Γ h_spaces_fin)
    (j : Fin r) {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C)
    (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F_star j = cuffPoint f '' Icc t₀ t₁)
    {x : BoundaryUnit S}
    (hx : (∃ u ∈ A.vertexSet ∩ (Γ.V ∩ F_star j), x = .vertex u) ∨
          (∃ s ∈ A.edgeSet ∩ drawingSpaces Γ, s ⊆ F_star j ∧ x = .space s)) :
    ∃ a b : ℝ, t₀ ≤ a ∧ a ≤ b ∧ b ≤ t₁ ∧
      cuffPoint f a ∈ A.vertexSet ∧ cuffPoint f a ∈ Γ.V ∧
      cuffPoint f b ∈ A.vertexSet ∧ cuffPoint f b ∈ Γ.V ∧
      ((a = b ∧ x = .vertex (cuffPoint f a)) ∨
       (∃ s ∈ A.edgeSet ∩ drawingSpaces Γ, a < b ∧ s = cuffPoint f '' Ioo a b ∧ x = .space s)) := by
  rcases hx with ⟨u, ⟨huA, huV, huF⟩, rfl⟩ | ⟨s, ⟨hsA, hs_sp⟩, hsF, rfl⟩
  · have hu_in : u ∈ cuffPoint f '' Icc t₀ t₁ := hF_eq ▸ huF
    rcases hu_in with ⟨τ, ⟨hτ1, hτ2⟩, rfl⟩
    exact ⟨τ, τ, hτ1, le_rfl, hτ2, huA, huV, huA, huV, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨a, b, ha, hab, hb, haVF, hbVF, hends, hs_eq, _⟩ :=
      space_in_support_eq_Ioo h_pres.is_surface h_pres.cuff_vertices_ge_two
        hC f hle hlt ht₀ hF_eq hs_sp hsF
    have hcl : cuffPoint f a ∈ closure s ∧ cuffPoint f b ∈ closure s := by
      rw [hends.2.2.2.2.2]
      exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    have haA : cuffPoint f a ∈ A.vertexSet :=
      A.vertex_mem_of_inc ((inc_iff_of_le hA hsA).2 ⟨Or.inr hs_sp, haVF.1, hcl.1⟩)
    have hbA : cuffPoint f b ∈ A.vertexSet :=
      A.vertex_mem_of_inc ((inc_iff_of_le hA hsA).2 ⟨Or.inr hs_sp, hbVF.1, hcl.2⟩)
    exact ⟨a, b, ha, hab.le, hb, haA, haVF.1, hbA, hbVF.1,
      Or.inr ⟨s, ⟨hsA, hs_sp⟩, hab, hs_eq, rfl⟩⟩

/-- **Graph Minors XXI, (7.2), Claim (1)** (page 30 of the preprint):
"(1) *If $(A, B)$ is a separation of $\Gamma^+$ then $(\sigma(A), \sigma(B))$ is a separation of
$G$ of order $\le q|V(A \cap B)|$.*" -/
theorem theorem_7_2_claim_1
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {d : ℕ}
    (hG_graph : G.IsGraph)
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hq_le : ∀ j : Fin r, q j ≤ d)
    (hd_pos : 1 ≤ d)
    {A B : Hypergraph S (Set S)}
    (hsep : (drawingPlusHypergraph Γ h_pres.spaces_finite).IsSeparation A B) :
    G.IsSeparation (sigmaSubgraph G Γ ιV ιE r F_star μ A) (sigmaSubgraph G Γ ιV ιE r F_star μ B) ∧
      Hypergraph.separationOrder
        (sigmaSubgraph G Γ ιV ιE r F_star μ A) (sigmaSubgraph G Γ ιV ιE r F_star μ B) ≤
        d * Hypergraph.separationOrder A B := by
  have h_iso := h_pres.bijOn_ιE_and_inc_iff
  have h_spaces_fin := h_pres.spaces_finite
  let σA := sigmaSubgraph G Γ ιV ιE r F_star μ A
  let σB := sigmaSubgraph G Γ ιV ιE r F_star μ B
  have hσA_le : σA ≤ G := sigmaSubgraph_le h_pres h_iso h_spaces_fin hsep.left_le
  have hσB_le : σB ≤ G := sigmaSubgraph_le h_pres h_iso h_spaces_fin hsep.right_le
  have hσ_union : σA ∪ σB = G := by
    rw [← sigmaSubgraph_union h_pres h_iso h_spaces_fin hsep.left_le hsep.right_le, hsep.union_eq,
      sigmaSubgraph_drawingPlusHypergraph h_pres h_iso h_spaces_fin]
  -- Disjointness of `σA.edgeSet` and `σB.edgeSet`
  have hσ_edge_disj : σA.edgeSet ∩ σB.edgeSet = ∅ := by
    ext e
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro heA heB
    -- Unpack `heA` and `heB`, eliminating vertex units since `E(μ(u)) = ∅`
    have unpack_edge : ∀ {X : Hypergraph S (Set S)}, e ∈ (sigmaSubgraph G Γ ιV ιE r F_star μ X).edgeSet →
        (∃ d ∈ X.edgeSet ∩ Γ.E, ιE d = e) ∨
        (∃ j : Fin r, ∃ s ∈ X.edgeSet ∩ drawingSpaces Γ, s ⊆ F_star j ∧ e ∈ (μ (.space s)).edgeSet) := by
      rintro X ⟨_, (⟨d, hd, rfl⟩ | he_u) | he_s⟩
      · exact Or.inl ⟨d, hd, rfl⟩
      · rw [mem_iUnion₂] at he_u
        rcases he_u with ⟨u, ⟨_, hu_bd⟩, heu⟩
        obtain ⟨_, _, _, hedge_empty, _, _⟩ := mu_vertex_props_of_mem_bd h_pres hu_bd
        rw [hedge_empty] at heu
        exact False.elim heu
      · rw [mem_iUnion] at he_s
        rcases he_s with ⟨j, he_j⟩
        rw [mem_iUnion₂] at he_j
        rcases he_j with ⟨s, ⟨hs, hsF⟩, hes⟩
        exact Or.inr ⟨j, s, hs, hsF, hes⟩
    rcases unpack_edge heA with ⟨d₁, ⟨hd₁A, hd₁E⟩, rfl⟩ | ⟨j₁, s₁, ⟨hs₁A, hs₁_sp⟩, hs₁F, hes₁⟩ <;>
    rcases unpack_edge heB with ⟨d₂, ⟨hd₂B, hd₂E⟩, hd₂_eq⟩ | ⟨j₂, s₂, ⟨hs₂B, hs₂_sp⟩, hs₂F, hes₂⟩
    · have hd_eq : d₁ = d₂ := h_iso.1.injOn hd₁E hd₂E hd₂_eq.symm
      subst hd_eq
      exact hsep.notMem_edgeSet_right hd₁A hd₂B
    · have he_sub : ιE d₁ ∈ Γ_sub.edgeSet := h_iso.1.mapsTo hd₁E
      have he_H : ιE d₁ ∈ (H j₂).edgeSet :=
        (h_pres.μ_space_sub j₂ s₂ hs₂_sp hs₂F).edgeSet_subset hes₂
      exact Set.disjoint_left.1 (h_pres.v1_inter_E j₂) he_H he_sub
    · subst hd₂_eq
      have he_sub : ιE d₂ ∈ Γ_sub.edgeSet := h_iso.1.mapsTo hd₂E
      have he_H : ιE d₂ ∈ (H j₁).edgeSet :=
        (h_pres.μ_space_sub j₁ s₁ hs₁_sp hs₁F).edgeSet_subset hes₁
      exact Set.disjoint_left.1 (h_pres.v1_inter_E j₁) he_H he_sub
    · have he_H₁ : e ∈ (H j₁).edgeSet :=
        (h_pres.μ_space_sub j₁ s₁ hs₁_sp hs₁F).edgeSet_subset hes₁
      have he_H₂ : e ∈ (H j₂).edgeSet :=
        (h_pres.μ_space_sub j₂ s₂ hs₂_sp hs₂F).edgeSet_subset hes₂
      have heG : e ∈ G.edgeSet := (h_pres.v1_sub j₁).edgeSet_subset he_H₁
      rcases (hG_graph e heG).1 with ⟨w, hw⟩
      have hw_H₁ : w ∈ (H j₁).vertexSet :=
        (H j₁).vertex_mem_of_inc ((inc_iff_of_le (h_pres.v1_sub j₁) he_H₁).2 hw)
      have hw_H₂ : w ∈ (H j₂).vertexSet :=
        (H j₂).vertex_mem_of_inc ((inc_iff_of_le (h_pres.v1_sub j₂) he_H₂).2 hw)
      have hj_eq : j₁ = j₂ := by
        by_contra hj_ne
        exact Set.disjoint_left.1 (h_pres.v1_disjoint hj_ne) hw_H₁ hw_H₂
      subst hj_eq
      have hs_ne : s₁ ≠ s₂ := by
        rintro rfl
        exact hsep.notMem_edgeSet_right hs₁A hs₂B
      obtain ⟨u, hu_in, hu_bet | hu_bet⟩ :=
        exists_liesBetweenInSupport_of_ne h_pres j₁ hs₁_sp hs₂_sp hs₁F hs₂F hs_ne
      · have hv4 := h_pres.v4_between j₁ s₁ s₂ u hu_bet
        have he_inter : e ∈ (μ (.space s₁) ∩ μ (.space s₂)).edgeSet := ⟨hes₁, hes₂⟩
        have he_u : e ∈ (μ (.vertex u)).edgeSet := hv4.edgeSet_subset he_inter
        rw [(h_pres.μ_vertex_sub j₁ u hu_in).2.1] at he_u
        exact he_u
      · have hv4 := h_pres.v4_between j₁ s₂ s₁ u hu_bet
        have he_inter : e ∈ (μ (.space s₂) ∩ μ (.space s₁)).edgeSet := ⟨hes₂, hes₁⟩
        have he_u : e ∈ (μ (.vertex u)).edgeSet := hv4.edgeSet_subset he_inter
        rw [(h_pres.μ_vertex_sub j₁ u hu_in).2.1] at he_u
        exact he_u
  have hsep_G : G.IsSeparation σA σB :=
    ⟨hσA_le, hσB_le, hσ_union, hσ_edge_disj⟩
  -- Vertex intersection inclusion:
  -- `V(σ(A) ∩ σ(B)) ⊆ ιV '' V(A ∩ B) ∪ ⋃ u ∈ V(A ∩ B) ∩ (Γ.V ∩ bd S), V(μ(u))`
  have hv_inter_sub : (σA ∩ σB).vertexSet ⊆
      ιV '' (A ∩ B).vertexSet ∪
      (⋃ u ∈ (A ∩ B).vertexSet ∩ (Γ.V ∩ bd S), (μ (.vertex u)).vertexSet) := by
    rintro v ⟨hvA, hvB⟩
    by_cases hv_sub : v ∈ Γ_sub.vertexSet
    · have hvA_im : v ∈ ιV '' A.vertexSet := by
        rw [← sigmaSubgraph_inter_Gamma_sub_vertexSet h_pres h_spaces_fin hsep.left_le]
        exact ⟨hvA, hv_sub⟩
      have hvB_im : v ∈ ιV '' B.vertexSet := by
        rw [← sigmaSubgraph_inter_Gamma_sub_vertexSet h_pres h_spaces_fin hsep.right_le]
        exact ⟨hvB, hv_sub⟩
      rcases hvA_im with ⟨u₁, hu₁A, rfl⟩
      rcases hvB_im with ⟨u₂, hu₂B, hu_eq⟩
      have hu₁V : u₁ ∈ Γ.V := hsep.left_le.vertexSet_subset hu₁A
      have hu₂V : u₂ ∈ Γ.V := hsep.right_le.vertexSet_subset hu₂B
      have hu12 : u₁ = u₂ := h_pres.ιV_injOn hu₁V hu₂V hu_eq.symm
      subst hu12
      exact Or.inl ⟨u₁, ⟨hu₁A, hu₂B⟩, rfl⟩
    · -- `v ∉ Γ_sub.vertexSet`, so `v` comes from a unit `x_A` in some `F_star j₁` and `x_B` in `F_star j₂`
      have unpack_non_sub : ∀ {X : Hypergraph S (Set S)},
          v ∈ (sigmaSubgraph G Γ ιV ιE r F_star μ X).vertexSet →
          ∃ j : Fin r, ∃ x : BoundaryUnit S, v ∈ (μ x).vertexSet ∧ v ∈ (H j).vertexSet ∧
            ((∃ u ∈ X.vertexSet ∩ (Γ.V ∩ F_star j), x = .vertex u) ∨
             (∃ s ∈ X.edgeSet ∩ drawingSpaces Γ, s ⊆ F_star j ∧ x = .space s)) := by
        rintro X ⟨_, (⟨u, ⟨_, huV⟩, rfl⟩ | hv_u) | hv_s⟩
        · exfalso
          apply hv_sub
          rw [← h_pres.ιV_image]
          exact ⟨u, huV, rfl⟩
        · rw [mem_iUnion₂] at hv_u
          rcases hv_u with ⟨u, ⟨huX, hu_bd⟩, hvu⟩
          have huF : u ∈ ⋃ j : Fin r, F_star j := h_pres.bd_vertices_covered hu_bd
          rcases mem_iUnion.1 huF with ⟨j, huj⟩
          have hu_in : u ∈ Γ.V ∩ F_star j := ⟨hu_bd.1, huj⟩
          have hvH : v ∈ (H j).vertexSet :=
            (h_pres.μ_vertex_sub j u hu_in).1.vertexSet_subset hvu
          exact ⟨j, .vertex u, hvu, hvH, Or.inl ⟨u, ⟨huX, hu_in⟩, rfl⟩⟩
        · rw [mem_iUnion] at hv_s
          rcases hv_s with ⟨j, hv_j⟩
          rw [mem_iUnion₂] at hv_j
          rcases hv_j with ⟨s, ⟨hsX, hsF⟩, hvs⟩
          have hvH : v ∈ (H j).vertexSet :=
            (h_pres.μ_space_sub j s hsX.2 hsF).vertexSet_subset hvs
          exact ⟨j, .space s, hvs, hvH, Or.inr ⟨s, hsX, hsF, rfl⟩⟩
      obtain ⟨j₁, x_A, hv_xA, hv_H₁, hx_A⟩ := unpack_non_sub hvA
      obtain ⟨j₂, x_B, hv_xB, hv_H₂, hx_B⟩ := unpack_non_sub hvB
      have hj_eq : j₁ = j₂ := by
        by_contra hj_ne
        exact Set.disjoint_left.1 (h_pres.v1_disjoint hj_ne) hv_H₁ hv_H₂
      subst hj_eq
      obtain ⟨C, hC, f, t₀, t₁, hle, hlt, ht₀, ht₁V, hF_eq⟩ :=
        support_param_of_isPresentation h_pres j₁
      obtain ⟨a_A, b_A, ha_A, hab_A, hb_A, ha_A_mem, ha_A_V, hb_A_mem, hb_A_V, hx_A_rep⟩ :=
        unit_interval_in_support_of_subgraph h_pres h_spaces_fin hsep.left_le
          j₁ hC f ht₀ hle hlt hF_eq hx_A
      obtain ⟨a_B, b_B, ha_B, hab_B, hb_B, ha_B_mem, ha_B_V, hb_B_mem, hb_B_V, hx_B_rep⟩ :=
        unit_interval_in_support_of_subgraph h_pres h_spaces_fin hsep.right_le
          j₁ hC f ht₀ hle hlt hF_eq hx_B
      -- The open intervals `(a_A, b_A)` and `(a_B, b_B)` are disjoint, so `b_A ≤ a_B` or `b_B ≤ a_A`.
      have h_order : b_A ≤ a_B ∨ b_B ≤ a_A := by
        rcases hx_A_rep with ⟨rfl, _⟩ | ⟨s_A, ⟨hs_A_mem, hs_A_sp⟩, hab_A_lt, hs_A_eq, _⟩
        · rcases hx_B_rep with ⟨rfl, _⟩ | ⟨s_B, ⟨hs_B_mem, hs_B_sp⟩, hab_B_lt, hs_B_eq, _⟩
          · exact le_total a_A a_B
          · by_contra hnot
            push Not at hnot
            have haA_in_sB : cuffPoint f a_A ∈ s_B := by
              rw [hs_B_eq]; exact ⟨a_A, ⟨hnot.1, hnot.2⟩, rfl⟩
            exact (subset_bd_diff_of_mem_drawingSpaces hs_B_sp haA_in_sB).2 ha_A_V
        · rcases hx_B_rep with ⟨rfl, _⟩ | ⟨s_B, ⟨hs_B_mem, hs_B_sp⟩, hab_B_lt, hs_B_eq, _⟩
          · by_contra hnot
            push Not at hnot
            have haB_in_sA : cuffPoint f a_B ∈ s_A := by
              rw [hs_A_eq]; exact ⟨a_B, ⟨hnot.2, hnot.1⟩, rfl⟩
            exact (subset_bd_diff_of_mem_drawingSpaces hs_A_sp haB_in_sA).2 ha_B_V
          · by_contra hnot
            push Not at hnot
            have hmax_lt_min : max a_A a_B < min b_A b_B :=
              max_lt (lt_min hab_A_lt hnot.2) (lt_min hnot.1 hab_B_lt)
            set m := (max a_A a_B + min b_A b_B) / 2 with hm_def
            have hm_A : a_A < m ∧ m < b_A := by
              constructor <;> linarith [le_max_left a_A a_B, min_le_left b_A b_B]
            have hm_B : a_B < m ∧ m < b_B := by
              constructor <;> linarith [le_max_right a_A a_B, min_le_right b_A b_B]
            have hm_sA : cuffPoint f m ∈ s_A := by rw [hs_A_eq]; exact ⟨m, hm_A, rfl⟩
            have hm_sB : cuffPoint f m ∈ s_B := by rw [hs_B_eq]; exact ⟨m, hm_B, rfl⟩
            have hs_eq : s_A = s_B :=
              eq_of_mem_drawingSpaces_of_mem hs_A_sp hs_B_sp hm_sA hm_sB
            subst hs_eq
            exact hsep.notMem_edgeSet_right hs_A_mem hs_B_mem
      rcases h_order with hba | hbb
      · obtain ⟨γ, ⟨hγ1, hγ2⟩, hγ_AB⟩ :=
          exists_angle_in_inter_of_isSeparation h_pres h_spaces_fin hsep j₁ hC f
            ht₀ ht₁V hle hlt hF_eq (ha_A.trans hab_A) hba (hab_B.trans hb_B) hb_A_mem ha_B_mem
        have hγV : cuffPoint f γ ∈ Γ.V := hsep.left_le.vertexSet_subset hγ_AB.1
        have hγF : cuffPoint f γ ∈ F_star j₁ := by
          rw [hF_eq]
          exact ⟨γ, ⟨(ha_A.trans hab_A).trans hγ1, hγ2.trans (hab_B.trans hb_B)⟩, rfl⟩
        have hγ_bd : cuffPoint f γ ∈ bd S := support_subset_bd (h_pres.supports_isSupport j₁) hγF
        have hx₁_unit :
            (∃ α₁ : ℝ, t₀ ≤ α₁ ∧ α₁ ≤ γ ∧ cuffPoint f α₁ ∈ Γ.V ∧ x_A = .vertex (cuffPoint f α₁)) ∨
            (∃ s₁ ∈ drawingSpaces Γ, ∃ α₁ β₁ : ℝ,
              t₀ ≤ α₁ ∧ α₁ < β₁ ∧ β₁ ≤ γ ∧ s₁ = cuffPoint f '' Ioo α₁ β₁ ∧ x_A = .space s₁) := by
          rcases hx_A_rep with ⟨rfl, rfl⟩ | ⟨s₁, ⟨_, hs₁_sp⟩, hab₁, hs₁_eq, rfl⟩
          · exact Or.inl ⟨a_A, ha_A, hγ1, ha_A_V, rfl⟩
          · exact Or.inr ⟨s₁, hs₁_sp, a_A, b_A, ha_A, hab₁, hγ1, hs₁_eq, rfl⟩
        have hx₂_unit :
            (∃ α₂ : ℝ, γ ≤ α₂ ∧ α₂ ≤ t₁ ∧ cuffPoint f α₂ ∈ Γ.V ∧ x_B = .vertex (cuffPoint f α₂)) ∨
            (∃ s₂ ∈ drawingSpaces Γ, ∃ α₂ β₂ : ℝ,
              γ ≤ α₂ ∧ α₂ < β₂ ∧ β₂ ≤ t₁ ∧ s₂ = cuffPoint f '' Ioo α₂ β₂ ∧ x_B = .space s₂) := by
          rcases hx_B_rep with ⟨rfl, rfl⟩ | ⟨s₂, ⟨_, hs₂_sp⟩, hab₂, hs₂_eq, rfl⟩
          · exact Or.inl ⟨a_B, hγ2, hb_B, ha_B_V, rfl⟩
          · exact Or.inr ⟨s₂, hs₂_sp, a_B, b_B, hγ2, hab₂, hb_B, hs₂_eq, rfl⟩
        have hv_γ : v ∈ (μ (.vertex (cuffPoint f γ))).vertexSet :=
          unit_inter_vertexSet_subset_of_angle_between h_pres j₁ hC f ht₀ ht₁V hle hlt hF_eq
            ((ha_A.trans hab_A).trans hγ1) (hγ2.trans (hab_B.trans hb_B)) hγV hx₁_unit hx₂_unit ⟨hv_xA, hv_xB⟩
        refine Or.inr ?_
        rw [mem_iUnion₂]
        exact ⟨cuffPoint f γ, ⟨hγ_AB, hγV, hγ_bd⟩, hv_γ⟩
      · obtain ⟨γ, ⟨hγ1, hγ2⟩, hγ_BA⟩ :=
          exists_angle_in_inter_of_isSeparation h_pres h_spaces_fin hsep.symm j₁ hC f
            ht₀ ht₁V hle hlt hF_eq (ha_B.trans hab_B) hbb (hab_A.trans hb_A) hb_B_mem ha_A_mem
        have hγ_AB : cuffPoint f γ ∈ (A ∩ B).vertexSet := ⟨hγ_BA.2, hγ_BA.1⟩
        have hγV : cuffPoint f γ ∈ Γ.V := hsep.left_le.vertexSet_subset hγ_AB.1
        have hγF : cuffPoint f γ ∈ F_star j₁ := by
          rw [hF_eq]
          exact ⟨γ, ⟨(ha_B.trans hab_B).trans hγ1, hγ2.trans (hab_A.trans hb_A)⟩, rfl⟩
        have hγ_bd : cuffPoint f γ ∈ bd S := support_subset_bd (h_pres.supports_isSupport j₁) hγF
        have hx₁_unit :
            (∃ α₁ : ℝ, t₀ ≤ α₁ ∧ α₁ ≤ γ ∧ cuffPoint f α₁ ∈ Γ.V ∧ x_B = .vertex (cuffPoint f α₁)) ∨
            (∃ s₁ ∈ drawingSpaces Γ, ∃ α₁ β₁ : ℝ,
              t₀ ≤ α₁ ∧ α₁ < β₁ ∧ β₁ ≤ γ ∧ s₁ = cuffPoint f '' Ioo α₁ β₁ ∧ x_B = .space s₁) := by
          rcases hx_B_rep with ⟨rfl, rfl⟩ | ⟨s₁, ⟨_, hs₁_sp⟩, hab₁, hs₁_eq, rfl⟩
          · exact Or.inl ⟨a_B, ha_B, hγ1, ha_B_V, rfl⟩
          · exact Or.inr ⟨s₁, hs₁_sp, a_B, b_B, ha_B, hab₁, hγ1, hs₁_eq, rfl⟩
        have hx₂_unit :
            (∃ α₂ : ℝ, γ ≤ α₂ ∧ α₂ ≤ t₁ ∧ cuffPoint f α₂ ∈ Γ.V ∧ x_A = .vertex (cuffPoint f α₂)) ∨
            (∃ s₂ ∈ drawingSpaces Γ, ∃ α₂ β₂ : ℝ,
              γ ≤ α₂ ∧ α₂ < β₂ ∧ β₂ ≤ t₁ ∧ s₂ = cuffPoint f '' Ioo α₂ β₂ ∧ x_A = .space s₂) := by
          rcases hx_A_rep with ⟨rfl, rfl⟩ | ⟨s₂, ⟨_, hs₂_sp⟩, hab₂, hs₂_eq, rfl⟩
          · exact Or.inl ⟨a_A, hγ2, hb_A, ha_A_V, rfl⟩
          · exact Or.inr ⟨s₂, hs₂_sp, a_A, b_A, hγ2, hab₂, hb_A, hs₂_eq, rfl⟩
        have hv_γ : v ∈ (μ (.vertex (cuffPoint f γ))).vertexSet :=
          unit_inter_vertexSet_subset_of_angle_between h_pres j₁ hC f ht₀ ht₁V hle hlt hF_eq
            ((ha_B.trans hab_B).trans hγ1) (hγ2.trans (hab_A.trans hb_A)) hγV hx₁_unit hx₂_unit ⟨hv_xB, hv_xA⟩
        refine Or.inr ?_
        rw [mem_iUnion₂]
        exact ⟨cuffPoint f γ, ⟨hγ_AB, hγV, hγ_bd⟩, hv_γ⟩
  -- Deduce the cardinality bound `separationOrder σA σB ≤ d * separationOrder A B`
  refine ⟨hsep_G, ?_⟩
  let fiber : S → Set α := fun u =>
    if u ∈ Γ.V ∩ bd S then (μ (.vertex u)).vertexSet else {ιV u}
  have hv_inter_fiber : (σA ∩ σB).vertexSet ⊆ ⋃ u ∈ (A ∩ B).vertexSet, fiber u := by
    intro v hv
    rcases hv_inter_sub hv with ⟨u, huAB, rfl⟩ | hv_u
    · rw [mem_iUnion₂]
      refine ⟨u, huAB, ?_⟩
      dsimp only [fiber]
      split_ifs with hu_bd
      · obtain ⟨_, _, _, _, _, hinter⟩ := mu_vertex_props_of_mem_bd h_pres hu_bd
        have h_in : ιV u ∈ (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet := by
          rw [hinter]; exact rfl
        exact h_in.1
      · exact rfl
    · rw [mem_iUnion₂] at hv_u
      rcases hv_u with ⟨u, ⟨huAB, hu_bd⟩, hvu⟩
      rw [mem_iUnion₂]
      refine ⟨u, huAB, ?_⟩
      dsimp only [fiber]
      split_ifs
      · exact hvu
  have hfiber_fin : ∀ u ∈ (A ∩ B).vertexSet, (fiber u).Finite := by
    intro u _
    dsimp only [fiber]
    split_ifs
    · exact (μ (.vertex u)).vertexSet_finite
    · exact finite_singleton _
  have hfiber_card : ∀ u ∈ (A ∩ B).vertexSet, (fiber u).ncard ≤ d := by
    intro u _
    dsimp only [fiber]
    split_ifs with hu_bd
    · obtain ⟨j, _, _, _, hcard, _⟩ := mu_vertex_props_of_mem_bd h_pres hu_bd
      rw [hcard]
      exact hq_le j
    · rw [ncard_singleton]
      exact hd_pos
  have hAB_fin : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  let F_AB := hAB_fin.toFinset
  have h_sub_finset : (σA ∩ σB).vertexSet ⊆ ⋃ u ∈ F_AB, fiber u := by
    intro v hv
    rcases mem_iUnion₂.1 (hv_inter_fiber hv) with ⟨u, hu, hvu⟩
    exact mem_iUnion₂.2 ⟨u, hAB_fin.mem_toFinset.2 hu, hvu⟩
  have h_union_fin : (⋃ u ∈ F_AB, fiber u).Finite :=
    F_AB.finite_toSet.biUnion (fun u hu => hfiber_fin u (hAB_fin.mem_toFinset.1 hu))
  calc
    Hypergraph.separationOrder σA σB = (σA ∩ σB).vertexSet.ncard := rfl
    _ ≤ (⋃ u ∈ F_AB, fiber u).ncard := ncard_le_ncard h_sub_finset h_union_fin
    _ ≤ ∑ u ∈ F_AB, (fiber u).ncard :=
        ncard_biUnion_le_sum F_AB fiber (fun u hu => hfiber_fin u (hAB_fin.mem_toFinset.1 hu))
    _ ≤ ∑ _u ∈ F_AB, d :=
        Finset.sum_le_sum (fun u hu => hfiber_card u (hAB_fin.mem_toFinset.1 hu))
    _ = F_AB.card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ = d * Hypergraph.separationOrder A B := by
        rw [mul_comm, Hypergraph.separationOrder, ncard_eq_toFinset_card (A ∩ B).vertexSet hAB_fin]

/-! ## 4. Helper Lemmas for the Third Tangle Axiom in `(7.2)` -/

/-- If `e ∈ E(Γ^+)` is either in `Γ.E` or a space not contained in any `F_star j`, then
`V(σ(Γ^+ \ {e})) = V(G)`. -/
lemma sigmaSubgraph_deleteEdges_vertexSet_eq_G
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_iso : BijOn ιE Γ.E Γ_sub.edgeSet ∧
      ∀ d ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE d) (ιV u) ↔ u ∈ closure d)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    {e : Set S}
    (he_not_supp : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → s ≠ e) :
    (sigmaSubgraph G Γ ιV ιE r F_star μ
      ((drawingPlusHypergraph Γ h_spaces_fin).deleteEdges {e})).vertexSet = G.vertexSet := by
  let Γ_plus := drawingPlusHypergraph Γ h_spaces_fin
  have hle : sigmaSubgraph G Γ ιV ιE r F_star μ (Γ_plus.deleteEdges {e}) ≤ G :=
    sigmaSubgraph_le h_pres h_iso h_spaces_fin (GM10.deleteEdges_le Γ_plus {e})
  refine Subset.antisymm hle.vertexSet_subset ?_
  have hG_V : G.vertexSet = (sigmaSubgraph G Γ ιV ιE r F_star μ Γ_plus).vertexSet :=
    congrArg Hypergraph.vertexSet (sigmaSubgraph_drawingPlusHypergraph h_pres h_iso h_spaces_fin).symm
  intro v hvG
  have hv_plus : v ∈ (sigmaSubgraph G Γ ιV ιE r F_star μ Γ_plus).vertexSet := hG_V ▸ hvG
  rcases hv_plus with ⟨_, (hv_draw | hv_vert) | hv_sp⟩
  · exact ⟨hvG, Or.inl (Or.inl hv_draw)⟩
  · exact ⟨hvG, Or.inl (Or.inr hv_vert)⟩
  · refine ⟨hvG, Or.inr ?_⟩
    rw [mem_iUnion] at hv_sp ⊢
    rcases hv_sp with ⟨j, hv_j⟩
    refine ⟨j, ?_⟩
    rw [mem_iUnion₂] at hv_j ⊢
    rcases hv_j with ⟨s, ⟨⟨hs_plus, hs_sp⟩, hsF⟩, hvs⟩
    have hs_ne : s ≠ e := he_not_supp j s hs_sp hsF
    exact ⟨s, ⟨⟨⟨hs_plus, hs_ne⟩, hs_sp⟩, hsF⟩, hvs⟩

/-- If `s ∈ drawingSpaces Γ` satisfies `s ⊆ F_star j`, then
`σ(edgeHypergraph Γ^+ s) = μ (.space s)`. -/
lemma sigmaSubgraph_edgeHypergraph_space_eq
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h_iso : BijOn ιE Γ.E Γ_sub.edgeSet ∧
      ∀ d ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE d) (ιV u) ↔ u ∈ closure d)
    (h_spaces_fin : (drawingSpaces Γ).Finite)
    (j : Fin r) {s : Set S} (hs_sp : s ∈ drawingSpaces Γ) (hsF : s ⊆ F_star j) :
    sigmaSubgraph G Γ ιV ιE r F_star μ
      (GM10.edgeHypergraph (drawingPlusHypergraph Γ h_spaces_fin) s) = μ (.space s) := by
  let Γ_plus := drawingPlusHypergraph Γ h_spaces_fin
  have hs_plus : s ∈ Γ_plus.edgeSet := Or.inr hs_sp
  have hKe_le : GM10.edgeHypergraph Γ_plus s ≤ Γ_plus := GM10.edgeHypergraph_le hs_plus
  have hσ_le : sigmaSubgraph G Γ ιV ιE r F_star μ (GM10.edgeHypergraph Γ_plus s) ≤ G :=
    sigmaSubgraph_le h_pres h_iso h_spaces_fin hKe_le
  have hμ_le : μ (.space s) ≤ G :=
    (h_pres.μ_space_sub j s hs_sp hsF).trans (h_pres.v1_sub j)
  obtain ⟨u₁, u₂, hends⟩ :=
    exists_spaceHasEnds_of_mem_drawingSpaces h_pres.is_surface h_pres.cuff_vertices_ge_two hs_sp
  obtain ⟨hv3_ends, hv3_sub1, hv3_sub2, _⟩ := h_pres.v3_space j s hs_sp u₁ u₂ hsF hends
  -- The ends of `s` in `Γ_plus` are `{u₁, u₂}`
  have hends_plus_eq : Γ_plus.ends s = {u₁, u₂} := by
    ext w
    simp only [Hypergraph.ends, Γ_plus, drawingPlusHypergraph, mem_ofPred_eq, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨_, hwV, hw_cl⟩
      rw [hends.2.2.2.2.2] at hw_cl
      rcases hw_cl with hws | (rfl | rfl)
      · exfalso
        exact (subset_bd_diff_of_mem_drawingSpaces hs_sp hws).2 hwV
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · refine ⟨hs_plus, hends.2.1.1, ?_⟩
        rw [hends.2.2.2.2.2]
        exact Or.inr (Or.inl rfl)
      · refine ⟨hs_plus, hends.2.2.1.1, ?_⟩
        rw [hends.2.2.2.2.2]
        exact Or.inr (Or.inr rfl)
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hσ_le hμ_le
  · ext v
    simp only [sigmaSubgraph, GM10.edgeHypergraph, hends_plus_eq, mem_inter_iff]
    constructor
    · rintro ⟨_, (⟨u, ⟨hu_ends, _⟩, rfl⟩ | hv_u) | hv_sp⟩
      · have hu_in : ιV u ∈ ({ιV u₁, ιV u₂} : Set α) := by
          rcases hu_ends with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        rw [← hv3_ends] at hu_in
        exact hu_in.1
      · rw [mem_iUnion₂] at hv_u
        rcases hv_u with ⟨u, ⟨hu_ends, _⟩, hvu⟩
        rcases hu_ends with rfl | rfl
        · exact hv3_sub1.vertexSet_subset hvu
        · exact hv3_sub2.vertexSet_subset hvu
      · rw [mem_iUnion] at hv_sp
        rcases hv_sp with ⟨j', hv_j'⟩
        rw [mem_iUnion₂] at hv_j'
        rcases hv_j' with ⟨s', ⟨⟨hs'_eq, _⟩, _⟩, hvs'⟩
        rw [mem_singleton_iff] at hs'_eq
        subst hs'_eq
        exact hvs'
    · intro hvs
      refine ⟨hμ_le.vertexSet_subset hvs, Or.inr ?_⟩
      rw [mem_iUnion]
      refine ⟨j, ?_⟩
      rw [mem_iUnion₂]
      exact ⟨s, ⟨⟨rfl, hs_sp⟩, hsF⟩, hvs⟩
  · ext e
    simp only [sigmaSubgraph, GM10.edgeHypergraph, hends_plus_eq, mem_inter_iff]
    constructor
    · rintro ⟨_, (⟨d, ⟨hd_eq, hdE⟩, rfl⟩ | he_u) | he_sp⟩
      · rw [mem_singleton_iff] at hd_eq
        rw [hd_eq] at hdE
        exfalso
        rcases hs_sp with ⟨x, hx, hcomp_eq⟩
        have hx_in_s : x ∈ s := hcomp_eq ▸ mem_connectedComponentIn hx
        have hx_in_U : x ∈ Γ.U \ Γ.V := hdE.2.1 hx_in_s
        exact hx.2 (h_pres.is_proper_drawing ⟨hx.1, hx_in_U.1⟩)
      · rw [mem_iUnion₂] at he_u
        rcases he_u with ⟨u, ⟨_, hu_bd⟩, heu⟩
        obtain ⟨_, _, _, hedge_empty, _, _⟩ := mu_vertex_props_of_mem_bd h_pres hu_bd
        rw [hedge_empty] at heu
        exact False.elim heu
      · rw [mem_iUnion] at he_sp
        rcases he_sp with ⟨j', he_j'⟩
        rw [mem_iUnion₂] at he_j'
        rcases he_j' with ⟨s', ⟨⟨hs'_eq, _⟩, _⟩, hes'⟩
        rw [mem_singleton_iff] at hs'_eq
        subst hs'_eq
        exact hes'
    · intro hes
      refine ⟨hμ_le.edgeSet_subset hes, Or.inr ?_⟩
      rw [mem_iUnion]
      refine ⟨j, ?_⟩
      rw [mem_iUnion₂]
      exact ⟨s, ⟨⟨rfl, hs_sp⟩, hsF⟩, hes⟩

/-! ## 5. Graph Minors XXI, `(7.2)`: Tangle in `Γ^+` -/

/-- **Graph Minors XXI, (7.2)** (page 30 of the preprint):
"Let $\theta \ge 1$, and let $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ be a presentation
of a graph $G$ in a surface $\Sigma$, of depth $\le q$, and surrounding a tangle of order
$\ge q\theta$. Then $\Gamma^+$ has a tangle of order $\ge \theta$." -/
theorem theorem_7_2_proof
    {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q θ θ_𝒯 : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hG_graph : G.IsGraph)
    (hθ : 1 ≤ θ)
    (hq : 1 ≤ q)
    (h_depth : PresentationHasDepthLe G Γ Γ_sub ιV ιE r F_star H μ q)
    (h𝒯 : GM10.IsTangle G θ_𝒯 𝒯)
    (hθ_𝒯 : q * θ ≤ θ_𝒯)
    (h_surr : PresentationSurroundsTangle Γ r F_star μ 𝒯) :
    ∃ 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)),
      GM10.IsTangle (drawingPlusHypergraph Γ h_depth.spaces_finite) θ 𝒯' := by
  obtain ⟨q_vec, h_pres, hq_le, _⟩ := h_depth
  have h_iso := h_pres.bijOn_ιE_and_inc_iff
  have h_spaces_fin := h_pres.spaces_finite
  let Γ_plus := drawingPlusHypergraph Γ h_spaces_fin
  let σ := sigmaSubgraph G Γ ιV ιE r F_star μ
  let 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
    {p | Γ_plus.IsSeparation p.1 p.2 ∧
      Hypergraph.separationOrder p.1 p.2 < θ ∧
      (σ p.1, σ p.2) ∈ 𝒯}
  refine ⟨𝒯', ?_⟩
  have hsep' : ∀ ⦃A B : Hypergraph S (Set S)⦄, (A, B) ∈ 𝒯' → Γ_plus.IsSeparation A B :=
    fun _ _ h => h.1
  have hord' : ∀ ⦃A B : Hypergraph S (Set S)⦄, (A, B) ∈ 𝒯' → Hypergraph.separationOrder A B < θ :=
    fun _ _ h => h.2.1
  -- First tangle axiom for `𝒯'`
  have hax1 : GM10.TangleAxiom1 Γ_plus θ 𝒯' := by
    intro A B hsep hord
    obtain ⟨hsep_σ, hord_σ_le⟩ :=
      theorem_7_2_claim_1 hG_graph h_pres hq_le hq hsep
    have hord_σ_lt : Hypergraph.separationOrder (σ A) (σ B) < θ_𝒯 :=
      (hord_σ_le.trans_lt (Nat.mul_lt_mul_of_pos_left hord hq)).trans_le hθ_𝒯
    rcases h𝒯.axiom1 hsep_σ hord_σ_lt with hAB | hBA
    · exact Or.inl ⟨hsep, hord, hAB⟩
    · exact Or.inr ⟨hsep.symm, by rwa [GM10.separationOrder_comm], hBA⟩
  -- Second tangle axiom for `𝒯'`
  have hax2 : GM10.TangleAxiom2 Γ_plus 𝒯' := by
    intro A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hU_eq
    apply h𝒯.axiom2 h1.2.2 h2.2.2 h3.2.2
    have hle1 : A₁ ≤ Γ_plus := h1.1.left_le
    have hle2 : A₂ ≤ Γ_plus := h2.1.left_le
    have hle3 : A₃ ≤ Γ_plus := h3.1.left_le
    rw [← sigmaSubgraph_union h_pres h_iso h_spaces_fin hle1 hle2,
        ← sigmaSubgraph_union h_pres h_iso h_spaces_fin (union_le hle1 hle2) hle3,
        hU_eq,
        sigmaSubgraph_drawingPlusHypergraph h_pres h_iso h_spaces_fin]
  -- Third tangle axiom for `𝒯'` via `GM10.theorem_2_7_proof`
  rw [GM10.theorem_2_7_proof hθ hsep' hord' hax1 hax2]
  intro e he hsize
  have hsep_Ke : Γ_plus.IsSeparation (GM10.edgeHypergraph Γ_plus e) (Γ_plus.deleteEdges {e}) :=
    GM10.isSeparation_edgeHypergraph_deleteEdges he
  have hord_Ke : Hypergraph.separationOrder (GM10.edgeHypergraph Γ_plus e) (Γ_plus.deleteEdges {e}) < θ := by
    rwa [GM10.separationOrder_edgeHypergraph_deleteEdges]
  rcases hax1 hsep_Ke hord_Ke with h_mem | h_rev
  · exact h_mem
  · exfalso
    have h_rev_in_𝒯 : (σ (Γ_plus.deleteEdges {e}), σ (GM10.edgeHypergraph Γ_plus e)) ∈ 𝒯 :=
      h_rev.2.2
    by_cases h_in_supp : ∃ j : Fin r, e ∈ drawingSpaces Γ ∧ e ⊆ F_star j
    · rcases h_in_supp with ⟨j, he_sp, heF⟩
      have hσ_Ke_eq : sigmaSubgraph G Γ ιV ιE r F_star μ (GM10.edgeHypergraph Γ_plus e) = μ (.space e) :=
        sigmaSubgraph_edgeHypergraph_space_eq h_pres h_iso h_spaces_fin j he_sp heF
      have hsmall : IsSmallSubgraph 𝒯 (μ (.space e)) :=
        h_surr e he_sp ⟨j, heF⟩
      have hμ_le : μ (.space e) ≤ G :=
        (h_pres.μ_space_sub j e he_sp heF).trans (h_pres.v1_sub j)
      have h71 := theorem_7_1_proof h𝒯 hμ_le
      have h_no := ((h71.1.trans h71.2).1 hsmall).2
      obtain ⟨hsep_σ, hord_σ_le⟩ :=
        theorem_7_2_claim_1 hG_graph h_pres hq_le hq hsep_Ke
      have hord_σ_lt : Hypergraph.separationOrder
          (sigmaSubgraph G Γ ιV ιE r F_star μ (GM10.edgeHypergraph Γ_plus e))
          (sigmaSubgraph G Γ ιV ιE r F_star μ (Γ_plus.deleteEdges {e})) < θ_𝒯 :=
        (hord_σ_le.trans_lt (Nat.mul_lt_mul_of_pos_left hord_Ke hq)).trans_le hθ_𝒯
      change (sigmaSubgraph G Γ ιV ιE r F_star μ (Γ_plus.deleteEdges {e}),
        sigmaSubgraph G Γ ιV ιE r F_star μ (GM10.edgeHypergraph Γ_plus e)) ∈ 𝒯 at h_rev_in_𝒯
      rw [hσ_Ke_eq] at hsep_σ hord_σ_lt h_rev_in_𝒯
      exact GM10.theorem_2_1_proof h𝒯
        (h_no (sigmaSubgraph G Γ ιV ιE r F_star μ (Γ_plus.deleteEdges {e})) hsep_σ hord_σ_lt)
        h_rev_in_𝒯
    · push Not at h_in_supp
      have he_not_supp : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → s ≠ e := by
        intro j s hs_sp hsF hse
        subst hse
        exact h_in_supp j hs_sp hsF
      have hV_eq : (σ (Γ_plus.deleteEdges {e})).vertexSet = G.vertexSet :=
        sigmaSubgraph_deleteEdges_vertexSet_eq_G h_pres h_iso h_spaces_fin he_not_supp
      exact h𝒯.axiom3 h_rev_in_𝒯 hV_eq

end Section7

end GraphMinor.GM21
