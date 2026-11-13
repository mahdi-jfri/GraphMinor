module

public import GraphMinor.GM22.Section7c5

/-!
# Graph Minors XXII – Section 7.4 (Part 1): Sufficiency and Claim (1)

This file begins the formalization of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 552–553):

- `IsAdequateFor.isSufficientFor`: adequacy implies sufficiency under `(J1)`–`(J6)`.
- `ValidConfig74`: valid counterexample configurations for the proof of (7.4).
- `lemma_7_4_claim_1`: Claim (1) of the proof of (7.4): existence of an extremal counterexample
  configuration maximizing `|E(Γ)|`, then minimizing `|V(L ∪ Γ)| + |E(L ∪ Γ)|`, then minimizing
  `|V(L)| + |E(L)|`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM09
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁

/-! ## Sufficiency from Adequacy (page 552) -/

/-- Under `(J1)`–`(J6)`, if $\mathcal{A}' \subseteq \mathcal{A}$ is adequate for a model $\phi'$,
then $\mathcal{A}'$ is sufficient for $\phi'$ (since $\Gamma$ is disjoint from $W$, any edge of
$A \cap \phi'(v)$ incident with a vertex in $W$ cannot belong to $\Gamma \cup N_W$). -/
theorem IsAdequateFor.isSufficientFor
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
    {q : ℕ} {ιV : S ↪ α} {ιE : Set S ↪ β}
    {W : Set α} {𝒜 𝒜' : Set (Graph α β)} {Γ : Drawing S} {K : Graph α β}
    {R_H : RootedDigraph αH βH q} {φV' : αH → Graph α β} {φE' : βH → β}
    (hAdeq : IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE')
    (hΓ_disj_W : Disjoint (ιV '' Γ.V) W) :
    IsSufficientFor W 𝒜 𝒜' K R_H φV' φE' where
  subset := hAdeq.subset
  mem_of_edge_inc_W := by
    intro v hv A hA ⟨e, he, w, hwW, hInc⟩
    apply hAdeq.mem_of_not_le_Γ_union_NW v hv A hA
    intro hle
    rcases hInc with ⟨y, hLink⟩
    have hLink_union : (graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β)).IsLink e w y :=
      hle.2 hLink
    rcases hLink_union with hLink_Γ | ⟨_, hLink_NW⟩
    · have hw_Γ : w ∈ V(Γ.toEmbeddedGraph ιV ιE) := hLink_Γ.left_mem
      exact Set.disjoint_left.mp hΓ_disj_W hw_Γ hwW
    · exact False.elim hLink_NW
  φV_meets := hAdeq.φV_meets
  φE_mem := hAdeq.φE_mem
  mem_of_inter_K_ne_NW := hAdeq.mem_of_inter_K_ne_NW

/-! ## Extremal Configuration Setup for Theorem 7.4 (page 553) -/

/-- A valid configuration $(\Gamma, \mathcal{T}, \phi)$ satisfying the hypotheses of Theorem 7.4
(with embeddings $\iota_V, \iota_E$ agreeing with the base embedding $\iota_{V,0}$ on $v^*$ and on
$\bar{\pi}(A)$ for all $A \in \mathcal{A}$). -/
structure ValidConfig74
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
    {q : ℕ}
    (ιV₀ : S ↪ α)
    (R_G : RootedDigraph α β q) (W : Set α)
    (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
    (orient : GM19.SurfaceOrientation S) (θ : ℕ)
    (D : Graph α β → Set S)
    (N K : Graph α β) (Δ : Set S) (v_star : S) (δ : ℕ)
    (R_H : RootedDigraph αH βH q)
    (t : ℕ) (A_fam A_fam' : Fin t → Graph α β) where
  /-- Vertex embedding into $\alpha$. -/
  ιV : S ↪ α
  /-- Edge embedding into $\beta$. -/
  ιE : Set S ↪ β
  /-- The drawing $\Gamma$ in $\Sigma$. -/
  Γ : Drawing S
  /-- The order of the tangle $\mathcal{T}$. -/
  ord : ℕ
  /-- The tangle $\mathcal{T}$ in $\Gamma$. -/
  T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))
  /-- The tangle-selected disc operator $\operatorname{ins}$. -/
  ins : Set S → Set S
  /-- The tangle metric $d$. -/
  d : Set S → Set S → ℕ
  /-- Vertex-model map $\phi_V$ of $(H, \chi)$ in $(G, \omega)$. -/
  φV : αH → Graph α β
  /-- Edge-model map $\phi_E$ of $(H, \chi)$ in $(G, \omega)$. -/
  φE : βH → β
  /-- $\iota_V$ agrees with $\iota_{V,0}$ on $v^*$ and on $\pi_S(A)$ for every $A \in \mathcal{A}$. -/
  ιV_eq : ∀ x : S, (x = v_star ∨ ∃ A ∈ 𝒜, x ∈ Set.range (πS A)) → ιV x = ιV₀ x
  /-- Conditions `(J1)`–`(J6)` hold. -/
  hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE
  /-- Condition `(J7)` holds. -/
  hJ7 : ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T
  /-- $\mathcal{B}$ is sufficient for $\phi$. -/
  hSuff : IsSufficientFor W 𝒜 ℬ K R_H φV φE
  /-- For every $A \in \mathcal{B} \setminus \{A_1, \dots, A_t\}$,
  $d(D(A), \Sigma \setminus \Delta) \ge \theta$. -/
  hdist_other : ∀ A ∈ ℬ \ Set.range A_fam,
    θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)
  /-- Hypothesis (iii) distance part: $d(v^*, D(A_i')) \ge \theta$. -/
  h_iii_dist : ∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i))
  /-- Hypothesis (iv): $d(D(A_i'), D(A_j')) \ge \theta$ for $i < j$. -/
  h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j))

namespace ValidConfig74

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
  {q : ℕ} {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
  {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
  {orient : GM19.SurfaceOrientation S} {θ : ℕ}
  {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
  {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}

/-- The union $L = \bigcup(\phi(v) : v \in V(H))$ as a subgraph of $G$. -/
noncomputable def L
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') :
    Graph α β :=
  subgraphSUnion R_G.G.toGraph (c.φV '' V(R_H.G.toGraph))

/-- The embedded graph of $\Gamma$ in $G$. -/
def Γ_emb
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') :
    Graph α β :=
  c.Γ.toEmbeddedGraph c.ιV c.ιE

/-- First minimization measure: $|E(G)| - |E(\Gamma)|$. -/
noncomputable def measure1
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') : ℕ :=
  E(R_G.G.toGraph).ncard - c.Γ.E.ncard

/-- Second minimization measure: $|V(L \cup \Gamma)| + |E(L \cup \Gamma)|$. -/
noncomputable def measure2
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') : ℕ :=
  V(graphUnion c.L c.Γ_emb).ncard + E(graphUnion c.L c.Γ_emb).ncard

/-- Third minimization measure: $|V(L)| + |E(L)|$. -/
noncomputable def measure3
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') : ℕ :=
  V(c.L).ncard + E(c.L).ncard

lemma card_Γ_E_le_card_G_E
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') :
    c.Γ.E.ncard ≤ E(R_G.G.toGraph).ncard := by
  have hsub : c.ιE '' c.Γ.E ⊆ E(R_G.G.toGraph) :=
    (c.hJ.Γ_le.trans Graph.deleteVerts_le).edgeSet_mono
  have hcard : (c.ιE '' c.Γ.E).ncard ≤ E(R_G.G.toGraph).ncard :=
    Set.ncard_le_ncard hsub c.hJ.finite_E
  rwa [Set.ncard_image_of_injective c.Γ.E c.ιE.injective] at hcard

lemma measure1_le_iff
    (c c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') :
    c.measure1 ≤ c'.measure1 ↔ c'.Γ.E.ncard ≤ c.Γ.E.ncard := by
  dsimp [measure1]
  have h1 := c.card_Γ_E_le_card_G_E
  have h2 := c'.card_Γ_E_le_card_G_E
  omega

lemma measure1_eq_iff
    (c c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') :
    c.measure1 = c'.measure1 ↔ c.Γ.E.ncard = c'.Γ.E.ncard := by
  dsimp [measure1]
  have h1 := c.card_Γ_E_le_card_G_E
  have h2 := c'.card_Γ_E_le_card_G_E
  omega

/-- A configuration `c` is extremal in the sense of Claim (1) of Theorem 7.4 (page 553). -/
def IsExtremal
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') : Prop :=
  (∀ c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam',
    c'.Γ.E.ncard ≤ c.Γ.E.ncard) ∧
  (∀ c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam',
    c'.Γ.E.ncard = c.Γ.E.ncard → c.measure2 ≤ c'.measure2) ∧
  (∀ c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam',
    c'.Γ.E.ncard = c.Γ.E.ncard → c'.measure2 = c.measure2 → c.measure3 ≤ c'.measure3)

end ValidConfig74

/-- **Graph Minors XXII, (7.4) Claim (1)** (page 553):
If there exists a valid configuration for Theorem 7.4, then there exists one with:
- $|E(\Gamma)|$ maximum (equivalently $|E(G)| - |E(\Gamma)|$ minimum),
- subject to that, with $|V(L \cup \Gamma)| + |E(L \cup \Gamma)|$ minimum, where
  $L = \bigcup(\phi(v) : v \in V(H))$, and
- subject to that, with $|V(L)| + |E(L)|$ minimum. -/
theorem lemma_7_4_claim_1
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c₀ : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam') :
    ∃ c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam',
      c.IsExtremal := by
  let C := ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam'
  -- Step 1: minimize `measure1`.
  have hne1 : (Set.range (ValidConfig74.measure1 (ιV₀ := ιV₀) (R_G := R_G) (W := W)
      (𝒜 := 𝒜) (ℬ := ℬ) (πLen := πLen) (πS := πS) (orient := orient) (θ := θ)
      (D := D) (N := N) (K := K) (Δ := Δ) (v_star := v_star) (δ := δ)
      (R_H := R_H) (t := t) (A_fam := A_fam) (A_fam' := A_fam'))).Nonempty :=
    ⟨c₀.measure1, c₀, rfl⟩
  obtain ⟨m₁, ⟨c₁, rfl⟩, hm₁_min⟩ := wellFounded_lt.has_min _ hne1
  let S₁ : Set C := {c : C | c.measure1 = c₁.measure1}
  have hc₁_S₁ : c₁ ∈ S₁ := rfl
  have hS₁_min : ∀ c' : C, c₁.measure1 ≤ c'.measure1 := by
    intro c'
    exact not_lt.mp (hm₁_min c'.measure1 ⟨c', rfl⟩)
  -- Step 2: minimize `measure2` on `S₁`.
  have hne2 : (ValidConfig74.measure2 '' S₁).Nonempty := ⟨c₁.measure2, c₁, hc₁_S₁, rfl⟩
  obtain ⟨m₂, ⟨c₂, hc₂_S₁, rfl⟩, hm₂_min⟩ := wellFounded_lt.has_min _ hne2
  let S₂ : Set C := {c ∈ S₁ | c.measure2 = c₂.measure2}
  have hc₂_S₂ : c₂ ∈ S₂ := ⟨hc₂_S₁, rfl⟩
  have hS₂_min : ∀ c' ∈ S₁, c₂.measure2 ≤ c'.measure2 := by
    intro c' hc'
    exact not_lt.mp (hm₂_min c'.measure2 ⟨c', hc', rfl⟩)
  -- Step 3: minimize `measure3` on `S₂`.
  have hne3 : (ValidConfig74.measure3 '' S₂).Nonempty := ⟨c₂.measure3, c₂, hc₂_S₂, rfl⟩
  obtain ⟨m₃, ⟨c₃, hc₃_S₂, rfl⟩, hm₃_min⟩ := wellFounded_lt.has_min _ hne3
  have hS₃_min : ∀ c' ∈ S₂, c₃.measure3 ≤ c'.measure3 := by
    intro c' hc'
    exact not_lt.mp (hm₃_min c'.measure3 ⟨c', hc', rfl⟩)
  refine ⟨c₃, ?_, ?_, ?_⟩
  · intro c'
    have hm1 : c₃.measure1 = c₁.measure1 := hc₃_S₂.1
    have hle : c₃.measure1 ≤ c'.measure1 := hm1.trans_le (hS₁_min c')
    exact (ValidConfig74.measure1_le_iff c₃ c').mp hle
  · intro c' hE_eq
    have hm1_c3 : c₃.measure1 = c₁.measure1 := hc₃_S₂.1
    have hm1_c' : c'.measure1 = c₁.measure1 := by
      have := (ValidConfig74.measure1_eq_iff c' c₃).mpr hE_eq
      exact this.trans hm1_c3
    have hc'_S₁ : c' ∈ S₁ := hm1_c'
    exact hc₃_S₂.2.trans_le (hS₂_min c' hc'_S₁)
  · intro c' hE_eq hM2_eq
    have hm1_c3 : c₃.measure1 = c₁.measure1 := hc₃_S₂.1
    have hm1_c' : c'.measure1 = c₁.measure1 :=
      ((ValidConfig74.measure1_eq_iff c' c₃).mpr hE_eq).trans hm1_c3
    have hc'_S₂ : c' ∈ S₂ := ⟨hm1_c', hM2_eq.trans hc₃_S₂.2⟩
    exact hS₃_min c' hc'_S₂

end GraphMinor.GM22
