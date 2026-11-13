module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM10.TreeWidth
public import GraphMinor.GM10.Section8
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM10.Section6

/-!
# Graph Minors XXI, Section 3: Tangles

This file formalizes Section 3 of N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616 (pages 8–10 of the preprint):
- `theorem_3_1`: **Graph Minors XXI, (3.1)** (page 8 of the preprint), relating tree-width
  and tangle order via Graph Minors X, (5.2).
- `theorem_3_2`: **Graph Minors XXI, (3.2)** (page 9 of the preprint), `𝒯 \ W` is a tangle
  of order `θ - |W|` in `G \ W` (Graph Minors X, (8.5)).
- `theorem_3_3`: **Graph Minors XXI, (3.3)** (page 9 of the preprint), restriction of a
  tangle across a separation `(C, D) ∈ 𝒯` of order `0`.
- `theorem_3_4`: **Graph Minors XXI, (3.4)** (page 9 of the preprint), the tangle in `G`
  induced by a tangle in a subgraph `G' ≤ G`.
- `theorem_3_5`: **Graph Minors XXI, (3.5)** (page 9 of the preprint), restricting a tangle
  to `B₀` for `(A₀, B₀) ∈ 𝒯`.
- `theorem_3_6`: **Graph Minors XXI, (3.6)** (page 10 of the preprint), splitting a vertex
  lowers tangle order by at most `1`.
- `theorem_3_7`: **Graph Minors XXI, (3.7)** (page 10 of the preprint), the `θ`-truncation
  of a tangle.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-! ## (3.1): Tree-width and tangle order -/

/-- **Graph Minors XXI, (3.1)** (Section 3, page 8 of the preprint):
"If a graph $G$ has tree-width $w$, then $G$ has a tangle of order $\ge \frac{2}{3}(w + 1)$, and
has no tangle of order $> w + 1$."
Proved from Graph Minors X, (5.2) (`GM10.theorem_5_2_proof`). -/
theorem theorem_3_1_proof (G : Hypergraph α β) (w : ℕ) (hw : treeWidthPlusOne G = w + 1) :
    (∃ (θ : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle G θ 𝒯 ∧ 2 * (w + 1) ≤ 3 * θ) ∧
    (∀ (θ : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle G θ 𝒯 → θ ≤ w + 1) := by
  have h52 := GM10.theorem_5_2_proof G
  rw [hw] at h52
  rcases h52 with ⟨hle_w, hge_w⟩
  refine ⟨?_, ?_⟩
  · have hθ_pos : 1 ≤ tangleNumber G := by omega
    obtain ⟨𝒯, h𝒯⟩ := GM10.exists_isTangle_of_le_tangleNumber hθ_pos le_rfl
    exact ⟨tangleNumber G, 𝒯, h𝒯, hge_w⟩
  · intro θ 𝒯 h𝒯
    have hle : θ ≤ tangleNumber G := h𝒯.le_tangleNumber
    exact hle.trans hle_w

/-! ## (3.2): Deleting vertices `W` from a tangle -/

/-- The set `𝒯 \ W` of separations of `G \ W` (Graph Minors XXI, Section 3, page 8 of the preprint):
`{(A \ W, B \ W) : (A, B) ∈ 𝒯, W ⊆ V(A ∩ B)}`. -/
abbrev deleteVerticesTangle (G : Hypergraph α β) (W : Set α)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  GM10.deleteVerticesTangle G W 𝒯 θ

/-- **Graph Minors XXI, (3.2)** (Section 3, page 9 of the preprint):
"With $\mathcal{T}, \theta, G, W$ as above, $\mathcal{T} \setminus W$ is a tangle of order
$\theta - |W|$ in $G \setminus W$."
Proved from Graph Minors X, (8.5) (`GM10.theorem_8_5_proof`). -/
theorem theorem_3_2_proof {G : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hcard : W.ncard < θ) :
    IsTangle (G.deleteVertices W) (θ - W.ncard) (deleteVerticesTangle G W 𝒯 θ) := by
  have h85 : IsTangle (G.deleteVertices W) (θ - W.ncard) (GM10.deleteVerticesTangle G W 𝒯 θ) :=
    GM10.theorem_8_5_proof hG h𝒯 hW hcard
  exact h85

/-! ## (3.3): Restricting a tangle across an order-0 separation -/

/-- The restriction `{(A ∩ D, B ∩ D) : (A, B) ∈ 𝒯}` of a tangle `𝒯` in `G` to `D` across an
order-0 separation `(C, D) ∈ 𝒯` (Graph Minors XXI, (3.3), page 9 of the preprint). -/
def restrictOrderZeroTangle (D : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | ∃ A B : Hypergraph α β, (A, B) ∈ 𝒯 ∧ p.1 = A ∩ D ∧ p.2 = B ∩ D}

private lemma separationOrder_inter_le {A B D : Hypergraph α β} :
    separationOrder (A ∩ D) (B ∩ D) ≤ separationOrder A B := by
  have hsub : ((A ∩ D) ∩ (B ∩ D)).vertexSet ⊆ (A ∩ B).vertexSet := by
    intro v hv
    exact ⟨hv.1.1, hv.2.1⟩
  exact Set.ncard_le_ncard hsub (A ∩ B).vertexSet_finite

private lemma disjoint_vertexSet_of_separationOrder_eq_zero {C D : Hypergraph α β}
    (hord : separationOrder C D = 0) :
    Disjoint C.vertexSet D.vertexSet := by
  rw [Set.disjoint_iff_inter_eq_empty]
  exact (Set.ncard_eq_zero (C ∩ D).vertexSet_finite).1 hord

private lemma lift_separation_of_order_zero {G C D A' B' : Hypergraph α β}
    (hCD : G.IsSeparation C D) (hord0 : separationOrder C D = 0)
    (hAB' : D.IsSeparation A' B') :
    G.IsSeparation (C ∪ A') B' ∧
      separationOrder (C ∪ A') B' = separationOrder A' B' ∧
      (C ∪ A') ∩ D = A' ∧
      B' ∩ D = B' := by
  have hdisV : Disjoint C.vertexSet D.vertexSet :=
    disjoint_vertexSet_of_separationOrder_eq_zero hord0
  have hdisE : Disjoint C.edgeSet D.edgeSet := hCD.disjoint_edgeSet
  have hA'_le_G : A' ≤ G := hAB'.left_le.trans hCD.right_le
  have hB'_le_G : B' ≤ G := hAB'.right_le.trans hCD.right_le
  have hCA'_le_G : C ∪ A' ≤ G := GM10.union_le hCD.left_le hA'_le_G
  have hsepG : G.IsSeparation (C ∪ A') B' := by
    rw [GM10.isSeparation_iff_of_le hCA'_le_G hB'_le_G]
    refine ⟨?_, ?_, ?_⟩
    · change (C.vertexSet ∪ A'.vertexSet) ∪ B'.vertexSet = G.vertexSet
      rw [Set.union_assoc, hAB'.vertexSet_union, hCD.vertexSet_union]
    · change (C.edgeSet ∪ A'.edgeSet) ∪ B'.edgeSet = G.edgeSet
      rw [Set.union_assoc, hAB'.edgeSet_union, hCD.edgeSet_union]
    · ext e
      change e ∈ (C.edgeSet ∪ A'.edgeSet) ∩ B'.edgeSet ↔ e ∈ (∅ : Set β)
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]
      rintro ⟨heC | heA', heB'⟩
      · exact Set.disjoint_left.1 hdisE heC (hAB'.right_le.edgeSet_subset heB')
      · exact hAB'.notMem_edgeSet_right heA' heB'
  have hV_inter : ((C ∪ A') ∩ B').vertexSet = (A' ∩ B').vertexSet := by
    ext v
    simp only [GM10.inter_vertexSet, GM10.union_vertexSet, Set.mem_inter_iff, Set.mem_union]
    refine ⟨?_, fun ⟨hvA', hvB'⟩ ↦ ⟨Or.inr hvA', hvB'⟩⟩
    rintro ⟨hvC | hvA', hvB'⟩
    · exfalso
      exact Set.disjoint_left.1 hdisV hvC (hAB'.right_le.vertexSet_subset hvB')
    · exact ⟨hvA', hvB'⟩
  have hord_eq : separationOrder (C ∪ A') B' = separationOrder A' B' := by
    unfold separationOrder
    rw [hV_inter]
  have hCA'_inter_D : (C ∪ A') ∩ D = A' := by
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (GM10.inter_le hCA'_le_G hCD.right_le) hA'_le_G ?_ ?_
    · ext v
      simp only [GM10.inter_vertexSet, GM10.union_vertexSet, Set.mem_inter_iff, Set.mem_union]
      refine ⟨?_, fun hvA' ↦ ⟨Or.inr hvA', hAB'.left_le.vertexSet_subset hvA'⟩⟩
      rintro ⟨hvC | hvA', hvD⟩
      · exact (Set.disjoint_left.1 hdisV hvC hvD).elim
      · exact hvA'
    · ext e
      simp only [GM10.inter_edgeSet, GM10.union_edgeSet, Set.mem_inter_iff, Set.mem_union]
      refine ⟨?_, fun heA' ↦ ⟨Or.inr heA', hAB'.left_le.edgeSet_subset heA'⟩⟩
      rintro ⟨heC | heA', heD⟩
      · exact (Set.disjoint_left.1 hdisE heC heD).elim
      · exact heA'
  have hB'_inter_D : B' ∩ D = B' := by
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (GM10.inter_le hB'_le_G hCD.right_le) hB'_le_G ?_ ?_
    · exact Set.inter_eq_left.2 hAB'.right_le.vertexSet_subset
    · exact Set.inter_eq_left.2 hAB'.right_le.edgeSet_subset
  exact ⟨hsepG, hord_eq, hCA'_inter_D, hB'_inter_D⟩

private lemma separationOrder_union_order_zero {C D A B : Hypergraph α β}
    (hord0 : separationOrder C D = 0) :
    separationOrder (C ∪ A) (D ∩ B) ≤ separationOrder A B := by
  have hdisV : Disjoint C.vertexSet D.vertexSet :=
    disjoint_vertexSet_of_separationOrder_eq_zero hord0
  have hsub : ((C ∪ A) ∩ (D ∩ B)).vertexSet ⊆ (A ∩ B).vertexSet := by
    rintro v ⟨hvC | hvA, hvD, hvB⟩
    · exact (Set.disjoint_left.1 hdisV hvC hvD).elim
    · exact ⟨hvA, hvB⟩
  exact Set.ncard_le_ncard hsub (A ∩ B).vertexSet_finite

/-- **Graph Minors XXI, (3.3)** (Section 3, page 9 of the preprint):
"Let $\mathcal{T}$ be a tangle in a graph $G$, and let $(C, D) \in \mathcal{T}$ of order $0$. Let
$$\mathcal{T}' = \{(A \cap D, B \cap D) : (A, B) \in \mathcal{T}\}.$$
Then $\mathcal{T}'$ is a tangle in $B$ of the same order as $\mathcal{T}$."

The print's $B$ is a misprint for $D$, and Lean uses $D$ (see the correction to (3.3) in
`corrections/GM21.md`). -/
theorem theorem_3_3_proof {G C D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hCD : (C, D) ∈ 𝒯) (hord0 : separationOrder C D = 0) :
    IsTangle D θ (restrictOrderZeroTangle D 𝒯) where
  one_le := h𝒯.one_le
  isSeparation A' B' h := by
    rcases h with ⟨A, B, hAB, rfl, rfl⟩
    have hsep := h𝒯.isSeparation hAB
    have hsepD := hsep.inter_left (h𝒯.isSeparation hCD).right_le
    simpa [GM10.inter_comm D A, GM10.inter_comm D B] using hsepD
  order_lt A' B' h := by
    rcases h with ⟨A, B, hAB, rfl, rfl⟩
    exact separationOrder_inter_le.trans_lt (h𝒯.order_lt hAB)
  axiom1 A' B' hsep' hord' := by
    have hCD_sep := h𝒯.isSeparation hCD
    obtain ⟨hsepG, hordG, hCA', hB'⟩ := lift_separation_of_order_zero hCD_sep hord0 hsep'
    rcases h𝒯.axiom1 hsepG (hordG.trans_lt hord') with hm | hm
    · exact Or.inl ⟨C ∪ A', B', hm, hCA'.symm, hB'.symm⟩
    · exact Or.inr ⟨B', C ∪ A', hm, hB'.symm, hCA'.symm⟩
  axiom2 A₁' B₁' A₂' B₂' A₃' B₃' h₁ h₂ h₃ hU := by
    rcases h₁ with ⟨A₁, B₁, hm₁, rfl, rfl⟩
    rcases h₂ with ⟨A₂, B₂, hm₂, rfl, rfl⟩
    rcases h₃ with ⟨A₃, B₃, hm₃, rfl, rfl⟩
    have hord_CA₁ : separationOrder (C ∪ A₁) (D ∩ B₁) < θ :=
      (separationOrder_union_order_zero hord0).trans_lt (h𝒯.order_lt hm₁)
    have hm_CA₁ : (C ∪ A₁, D ∩ B₁) ∈ 𝒯 := GM10.theorem_2_2_proof h𝒯 hCD hm₁ hord_CA₁
    apply h𝒯.axiom2 hm_CA₁ hm₂ hm₃
    have hCD_sep := h𝒯.isSeparation hCD
    have hle₁ := (h𝒯.isSeparation hm_CA₁).left_le
    have hle₂ := (h𝒯.isSeparation hm₂).left_le
    have hle₃ := (h𝒯.isSeparation hm₃).left_le
    have hU_le : (C ∪ A₁) ∪ A₂ ∪ A₃ ≤ G := GM10.union_le (GM10.union_le hle₁ hle₂) hle₃
    have hVD : ((A₁ ∩ D) ∪ (A₂ ∩ D) ∪ (A₃ ∩ D)).vertexSet = D.vertexSet :=
      congrArg Hypergraph.vertexSet hU
    have hED : ((A₁ ∩ D) ∪ (A₂ ∩ D) ∪ (A₃ ∩ D)).edgeSet = D.edgeSet :=
      congrArg Hypergraph.edgeSet hU
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
    · ext v
      refine ⟨fun hv ↦ hU_le.vertexSet_subset hv, fun hvG ↦ ?_⟩
      rcases (hCD_sep.vertexSet_union.symm ▸ hvG) with hvC | hvD
      · exact Or.inl (Or.inl (Or.inl hvC))
      · rcases (hVD.symm ▸ hvD) with (⟨hv₁, _⟩ | ⟨hv₂, _⟩) | ⟨hv₃, _⟩
        · exact Or.inl (Or.inl (Or.inr hv₁))
        · exact Or.inl (Or.inr hv₂)
        · exact Or.inr hv₃
    · ext e
      refine ⟨fun he ↦ hU_le.edgeSet_subset he, fun heG ↦ ?_⟩
      rcases (hCD_sep.edgeSet_union.symm ▸ heG) with heC | heD
      · exact Or.inl (Or.inl (Or.inl heC))
      · rcases (hED.symm ▸ heD) with (⟨he₁, _⟩ | ⟨he₂, _⟩) | ⟨he₃, _⟩
        · exact Or.inl (Or.inl (Or.inr he₁))
        · exact Or.inl (Or.inr he₂)
        · exact Or.inr he₃
  axiom3 A' B' h hVA' := by
    rcases h with ⟨A, B, hm, rfl, rfl⟩
    have hord_CA : separationOrder (C ∪ A) (D ∩ B) < θ :=
      (separationOrder_union_order_zero hord0).trans_lt (h𝒯.order_lt hm)
    have hm_CA : (C ∪ A, D ∩ B) ∈ 𝒯 := GM10.theorem_2_2_proof h𝒯 hCD hm hord_CA
    apply h𝒯.axiom3 hm_CA
    have hCD_sep := h𝒯.isSeparation hCD
    have hle_CA := (h𝒯.isSeparation hm_CA).left_le
    refine Set.Subset.antisymm hle_CA.vertexSet_subset ?_
    intro v hvG
    rcases (hCD_sep.vertexSet_union.symm ▸ hvG) with hvC | hvD
    · exact Or.inl hvC
    · have hvAD : v ∈ (A ∩ D).vertexSet := hVA'.symm ▸ hvD
      exact Or.inr hvAD.1

/-! ## (3.4): Tangle induced by a subgraph -/

/-- **Graph Minors XXI, (3.4)** (Section 3, page 9 of the preprint):
"Let $G'$ be a subgraph of $G$, and let $\mathcal{T}'$ be a tangle in $G'$. Let $\mathcal{T}$ be
the set of all separations $(A, B)$ of $G$ of order $< ord(\mathcal{T}')$ such that
$(A \cap G', B \cap G') \in \mathcal{T}'$. Then $\mathcal{T}$ is a tangle in $G$ of order
$ord(\mathcal{T}')$." -/
theorem theorem_3_4_proof {G G' : Hypergraph α β} (hG' : G' ≤ G) {θ : ℕ}
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : IsTangle G' θ 𝒯') :
    IsTangle G θ (GM12.inducedBySubgraph G G' θ 𝒯') where
  one_le := h𝒯'.one_le
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have hsep' : G'.IsSeparation (A ∩ G') (B ∩ G') := by
      simpa [GM10.inter_comm G' A, GM10.inter_comm G' B] using hsep.inter_left hG'
    have hord' : separationOrder (A ∩ G') (B ∩ G') < θ :=
      separationOrder_inter_le.trans_lt hord
    rcases h𝒯'.axiom1 hsep' hord' with hm | hm
    · exact Or.inl ⟨hsep, hord, hm⟩
    · exact Or.inr ⟨hsep.symm, by rwa [GM10.separationOrder_comm], hm⟩
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU := by
    apply h𝒯'.axiom2 h₁.2.2 h₂.2.2 h₃.2.2
    have hle₁ := (h𝒯'.isSeparation h₁.2.2).left_le
    have hle₂ := (h𝒯'.isSeparation h₂.2.2).left_le
    have hle₃ := (h𝒯'.isSeparation h₃.2.2).left_le
    have hU_le : (A₁ ∩ G') ∪ (A₂ ∩ G') ∪ (A₃ ∩ G') ≤ G' :=
      GM10.union_le (GM10.union_le hle₁ hle₂) hle₃
    have hVG : (A₁ ∪ A₂ ∪ A₃).vertexSet = G.vertexSet := congrArg Hypergraph.vertexSet hU
    have hEG : (A₁ ∪ A₂ ∪ A₃).edgeSet = G.edgeSet := congrArg Hypergraph.edgeSet hU
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
    · ext v
      refine ⟨fun hv ↦ hU_le.vertexSet_subset hv, fun hvG' ↦ ?_⟩
      have hvG : v ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hVG.symm ▸ hG'.vertexSet_subset hvG'
      rcases hvG with (hv₁ | hv₂) | hv₃
      · exact Or.inl (Or.inl ⟨hv₁, hvG'⟩)
      · exact Or.inl (Or.inr ⟨hv₂, hvG'⟩)
      · exact Or.inr ⟨hv₃, hvG'⟩
    · ext e
      refine ⟨fun he ↦ hU_le.edgeSet_subset he, fun heG' ↦ ?_⟩
      have heG : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := hEG.symm ▸ hG'.edgeSet_subset heG'
      rcases heG with (he₁ | he₂) | he₃
      · exact Or.inl (Or.inl ⟨he₁, heG'⟩)
      · exact Or.inl (Or.inr ⟨he₂, heG'⟩)
      · exact Or.inr ⟨he₃, heG'⟩
  axiom3 A B h hVA := by
    apply h𝒯'.axiom3 h.2.2
    change A.vertexSet ∩ G'.vertexSet = G'.vertexSet
    rw [hVA, Set.inter_eq_right.2 hG'.vertexSet_subset]

/-! ## (3.5): Restricting a tangle to `B₀` for `(A₀, B₀) ∈ 𝒯` -/

/-- The subhypergraph `A` of `G` with vertex set `A.vertexSet ∪ W` and edge set `A.edgeSet`
(used in the proof of **Graph Minors XXI, (3.5)**, page 9 of the preprint). -/
def addVerticesSubhypergraph (G A : Hypergraph α β) (W : Set α)
    (hA : A ≤ G) (hW : W ⊆ G.vertexSet) : Hypergraph α β where
  vertexSet := A.vertexSet ∪ W
  edgeSet := A.edgeSet
  Inc e v := A.Inc e v
  vertex_mem_of_inc _ _ h := Or.inl (A.vertex_mem_of_inc h)
  edge_mem_of_inc _ _ h := A.edge_mem_of_inc h
  vertexSet_finite := G.vertexSet_finite.subset (Set.union_subset hA.vertexSet_subset hW)
  edgeSet_finite := A.edgeSet_finite

private lemma addVerticesSubhypergraph_le {G A : Hypergraph α β} {W : Set α}
    (hA : A ≤ G) (hW : W ⊆ G.vertexSet) :
    addVerticesSubhypergraph G A W hA hW ≤ G where
  vertexSet_subset := Set.union_subset hA.vertexSet_subset hW
  edgeSet_subset := hA.edgeSet_subset
  ends_eq e he := hA.ends_eq e he

private lemma addVerticesSubhypergraph_isSeparation {G A B : Hypergraph α β} {W : Set α}
    (hsep : G.IsSeparation A B) (hW : W ⊆ G.vertexSet) :
    G.IsSeparation
      (addVerticesSubhypergraph G A W hsep.left_le hW)
      (addVerticesSubhypergraph G B W hsep.right_le hW) := by
  have hleA := addVerticesSubhypergraph_le hsep.left_le hW
  have hleB := addVerticesSubhypergraph_le hsep.right_le hW
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, hsep.edgeSet_union, hsep.edgeSet_inter_eq⟩
  change (A.vertexSet ∪ W) ∪ (B.vertexSet ∪ W) = G.vertexSet
  ext v
  simp only [Set.mem_union]
  refine ⟨?_, fun hvG ↦ ?_⟩
  · rintro ((hvA | hvW) | (hvB | hvW))
    · exact hsep.left_le.vertexSet_subset hvA
    · exact hW hvW
    · exact hsep.right_le.vertexSet_subset hvB
    · exact hW hvW
  · rcases (hsep.vertexSet_union.symm ▸ hvG) with hvA | hvB
    · exact Or.inl (Or.inl hvA)
    · exact Or.inr (Or.inl hvB)

private lemma addVerticesSubhypergraph_separationOrder_le {G A B : Hypergraph α β} {W : Set α}
    (hsep : G.IsSeparation A B) (hW : W ⊆ G.vertexSet) :
    separationOrder
      (addVerticesSubhypergraph G A W hsep.left_le hW)
      (addVerticesSubhypergraph G B W hsep.right_le hW) ≤
      separationOrder A B + W.ncard := by
  have h_eq :
      ((addVerticesSubhypergraph G A W hsep.left_le hW) ∩
        (addVerticesSubhypergraph G B W hsep.right_le hW)).vertexSet =
      (A ∩ B).vertexSet ∪ W := by
    ext v
    change (v ∈ A.vertexSet ∨ v ∈ W) ∧ (v ∈ B.vertexSet ∨ v ∈ W) ↔
      (v ∈ A.vertexSet ∧ v ∈ B.vertexSet) ∨ v ∈ W
    tauto
  unfold separationOrder
  rw [h_eq]
  exact Set.ncard_union_le (A ∩ B).vertexSet W

private lemma deleteVertices_addVerticesSubhypergraph_eq {G A : Hypergraph α β} {W : Set α}
    (hA : A ≤ G) (hW : W ⊆ G.vertexSet) :
    (addVerticesSubhypergraph G A W hA hW).deleteVertices W = A.deleteVertices W := by
  have h1 : (addVerticesSubhypergraph G A W hA hW).deleteVertices W ≤ G :=
    (GM10.deleteVertices_le _ W).trans (addVerticesSubhypergraph_le hA hW)
  have h2 : A.deleteVertices W ≤ G := (GM10.deleteVertices_le A W).trans hA
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ rfl
  ext v
  change (v ∈ A.vertexSet ∨ v ∈ W) ∧ v ∉ W ↔ v ∈ A.vertexSet ∧ v ∉ W
  tauto

private lemma deleteVertices_inter_deleteVertices_eq {G A B₀ : Hypergraph α β} {W : Set α}
    (hA : A ≤ G) (hB₀ : B₀ ≤ G) :
    (A.deleteVertices W) ∩ (B₀.deleteVertices W) = (A ∩ B₀) ∩ (B₀.deleteVertices W) := by
  have h1 : (A.deleteVertices W) ∩ (B₀.deleteVertices W) ≤ G :=
    GM10.inter_le ((GM10.deleteVertices_le A W).trans hA) ((GM10.deleteVertices_le B₀ W).trans hB₀)
  have h2 : (A ∩ B₀) ∩ (B₀.deleteVertices W) ≤ G :=
    GM10.inter_le (GM10.inter_le hA hB₀) ((GM10.deleteVertices_le B₀ W).trans hB₀)
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ ?_
  · ext v
    change (v ∈ A.vertexSet ∧ v ∉ W) ∧ (v ∈ B₀.vertexSet ∧ v ∉ W) ↔
      (v ∈ A.vertexSet ∧ v ∈ B₀.vertexSet) ∧ (v ∈ B₀.vertexSet ∧ v ∉ W)
    tauto
  · ext e
    simp only [GM10.inter_edgeSet, deleteVertices, Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun ⟨⟨heA, _⟩, ⟨heB₀, hnoB₀⟩⟩ ↦ ⟨⟨heA, heB₀⟩, ⟨heB₀, hnoB₀⟩⟩, ?_⟩
    rintro ⟨⟨heA, heB₀⟩, ⟨_, hnoB₀⟩⟩
    refine ⟨⟨heA, fun w hwW hincA ↦ hnoB₀ w hwW ?_⟩, ⟨heB₀, hnoB₀⟩⟩
    have hincG : G.Inc e w := GM10.inc_of_le hA hincA
    exact (GM10.inc_iff_of_le hB₀ heB₀).2 hincG

private lemma deleteVertices_mono {A G : Hypergraph α β} (h : A ≤ G) (W : Set α) :
    A.deleteVertices W ≤ G.deleteVertices W where
  vertexSet_subset := Set.sdiff_subset_sdiff h.vertexSet_subset Subset.rfl
  edgeSet_subset e he :=
    ⟨h.edgeSet_subset he.1, fun w hwW hincG ↦ he.2 w hwW ((GM10.inc_iff_of_le h he.1).2 hincG)⟩
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, Set.mem_ofPred_eq, deleteVertices]
    rw [GM10.inc_iff_of_le h he.1]
    exact ⟨fun ⟨hinc, _⟩ ↦ ⟨hinc, he.2⟩, fun ⟨hinc, _⟩ ↦ ⟨hinc, fun w hwW hA ↦
      he.2 w hwW ((GM10.inc_iff_of_le h he.1).2 hA)⟩⟩

private lemma isSeparation_deleteVertices_of_isSeparation {G A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) (W : Set α) :
    (G.deleteVertices W).IsSeparation (A.deleteVertices W) (B.deleteVertices W) := by
  have hleA := deleteVertices_mono hsep.left_le W
  have hleB := deleteVertices_mono hsep.right_le W
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · change (A.vertexSet \ W) ∪ (B.vertexSet \ W) = G.vertexSet \ W
    rw [← Set.union_sdiff_distrib, hsep.vertexSet_union]
  · ext e
    simp only [Set.mem_union, deleteVertices, Set.mem_ofPred_eq]
    constructor
    · rintro (he | he)
      · exact hleA.edgeSet_subset he
      · exact hleB.edgeSet_subset he
    · rintro ⟨heG, hnoW⟩
      rcases (hsep.edgeSet_union.symm ▸ heG) with heA | heB
      · exact Or.inl ⟨heA, fun w hwW hincA ↦ hnoW w hwW (GM10.inc_of_le hsep.left_le hincA)⟩
      · exact Or.inr ⟨heB, fun w hwW hincB ↦ hnoW w hwW (GM10.inc_of_le hsep.right_le hincB)⟩
  · ext e
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨heA, _⟩, ⟨heB, _⟩⟩
    exact hsep.notMem_edgeSet_right heA heB

/-- First step of **Graph Minors XXI, (3.5)** (Section 3, page 9 of the preprint):
for `(A₀, B₀) ∈ 𝒯`, deleting `W = V(A₀ ∩ B₀)` by `(3.2)` and restricting to `B₀ \ W` along the
order-0 separation `(A₀ \ W, B₀ \ W)` by `(3.3)` produces a tangle in `B₀ \ W` of order
`θ - |V(A₀ ∩ B₀)|`. -/
theorem theorem_3_5_deleteVertices {G A₀ B₀ : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hAB₀ : (A₀, B₀) ∈ 𝒯) :
    IsTangle (B₀.deleteVertices (A₀ ∩ B₀).vertexSet) (θ - separationOrder A₀ B₀)
      (restrictOrderZeroTangle (B₀.deleteVertices (A₀ ∩ B₀).vertexSet)
        (deleteVerticesTangle G (A₀ ∩ B₀).vertexSet 𝒯 θ)) := by
  let W : Set α := (A₀ ∩ B₀).vertexSet
  have hW_eq : W.ncard = separationOrder A₀ B₀ := rfl
  have hsep₀ : G.IsSeparation A₀ B₀ := h𝒯.isSeparation hAB₀
  have hW_sub : W ⊆ G.vertexSet :=
    (GM10.inter_le hsep₀.left_le hsep₀.right_le).vertexSet_subset
  have hW_lt : W.ncard < θ := h𝒯.order_lt hAB₀
  have h𝒯_W : IsTangle (G.deleteVertices W) (θ - W.ncard) (deleteVerticesTangle G W 𝒯 θ) :=
    theorem_3_2_proof hG h𝒯 hW_sub hW_lt
  have hAB₀_W_sep : (G.deleteVertices W).IsSeparation
      (A₀.deleteVertices W) (B₀.deleteVertices W) :=
    isSeparation_deleteVertices_of_isSeparation hsep₀ W
  have hAB₀_W_ord : separationOrder (A₀.deleteVertices W) (B₀.deleteVertices W) = 0 := by
    have hemp : ((A₀.deleteVertices W) ∩ (B₀.deleteVertices W)).vertexSet = ∅ := by
      ext v
      change v ∈ (A₀.vertexSet \ W) ∩ (B₀.vertexSet \ W) ↔ False
      simp only [W, GM10.inter_vertexSet, Set.mem_inter_iff, Set.mem_sdiff, iff_false]
      rintro ⟨⟨hvA₀, hnotW⟩, ⟨hvB₀, _⟩⟩
      exact hnotW ⟨hvA₀, hvB₀⟩
    unfold separationOrder
    rw [hemp, Set.ncard_empty]
  have hAB₀_W_mem : (A₀.deleteVertices W, B₀.deleteVertices W) ∈
      deleteVerticesTangle G W 𝒯 θ := by
    refine ⟨hAB₀_W_sep, ?_, ⟨(A₀, B₀), hAB₀, Subset.rfl, rfl, rfl⟩⟩
    rw [hAB₀_W_ord]
    omega
  exact theorem_3_3_proof h𝒯_W hAB₀_W_mem hAB₀_W_ord

/-- **Graph Minors XXI, (3.5)** (Section 3, page 9 of the preprint):
"Let $\mathcal{T}$ be a tangle in $G$ and let $(A_0, B_0) \in \mathcal{T}$. Then there is a tangle
$\mathcal{T}_0$ in $B_0$ of order $ord(\mathcal{T}) - |V(A_0 \cap B_0)|$, such that
$(A \cap B_0, B \cap B_0) \in \mathcal{T}_0$ for every $(A, B) \in \mathcal{T}$ of order
$< ord(\mathcal{T}) - |V(A_0 \cap B_0)|$." -/
theorem theorem_3_5_proof {G A₀ B₀ : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hAB₀ : (A₀, B₀) ∈ 𝒯) :
    ∃ 𝒯₀ : Set (Hypergraph α β × Hypergraph α β),
      IsTangle B₀ (θ - separationOrder A₀ B₀) 𝒯₀ ∧
      ∀ A B : Hypergraph α β, (A, B) ∈ 𝒯 →
        separationOrder A B < θ - separationOrder A₀ B₀ →
        (A ∩ B₀, B ∩ B₀) ∈ 𝒯₀ := by
  let W : Set α := (A₀ ∩ B₀).vertexSet
  have hW_eq : W.ncard = separationOrder A₀ B₀ := rfl
  have hsep₀ : G.IsSeparation A₀ B₀ := h𝒯.isSeparation hAB₀
  have hW_sub : W ⊆ G.vertexSet :=
    (GM10.inter_le hsep₀.left_le hsep₀.right_le).vertexSet_subset
  -- By (3.2) and (3.3), `𝒯₁` is a tangle in `B₀ \ W` of order `θ - |W|`.
  let 𝒯₁ := restrictOrderZeroTangle (B₀.deleteVertices W) (deleteVerticesTangle G W 𝒯 θ)
  have h𝒯₁ : IsTangle (B₀.deleteVertices W) (θ - W.ncard) 𝒯₁ :=
    theorem_3_5_deleteVertices hG h𝒯 hAB₀
  -- By (3.4), `𝒯₀` is the tangle in `B₀` of order `θ - |W|` induced by `𝒯₁`.
  let 𝒯₀ := GM12.inducedBySubgraph B₀ (B₀.deleteVertices W) (θ - W.ncard) 𝒯₁
  have h𝒯₀ : IsTangle B₀ (θ - W.ncard) 𝒯₀ :=
    theorem_3_4_proof (GM10.deleteVertices_le B₀ W) h𝒯₁
  refine ⟨𝒯₀, h𝒯₀, ?_⟩
  intro A B hAB hord
  have hsep : G.IsSeparation A B := h𝒯.isSeparation hAB
  have hsep_B₀ : B₀.IsSeparation (A ∩ B₀) (B ∩ B₀) := by
    simpa [GM10.inter_comm B₀ A, GM10.inter_comm B₀ B] using hsep.inter_left hsep₀.right_le
  have hord_B₀ : separationOrder (A ∩ B₀) (B ∩ B₀) < θ - W.ncard :=
    separationOrder_inter_le.trans_lt hord
  refine ⟨hsep_B₀, hord_B₀, ?_⟩
  let A' := addVerticesSubhypergraph G A W hsep.left_le hW_sub
  let B' := addVerticesSubhypergraph G B W hsep.right_le hW_sub
  have hsep' : G.IsSeparation A' B' := addVerticesSubhypergraph_isSeparation hsep hW_sub
  have hord'_le : separationOrder A' B' ≤ separationOrder A B + W.ncard :=
    addVerticesSubhypergraph_separationOrder_le hsep hW_sub
  have hord' : separationOrder A' B' < θ := by
    rw [← hW_eq] at hord
    omega
  have hVB_sub : B.vertexSet ⊆ B'.vertexSet := Set.subset_union_left
  have hA'B'_mem : (A', B') ∈ 𝒯 :=
    GM10.theorem_2_9_proof h𝒯 hAB hsep' hord' (Or.inl hVB_sub)
  have hW_sub_A'B' : W ⊆ (A' ∩ B').vertexSet :=
    fun v hvW ↦ ⟨Or.inr hvW, Or.inr hvW⟩
  have hA'B'_W_sep : (G.deleteVertices W).IsSeparation
      (A'.deleteVertices W) (B'.deleteVertices W) :=
    isSeparation_deleteVertices_of_isSeparation hsep' W
  have hA'W_eq : A'.deleteVertices W = A.deleteVertices W :=
    deleteVertices_addVerticesSubhypergraph_eq hsep.left_le hW_sub
  have hB'W_eq : B'.deleteVertices W = B.deleteVertices W :=
    deleteVertices_addVerticesSubhypergraph_eq hsep.right_le hW_sub
  have hA'B'_W_ord : separationOrder (A'.deleteVertices W) (B'.deleteVertices W) < θ - W.ncard := by
    rw [hA'W_eq, hB'W_eq]
    have hsub : ((A.deleteVertices W) ∩ (B.deleteVertices W)).vertexSet ⊆ (A ∩ B).vertexSet :=
      fun v hv ↦ ⟨hv.1.1, hv.2.1⟩
    exact (Set.ncard_le_ncard hsub (A ∩ B).vertexSet_finite).trans_lt hord
  have hA'B'_W_mem : (A'.deleteVertices W, B'.deleteVertices W) ∈
      deleteVerticesTangle G W 𝒯 θ :=
    ⟨hA'B'_W_sep, hA'B'_W_ord, ⟨(A', B'), hA'B'_mem, hW_sub_A'B', rfl, rfl⟩⟩
  refine ⟨A'.deleteVertices W, B'.deleteVertices W, hA'B'_W_mem, ?_, ?_⟩
  · rw [hA'W_eq, ← deleteVertices_inter_deleteVertices_eq hsep.left_le hsep₀.right_le]
  · rw [hB'W_eq, ← deleteVertices_inter_deleteVertices_eq hsep.right_le hsep₀.right_le]

/-! ## (3.6): Splitting a vertex lowers tangle order by at most `1` -/

/-- If `G'` is obtained from `G` by splitting a vertex `v`, then `G \ {v}` is a subgraph of `G'`. -/
theorem deleteVertex_le_of_isVertexSplit {G G' : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hsplit : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) :
    G.deleteVertices {v} ≤ G' where
  vertexSet_subset := by
    rw [hsplit.vertexSet_eq]
    exact Set.subset_union_left
  edgeSet_subset := by
    rw [hsplit.edgeSet_eq]
    exact fun _ h ↦ h.1
  ends_eq e he := by
    rcases he with ⟨heG, hno_v⟩
    have heG' : e ∈ G'.edgeSet := hsplit.edgeSet_eq ▸ heG
    have he_not_inc : e ∉ incidentEdges G v := by
      rintro ⟨_, hinc_v⟩
      exact hno_v v (Set.mem_singleton v) hinc_v
    have he_not_δ₁ : e ∉ δ₁ := fun h ↦ he_not_inc (hsplit.δ_union ▸ Or.inl h)
    have he_not_δ₂ : e ∉ δ₂ := fun h ↦ he_not_inc (hsplit.δ_union ▸ Or.inr h)
    ext u
    change G'.Inc e u ↔ G.Inc e u ∧ ∀ w ∈ ({v} : Set α), ¬ G.Inc e w
    constructor
    · intro hincG'
      have huG' : u ∈ G'.vertexSet := G'.vertex_mem_of_inc hincG'
      rcases (hsplit.inc_iff e heG' u huG').1 hincG' with
        ⟨_, _, hincG⟩ | ⟨_, h₁⟩ | ⟨_, h₂⟩
      · exact ⟨hincG, hno_v⟩
      · exact (he_not_δ₁ h₁).elim
      · exact (he_not_δ₂ h₂).elim
    · rintro ⟨hincG, _⟩
      have huG : u ∈ G.vertexSet := G.vertex_mem_of_inc hincG
      have hu_ne_v : u ≠ v := fun h ↦ hno_v u (Set.mem_singleton_iff.2 h) hincG
      have huG' : u ∈ G'.vertexSet := by
        rw [hsplit.vertexSet_eq]
        exact Or.inl ⟨huG, Set.notMem_singleton_iff.2 hu_ne_v⟩
      have hu_ne_v₁ : u ≠ v₁ := fun h ↦ hsplit.v₁_not_mem (h ▸ huG)
      have hu_ne_v₂ : u ≠ v₂ := fun h ↦ hsplit.v₂_not_mem (h ▸ huG)
      exact (hsplit.inc_iff e heG' u huG').2 (Or.inl ⟨hu_ne_v₁, hu_ne_v₂, hincG⟩)

/-- **Graph Minors XXI, (3.6)** (Section 3, page 10 of the preprint):
"If $G'$ can be obtained from $G$ by splitting a vertex, and $\mathcal{T}$ is a tangle in $G$ of
order $\ge 2$, there is a tangle in $G'$ of order $ord(\mathcal{T}) - 1$." -/
theorem theorem_3_6_proof {G G' : Hypergraph α β} (hG : G.IsGraph)
    (hsplit : ObtainedBySplittingVertex G G') {θ : ℕ} (hθ : 2 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ 𝒯' : Set (Hypergraph α β × Hypergraph α β), IsTangle G' (θ - 1) 𝒯' := by
  rcases hsplit with ⟨v, v₁, v₂, δ₁, δ₂, hvsplit⟩
  have hv_sub : ({v} : Set α) ⊆ G.vertexSet := Set.singleton_subset_iff.2 hvsplit.v_mem
  have hv_card : ({v} : Set α).ncard < θ := by
    rw [Set.ncard_singleton]
    omega
  have h𝒯_del : IsTangle (G.deleteVertices {v}) (θ - 1)
      (deleteVerticesTangle G {v} 𝒯 θ) := by
    simpa [Set.ncard_singleton] using theorem_3_2_proof hG h𝒯 hv_sub hv_card
  have hle : G.deleteVertices {v} ≤ G' := deleteVertex_le_of_isVertexSplit hvsplit
  exact ⟨GM12.inducedBySubgraph G' (G.deleteVertices {v}) (θ - 1)
    (deleteVerticesTangle G {v} 𝒯 θ), theorem_3_4_proof hle h𝒯_del⟩

/-! ## (3.7): Truncation of a tangle -/

/-- **Graph Minors XXI, (3.7)** (Section 3, page 10 of the preprint):
"If $\mathcal{T}$ is a tangle in $G$, and $\theta$ is an integer with $1 \le \theta \le ord(\mathcal{T})$,
then the set of all members of $\mathcal{T}$ of order $< \theta$ is a tangle in $G$ of order $\theta$." -/
theorem theorem_3_7_proof {G : Hypergraph α β} {θ₀ θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ₀ 𝒯)
    (h1 : 1 ≤ θ) (hle : θ ≤ θ₀) :
    IsTangle G θ (truncation 𝒯 θ) := by
  have htrunc : IsTangle G θ (truncation 𝒯 θ) :=
    h𝒯.truncation h1 hle
  exact htrunc

end GM21
end GraphMinor
