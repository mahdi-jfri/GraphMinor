module

public import GraphMinor.GM21.Section6SplitGraph
public import GraphMinor.GM21.Section6Supports

/-!
# Graph Minors XXI, (6.3): the presentation of a split graph

Claim (2) of the proof of (6.3) (page 28 of the preprint) splits vertices and says: "we obtain
a graph $G'$ which has a presentation in $\Sigma'$ ... of depth $\le q$ and defect $\le r + 2$".
The correction to claim (4) (see the correction to the proof of (6.3) in `corrections/GM21.md`)
needs the same step. In both cases the data before the
split satisfy every condition of a presentation except one: two of the graphs `H_i` share some
vertices, so (V1) fails. Splitting each shared vertex, with the edges of one graph on one side and
the edges of the other graph on the other side, gives a true presentation.

This file states the conditions of a presentation without the disjointness of the graphs `H_i`
(`IsOverlappingPresentation`), and proves that splitting the shared vertices gives a presentation
(`isPresentation_splitAlong`). Each support `F_i*` gets a side `c i`. The graph `H_i`, and `μ(x)`
for every unit `x` in `F_i*`, are copied by `splitName X (c i)`: a vertex outside the set `X` of
split vertices keeps its name, and a vertex of `X` is sent to its copy on side `c i`. The conditions
needed are:
* an edge of `H_i` lies in the set `E₂` of edges that go to the second copies exactly when
  `c i = true`, and no edge of `Γ` is in `E₂`;
* `X` contains no vertex of `Γ`;
* two graphs `H_i, H_{i'}` share only vertices of `X`, and none if `c i = c i'`;
* each vertex of `X` lies in some `H_i` with `c i = false` and in some `H_i` with `c i = true`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Split

open Set Function Hypergraph GraphMinor.Surface

universe u v w

/-- The conditions of a presentation (Graph Minors XXI, Section 6, pages 21–22 of the preprint)
except that the graphs `H_1, …, H_r` are mutually vertex-disjoint. This is the situation before the
split of claim (2) of the proof of (6.3) (page 28 of the preprint), and on one side of the line in
claim (4) when one support holds both ends of the line. The fields are those of `IsPresentation`
without `v1_disjoint`. -/
structure IsOverlappingPresentation {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S) (H : Fin r → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (q : Fin r → ℕ) : Prop where
  is_surface : IsSurface S
  is_connected_surface : ConnectedSpace S
  is_proper_drawing : Γ.IsProper
  cuff_vertices_ge_two : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard
  drawing_subgraph : Γ_sub ≤ G
  drawing_iso : IsDrawingIso Γ Γ_sub ιV ιE
  supports_isSupport : ∀ j : Fin r, IsSupportOfDrawing Γ (F_star j)
  supports_disjoint : Pairwise (fun i j : Fin r => Disjoint (F_star i) (F_star j))
  bd_vertices_covered : Γ.V ∩ bd S ⊆ ⋃ j : Fin r, F_star j
  v1_sub : ∀ j : Fin r, H j ≤ G
  v1_union_V : G.vertexSet = (⋃ j : Fin r, (H j).vertexSet) ∪ Γ_sub.vertexSet
  v1_union_E : G.edgeSet = (⋃ j : Fin r, (H j).edgeSet) ∪ Γ_sub.edgeSet
  v1_inter_V : ∀ j : Fin r, (H j).vertexSet ∩ Γ_sub.vertexSet = ιV '' (Γ.V ∩ F_star j)
  v1_inter_E : ∀ j : Fin r, Disjoint (H j).edgeSet Γ_sub.edgeSet
  q_pos : ∀ j : Fin r, 1 ≤ q j
  μ_vertex_sub : ∀ j : Fin r, ∀ u ∈ Γ.V ∩ F_star j,
    μ (.vertex u) ≤ H j ∧
    (μ (.vertex u)).edgeSet = ∅ ∧
    (μ (.vertex u)).vertexSet.ncard = q j ∧
    (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet = {ιV u}
  μ_space_sub : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → μ (.space s) ≤ H j
  v2_eq : ∀ j : Fin r, H j = supportGraph G Γ μ (F_star j)
  v3_space : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, ∀ u₁ u₂ : S,
    s ⊆ F_star j → SpaceHasEnds Γ s u₁ u₂ →
    (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet = {ιV u₁, ιV u₂} ∧
    μ (.vertex u₁) ≤ μ (.space s) ∧
    μ (.vertex u₂) ≤ μ (.space s) ∧
    HasDisjointPaths (μ (.space s)).skeleton (μ (.vertex u₁)).vertexSet
      (μ (.vertex u₂)).vertexSet (q j)
  v4_between : ∀ j : Fin r, ∀ s₁ s₂ : Set S, ∀ u : S,
    LiesBetweenInSupport Γ (F_star j) s₁ s₂ u →
    μ (.space s₁) ∩ μ (.space s₂) ≤ μ (.vertex u)

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-! ## Copies of hypergraphs by an injective map -/

section isoImage

variable {γ δ : Type*}

/-- `(f ∘ ιV, ιE)` maps a drawing onto the copy by an injective map `f` of its subgraph. -/
theorem isDrawingIso_isoImage {Γ : Drawing S} {A : Hypergraph γ β} {ιV : S → γ}
    {ιE : Set S → β} (h : IsDrawingIso Γ A ιV ιE) {f : γ → δ} (hf : Injective f) :
    IsDrawingIso Γ (isoImage f id A) (f ∘ ιV) ιE where
  ιV_injOn := hf.comp_injOn h.ιV_injOn
  ιV_image := by rw [image_comp, h.ιV_image]; rfl
  ιE_injOn := h.ιE_injOn
  ιE_image := by rw [h.ιE_image]; exact (image_id _).symm
  inc_iff := by
    intro e he u hu
    rw [← h.inc_iff e he u hu]
    constructor
    · rintro ⟨e₀, v₀, hinc, rfl, hv⟩
      rwa [← hf hv]
    · intro hinc
      exact ⟨_, _, hinc, rfl, rfl⟩

/-- The copy of an intersection by an injective map is the intersection of the copies. -/
theorem isoImage_inter {A B : Hypergraph γ β} {f : γ → δ} (hf : Injective f) :
    isoImage f id (A ∩ B) = isoImage f id A ∩ isoImage f id B := by
  refine Hypergraph.ext ?_ ?_ ?_
  · exact image_inter hf
  · show id '' (A.edgeSet ∩ B.edgeSet) = id '' A.edgeSet ∩ id '' B.edgeSet
    simp only [image_id]
  · funext e x
    apply propext
    show (∃ e₀ v₀, (A.Inc e₀ v₀ ∧ B.Inc e₀ v₀) ∧ id e₀ = e ∧ f v₀ = x) ↔
      (∃ e₀ v₀, A.Inc e₀ v₀ ∧ id e₀ = e ∧ f v₀ = x) ∧ (∃ e₀ v₀, B.Inc e₀ v₀ ∧ id e₀ = e ∧ f v₀ = x)
    constructor
    · rintro ⟨e₀, v₀, ⟨hA, hB⟩, rfl, rfl⟩
      exact ⟨⟨e₀, v₀, hA, rfl, rfl⟩, ⟨e₀, v₀, hB, rfl, rfl⟩⟩
    · rintro ⟨⟨e₀, v₀, hA, rfl, rfl⟩, ⟨e₁, v₁, hB, he, hv⟩⟩
      rw [hf hv, show e₁ = e₀ from he] at hB
      exact ⟨e₀, v₀, ⟨hA, hB⟩, rfl, rfl⟩

end isoImage

/-! ## Copies on one side -/

section sides

variable {X : Set α}

/-- `splitName X c v` is `inr (inl w)` exactly for `v = w ∈ X` and `c = false`. -/
theorem splitName_eq_inr_inl_iff {c : Bool} {v w : α} :
    splitName X c v = .inr (.inl w) ↔ v = w ∧ w ∈ X ∧ c = false := by
  unfold splitName
  constructor
  · intro h
    split_ifs at h with hv hc <;> simp_all
  · rintro ⟨rfl, hv, rfl⟩
    simp [hv]

/-- `splitName X c v` is `inr (inr w)` exactly for `v = w ∈ X` and `c = true`. -/
theorem splitName_eq_inr_inr_iff {c : Bool} {v w : α} :
    splitName X c v = .inr (.inr w) ↔ v = w ∧ w ∈ X ∧ c = true := by
  unfold splitName
  constructor
  · intro h
    split_ifs at h with hv hc <;> simp_all
  · rintro ⟨rfl, hv, rfl⟩
    simp [hv]

/-- `splitName X c v` is `inl w` exactly for `v = w ∉ X`. -/
theorem splitName_eq_inl_iff {c : Bool} {v w : α} :
    splitName X c v = .inl w ↔ v = w ∧ w ∉ X := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨rfl, hv⟩ := splitName_eq_inl h
    exact ⟨rfl, hv⟩
  · rintro ⟨rfl, hv⟩
    exact splitName_of_notMem hv

/-- A copy on side `c` of a vertex of `A` that is also a copy on side `false` of a vertex of a set
`B` outside `X` is the copy of a vertex of `A ∩ B`. -/
theorem image_splitName_inter {c : Bool} {A B : Set α} (hB : Disjoint B X) :
    splitName X c '' A ∩ splitName X false '' B = splitName X false '' (A ∩ B) := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have hba := eq_of_splitName_eq hab
    subst hba
    have hbX : b ∉ X := disjoint_left.mp hB hb
    exact ⟨b, ⟨ha, hb⟩, by rw [splitName_of_notMem hbX, splitName_of_notMem hbX]⟩
  · rintro ⟨b, ⟨ha, hb⟩, rfl⟩
    have hbX : b ∉ X := disjoint_left.mp hB hb
    exact ⟨⟨b, ha, by rw [splitName_of_notMem hbX, splitName_of_notMem hbX]⟩, ⟨b, hb, rfl⟩⟩

end sides

/-! ## The graph `μ(F)` of the split graph -/

/-- **`μ'(F)` is the copy of `μ(F)`.** Let every unit `x` in `F` have side `cu x = c`, let
`μ(x) ≤ G`, and let each edge of `μ(x)` be in `E₂` exactly when `c = true`. Then `μ'(F)`, computed
in the split graph with `μ'(x)` the copy of `μ(x)` on side `cu x`, is the copy of `μ(F)` on side
`c`. -/
theorem supportGraph_splitAlong {G : Hypergraph α β} {Γ : Drawing S} {μ : BoundaryUnit S → Hypergraph α β}
    {X : Set α} {E₂ : Set β} {cu : BoundaryUnit S → Bool} {c : Bool} {F : Set S}
    (hcu : ∀ x : BoundaryUnit S, ((∃ u ∈ Γ.V ∩ F, x = .vertex u) ∨
      (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x = .space s)) →
      cu x = c ∧ μ x ≤ G ∧ ∀ e ∈ (μ x).edgeSet, (e ∈ E₂ ↔ c = true)) :
    supportGraph (splitAlong G X E₂) Γ (fun x => isoImage (splitName X (cu x)) id (μ x)) F =
      isoImage (splitName X c) id (supportGraph G Γ μ F) := by
  have hv : ∀ u ∈ Γ.V ∩ F, cu (.vertex u) = c ∧ μ (.vertex u) ≤ G ∧
      ∀ e ∈ (μ (.vertex u)).edgeSet, (e ∈ E₂ ↔ c = true) :=
    fun u hu => hcu _ (Or.inl ⟨u, hu, rfl⟩)
  have hs : ∀ s ∈ drawingSpaces Γ, s ⊆ F → cu (.space s) = c ∧ μ (.space s) ≤ G ∧
      ∀ e ∈ (μ (.space s)).edgeSet, (e ∈ E₂ ↔ c = true) :=
    fun s hs hsF => hcu _ (Or.inr ⟨s, hs, hsF, rfl⟩)
  refine Hypergraph.ext ?_ ?_ ?_
  · ext x
    simp only [supportGraph, isoImage, mem_inter_iff, mem_union, mem_iUnion, mem_image,
      exists_prop, mem_ofPred_eq]
    constructor
    · rintro ⟨-, ⟨s, ⟨hsS, hsF⟩, v, hv', rfl⟩ | ⟨u, hu, v, hv', rfl⟩⟩
      · rw [(hs s hsS hsF).1]
        exact ⟨v, ⟨(hs s hsS hsF).2.1.vertexSet_subset hv', Or.inl ⟨s, ⟨hsS, hsF⟩, hv'⟩⟩, rfl⟩
      · rw [(hv u hu).1]
        exact ⟨v, ⟨(hv u hu).2.1.vertexSet_subset hv', Or.inr ⟨u, hu, hv'⟩⟩, rfl⟩
    · rintro ⟨v, ⟨hvG, ⟨s, ⟨hsS, hsF⟩, hvs⟩ | ⟨u, hu, hvu⟩⟩, rfl⟩
      · refine ⟨splitName_mem c hvG, Or.inl ⟨s, ⟨hsS, hsF⟩, v, hvs, ?_⟩⟩
        rw [(hs s hsS hsF).1]
      · refine ⟨splitName_mem c hvG, Or.inr ⟨u, hu, v, hvu, ?_⟩⟩
        rw [(hv u hu).1]
  · ext e
    simp only [supportGraph, isoImage, splitAlong_edgeSet, image_id, mem_inter_iff]
  · funext e x
    apply propext
    simp only [supportGraph, isoImage, id_eq]
    constructor
    · rintro ⟨hG, ⟨s, hsS, hsF, e₀, v, hinc, rfl, rfl⟩ | ⟨u, hu, e₀, v, hinc, rfl, rfl⟩⟩
      · rw [(hs s hsS hsF).1] at hG ⊢
        exact ⟨e₀, v, ⟨GM10.inc_of_le (hs s hsS hsF).2.1 hinc, Or.inl ⟨s, hsS, hsF, hinc⟩⟩,
          rfl, rfl⟩
      · rw [(hv u hu).1] at hG ⊢
        exact ⟨e₀, v, ⟨GM10.inc_of_le (hv u hu).2.1 hinc, Or.inr ⟨u, hu, hinc⟩⟩, rfl, rfl⟩
    · rintro ⟨e₀, v, ⟨hG, ⟨s, hsS, hsF, hinc⟩ | ⟨u, hu, hinc⟩⟩, rfl, rfl⟩
      · have hcol := (hs s hsS hsF).2.2 e₀ ((μ _).edge_mem_of_inc hinc)
        refine ⟨(splitAlong_inc_splitName_iff hcol).mpr hG, Or.inl ⟨s, hsS, hsF, e₀, v, hinc,
          rfl, ?_⟩⟩
        rw [(hs s hsS hsF).1]
      · have hcol := (hv u hu).2.2 e₀ ((μ _).edge_mem_of_inc hinc)
        refine ⟨(splitAlong_inc_splitName_iff hcol).mpr hG, Or.inr ⟨u, hu, e₀, v, hinc,
          rfl, ?_⟩⟩
        rw [(hv u hu).1]

/-! ## The presentation of the split graph -/

section presentation

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- **The presentation of the split graph** (Graph Minors XXI, proof of (6.3), claim (2),
page 28 of the preprint: "we obtain a graph $G'$ which has a presentation in $\Sigma'$ ...", and the
correction to claim (4)). Let the data satisfy all conditions of a presentation except the
disjointness of the graphs `H_i`, and let every shared vertex be in `X`. Give each support `F_i*` a
side `c i`, and each unit of `F_i*` the side `c i`. Then the copies `H_i'` of `H_i` and `μ'(x)` of
`μ(x)` on these sides form a presentation of `splitAlong G X E₂`, with the same drawing `Γ` and the
same numbers `q_i`. -/
theorem isPresentation_splitAlong (hP : IsOverlappingPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    {X : Set α} (hXG : X ⊆ G.vertexSet) {E₂ : Set β} (c : Fin r → Bool)
    (cu : BoundaryUnit S → Bool)
    (hcolor : ∀ i, ∀ e ∈ (H i).edgeSet, (e ∈ E₂ ↔ c i = true))
    (hΓE : Disjoint Γ_sub.edgeSet E₂) (hΓX : Disjoint Γ_sub.vertexSet X)
    (hcu_vertex : ∀ i, ∀ u ∈ Γ.V ∩ F_star i, cu (.vertex u) = c i)
    (hcu_space : ∀ i, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star i → cu (.space s) = c i)
    (hover : ∀ i i', i ≠ i' → (H i).vertexSet ∩ (H i').vertexSet ⊆ X ∧
      (c i = c i' → Disjoint (H i).vertexSet (H i').vertexSet))
    (hX₁ : ∀ v ∈ X, ∃ i, c i = false ∧ v ∈ (H i).vertexSet)
    (hX₂ : ∀ v ∈ X, ∃ i, c i = true ∧ v ∈ (H i).vertexSet) :
    IsPresentation (splitAlong G X E₂) Γ (isoImage (splitName X false) id Γ_sub)
      (splitName X false ∘ ιV) ιE r F_star (fun i => isoImage (splitName X (c i)) id (H i))
      (fun x => isoImage (splitName X (cu x)) id (μ x)) q := by
  have hS := hP.is_surface
  have hΓle : isoImage (splitName X false) id Γ_sub ≤ splitAlong G X E₂ :=
    isoImage_splitName_le hP.drawing_subgraph fun e he =>
      ⟨fun h => absurd h (disjoint_left.mp hΓE he), fun h => absurd h (by simp)⟩
  have hFcl : ∀ i, IsClosed (F_star i) := fun i =>
    Supports.isClosed_of_isSupportOfDrawing hS (hP.supports_isSupport i)
  -- The units of `F_i*`.
  have hunit : ∀ i, ∀ x : BoundaryUnit S, ((∃ u ∈ Γ.V ∩ F_star i, x = .vertex u) ∨
      (∃ s ∈ drawingSpaces Γ, s ⊆ F_star i ∧ x = .space s)) →
      cu x = c i ∧ μ x ≤ G ∧ ∀ e ∈ (μ x).edgeSet, (e ∈ E₂ ↔ c i = true) := by
    rintro i x (⟨u, hu, rfl⟩ | ⟨s, hs, hsF, rfl⟩)
    · have hle := (hP.μ_vertex_sub i u hu).1
      exact ⟨hcu_vertex i u hu, hle.trans (hP.v1_sub i),
        fun e he => hcolor i e (hle.edgeSet_subset he)⟩
    · have hle := hP.μ_space_sub i s hs hsF
      exact ⟨hcu_space i s hs hsF, hle.trans (hP.v1_sub i),
        fun e he => hcolor i e (hle.edgeSet_subset he)⟩
  have hΓV : Disjoint Γ_sub.vertexSet X := hΓX
  exact {
    is_surface := hS
    is_connected_surface := hP.is_connected_surface
    is_proper_drawing := hP.is_proper_drawing
    cuff_vertices_ge_two := hP.cuff_vertices_ge_two
    drawing_subgraph := hΓle
    drawing_iso := isDrawingIso_isoImage hP.drawing_iso (splitName_injective false)
    supports_isSupport := hP.supports_isSupport
    supports_disjoint := hP.supports_disjoint
    bd_vertices_covered := hP.bd_vertices_covered
    v1_sub := fun i => isoImage_splitName_le (hP.v1_sub i) (hcolor i)
    v1_union_V := by
      ext x
      simp only [isoImage, mem_union, mem_iUnion, mem_image]
      rcases x with w | w | w
      · simp only [splitName_eq_inl_iff, mem_splitAlong_inl, hP.v1_union_V, mem_union,
          mem_iUnion]
        constructor
        · rintro ⟨⟨i, hw⟩ | hw, hwX⟩
          · exact Or.inl ⟨i, w, hw, rfl, hwX⟩
          · exact Or.inr ⟨w, hw, rfl, hwX⟩
        · rintro (⟨i, v, hv, rfl, hvX⟩ | ⟨v, hv, rfl, hvX⟩)
          · exact ⟨Or.inl ⟨i, hv⟩, hvX⟩
          · exact ⟨Or.inr hv, hvX⟩
      · simp only [splitName_eq_inr_inl_iff, mem_splitAlong_inr_inl]
        constructor
        · rintro ⟨-, hwX⟩
          obtain ⟨i, hci, hw⟩ := hX₁ w hwX
          exact Or.inl ⟨i, w, hw, rfl, hwX, hci⟩
        · rintro (⟨i, v, -, rfl, hvX, -⟩ | ⟨v, -, rfl, hvX, -⟩)
          · exact ⟨hXG hvX, hvX⟩
          · exact ⟨hXG hvX, hvX⟩
      · simp only [splitName_eq_inr_inr_iff, mem_splitAlong_inr_inr]
        constructor
        · rintro ⟨-, hwX⟩
          obtain ⟨i, hci, hw⟩ := hX₂ w hwX
          exact Or.inl ⟨i, w, hw, rfl, hwX, hci⟩
        · rintro (⟨i, v, -, rfl, hvX, -⟩ | ⟨v, -, rfl, hvX, hc⟩)
          · exact ⟨hXG hvX, hvX⟩
          · exact absurd hc (by simp)
    v1_union_E := by
      simp only [isoImage, splitAlong_edgeSet, image_id]
      exact hP.v1_union_E
    v1_disjoint := by
      intro i i' hii'
      rw [Set.disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
      have hwv := eq_of_splitName_eq hvw
      subst hwv
      have hX := (hover i i' hii').1 ⟨hv, hw⟩
      by_cases hc : c i = c i'
      · exact disjoint_left.mp ((hover i i' hii').2 hc) hv hw
      · exact notMem_of_splitName_eq (Ne.symm hc) hvw hX
    v1_inter_V := by
      intro i
      show splitName X (c i) '' (H i).vertexSet ∩ splitName X false '' Γ_sub.vertexSet = _
      rw [image_splitName_inter hΓV, hP.v1_inter_V i, image_comp]
    v1_inter_E := fun i => by
      simp only [isoImage, image_id]
      exact hP.v1_inter_E i
    q_pos := hP.q_pos
    μ_vertex_sub := by
      intro i u hu
      obtain ⟨hle, he, hcard, hint⟩ := hP.μ_vertex_sub i u hu
      rw [hcu_vertex i u hu]
      refine ⟨isoImage_le hle le_rfl (injOn_id _) hle, ?_, ?_, ?_⟩
      · show id '' _ = ∅
        rw [he, image_empty]
      · show (splitName X (c i) '' _).ncard = q i
        rw [(splitName_injective (c i)).injOn.ncard_image, hcard]
      · show splitName X (c i) '' _ ∩ splitName X false '' Γ_sub.vertexSet = _
        rw [image_splitName_inter hΓV, hint, image_singleton]
        rfl
    μ_space_sub := by
      intro i s hs hsF
      rw [hcu_space i s hs hsF]
      exact isoImage_le (hP.μ_space_sub i s hs hsF) le_rfl (injOn_id _)
        (hP.μ_space_sub i s hs hsF)
    v2_eq := by
      intro i
      rw [supportGraph_splitAlong (c := c i) (hunit i), hP.v2_eq i]
    v3_space := by
      intro i s hs u₁ u₂ hsF hends
      obtain ⟨hint, h₁, h₂, hpaths⟩ := hP.v3_space i s hs u₁ u₂ hsF hends
      have hcl : closure s ⊆ F_star i := closure_minimal hsF (hFcl i)
      rw [hends.2.2.2.2.2] at hcl
      have hu₁ : u₁ ∈ Γ.V ∩ F_star i := ⟨hends.2.1.1, hcl (Or.inr (Or.inl rfl))⟩
      have hu₂ : u₂ ∈ Γ.V ∩ F_star i := ⟨hends.2.2.1.1, hcl (Or.inr (Or.inr rfl))⟩
      rw [hcu_space i s hs hsF, hcu_vertex i u₁ hu₁, hcu_vertex i u₂ hu₂]
      refine ⟨?_, isoImage_le h₁ le_rfl (injOn_id _) h₁, isoImage_le h₂ le_rfl (injOn_id _) h₂,
        ?_⟩
      · show splitName X (c i) '' _ ∩ splitName X false '' Γ_sub.vertexSet = _
        rw [image_splitName_inter hΓV, hint, image_pair]
        rfl
      · exact HasDisjointPaths.image_of_injective (splitName_injective (c i))
          (skeleton_adj_isoImage_of_injective (splitName_injective (c i))) hpaths
    v4_between := by
      intro i s₁ s₂ u hbtw
      have hle := hP.v4_between i s₁ s₂ u hbtw
      obtain ⟨⟨huF, huV⟩, hs₁, hs₂, hs₁F, hs₂F, -⟩ := hbtw
      rw [hcu_space i s₁ hs₁ hs₁F, hcu_space i s₂ hs₂ hs₂F, hcu_vertex i u ⟨huV, huF⟩,
        ← isoImage_inter (splitName_injective (c i))]
      exact isoImage_le hle le_rfl (injOn_id _) hle }

end presentation


/-! ## The split graph is a graph, and its jumps -/

open Classical in
/-- Each edge of the split graph has, as ends, the copies on its side of its ends in `G`. -/
theorem ends_splitAlong {G : Hypergraph α β} {X : Set α} {E₂ : Set β} (e : β) :
    (splitAlong G X E₂).ends e = splitName X (decide (e ∈ E₂)) '' G.ends e := by
  have hc : e ∈ E₂ ↔ decide (e ∈ E₂) = true := decide_eq_true_iff.symm
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := eq_splitName_of_splitAlong_inc hc hx
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact (splitAlong_inc_splitName_iff hc).mpr hv

/-- Splitting vertices of a graph gives a graph. -/
theorem isGraph_splitAlong {G : Hypergraph α β} (hG : G.IsGraph) (X : Set α) (E₂ : Set β) :
    (splitAlong G X E₂).IsGraph := by
  classical
  intro e he
  rw [ends_splitAlong, (splitName_injective _).injOn.ncard_image]
  exact ⟨(hG e he).1.image _, (hG e he).2⟩

/-- A `Σ`-jump of `Γ`, drawn as a subgraph of `A`, is copied to a `Σ`-jump of `Γ` drawn as the copy
of `A` by an injective map. So the copy has at least as many jumps. -/
theorem encard_sigmaJumps_le_isoImage {γ δ : Type*} {Γ : Drawing S} {A : Hypergraph γ β}
    {ιV : S → γ} {f : γ → δ} (hf : Injective f) :
    (sigmaJumps Γ A ιV).encard ≤ (sigmaJumps Γ (isoImage f id A) (f ∘ ιV)).encard := by
  refine encard_le_encard_of_injOn (f := fun J => isoImage f id J) ?_ ?_
  · rintro J ⟨hJA, hpath, u, hu, w, hw, huw, hterm, hint⟩
    refine ⟨isoImage_le hJA le_rfl (injOn_id _) hJA, (isPathGraph_isoImage hJA
      hf.injOn (injOn_id _)).mpr hpath, u, hu, w, hw, huw, ?_, ?_⟩
    · rw [terminals_isoImage hJA hf.injOn (injOn_id _), hterm, image_pair]
      rfl
    · rintro x hx ⟨y, hy, hxy⟩
      exact hint x hx (hf hxy ▸ hy)
  · intro J hJ J' hJ' hJJ'
    have h₁ := isoPreimage_isoImage hJ.1 hf.injOn (injOn_id _)
    have h₂ := isoPreimage_isoImage hJ'.1 hf.injOn (injOn_id _)
    simp only at hJJ'
    rw [← h₁, ← h₂, hJJ']

end Split
end GM21
end GraphMinor
