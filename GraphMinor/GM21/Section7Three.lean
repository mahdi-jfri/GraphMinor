module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.Section7Jumps
import GraphMinor.GM04.Decomposition.Basic
import GraphMinor.Surface.Classification

/-!
# Graph Minors XXI, proof of (7.3): the presentation of `G'`

The proof of (7.3) (page 31 of the preprint) passes from a presentation
`Γ, F₁*, …, F_r*, H₁, …, H_r, μ` of `G` to a presentation `Γ', F₁*, …, F_r*, H₁, …, H_r, μ`
of `G' = Γ' ∪ H₁ ∪ … ∪ H_r`, where `Γ' ⊆ Γ` contains every vertex of `Γ` in `bd(Σ)`.

Every condition of a presentation sees `Γ` only through `V(Γ) ∩ bd(Σ)`, through `Γ` itself
(as a subgraph of `G`), and through `G`. This file checks this. The drawing of `Γ'` is
`restrictDrawing Γ ιV ιE K`: the subdrawing of `Γ` whose vertices and edges are those mapped by
`ιV`, `ιE` into the subgraph `K` of `Γ_sub`. The main result is `IsPresentation.restrict`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Hypergraph GraphMinor.GM10 GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
variable {Γ : Drawing S} {Γ_sub K : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}

/-! ## The drawing of a subgraph of `Γ` -/

section restrict

variable [T1Space S]

/-- The subdrawing of `Γ` formed by the vertices and edges that `ιV` and `ιE` map into `K`. -/
def restrictDrawing (Γ : Drawing S) (ιV : S → α) (ιE : Set S → β) (K : Hypergraph α β) :
    Drawing S :=
  Γ.span {x ∈ Γ.V | ιV x ∈ K.vertexSet} {e ∈ Γ.E | ιE e ∈ K.edgeSet}

theorem restrictDrawing_E : (restrictDrawing Γ ιV ιE K).E = {e ∈ Γ.E | ιE e ∈ K.edgeSet} := by
  rw [restrictDrawing, Drawing.span_E]
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

/-- The ends of an edge of `restrictDrawing Γ ιV ιE K` are vertices of it, since `K` is a
subgraph of `Γ_sub`. -/
theorem restrictDrawing_V (hiso : IsDrawingIso Γ Γ_sub ιV ιE) (hK : K ≤ Γ_sub) :
    (restrictDrawing Γ ιV ιE K).V = {x ∈ Γ.V | ιV x ∈ K.vertexSet} := by
  rw [restrictDrawing, Drawing.span_V, Drawing.spanV]
  ext x
  simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨h, _⟩ | ⟨e, ⟨⟨he, heK⟩, _⟩, hxe, hxV⟩)
    · exact h
    · refine ⟨hxV, ?_⟩
      have hinc : Γ_sub.Inc (ιE e) (ιV x) := (hiso.inc_iff e he x hxV).2 hxe
      exact K.vertex_mem_of_inc ((GM10.inc_iff_of_le hK heK).2 hinc)
  · exact fun h => Or.inl ⟨h, h.1⟩

theorem isDrawingIso_restrictDrawing (hiso : IsDrawingIso Γ Γ_sub ιV ιE) (hK : K ≤ Γ_sub) :
    IsDrawingIso (restrictDrawing Γ ιV ιE K) K ιV ιE where
  ιV_injOn := by
    rw [restrictDrawing_V hiso hK]
    exact hiso.ιV_injOn.mono fun x hx => hx.1
  ιV_image := by
    rw [restrictDrawing_V hiso hK]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      have hy' : y ∈ ιV '' Γ.V := by
        rw [hiso.ιV_image]
        exact hK.vertexSet_subset hy
      obtain ⟨x, hx, rfl⟩ := hy'
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  ιE_injOn := by
    rw [restrictDrawing_E]
    exact hiso.ιE_injOn.mono fun x hx => hx.1
  ιE_image := by
    rw [restrictDrawing_E]
    apply Subset.antisymm
    · rintro _ ⟨e, he, rfl⟩
      exact he.2
    · intro y hy
      have hy' : y ∈ ιE '' Γ.E := by
        rw [hiso.ιE_image]
        exact hK.edgeSet_subset hy
      obtain ⟨e, he, rfl⟩ := hy'
      exact ⟨e, ⟨he, hy⟩, rfl⟩
  inc_iff e he u hu := by
    rw [restrictDrawing_E] at he
    rw [restrictDrawing_V hiso hK] at hu
    rw [GM10.inc_iff_of_le hK he.2]
    exact hiso.inc_iff e he.1 u hu.1

/-- If `K` contains the image of every vertex of `Γ` in `bd(S)`, then `Γ` and
`restrictDrawing Γ ιV ιE K` have the same vertices in `bd(S)`. -/
theorem restrictDrawing_V_inter_bd (hiso : IsDrawingIso Γ Γ_sub ιV ιE) (hK : K ≤ Γ_sub)
    (hB : ιV '' (Γ.V ∩ bd S) ⊆ K.vertexSet) :
    (restrictDrawing Γ ιV ιE K).V ∩ bd S = Γ.V ∩ bd S := by
  rw [restrictDrawing_V hiso hK]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hB ⟨x, h, rfl⟩⟩, h.2⟩⟩

theorem restrictDrawing_isProper (hprop : Γ.IsProper) :
    (restrictDrawing Γ ιV ιE K).IsProper := by
  intro x ⟨hxbd, hxU⟩
  rw [restrictDrawing, Drawing.span_U, Drawing.spanU] at hxU
  rw [restrictDrawing, Drawing.span_V, Drawing.spanV]
  rcases hxU with hx | hx
  · exact hx
  · simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨e, he, hxe⟩ := hx
    have hxV : x ∈ Γ.V := hprop ⟨hxbd, Γ.closure_subset_U he.2 hxe⟩
    exact Or.inr (mem_biUnion he ⟨hxe, hxV⟩)

end restrict

/-! ## Conditions that see `Γ` only through `V(Γ) ∩ bd(S)` -/

section congr

variable {Γ' : Drawing S}

theorem drawingSpaces_congr (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) :
    drawingSpaces Γ' = drawingSpaces Γ := by
  have : bd S \ Γ'.V = bd S \ Γ.V := by
    ext x
    have := Set.ext_iff.1 h x
    simp only [mem_inter_iff] at this
    simp only [mem_sdiff]
    tauto
  rw [drawingSpaces, drawingSpaces, this]

theorem spaceHasEnds_congr (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) {s : Set S} {a b : S} :
    SpaceHasEnds Γ' s a b ↔ SpaceHasEnds Γ s a b := by
  simp only [SpaceHasEnds, drawingSpaces_congr h, h]

theorem supportHasEnds_congr (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) {F : Set S} {a b : S} :
    SupportHasEnds Γ' F a b ↔ SupportHasEnds Γ F a b := by
  simp only [SupportHasEnds, h]

theorem isSupportOfDrawing_congr (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) {F : Set S} :
    IsSupportOfDrawing Γ' F ↔ IsSupportOfDrawing Γ F := by
  simp only [IsSupportOfDrawing, supportHasEnds_congr h]

theorem subset_bd_of_supportHasEnds {F : Set S} {a b : S} (hF : SupportHasEnds Γ F a b) :
    F ⊆ bd S := by
  rcases hF with ⟨v, hv, rfl, -, -⟩ | ⟨hF, -⟩
  · exact singleton_subset_iff.2 hv.2
  · exact hF

theorem subset_bd_of_isSupportOfDrawing {F : Set S} (hF : IsSupportOfDrawing Γ F) :
    F ⊆ bd S := by
  obtain ⟨a, b, h⟩ := hF
  exact subset_bd_of_supportHasEnds h

theorem inter_eq_of_subset_bd (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) {F : Set S} (hF : F ⊆ bd S) :
    Γ'.V ∩ F = Γ.V ∩ F := by
  rw [← inter_eq_right.2 hF, ← Set.inter_assoc, ← Set.inter_assoc, h]

theorem liesBetweenInSupport_congr (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) {F s₁ s₂ : Set S} {u : S}
    (hF : F ⊆ bd S) :
    LiesBetweenInSupport Γ' F s₁ s₂ u ↔ LiesBetweenInSupport Γ F s₁ s₂ u := by
  have hFV : F ∩ Γ'.V = F ∩ Γ.V := by
    rw [Set.inter_comm, inter_eq_of_subset_bd h hF, Set.inter_comm]
  simp only [LiesBetweenInSupport, hFV, drawingSpaces_congr h, isSupportOfDrawing_congr h]

theorem supportGraph_congr (G : Hypergraph α β) (μ : BoundaryUnit S → Hypergraph α β)
    (h : Γ'.V ∩ bd S = Γ.V ∩ bd S) {F : Set S} (hF : F ⊆ bd S) :
    supportGraph G Γ' μ F = supportGraph G Γ μ F := by
  have hV := inter_eq_of_subset_bd h hF
  have hsp := drawingSpaces_congr h
  apply Hypergraph.ext
  · simp only [supportGraph, hV, hsp]
  · simp only [supportGraph, hV, hsp]
  · funext e x
    simp only [supportGraph, hV, hsp]

end congr

/-- If `G' ≤ G` contains `supportGraph G Γ μ F`, then `supportGraph G' Γ μ F` is the same
subgraph. -/
theorem supportGraph_eq_of_le {G G' : Hypergraph α β} (μ : BoundaryUnit S → Hypergraph α β)
    {F : Set S} (hG' : G' ≤ G) (hsub : supportGraph G Γ μ F ≤ G') :
    supportGraph G' Γ μ F = supportGraph G Γ μ F := by
  apply Hypergraph.ext
  · ext x
    simp only [supportGraph, mem_inter_iff]
    exact ⟨fun h => ⟨hG'.vertexSet_subset h.1, h.2⟩,
      fun h => ⟨hsub.vertexSet_subset h, h.2⟩⟩
  · ext e
    simp only [supportGraph, mem_inter_iff]
    exact ⟨fun h => ⟨hG'.edgeSet_subset h.1, h.2⟩,
      fun h => ⟨hsub.edgeSet_subset h, h.2⟩⟩
  · funext e x
    apply propext
    simp only [supportGraph]
    constructor
    · rintro ⟨hinc, hrest⟩
      exact ⟨GM10.inc_of_le hG' hinc, hrest⟩
    · rintro ⟨hinc, hrest⟩
      have hinc' : (supportGraph G Γ μ F).Inc e x := ⟨hinc, hrest⟩
      exact ⟨GM10.inc_of_le hsub hinc', hrest⟩

/-! ## The presentation of `G' = K ∪ H₁ ∪ … ∪ H_r` -/

section presentation

variable [T2Space S] {G : Hypergraph α β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

omit [T2Space S] in
theorem biUnion_H_le (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    Hypergraph.biUnion Finset.univ H ≤ G :=
  Hypergraph.biUnion_le fun j _ => hP.v1_sub j

/-- Let `K ≤ Γ_sub` contain `ιV(V(Γ) ∩ bd(S))`. Replacing `G` by `K ∪ H₁ ∪ … ∪ H_r`, `Γ_sub` by
`K` and `Γ` by `restrictDrawing Γ ιV ιE K` gives again a presentation, with the same supports,
the same `H_j`, the same `μ` and the same depths. This is the step "Then
$\Gamma', F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ is a presentation of
$G' = \Gamma' \cup H_1 \cup \dots \cup H_r$ in $\Sigma$, of depth $\le q$" of the proof of (7.3)
(page 31 of the preprint). -/
theorem IsPresentation.restrict (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hK : K ≤ Γ_sub) (hB : ιV '' (Γ.V ∩ bd S) ⊆ K.vertexSet) :
    IsPresentation (K ∪ Hypergraph.biUnion Finset.univ H) (restrictDrawing Γ ιV ιE K) K ιV ιE
      r F_star H μ q := by
  have hiso := hP.drawing_iso
  have hVbd := restrictDrawing_V_inter_bd hiso hK hB
  have hKG : K ≤ G := hK.trans hP.drawing_subgraph
  have hHG := biUnion_H_le hP
  have hG'G : K ∪ Hypergraph.biUnion Finset.univ H ≤ G := Hypergraph.union_le hKG hHG
  have hHG' : ∀ j, H j ≤ K ∪ Hypergraph.biUnion Finset.univ H := fun j =>
    (Hypergraph.le_biUnion (fun i _ => hP.v1_sub i) (Finset.mem_univ j)).trans
      (Hypergraph.le_union_right hKG hHG)
  have hFbd : ∀ j, F_star j ⊆ bd S := fun j =>
    subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j)
  have hFV : ∀ j, (restrictDrawing Γ ιV ιE K).V ∩ F_star j = Γ.V ∩ F_star j := fun j =>
    inter_eq_of_subset_bd hVbd (hFbd j)
  have hsp := drawingSpaces_congr hVbd
  -- The image of a boundary vertex lies in `K`.
  have hBK : ∀ u ∈ Γ.V ∩ bd S, ιV u ∈ K.vertexSet := fun u hu => hB ⟨u, hu, rfl⟩
  -- Intersections with `Γ_sub` that contain only images of boundary vertices are the same with `K`.
  have hcut : ∀ (A : Set α) (T : Set S), T ⊆ Γ.V ∩ bd S → A ∩ Γ_sub.vertexSet = ιV '' T →
      A ∩ K.vertexSet = ιV '' T := by
    intro A T hT hA
    apply Subset.antisymm
    · intro x hx
      rw [← hA]
      exact ⟨hx.1, hK.vertexSet_subset hx.2⟩
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : ιV u ∈ A ∩ Γ_sub.vertexSet := hA ▸ ⟨u, hu, rfl⟩
      exact ⟨hu'.1, hBK u (hT hu)⟩
  refine
    { is_surface := hP.is_surface
      is_connected_surface := hP.is_connected_surface
      is_proper_drawing := restrictDrawing_isProper hP.is_proper_drawing
      cuff_vertices_ge_two := fun C hC => ?_
      drawing_subgraph := Hypergraph.le_union_left hKG hHG
      drawing_iso := isDrawingIso_restrictDrawing hiso hK
      supports_isSupport := fun j => (isSupportOfDrawing_congr hVbd).2 (hP.supports_isSupport j)
      supports_disjoint := hP.supports_disjoint
      bd_vertices_covered := hVbd ▸ hP.bd_vertices_covered
      v1_sub := hHG'
      v1_union_V := ?_
      v1_union_E := ?_
      v1_disjoint := hP.v1_disjoint
      v1_inter_V := fun j => ?_
      v1_inter_E := fun j => disjoint_of_subset_right hK.edgeSet_subset (hP.v1_inter_E j)
      q_pos := hP.q_pos
      μ_vertex_sub := fun j u hu => ?_
      μ_space_sub := fun j s hs hsF => hP.μ_space_sub j s (hsp ▸ hs) hsF
      v2_eq := fun j => ?_
      v3_space := fun j s hs u₁ u₂ hsF hends => ?_
      v4_between := fun j s₁ s₂ u hbet => ?_ }
  · have hCbd : C ⊆ bd S := sUnion_cuffs (S := S) ▸ subset_sUnion_of_mem hC
    rw [inter_eq_of_subset_bd hVbd hCbd]
    exact hP.cuff_vertices_ge_two C hC
  · ext x
    simp only [Hypergraph.union_vertexSet, mem_union, Hypergraph.biUnion, Finset.mem_univ, iUnion_true,
      mem_iUnion]
    tauto
  · ext x
    simp only [Hypergraph.union_edgeSet, mem_union, Hypergraph.biUnion, Finset.mem_univ, iUnion_true,
      mem_iUnion]
    tauto
  · rw [hFV j]
    exact hcut _ _ (inter_subset_inter_right _ (hFbd j)) (hP.v1_inter_V j)
  · rw [hFV j] at hu
    obtain ⟨h1, h2, h3, h4⟩ := hP.μ_vertex_sub j u hu
    refine ⟨h1, h2, h3, ?_⟩
    have hu' : u ∈ Γ.V ∩ bd S := ⟨hu.1, hFbd j hu.2⟩
    have := hcut _ {u} (singleton_subset_iff.2 hu') (by rw [h4, image_singleton])
    rw [this, image_singleton]
  · rw [supportGraph_congr _ μ hVbd (hFbd j), supportGraph_eq_of_le μ hG'G, hP.v2_eq j]
    rw [← hP.v2_eq j]
    exact hHG' j
  · rw [hsp] at hs
    rw [spaceHasEnds_congr hVbd] at hends
    obtain ⟨h1, h2, h3, h4⟩ := hP.v3_space j s hs u₁ u₂ hsF hends
    refine ⟨?_, h2, h3, h4⟩
    have hT : ({u₁, u₂} : Set S) ⊆ Γ.V ∩ bd S := by
      rintro x (rfl | rfl)
      · exact hends.2.1
      · exact hends.2.2.1
    have := hcut _ {u₁, u₂} hT (by rw [h1, image_pair])
    rw [this, image_pair]
  · rw [liesBetweenInSupport_congr hVbd (hFbd j)] at hbet
    exact hP.v4_between j s₁ s₂ u hbet

theorem PresentationHasDepthLe.restrict {d : ℕ}
    (hP : PresentationHasDepthLe G Γ Γ_sub ιV ιE r F_star H μ d)
    (hK : K ≤ Γ_sub) (hB : ιV '' (Γ.V ∩ bd S) ⊆ K.vertexSet) :
    PresentationHasDepthLe (K ∪ Hypergraph.biUnion Finset.univ H) (restrictDrawing Γ ιV ιE K) K
      ιV ιE r F_star H μ d := by
  obtain ⟨q, hq, hqd, hr⟩ := hP
  exact ⟨q, hq.restrict hK hB, hqd, hr⟩

end presentation

end GM21
end GraphMinor
