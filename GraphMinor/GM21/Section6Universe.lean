module

public import GraphMinor.GM21.Parallel
import GraphMinor.GM21.Section6Three
import GraphMinor.Surface.AddCrosscap
import GraphMinor.Surface.Classification
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.Surface.PlaneDisc

/-!
# Graph Minors XXI, (6.3), for surfaces in any universe

The proof of (6.3) in `Section6Three.lean` (`theorem_6_3_parallel_proof`) works with surfaces in
`Type`, since its induction on the type of the surface builds new surfaces in `Type`. Here we lift
it to a surface `S` in any universe.

By the classification of surfaces, `S` is homeomorphic to a model surface `Σ(a, b, c)`, which lies
in `Type`. A homeomorphism `ψ : S ≃ₜ S'` carries a presentation in `S` to a presentation in `S'`:
we move the drawing, the supports and the map `μ` along `ψ`, and keep the graph, the subgraphs
`H_j` and the linkage. Every `Σ`-jump of the old presentation is a `Σ'`-jump of the new one, so the
bound for the model bounds the jumps in `S` (`theorem_6_3_proof`).
-/

public section

universe u v w w'

namespace GraphMinor
namespace GM21
namespace Homeo

open Set Topology Hypergraph GraphMinor.Surface

section Transport

variable {S : Type w} {S' : Type w'} [TopologicalSpace S] [TopologicalSpace S'] (ψ : S ≃ₜ S')

theorem symm_image_image' (X : Set S) : ψ.symm '' (ψ '' X) = X := by
  rw [← image_comp]
  simp

/-- The image of a drawing under a homeomorphism (Graph Minors VII, Section 3, page 220). -/
noncomputable abbrev mapDrawing (Γ : Drawing S) : Drawing S' := GM07.mapDrawingHomeo ψ Γ

theorem mapDrawing_V (Γ : Drawing S) : (mapDrawing ψ Γ).V = ψ '' Γ.V := rfl

theorem mapDrawing_E (Γ : Drawing S) : (mapDrawing ψ Γ).E = image ψ '' Γ.E := by
  change arcComponentsIn (ψ '' Γ.U \ ψ '' Γ.V) = _
  rw [← image_sdiff ψ.injective]
  exact GM07.arcComponentsIn_image_homeo ψ _

/-- Moving a drawing there and back gives the same drawing. -/
theorem mapDrawing_symm_mapDrawing (Γ : Drawing S) : mapDrawing ψ.symm (mapDrawing ψ Γ) = Γ := by
  cases Γ
  simp only [mapDrawing, GM07.mapDrawingHomeo, symm_image_image' ψ]

theorem image_bd : ψ '' bd S = bd S' := image_bd_homeomorph ψ

theorem drawingSpaces_mapDrawing (Γ : Drawing S) :
    drawingSpaces (mapDrawing ψ Γ) = image ψ '' drawingSpaces Γ := by
  unfold drawingSpaces
  rw [mapDrawing_V, ← image_bd ψ, ← image_sdiff ψ.injective]
  exact componentsIn_image (f' := ψ.symm) ψ.continuous.continuousOn
    ψ.symm.continuous.continuousOn (fun x _ => by simp)

theorem cuffs_eq : cuffs S' = image ψ '' cuffs S := by
  unfold cuffs
  rw [← image_bd ψ]
  exact componentsIn_image (f' := ψ.symm) ψ.continuous.continuousOn
    ψ.symm.continuous.continuousOn (fun x _ => by simp)

theorem isLineWithEnds_image {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    IsLineWithEnds (ψ '' L) (ψ a) (ψ b) := by
  obtain ⟨f, h₀, h₁⟩ := h
  exact ⟨f.trans (ψ.image L), by rw [← h₀]; rfl, by rw [← h₁]; rfl⟩

theorem mem_image_iff {X : Set S} {x : S} : ψ x ∈ ψ '' X ↔ x ∈ X :=
  ψ.injective.mem_set_image

theorem image_inter' (X Y : Set S) : ψ '' (X ∩ Y) = ψ '' X ∩ ψ '' Y :=
  image_inter ψ.injective

theorem spaceHasEnds_image {Γ : Drawing S} {s : Set S} {a b : S} (h : SpaceHasEnds Γ s a b) :
    SpaceHasEnds (mapDrawing ψ Γ) (ψ '' s) (ψ a) (ψ b) := by
  obtain ⟨hs, ha, hb, hab, hL, hcl⟩ := h
  refine ⟨?_, ?_, ?_, fun h => hab (ψ.injective h), ?_, ?_⟩
  · rw [drawingSpaces_mapDrawing]; exact mem_image_of_mem _ hs
  · rw [mapDrawing_V, ← image_bd ψ, ← image_inter' ψ]; exact mem_image_of_mem _ ha
  · rw [mapDrawing_V, ← image_bd ψ, ← image_inter' ψ]; exact mem_image_of_mem _ hb
  · have := isLineWithEnds_image ψ hL
    rwa [image_union, image_pair] at this
  · rw [← ψ.image_closure, hcl, image_union, image_pair]

theorem supportHasEnds_image {Γ : Drawing S} {F : Set S} {a b : S} (h : SupportHasEnds Γ F a b) :
    SupportHasEnds (mapDrawing ψ Γ) (ψ '' F) (ψ a) (ψ b) := by
  have hV : (mapDrawing ψ Γ).V ∩ bd S' = ψ '' (Γ.V ∩ bd S) := by
    rw [mapDrawing_V, ← image_bd ψ, image_inter' ψ]
  rcases h with ⟨x, hx, hFx, hax, hbx⟩ | ⟨hF, hab, ha, hb, hL⟩
  · exact Or.inl ⟨ψ x, hV ▸ mem_image_of_mem _ hx, by rw [hFx, image_singleton], by rw [hax],
      by rw [hbx]⟩
  · refine Or.inr ⟨?_, fun h => hab (ψ.injective h), hV ▸ mem_image_of_mem _ ha,
      hV ▸ mem_image_of_mem _ hb, isLineWithEnds_image ψ hL⟩
    rw [← image_bd ψ]; exact image_mono hF

theorem isSupportOfDrawing_image {Γ : Drawing S} {F : Set S} (h : IsSupportOfDrawing Γ F) :
    IsSupportOfDrawing (mapDrawing ψ Γ) (ψ '' F) := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨ψ a, ψ b, supportHasEnds_image ψ h⟩

theorem liesBetweenInSupport_image {Γ : Drawing S} {F s₁ s₂ : Set S} {x : S}
    (h : LiesBetweenInSupport Γ F s₁ s₂ x) :
    LiesBetweenInSupport (mapDrawing ψ Γ) (ψ '' F) (ψ '' s₁) (ψ '' s₂) (ψ x) := by
  obtain ⟨hx, hs₁, hs₂, h₁F, h₂F, I₁, I₂, hI₁, hI₂, hun, hint, h₁, h₂⟩ := h
  refine ⟨?_, ?_, ?_, image_mono h₁F, image_mono h₂F, ψ '' I₁, ψ '' I₂,
    isSupportOfDrawing_image ψ hI₁, isSupportOfDrawing_image ψ hI₂, ?_, ?_, image_mono h₁,
    image_mono h₂⟩
  · rw [mapDrawing_V, ← image_inter' ψ]; exact mem_image_of_mem _ hx
  · rw [drawingSpaces_mapDrawing]; exact mem_image_of_mem _ hs₁
  · rw [drawingSpaces_mapDrawing]; exact mem_image_of_mem _ hs₂
  · rw [← image_union, hun]
  · rw [← image_inter' ψ, hint, image_singleton]

/-- The map `μ` of a presentation, moved along `ψ`. -/
def mapUnit {α : Type u} {β : Type v} (μ : BoundaryUnit S → Hypergraph α β) :
    BoundaryUnit S' → Hypergraph α β
  | .vertex x => μ (.vertex (ψ.symm x))
  | .space s => μ (.space (ψ.symm '' s))

theorem mapUnit_vertex {α : Type u} {β : Type v} (μ : BoundaryUnit S → Hypergraph α β) (x : S) :
    mapUnit ψ μ (.vertex (ψ x)) = μ (.vertex x) := by
  simp [mapUnit]

theorem mapUnit_space {α : Type u} {β : Type v} (μ : BoundaryUnit S → Hypergraph α β) (s : Set S) :
    mapUnit ψ μ (.space (ψ '' s)) = μ (.space s) := by
  simp [mapUnit, symm_image_image' ψ]

theorem spaces_sub_image (Γ : Drawing S) (F : Set S) :
    {s ∈ drawingSpaces (mapDrawing ψ Γ) | s ⊆ ψ '' F} = image ψ '' {s ∈ drawingSpaces Γ | s ⊆ F} := by
  ext s'
  rw [drawingSpaces_mapDrawing]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hsF⟩
    exact ⟨s, ⟨hs, (image_subset_image_iff ψ.injective).mp hsF⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hsF⟩, rfl⟩
    exact ⟨mem_image_of_mem _ hs, image_mono hsF⟩

theorem supportGraph_image {α : Type u} {β : Type v} (G : Hypergraph α β) (Γ : Drawing S)
    (μ : BoundaryUnit S → Hypergraph α β) (F : Set S) :
    supportGraph G (mapDrawing ψ Γ) (mapUnit ψ μ) (ψ '' F) = supportGraph G Γ μ F := by
  have hV : (mapDrawing ψ Γ).V ∩ ψ '' F = ψ '' (Γ.V ∩ F) := by
    rw [mapDrawing_V, image_inter' ψ]
  ext
  · simp only [supportGraph, spaces_sub_image, hV, biUnion_image, mapUnit_space, mapUnit_vertex]
  · simp only [supportGraph, spaces_sub_image, hV, biUnion_image, mapUnit_space, mapUnit_vertex]
  · simp only [supportGraph]
    rw [drawingSpaces_mapDrawing, hV]
    constructor
    · rintro ⟨hG, ⟨_, ⟨s, hs, rfl⟩, hsF, hinc⟩ | ⟨_, ⟨x, hx, rfl⟩, hinc⟩⟩
      · rw [mapUnit_space] at hinc
        exact ⟨hG, Or.inl ⟨s, hs, (image_subset_image_iff ψ.injective).mp hsF, hinc⟩⟩
      · rw [mapUnit_vertex] at hinc
        exact ⟨hG, Or.inr ⟨x, hx, hinc⟩⟩
    · rintro ⟨hG, ⟨s, hs, hsF, hinc⟩ | ⟨x, hx, hinc⟩⟩
      · exact ⟨hG, Or.inl ⟨ψ '' s, mem_image_of_mem _ hs, image_mono hsF,
          by rwa [mapUnit_space]⟩⟩
      · exact ⟨hG, Or.inr ⟨ψ x, mem_image_of_mem _ hx, by rwa [mapUnit_vertex]⟩⟩

variable {α : Type u} {β : Type v} {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

theorem isDrawingIso_image (h : IsDrawingIso Γ Γ_sub ιV ιE) :
    IsDrawingIso (mapDrawing ψ Γ) Γ_sub (ιV ∘ ψ.symm) (fun e => ιE (ψ.symm '' e)) := by
  have hcomp : ∀ X : Set S, (ιV ∘ ψ.symm) '' (ψ '' X) = ιV '' X := fun X => by
    rw [← image_comp, Function.comp_assoc, ψ.symm_comp_self, Function.comp_id]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply] at hxy
    rw [h.ιV_injOn hx hy hxy]
  · rw [mapDrawing_V, hcomp, h.ιV_image]
  · rw [mapDrawing_E]
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hef
    simp only [symm_image_image' ψ] at hef
    rw [h.ιE_injOn he hf hef]
  · rw [mapDrawing_E, ← h.ιE_image, ← image_comp]
    congr 1
    funext e
    simp [symm_image_image' ψ]
  · rw [mapDrawing_E, mapDrawing_V]
    rintro _ ⟨e, he, rfl⟩ _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply, symm_image_image' ψ]
    rw [h.inc_iff e he x hx, ← ψ.image_closure, mem_image_iff]

/-- A presentation of `G` in `S`, moved along a homeomorphism `ψ : S ≃ₜ S'`, is a presentation of
`G` in `S'` with the same depths. -/
theorem isPresentation_image (h : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    IsPresentation G (mapDrawing ψ Γ) Γ_sub (ιV ∘ ψ.symm) (fun e => ιE (ψ.symm '' e)) r
      (fun j => ψ '' F_star j) H (mapUnit ψ μ) q := by
  have hback : mapDrawing ψ.symm (mapDrawing ψ Γ) = Γ := mapDrawing_symm_mapDrawing ψ Γ
  have hcomp : ∀ X : Set S, (ιV ∘ ψ.symm) '' (ψ '' X) = ιV '' X := fun X => by
    rw [← image_comp, Function.comp_assoc, ψ.symm_comp_self, Function.comp_id]
  -- A space of the new drawing comes from a space of the old one.
  have hspace : ∀ s' ∈ drawingSpaces (mapDrawing ψ Γ), ψ.symm '' s' ∈ drawingSpaces Γ := by
    intro s' hs'
    rw [← hback, drawingSpaces_mapDrawing]
    exact mem_image_of_mem _ hs'
  have hsub : ∀ (s' : Set S') (X : Set S), s' ⊆ ψ '' X → ψ.symm '' s' ⊆ X := by
    intro s' X hs'
    have := image_mono (f := ψ.symm) hs'
    rwa [symm_image_image' ψ] at this
  have hvert : ∀ (x' : S') (X : Set S), x' ∈ ψ '' X → ψ.symm x' ∈ X := by
    rintro _ X ⟨x, hx, rfl⟩
    simpa using hx
  refine
    { is_surface := isSurface_of_homeo ψ h.is_surface
      is_connected_surface := by
        have := h.is_connected_surface
        exact ψ.surjective.connectedSpace ψ.continuous
      is_proper_drawing := ?_
      cuff_vertices_ge_two := ?_
      drawing_subgraph := h.drawing_subgraph
      drawing_iso := isDrawingIso_image ψ h.drawing_iso
      supports_isSupport := fun j => isSupportOfDrawing_image ψ (h.supports_isSupport j)
      supports_disjoint := fun i j hij =>
        (disjoint_image_iff ψ.injective).mpr (h.supports_disjoint hij)
      bd_vertices_covered := ?_
      v1_sub := h.v1_sub
      v1_union_V := h.v1_union_V
      v1_union_E := h.v1_union_E
      v1_disjoint := h.v1_disjoint
      v1_inter_V := fun j => by
        rw [h.v1_inter_V j, mapDrawing_V, ← image_inter' ψ, hcomp]
      v1_inter_E := h.v1_inter_E
      q_pos := h.q_pos
      μ_vertex_sub := ?_
      μ_space_sub := ?_
      v2_eq := fun j => by
        rw [supportGraph_image]
        exact h.v2_eq j
      v3_space := ?_
      v4_between := ?_ }
  · change bd S' ∩ ψ '' Γ.U ⊆ ψ '' Γ.V
    rw [← image_bd ψ, ← image_inter' ψ]
    exact image_mono h.is_proper_drawing
  · intro C hC
    rw [cuffs_eq ψ] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    rw [mapDrawing_V, ← image_inter' ψ, ncard_image_of_injective _ ψ.injective]
    exact h.cuff_vertices_ge_two C₀ hC₀
  · rw [mapDrawing_V, ← image_bd ψ, ← image_inter' ψ, ← image_iUnion]
    exact image_mono h.bd_vertices_covered
  · intro j x hx
    rw [mapDrawing_V, ← image_inter' ψ] at hx
    exact h.μ_vertex_sub j (ψ.symm x) (hvert x _ hx)
  · intro j s hs hsF
    exact h.μ_space_sub j _ (hspace s hs) (hsub s _ hsF)
  · intro j s hs u₁ u₂ hsF hends
    have hends' : SpaceHasEnds Γ (ψ.symm '' s) (ψ.symm u₁) (ψ.symm u₂) := by
      have := spaceHasEnds_image ψ.symm hends
      rwa [hback] at this
    exact h.v3_space j _ (hspace s hs) _ _ (hsub s _ hsF) hends'
  · intro j s₁ s₂ x hx
    have := liesBetweenInSupport_image ψ.symm hx
    rw [hback, symm_image_image' ψ] at this
    exact h.v4_between j _ _ _ this

/-- Moving along `ψ` keeps a presentation of depth `≤ d`. -/
theorem presentationHasDepthLe_image {d : ℕ}
    (h : PresentationHasDepthLe G Γ Γ_sub ιV ιE r F_star H μ d) :
    PresentationHasDepthLe G (mapDrawing ψ Γ) Γ_sub (ιV ∘ ψ.symm) (fun e => ιE (ψ.symm '' e)) r
      (fun j => ψ '' F_star j) H (mapUnit ψ μ) d := by
  obtain ⟨q, hP, hq, h0⟩ := h
  exact ⟨q, isPresentation_image ψ hP, hq, fun hr => by rw [← image_bd ψ, h0 hr, image_empty]⟩

/-- Every `Σ`-jump of `Γ` is a `Σ'`-jump of the drawing moved along `ψ`. -/
theorem sigmaJumps_subset (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) :
    sigmaJumps Γ Γ_sub ιV ⊆ sigmaJumps (mapDrawing ψ Γ) Γ_sub (ιV ∘ ψ.symm) := by
  rintro J ⟨hJ, hP, x, hx, y, hy, hxy, hterm, hall⟩
  have hV : (mapDrawing ψ Γ).V ∩ bd S' = ψ '' (Γ.V ∩ bd S) := by
    rw [mapDrawing_V, ← image_bd ψ, image_inter' ψ]
  refine ⟨hJ, hP, ψ x, hV ▸ mem_image_of_mem _ hx, ψ y, hV ▸ mem_image_of_mem _ hy,
    fun h => hxy (ψ.injective h), by simpa using hterm, ?_⟩
  intro z hz hzJ
  rw [hV] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply] at hzJ
  rcases hall z₀ hz₀ hzJ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Transport

end Homeo

open Homeo

/-- **Graph Minors XXI, (6.3)** (page 24 of the preprint), for a surface in any universe:
"**6.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\lambda \ge 0$ such that, if $G$ is a graph with a presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$, and there is an exhaustive vital $p$-linkage in $G$, then there are at most
$\lambda$ $\Sigma$-jumps.*"

By the classification of surfaces, `S` is homeomorphic to a model `Σ(a, b, c)` in `Type`. We take
`λ` from `theorem_6_3_parallel_proof` for the model. A presentation in `S` moves to one in the
model (`presentationHasDepthLe_image`), and its jumps become jumps there (`sigmaJumps_subset`). -/
theorem theorem_6_3_proof : GM21Theorem63Statement.{u, v, w} := by
  intro S _ _ hS p r q hq
  obtain ⟨a, b, c, ⟨ψ⟩⟩ := Surface.classification S hS inferInstance
  have : ConnectedSpace (Surface.SurfaceModel a b c) := ψ.surjective.connectedSpace ψ.continuous
  obtain ⟨lam, hlam⟩ := theorem_6_3_parallel_proof.{u, v} (Surface.SurfaceModel a b c)
    (Surface.isSurface_of_homeo ψ hS) p r q hq
  refine ⟨lam, fun G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp => ?_⟩
  exact (Set.encard_le_encard (sigmaJumps_subset ψ Γ Γ_sub ιV)).trans
    (hlam G _ Γ_sub _ _ r' _ H _ L hG hr (presentationHasDepthLe_image ψ hd) hL hLp)

end GM21
end GraphMinor
