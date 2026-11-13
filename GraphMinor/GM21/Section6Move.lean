module

public import GraphMinor.GM21.Defs
import GraphMinor.GM11.DrawingOps
import GraphMinor.Surface.PlaneDisc

/-!
# Moving a presentation to a new surface

At the end of the proof of (6.3) (page 29 of the preprint) the paper moves a presentation to a
new surface: "By extending $\Delta$ to a sphere and removing $R \setminus bd(R)$ from it, we deduce
that $G$ has a presentation in a disc $\Sigma'$, with depth $\le q$ and defect $\le r$."

A presentation only looks at the drawing `Γ` and at `bd(Σ)`. So it moves along any map that is a
homeomorphism from a closed set `K ⊇ U(Γ) ∪ bd(Σ)` of `Σ` onto a closed set `K'` of `Σ'` and takes
`bd(Σ)` onto `bd(Σ')`. Such a map is a `Move`. We move the drawing, the supports and the map `μ`,
and keep the graph, the subgraphs `H_j` and the linkage (`Move.presentationHasDepthLe_image`).
Every `Σ`-jump of the old presentation is a `Σ'`-jump of the new one (`Move.sigmaJumps_subset`).

The case of a homeomorphism of the whole surface is `Homeo.presentationHasDepthLe_image` in
`Section6Universe.lean`.
-/

@[expose] public section

universe u v w w'

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface

variable {S : Type w} {S' : Type w'} [TopologicalSpace S] [TopologicalSpace S']

/-- `ψ` maps the closed set `K` homeomorphically onto the closed set `K'`, with inverse `φ`. -/
structure ClosedMatch (ψ : S → S') (φ : S' → S) (K : Set S) (K' : Set S') : Prop where
  isClosed : IsClosed K
  isClosed' : IsClosed K'
  mapsTo : MapsTo ψ K K'
  mapsTo' : MapsTo φ K' K
  left : LeftInvOn φ ψ K
  right : LeftInvOn ψ φ K'
  cont : ContinuousOn ψ K
  cont' : ContinuousOn φ K'

namespace ClosedMatch

variable {ψ : S → S'} {φ : S' → S} {K : Set S} {K' : Set S'} (h : ClosedMatch ψ φ K K')
include h

theorem symm : ClosedMatch φ ψ K' K :=
  ⟨h.isClosed', h.isClosed, h.mapsTo', h.mapsTo, h.right, h.left, h.cont', h.cont⟩

theorem injOn : InjOn ψ K := h.left.injOn

theorem image_subset {X : Set S} (hX : X ⊆ K) : ψ '' X ⊆ K' :=
  (h.mapsTo.mono_left hX).image_subset

theorem image_image {X : Set S} (hX : X ⊆ K) : φ '' (ψ '' X) = X := by
  rw [Set.image_image]
  exact (image_congr fun x hx => h.left (hX hx)).trans (image_id X)

theorem image_inter {X Y : Set S} (hX : X ⊆ K) (hY : Y ⊆ K) : ψ '' (X ∩ Y) = ψ '' X ∩ ψ '' Y :=
  h.injOn.image_inter hX hY

theorem image_sdiff {X Y : Set S} (hX : X ⊆ K) (hY : Y ⊆ K) : ψ '' (X \ Y) = ψ '' X \ ψ '' Y := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxX, hxY⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hxX, ?_⟩
    rintro ⟨x', hx'Y, he⟩
    exact hxY (h.injOn (hY hx'Y) (hX hxX) he ▸ hx'Y)
  · rintro ⟨⟨x, hxX, rfl⟩, hy⟩
    exact ⟨x, ⟨hxX, fun hxY => hy (mem_image_of_mem _ hxY)⟩, rfl⟩

theorem mem_image_iff {X : Set S} (hX : X ⊆ K) {x : S} (hx : x ∈ K) : ψ x ∈ ψ '' X ↔ x ∈ X :=
  ⟨fun ⟨_, hx', he⟩ => h.injOn (hX hx') hx he ▸ hx', mem_image_of_mem _⟩

theorem image_subset_image_iff {X Y : Set S} (hX : X ⊆ K) (hY : Y ⊆ K) :
    ψ '' X ⊆ ψ '' Y ↔ X ⊆ Y :=
  ⟨fun hXY _ hx => (h.mem_image_iff hY (hX hx)).1 (hXY (mem_image_of_mem _ hx)), image_mono⟩

theorem image_ne_image {x y : S} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) : ψ x ≠ ψ y :=
  fun he => hxy (h.injOn hx hy he)

theorem continuousOn_sub {X : Set S} (hX : X ⊆ K) : ContinuousOn ψ X := h.cont.mono hX

theorem continuousOn_image {X : Set S} (hX : X ⊆ K) : ContinuousOn φ (ψ '' X) :=
  h.cont'.mono (h.image_subset hX)

theorem leftInvOn_sub {X : Set S} (hX : X ⊆ K) : LeftInvOn φ ψ X := h.left.mono hX

theorem closure_subset {X : Set S} (hX : X ⊆ K) : closure X ⊆ K :=
  closure_minimal hX h.isClosed

/-- Closures move along `ψ`. -/
theorem closure_image {X : Set S} (hX : X ⊆ K) : closure (ψ '' X) = ψ '' closure X := by
  have hc : closure X ⊆ K := h.closure_subset hX
  have hc' : closure (ψ '' X) ⊆ K' := closure_minimal (h.image_subset hX) h.isClosed'
  refine Subset.antisymm (fun y hy => ?_) ((h.cont.mono hc).image_closure)
  -- `φ y` lies in the closure of `φ '' (ψ '' X) = X`, and `ψ (φ y) = y`.
  have hφ : φ y ∈ closure X := by
    have := (h.cont'.mono hc').image_closure (mem_image_of_mem φ hy)
    rwa [h.image_image hX] at this
  exact ⟨φ y, hφ, h.right (hc' hy)⟩

theorem isLineWithEnds_image {L : Set S} (hL : L ⊆ K) {a b : S} (hl : IsLineWithEnds L a b) :
    IsLineWithEnds (ψ '' L) (ψ a) (ψ b) := by
  obtain ⟨e, he⟩ := exists_homeomorph_image (h.continuousOn_sub hL) (h.continuousOn_image hL)
    (h.leftInvOn_sub hL)
  obtain ⟨f, h₀, h₁⟩ := hl
  exact ⟨f.trans e, by simp [he, h₀], by simp [he, h₁]⟩

theorem isOArc_image {L : Set S} (hL : L ⊆ K) (hl : IsOArc L) : IsOArc (ψ '' L) :=
  hl.image (h.continuousOn_sub hL) (h.continuousOn_image hL) (h.leftInvOn_sub hL)

theorem componentsIn_image {A : Set S} (hA : A ⊆ K) :
    componentsIn (ψ '' A) = image ψ '' componentsIn A :=
  Surface.componentsIn_image (h.continuousOn_sub hA) (h.continuousOn_image hA)
    (h.leftInvOn_sub hA)

theorem isClosed_image {X : Set S} (hX : X ⊆ K) (hXc : IsClosed X) : IsClosed (ψ '' X) := by
  rw [← closure_eq_iff_isClosed, h.closure_image hX, hXc.closure_eq]

theorem arcComponentsIn_image [T2Space S] {A : Set S} (hA : A ⊆ K) :
    arcComponentsIn (ψ '' A) = image ψ '' arcComponentsIn A :=
  GM11.arcComponentsIn_image (h.continuousOn_sub hA) (h.continuousOn_image hA)
    fun _ hx => h.left (hA hx)

end ClosedMatch

theorem biUnion_congr' {ι γ : Type*} {s : Set ι} {f g : ι → Set γ} (hfg : ∀ i ∈ s, f i = g i) :
    ⋃ i ∈ s, f i = ⋃ i ∈ s, g i := by
  ext x
  simp only [mem_iUnion]
  exact ⟨fun ⟨i, hi, hx⟩ => ⟨i, hi, hfg i hi ▸ hx⟩, fun ⟨i, hi, hx⟩ => ⟨i, hi, (hfg i hi).symm ▸ hx⟩⟩

theorem subset_of_mem_componentsIn {A C : Set S} (hC : C ∈ componentsIn A) : C ⊆ A := by
  obtain ⟨x, -, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

/-- The image of a drawing under a `ClosedMatch` whose domain holds `U(Γ)`. -/
noncomputable def ClosedMatch.mapDrawing [T2Space S] {ψ : S → S'} {φ : S' → S} {K : Set S} {K' : Set S'}
    (h : ClosedMatch ψ φ K K') (Γ : Drawing S) (hU : Γ.U ⊆ K) : Drawing S' where
  U := ψ '' Γ.U
  V := ψ '' Γ.V
  V_subset_U := image_mono Γ.V_subset_U
  isClosed_U := h.isClosed_image hU Γ.isClosed_U
  finite_V := Γ.finite_V.image _
  finite_edges := by
    have hVK : Γ.V ⊆ K := Γ.V_subset_U.trans hU
    rw [← h.image_sdiff hU hVK, h.arcComponentsIn_image (sdiff_subset.trans hU)]
    exact Γ.finite_edges.image _
  edge_cond := by
    have hVK : Γ.V ⊆ K := Γ.V_subset_U.trans hU
    rw [← h.image_sdiff hU hVK, h.arcComponentsIn_image (sdiff_subset.trans hU)]
    rintro _ ⟨e, he, rfl⟩
    have heK : e ⊆ K := he.2.1.trans (sdiff_subset.trans hU)
    have hcK : closure e ⊆ K := h.closure_subset heK
    have hcap : closure (ψ '' e) ∩ ψ '' Γ.V = ψ '' (closure e ∩ Γ.V) := by
      rw [h.closure_image heK, h.image_inter hcK hVK]
    rcases Γ.edge_cond e he with ⟨a, b, hab, h2, h3⟩ | ⟨a, h2, h3⟩
    · have ha : a ∈ K := hVK (h2.symm ▸ mem_insert a {b} : a ∈ closure e ∩ Γ.V).2
      have hb : b ∈ K := hVK (h2.symm ▸ mem_insert_of_mem a rfl : b ∈ closure e ∩ Γ.V).2
      refine .inl ⟨ψ a, ψ b, h.image_ne_image ha hb hab, by rw [hcap, h2, image_pair], ?_⟩
      rw [h.closure_image heK]
      exact h.isLineWithEnds_image hcK h3
    · refine .inr ⟨ψ a, by rw [hcap, h2, image_singleton], ?_⟩
      rw [h.closure_image heK]
      exact h.isOArc_image hcK h3

namespace ClosedMatch

variable [T2Space S] [T2Space S'] {ψ : S → S'} {φ : S' → S} {K : Set S} {K' : Set S'}
  (h : ClosedMatch ψ φ K K')
include h

omit [T2Space S'] in
theorem mapDrawing_U (Γ : Drawing S) (hU : Γ.U ⊆ K) : (h.mapDrawing Γ hU).U = ψ '' Γ.U := rfl

omit [T2Space S'] in
theorem mapDrawing_V (Γ : Drawing S) (hU : Γ.U ⊆ K) : (h.mapDrawing Γ hU).V = ψ '' Γ.V := rfl

omit [T2Space S'] in
theorem mapDrawing_E (Γ : Drawing S) (hU : Γ.U ⊆ K) :
    (h.mapDrawing Γ hU).E = image ψ '' Γ.E := by
  change arcComponentsIn (ψ '' Γ.U \ ψ '' Γ.V) = _
  rw [← h.image_sdiff hU (Γ.V_subset_U.trans hU), h.arcComponentsIn_image (sdiff_subset.trans hU)]
  rfl

omit [T2Space S'] in
theorem mapDrawing_U_subset (Γ : Drawing S) (hU : Γ.U ⊆ K) : (h.mapDrawing Γ hU).U ⊆ K' :=
  h.image_subset hU

/-- Moving a drawing there and back gives the same drawing. -/
theorem mapDrawing_symm (Γ : Drawing S) (hU : Γ.U ⊆ K) :
    h.symm.mapDrawing (h.mapDrawing Γ hU) (h.mapDrawing_U_subset Γ hU) = Γ := by
  have hVK : Γ.V ⊆ K := Γ.V_subset_U.trans hU
  cases Γ
  simp only [ClosedMatch.mapDrawing, h.image_image hU, h.image_image hVK]

end ClosedMatch

/-- A `Move` is a `ClosedMatch` whose domain holds `bd(Σ)` and which takes `bd(Σ)` onto
`bd(Σ')`. -/
structure Move (ψ : S → S') (φ : S' → S) (K : Set S) (K' : Set S') : Prop
    extends ClosedMatch ψ φ K K' where
  bd_subset : bd S ⊆ K
  image_bd : ψ '' bd S = bd S'

namespace Move

variable {ψ : S → S'} {φ : S' → S} {K : Set S} {K' : Set S'} (h : Move ψ φ K K')
include h

theorem bd_subset' : bd S' ⊆ K' := h.image_bd ▸ h.toClosedMatch.image_subset h.bd_subset

theorem symm : Move φ ψ K' K :=
  ⟨h.toClosedMatch.symm, h.bd_subset', by
    rw [← h.image_bd, h.toClosedMatch.image_image h.bd_subset]⟩

theorem cuffs_eq : cuffs S' = image ψ '' cuffs S := by
  unfold cuffs
  rw [← h.image_bd]
  exact h.toClosedMatch.componentsIn_image h.bd_subset

variable [T2Space S] {Γ : Drawing S} (hU : Γ.U ⊆ K)
include hU

omit [TopologicalSpace S'] [T2Space S] h in
theorem V_subset : Γ.V ⊆ K := Γ.V_subset_U.trans hU

theorem V_inter_bd : (h.mapDrawing Γ hU).V ∩ bd S' = ψ '' (Γ.V ∩ bd S) := by
  rw [ClosedMatch.mapDrawing_V, ← h.image_bd,
    h.toClosedMatch.image_inter (V_subset hU) h.bd_subset]

theorem drawingSpaces_mapDrawing :
    drawingSpaces (h.mapDrawing Γ hU) = image ψ '' drawingSpaces Γ := by
  unfold drawingSpaces
  rw [ClosedMatch.mapDrawing_V, ← h.image_bd,
    ← h.toClosedMatch.image_sdiff h.bd_subset (V_subset hU)]
  exact h.toClosedMatch.componentsIn_image (sdiff_subset.trans h.bd_subset)

omit [T2Space S] hU in
theorem space_subset {s : Set S} (hs : s ∈ drawingSpaces Γ) : s ⊆ K :=
  (subset_of_mem_componentsIn hs).trans (sdiff_subset.trans h.bd_subset)

theorem spaceHasEnds_image {s : Set S} {a b : S} (hsp : SpaceHasEnds Γ s a b) :
    SpaceHasEnds (h.mapDrawing Γ hU) (ψ '' s) (ψ a) (ψ b) := by
  obtain ⟨hs, ha, hb, hab, hL, hcl⟩ := hsp
  have hsK := h.space_subset hs
  have haK : a ∈ K := h.bd_subset ha.2
  have hbK : b ∈ K := h.bd_subset hb.2
  have hLK : s ∪ {a, b} ⊆ K := union_subset hsK (pair_subset haK hbK)
  refine ⟨?_, ?_, ?_, h.toClosedMatch.image_ne_image haK hbK hab, ?_, ?_⟩
  · rw [h.drawingSpaces_mapDrawing hU]; exact mem_image_of_mem _ hs
  · rw [h.V_inter_bd hU]; exact mem_image_of_mem _ ha
  · rw [h.V_inter_bd hU]; exact mem_image_of_mem _ hb
  · have := h.toClosedMatch.isLineWithEnds_image hLK hL
    rwa [image_union, image_pair] at this
  · rw [h.toClosedMatch.closure_image hsK, hcl, image_union, image_pair]

omit [TopologicalSpace S'] [T2Space S] h hU in
theorem support_subset {F : Set S} {a b : S} (hF : SupportHasEnds Γ F a b) : F ⊆ bd S := by
  rcases hF with ⟨x, hx, rfl, -, -⟩ | ⟨hF, -⟩
  · exact singleton_subset_iff.2 hx.2
  · exact hF

theorem supportHasEnds_image {F : Set S} {a b : S} (hF : SupportHasEnds Γ F a b) :
    SupportHasEnds (h.mapDrawing Γ hU) (ψ '' F) (ψ a) (ψ b) := by
  have hV := h.V_inter_bd hU
  rcases hF with ⟨x, hx, hFx, hax, hbx⟩ | ⟨hF, hab, ha, hb, hL⟩
  · exact Or.inl ⟨ψ x, hV ▸ mem_image_of_mem _ hx, by rw [hFx, image_singleton], by rw [hax],
      by rw [hbx]⟩
  · refine Or.inr ⟨?_, h.toClosedMatch.image_ne_image (h.bd_subset ha.2) (h.bd_subset hb.2) hab,
      hV ▸ mem_image_of_mem _ ha, hV ▸ mem_image_of_mem _ hb,
      h.toClosedMatch.isLineWithEnds_image (hF.trans h.bd_subset) hL⟩
    rw [← h.image_bd]; exact image_mono hF

theorem isSupportOfDrawing_image {F : Set S} (hF : IsSupportOfDrawing Γ F) :
    IsSupportOfDrawing (h.mapDrawing Γ hU) (ψ '' F) := by
  obtain ⟨a, b, hF⟩ := hF
  exact ⟨ψ a, ψ b, h.supportHasEnds_image hU hF⟩

omit [T2Space S] hU in
theorem support_subset' {F : Set S} (hF : IsSupportOfDrawing Γ F) : F ⊆ K := by
  obtain ⟨a, b, hF⟩ := hF
  exact (support_subset hF).trans h.bd_subset

theorem liesBetweenInSupport_image {F s₁ s₂ : Set S} {x : S}
    (hx : LiesBetweenInSupport Γ F s₁ s₂ x) :
    LiesBetweenInSupport (h.mapDrawing Γ hU) (ψ '' F) (ψ '' s₁) (ψ '' s₂) (ψ x) := by
  obtain ⟨hx, hs₁, hs₂, h₁F, h₂F, I₁, I₂, hI₁, hI₂, hun, hint, h₁, h₂⟩ := hx
  refine ⟨?_, ?_, ?_, image_mono h₁F, image_mono h₂F, ψ '' I₁, ψ '' I₂,
    h.isSupportOfDrawing_image hU hI₁, h.isSupportOfDrawing_image hU hI₂, ?_, ?_, image_mono h₁,
    image_mono h₂⟩
  · rw [ClosedMatch.mapDrawing_V, ← h.toClosedMatch.image_inter (hun ▸ union_subset
      (h.support_subset' hI₁) (h.support_subset' hI₂)) (V_subset hU)]
    exact mem_image_of_mem _ hx
  · rw [h.drawingSpaces_mapDrawing hU]; exact mem_image_of_mem _ hs₁
  · rw [h.drawingSpaces_mapDrawing hU]; exact mem_image_of_mem _ hs₂
  · rw [← image_union, hun]
  · rw [← h.toClosedMatch.image_inter (h.support_subset' hI₁) (h.support_subset' hI₂), hint,
      image_singleton]

end Move

/-- The map `μ` of a presentation, moved along `φ`. -/
def mapUnit {α : Type u} {β : Type v} (φ : S' → S) (μ : BoundaryUnit S → Hypergraph α β) :
    BoundaryUnit S' → Hypergraph α β
  | .vertex x => μ (.vertex (φ x))
  | .space s => μ (.space (φ '' s))

namespace Move

variable {ψ : S → S'} {φ : S' → S} {K : Set S} {K' : Set S'} (h : Move ψ φ K K')
include h

theorem mapUnit_vertex {α : Type u} {β : Type v} (μ : BoundaryUnit S → Hypergraph α β) {x : S}
    (hx : x ∈ K) : mapUnit φ μ (.vertex (ψ x)) = μ (.vertex x) := by
  simp [mapUnit, h.left hx]

theorem mapUnit_space {α : Type u} {β : Type v} (μ : BoundaryUnit S → Hypergraph α β) {s : Set S}
    (hs : s ⊆ K) : mapUnit φ μ (.space (ψ '' s)) = μ (.space s) := by
  simp [mapUnit, h.toClosedMatch.image_image hs]

variable [T2Space S] {Γ : Drawing S} (hU : Γ.U ⊆ K)
include hU

theorem spaces_sub_image {F : Set S} (hF : F ⊆ K) :
    {s ∈ drawingSpaces (h.mapDrawing Γ hU) | s ⊆ ψ '' F} =
      image ψ '' {s ∈ drawingSpaces Γ | s ⊆ F} := by
  ext s'
  rw [h.drawingSpaces_mapDrawing hU]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hsF⟩
    exact ⟨s, ⟨hs, (h.toClosedMatch.image_subset_image_iff (h.space_subset hs) hF).1 hsF⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hsF⟩, rfl⟩
    exact ⟨mem_image_of_mem _ hs, image_mono hsF⟩

theorem supportGraph_image {α : Type u} {β : Type v} (G : Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) {F : Set S} (hF : F ⊆ K) :
    supportGraph G (h.mapDrawing Γ hU) (mapUnit φ μ) (ψ '' F) = supportGraph G Γ μ F := by
  have hV : (h.mapDrawing Γ hU).V ∩ ψ '' F = ψ '' (Γ.V ∩ F) := by
    rw [ClosedMatch.mapDrawing_V, h.toClosedMatch.image_inter (V_subset hU) hF]
  have hsp : ∀ s ∈ {s ∈ drawingSpaces Γ | s ⊆ F},
      mapUnit φ μ (.space (ψ '' s)) = μ (.space s) := fun s hs =>
    h.mapUnit_space μ (h.space_subset hs.1)
  have hvx : ∀ x ∈ Γ.V ∩ F, mapUnit φ μ (.vertex (ψ x)) = μ (.vertex x) := fun x hx =>
    h.mapUnit_vertex μ (V_subset hU hx.1)
  ext
  · simp only [supportGraph, h.spaces_sub_image hU hF, hV, biUnion_image]
    rw [biUnion_congr' (s := {s ∈ drawingSpaces Γ | s ⊆ F}) fun s hs => by rw [hsp s hs],
      biUnion_congr' (s := Γ.V ∩ F) fun x hx => by rw [hvx x hx]]
  · simp only [supportGraph, h.spaces_sub_image hU hF, hV, biUnion_image]
    rw [biUnion_congr' (s := {s ∈ drawingSpaces Γ | s ⊆ F}) fun s hs => by rw [hsp s hs],
      biUnion_congr' (s := Γ.V ∩ F) fun x hx => by rw [hvx x hx]]
  · simp only [supportGraph]
    rw [h.drawingSpaces_mapDrawing hU, hV]
    constructor
    · rintro ⟨hG, ⟨_, ⟨s, hs, rfl⟩, hsF, hinc⟩ | ⟨_, ⟨x, hx, rfl⟩, hinc⟩⟩
      · have hsF' := (h.toClosedMatch.image_subset_image_iff (h.space_subset hs) hF).1 hsF
        rw [h.mapUnit_space μ (h.space_subset hs)] at hinc
        exact ⟨hG, Or.inl ⟨s, hs, hsF', hinc⟩⟩
      · rw [hvx x hx] at hinc
        exact ⟨hG, Or.inr ⟨x, hx, hinc⟩⟩
    · rintro ⟨hG, ⟨s, hs, hsF, hinc⟩ | ⟨x, hx, hinc⟩⟩
      · exact ⟨hG, Or.inl ⟨ψ '' s, mem_image_of_mem _ hs, image_mono hsF,
          by rwa [h.mapUnit_space μ (h.space_subset hs)]⟩⟩
      · exact ⟨hG, Or.inr ⟨ψ x, mem_image_of_mem _ hx, by rwa [hvx x hx]⟩⟩

variable {α : Type u} {β : Type v} {G : Hypergraph α β} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

omit [TopologicalSpace S'] [T2Space S] h in
theorem edge_subset {e : Set S} (he : e ∈ Γ.E) : e ⊆ K := he.2.1.trans (sdiff_subset.trans hU)

theorem isDrawingIso_image (hi : IsDrawingIso Γ Γ_sub ιV ιE) :
    IsDrawingIso (h.mapDrawing Γ hU) Γ_sub (ιV ∘ φ) (fun e => ιE (φ '' e)) := by
  have hVK := V_subset hU
  have hcomp : (ιV ∘ φ) '' (ψ '' Γ.V) = ιV '' Γ.V := by
    rw [← Set.image_comp, Function.comp_assoc]
    exact image_congr fun x hx => by simp [h.left (hVK hx)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    simp only [Function.comp_apply, h.left (hVK hx), h.left (hVK hy)] at hxy
    rw [hi.ιV_injOn hx hy hxy]
  · rw [ClosedMatch.mapDrawing_V, hcomp, hi.ιV_image]
  · rw [ClosedMatch.mapDrawing_E]
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hef
    simp only [h.toClosedMatch.image_image (edge_subset hU he),
      h.toClosedMatch.image_image (edge_subset hU hf)] at hef
    rw [hi.ιE_injOn he hf hef]
  · rw [ClosedMatch.mapDrawing_E, ← hi.ιE_image, ← Set.image_comp]
    exact image_congr fun e he => by
      simp [h.toClosedMatch.image_image (edge_subset hU he)]
  · rw [ClosedMatch.mapDrawing_E, ClosedMatch.mapDrawing_V]
    rintro _ ⟨e, he, rfl⟩ _ ⟨x, hx, rfl⟩
    have heK := edge_subset hU he
    simp only [Function.comp_apply, h.left (hVK hx), h.toClosedMatch.image_image heK]
    rw [hi.inc_iff e he x hx, h.toClosedMatch.closure_image heK,
      h.toClosedMatch.mem_image_iff (h.toClosedMatch.closure_subset heK) (hVK hx)]

/-- **Moving a presentation.** A presentation of `G` in `Σ`, moved along a `Move` whose domain holds
`U(Γ)`, is a presentation of `G` in `Σ'` with the same depths, if `Σ'` is a connected surface. -/
theorem isPresentation_image [T2Space S'] (hS' : IsSurface S') [ConnectedSpace S']
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    IsPresentation G (h.mapDrawing Γ hU) Γ_sub (ιV ∘ φ) (fun e => ιE (φ '' e)) r
      (fun j => ψ '' F_star j) H (mapUnit φ μ) q := by
  have hVK := V_subset hU
  have hU' := h.mapDrawing_U_subset Γ hU
  have hback := h.mapDrawing_symm Γ hU
  have hFK : ∀ j, F_star j ⊆ K := fun j => h.support_subset' (hP.supports_isSupport j)
  have hcomp : ∀ X ⊆ K, (ιV ∘ φ) '' (ψ '' X) = ιV '' X := fun X hX => by
    rw [← Set.image_comp, Function.comp_assoc]
    exact image_congr fun x hx => by simp [h.left (hX hx)]
  -- A space of the new drawing comes from a space of the old one.
  have hspace : ∀ s' ∈ drawingSpaces (h.mapDrawing Γ hU), φ '' s' ∈ drawingSpaces Γ := by
    intro s' hs'
    rw [h.drawingSpaces_mapDrawing hU] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    rwa [h.toClosedMatch.image_image (h.space_subset hs)]
  have hsub : ∀ s' ∈ drawingSpaces (h.mapDrawing Γ hU), ∀ X ⊆ K, s' ⊆ ψ '' X → φ '' s' ⊆ X := by
    intro s' hs' X hX hsX
    have := image_mono (f := φ) hsX
    rwa [h.toClosedMatch.image_image hX] at this
  have hvert : ∀ (x' : S') (X : Set S), X ⊆ K → x' ∈ ψ '' X → φ x' ∈ X := by
    rintro _ X hX ⟨x, hx, rfl⟩
    rwa [h.left (hX hx)]
  refine
    { is_surface := hS'
      is_connected_surface := inferInstance
      is_proper_drawing := ?_
      cuff_vertices_ge_two := ?_
      drawing_subgraph := hP.drawing_subgraph
      drawing_iso := h.isDrawingIso_image hU hP.drawing_iso
      supports_isSupport := fun j => h.isSupportOfDrawing_image hU (hP.supports_isSupport j)
      supports_disjoint := fun i j hij => by
        show Disjoint _ _
        rw [disjoint_iff_inter_eq_empty, ← h.toClosedMatch.image_inter (hFK i) (hFK j),
          disjoint_iff_inter_eq_empty.1 (hP.supports_disjoint hij), image_empty]
      bd_vertices_covered := ?_
      v1_sub := hP.v1_sub
      v1_union_V := hP.v1_union_V
      v1_union_E := hP.v1_union_E
      v1_disjoint := hP.v1_disjoint
      v1_inter_V := fun j => by
        rw [hP.v1_inter_V j, ClosedMatch.mapDrawing_V,
          ← h.toClosedMatch.image_inter hVK (hFK j), hcomp _ (inter_subset_right.trans (hFK j))]
      v1_inter_E := hP.v1_inter_E
      q_pos := hP.q_pos
      μ_vertex_sub := ?_
      μ_space_sub := ?_
      v2_eq := fun j => by
        rw [h.supportGraph_image hU G μ (hFK j)]
        exact hP.v2_eq j
      v3_space := ?_
      v4_between := ?_ }
  · change bd S' ∩ ψ '' Γ.U ⊆ ψ '' Γ.V
    rw [← h.image_bd, ← h.toClosedMatch.image_inter h.bd_subset hU]
    exact image_mono hP.is_proper_drawing
  · intro C hC
    rw [h.cuffs_eq] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    have hC₀K : C₀ ⊆ K := (subset_of_mem_componentsIn hC₀).trans h.bd_subset
    rw [ClosedMatch.mapDrawing_V, ← h.toClosedMatch.image_inter hVK hC₀K,
      (h.toClosedMatch.injOn.mono (inter_subset_left.trans hVK)).ncard_image]
    exact hP.cuff_vertices_ge_two C₀ hC₀
  · rw [h.V_inter_bd hU, ← image_iUnion]
    exact image_mono hP.bd_vertices_covered
  · intro j x hx
    rw [ClosedMatch.mapDrawing_V, ← h.toClosedMatch.image_inter hVK (hFK j)] at hx
    exact hP.μ_vertex_sub j (φ x) (hvert x _ (inter_subset_left.trans hVK) hx)
  · intro j s hs hsF
    exact hP.μ_space_sub j _ (hspace s hs) (hsub s hs _ (hFK j) hsF)
  · intro j s hs u₁ u₂ hsF hends
    have hends' : SpaceHasEnds Γ (φ '' s) (φ u₁) (φ u₂) := by
      have := h.symm.spaceHasEnds_image hU' hends
      rwa [hback] at this
    exact hP.v3_space j _ (hspace s hs) _ _ (hsub s hs _ (hFK j) hsF) hends'
  · intro j s₁ s₂ x hx
    have := h.symm.liesBetweenInSupport_image hU' hx
    rw [hback, h.toClosedMatch.image_image (hFK j)] at this
    exact hP.v4_between j _ _ _ this

/-- Moving along a `Move` keeps a presentation of depth `≤ d`. -/
theorem presentationHasDepthLe_image [T2Space S'] (hS' : IsSurface S') [ConnectedSpace S'] {d : ℕ}
    (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r F_star H μ d) :
    PresentationHasDepthLe G (h.mapDrawing Γ hU) Γ_sub (ιV ∘ φ) (fun e => ιE (φ '' e)) r
      (fun j => ψ '' F_star j) H (mapUnit φ μ) d := by
  obtain ⟨q, hP, hq, h0⟩ := hd
  exact ⟨q, h.isPresentation_image hU hS' hP, hq,
    fun hr => by rw [← h.image_bd, h0 hr, image_empty]⟩

/-- Every `Σ`-jump of `Γ` is a `Σ'`-jump of the moved drawing. -/
theorem sigmaJumps_subset :
    sigmaJumps Γ Γ_sub ιV ⊆ sigmaJumps (h.mapDrawing Γ hU) Γ_sub (ιV ∘ φ) := by
  rintro J ⟨hJ, hP, x, hx, y, hy, hxy, hterm, hall⟩
  have hV := h.V_inter_bd hU
  have hK : ∀ {z}, z ∈ Γ.V ∩ bd S → z ∈ K := fun hz => h.bd_subset hz.2
  refine ⟨hJ, hP, ψ x, hV ▸ mem_image_of_mem _ hx, ψ y, hV ▸ mem_image_of_mem _ hy,
    h.toClosedMatch.image_ne_image (hK hx) (hK hy) hxy, by
      simpa [h.left (hK hx), h.left (hK hy)] using hterm, ?_⟩
  intro z hz hzJ
  rw [hV] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  simp only [Function.comp_apply, h.left (hK hz₀)] at hzJ
  rcases hall z₀ hz₀ hzJ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Move

end GM21
end GraphMinor
