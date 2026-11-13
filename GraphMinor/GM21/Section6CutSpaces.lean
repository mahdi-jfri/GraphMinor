module

public import GraphMinor.GM21.Section6CutDrawing
import GraphMinor.GM19.CutMap
import GraphMinor.Surface.DiscGrow

/-!
# Graph Minors XXI, (6.3), claim (2): spaces and supports on the cut surface

Let `ψ : Σ' → Σ` undo the cut along a proper line `F` with ends `a, b ∈ V(Γ)`, and let
`Γ' = ψ⁻¹(Γ)` be the drawing on `Σ'`. The boundary of `Σ'` is the set over `bd(Σ) ∪ F`. This file
compares the spaces and supports of `Γ'` in `Σ'` with those of `Γ` in `Σ`, as the presentation of
claim (2) of the proof of (6.3) (page 28 of the preprint) needs.

* Each space `s` of `Γ` lifts to the space `ψ⁻¹(s)` of `Γ'` (`preimage_mem_drawingSpaces`), and
  each space of `Γ'` over `bd(Σ)` is such a lift (`exists_eq_preimage_of_mem_drawingSpaces`). The
  reason is that `bd(Σ') \ V(Γ')` is the union of the parts over `bd(Σ) \ V(Γ)` and over
  `F \ {a, b}`, which are closed in it and disjoint, and `ψ` is a homeomorphism off `F`.
* On a closed set `K'` over `bd(Σ)` on which `ψ` is one to one, `ψ` carries the ends of spaces,
  supports, and betweenness in `K'` to `Γ` (`spaceHasEnds_image`, `supportHasEnds_image`,
  `liesBetweenInSupport_image`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- A continuous map that is one to one on a line carries it to a line, if the target is
Hausdorff. -/
theorem isLineWithEnds_image_of_injOn [T2Space S] {L : Set S'} {u v : S'}
    (hL : IsLineWithEnds L u v) {f : S' → S} (hc : Continuous f) (hi : InjOn f L) :
    IsLineWithEnds (f '' L) (f u) (f v) := by
  obtain ⟨c, hcarc, hr, h0, h1⟩ := hL.exists_arc
  have harc : IsArcMap (f ∘ c) :=
    ⟨hc.comp hcarc.1, fun s t he => hcarc.2 (hi (hr ▸ mem_range_self s)
      (hr ▸ mem_range_self t) he)⟩
  have h3 := harc.isLineWithEnds
  rw [range_comp, hr] at h3
  simpa [Function.comp, h0, h1] using h3

variable {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

namespace IsLineCut

variable (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)
include h

/-- `ψ` is onto, so the image of the lift of a set is the set. -/
theorem image_preimage (A : Set S) : ψ '' (ψ ⁻¹' A) = A :=
  image_preimage_eq A h.cutting.2.1

/-- The boundary of `Σ'` minus the vertices of `Γ'` splits into the parts over `bd(Σ)` and over `F`.
A preconnected subset of it that meets the part over `bd(Σ) \ V(Γ)` lies in that part. -/
theorem subset_preimage_bd_of_isPreconnected (hS : IsSurface S) (hF : IsProperLineInSurface F a b)
    {Γ : Drawing S} (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {T : Set S'} (hT : IsPreconnected T)
    (hTsub : T ⊆ bd S' \ ψ ⁻¹' Γ.V) {z : S'} (hzT : z ∈ T) (hz : ψ z ∈ bd S) :
    T ⊆ ψ ⁻¹' (bd S \ Γ.V) := by
  have : T2Space S := hS.2.1
  have hFc : IsClosed F := hF.1.isCompact.isClosed
  have hbd := h.bd_eq hS hF
  have hcov : T ⊆ ψ ⁻¹' bd S ∪ ψ ⁻¹' F := fun y hy => by
    have := (hTsub hy).1
    rw [hbd] at this
    exact this
  have hdis : T ∩ (ψ ⁻¹' bd S ∩ ψ ⁻¹' F) = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    intro hyT hyb hyF
    have : ψ y ∈ F ∩ bd S := ⟨hyF, hyb⟩
    rw [hF.inter_bd_eq] at this
    rcases this with h1 | h1
    · exact (hTsub hyT).2 (show ψ y ∈ Γ.V by rw [h1]; exact habV.1)
    · exact (hTsub hyT).2 (show ψ y ∈ Γ.V by rw [h1]; exact habV.2)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hT) _ _
      ((isClosed_bd S).preimage h.continuous) (hFc.preimage h.continuous) hcov hdis with h1 | h1
  · exact fun y hy => ⟨h1 hy, (hTsub hy).2⟩
  · exfalso
    have hzF : ψ z ∈ F := h1 hzT
    have : ψ z ∈ F ∩ bd S := ⟨hzF, hz⟩
    rw [hF.inter_bd_eq] at this
    rcases this with h2 | h2
    · exact (hTsub hzT).2 (show ψ z ∈ Γ.V by rw [h2]; exact habV.1)
    · exact (hTsub hzT).2 (show ψ z ∈ Γ.V by rw [h2]; exact habV.2)

/-- **The lift of a space is a space.** Let `s` be the space of `Γ` containing `ψ(z)`. The lift
`ψ⁻¹(s)` is preconnected, since `ψ` is a homeomorphism off `F`, so it lies in the component of `z`.
Conversely that component lies over `bd(Σ) \ V(Γ)`, and its image is a preconnected set through
`ψ(z)`, so it lies in `s`. -/
theorem preimage_connectedComponentIn (hS : IsSurface S) (hF : IsProperLineInSurface F a b)
    {Γ : Drawing S} (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V)
    {z : S'} (hz : ψ z ∈ bd S \ Γ.V) :
    ψ ⁻¹' connectedComponentIn (bd S \ Γ.V) (ψ z) = connectedComponentIn (bd S' \ Γ'.V) z := by
  have : T2Space S := hS.2.1
  have : CompactSpace S' := h.compactSpace
  have hFc : IsClosed F := hF.1.isCompact.isClosed
  have hbd := h.bd_eq hS hF
  have hoff : bd S \ Γ.V ⊆ Fᶜ := fun x hx hxF => by
    have : x ∈ F ∩ bd S := ⟨hxF, hx.1⟩
    rw [hF.inter_bd_eq] at this
    rcases this with rfl | rfl
    · exact hx.2 habV.1
    · exact hx.2 habV.2
  have hsub : ψ ⁻¹' (bd S \ Γ.V) ⊆ bd S' \ Γ'.V := fun y hy => by
    refine ⟨?_, ?_⟩
    · rw [hbd]
      exact Or.inl hy.1
    · rw [hV]
      exact hy.2
  apply subset_antisymm
  · have hpre : IsPreconnected (ψ ⁻¹' connectedComponentIn (bd S \ Γ.V) (ψ z)) :=
      GM19.isPreconnected_preimage_of_isCutMap h.isCutMap hFc
        ((connectedComponentIn_subset _ _).trans hoff) isPreconnected_connectedComponentIn
    exact hpre.subset_connectedComponentIn (mem_connectedComponentIn hz)
      ((preimage_mono (connectedComponentIn_subset _ _)).trans hsub)
  · have hzT : z ∈ connectedComponentIn (bd S' \ Γ'.V) z :=
      mem_connectedComponentIn (hsub hz)
    have hTsub : connectedComponentIn (bd S' \ Γ'.V) z ⊆ bd S' \ ψ ⁻¹' Γ.V := by
      rw [← hV]
      exact connectedComponentIn_subset _ _
    have h1 := h.subset_preimage_bd_of_isPreconnected hS hF habV
      isPreconnected_connectedComponentIn hTsub hzT hz.1
    have h2 : IsPreconnected (ψ '' connectedComponentIn (bd S' \ Γ'.V) z) :=
      isPreconnected_connectedComponentIn.image _ h.continuous.continuousOn
    intro y hy
    exact h2.subset_connectedComponentIn (mem_image_of_mem ψ hzT)
      (image_subset_iff.mpr h1) (mem_image_of_mem ψ hy)

/-- **Each space of `Γ` lifts to a space of `Γ'`.** -/
theorem preimage_mem_drawingSpaces (hS : IsSurface S) (hF : IsProperLineInSurface F a b)
    {Γ : Drawing S} (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V)
    {s : Set S} (hs : s ∈ drawingSpaces Γ) : ψ ⁻¹' s ∈ drawingSpaces Γ' := by
  obtain ⟨x, hx, rfl⟩ := hs
  obtain ⟨z, rfl⟩ := h.cutting.2.1 x
  rw [h.preimage_connectedComponentIn hS hF habV hV hx]
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · rw [h.bd_eq hS hF]
    exact Or.inl hx.1
  · rw [hV]
    exact hx.2

/-- **Each space of `Γ'` over `bd(Σ)` is the lift of a space of `Γ`.** -/
theorem exists_eq_preimage_of_mem_drawingSpaces (hS : IsSurface S)
    (hF : IsProperLineInSurface F a b) {Γ : Drawing S} (habV : a ∈ Γ.V ∧ b ∈ Γ.V)
    {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V) {s' : Set S'} (hs' : s' ∈ drawingSpaces Γ')
    {z : S'} (hzs : z ∈ s') (hz : ψ z ∈ bd S) :
    ∃ s ∈ drawingSpaces Γ, s' = ψ ⁻¹' s := by
  obtain ⟨y, hy, rfl⟩ := hs'
  have hzV : ψ z ∉ Γ.V := fun h' => ((connectedComponentIn_subset _ _ hzs).2) (hV ▸ h')
  rw [connectedComponentIn_eq hzs]
  refine ⟨connectedComponentIn (bd S \ Γ.V) (ψ z), ⟨ψ z, ⟨hz, hzV⟩, rfl⟩, ?_⟩
  exact (h.preimage_connectedComponentIn hS hF habV hV ⟨hz, hzV⟩).symm

end IsLineCut

/-! ## Moving ends, supports and betweenness along `ψ` -/

section Image

variable [T2Space S] {Γ : Drawing S} {Γ' : Drawing S'} {K' : Set S'}

/-- The closure of the image of a set in a compact space under a continuous map to a Hausdorff
space is the image of the closure. -/
theorem closure_image_eq [CompactSpace S'] {f : S' → S} (hf : Continuous f) (A : Set S') :
    closure (f '' A) = f '' closure A :=
  subset_antisymm (closure_minimal (image_mono subset_closure)
    (isClosed_closure.isCompact.image hf).isClosed) (image_closure_subset_closure_image hf)

/-- The ends of a space in `K'` move along `ψ`, if `ψ` is one to one on the closed set `K'` and maps
spaces in `K'` to spaces. -/
theorem spaceHasEnds_image [CompactSpace S'] (hψ : Continuous ψ) (hK' : IsClosed K')
    (hinj : InjOn ψ K') (hV : Γ'.V = ψ ⁻¹' Γ.V) (hKbd : ψ '' K' ⊆ bd S) {s' : Set S'}
    (hsK : s' ⊆ K') (hsp : ψ '' s' ∈ drawingSpaces Γ) {u₁ u₂ : S'}
    (hends : SpaceHasEnds Γ' s' u₁ u₂) : SpaceHasEnds Γ (ψ '' s') (ψ u₁) (ψ u₂) := by
  obtain ⟨-, hu₁, hu₂, hne, hline, hcl⟩ := hends
  have hclK : closure s' ⊆ K' := closure_minimal hsK hK'
  have hu₁K : u₁ ∈ K' := hclK (hcl ▸ Or.inr (Or.inl rfl))
  have hu₂K : u₂ ∈ K' := hclK (hcl ▸ Or.inr (Or.inr rfl))
  have hsuK : s' ∪ {u₁, u₂} ⊆ K' := by
    rintro y (hy | rfl | rfl)
    · exact hsK hy
    · exact hu₁K
    · exact hu₂K
  refine ⟨hsp, ⟨?_, hKbd (mem_image_of_mem ψ hu₁K)⟩, ⟨?_, hKbd (mem_image_of_mem ψ hu₂K)⟩,
    fun he => hne (hinj hu₁K hu₂K he), ?_, ?_⟩
  · have := hu₁.1
    rw [hV] at this
    exact this
  · have := hu₂.1
    rw [hV] at this
    exact this
  · have h1 := isLineWithEnds_image_of_injOn hline hψ (hinj.mono hsuK)
    rwa [image_union, image_pair] at h1
  · rw [closure_image_eq hψ, hcl, image_union, image_pair]

/-- A support of `Γ'` in `K'` moves along `ψ` to a support of `Γ`. -/
theorem supportHasEnds_image (hψ : Continuous ψ) (hinj : InjOn ψ K') (hV : Γ'.V = ψ ⁻¹' Γ.V)
    (hKbd : ψ '' K' ⊆ bd S) {I : Set S'} (hIK : I ⊆ K') {u v : S'}
    (hI : SupportHasEnds Γ' I u v) : SupportHasEnds Γ (ψ '' I) (ψ u) (ψ v) := by
  rcases hI with ⟨w, hw, hIw, huw, hvw⟩ | ⟨-, hne, hu, hv, hline⟩
  · left
    refine ⟨ψ w, ⟨?_, hKbd (mem_image_of_mem ψ (hIK (hIw ▸ rfl)))⟩,
      by rw [hIw, image_singleton], by rw [huw], by rw [hvw]⟩
    have := hw.1
    rw [hV] at this
    exact this
  · right
    have huK : u ∈ K' := hIK hline.left_mem
    have hvK : v ∈ K' := hIK hline.right_mem
    refine ⟨(image_mono hIK).trans hKbd, fun he => hne (hinj huK hvK he),
      ⟨?_, hKbd (mem_image_of_mem ψ huK)⟩, ⟨?_, hKbd (mem_image_of_mem ψ hvK)⟩,
      isLineWithEnds_image_of_injOn hline hψ (hinj.mono hIK)⟩
    · have := hu.1
      rw [hV] at this
      exact this
    · have := hv.1
      rw [hV] at this
      exact this

/-- Betweenness in `K'` moves along `ψ`, if `ψ` is one to one on `K'` and maps the spaces in `K'`
to spaces. -/
theorem liesBetweenInSupport_image (hψ : Continuous ψ) (hinj : InjOn ψ K')
    (hV : Γ'.V = ψ ⁻¹' Γ.V) (hKbd : ψ '' K' ⊆ bd S)
    (hsp : ∀ s' ∈ drawingSpaces Γ', s' ⊆ K' → ψ '' s' ∈ drawingSpaces Γ) {s₁ s₂ : Set S'}
    {u : S'} (hb : LiesBetweenInSupport Γ' K' s₁ s₂ u) :
    LiesBetweenInSupport Γ (ψ '' K') (ψ '' s₁) (ψ '' s₂) (ψ u) := by
  obtain ⟨⟨huK, huV⟩, hs₁, hs₂, hs₁K, hs₂K, I₁, I₂, ⟨u₁, v₁, hI₁⟩, ⟨u₂, v₂, hI₂⟩, hun, hint,
    hsI₁, hsI₂⟩ := hb
  have hI₁K : I₁ ⊆ K' := hun ▸ subset_union_left
  have hI₂K : I₂ ⊆ K' := hun ▸ subset_union_right
  refine ⟨⟨mem_image_of_mem ψ huK, ?_⟩, hsp s₁ hs₁ hs₁K, hsp s₂ hs₂ hs₂K, image_mono hs₁K,
    image_mono hs₂K, ψ '' I₁, ψ '' I₂,
    ⟨_, _, supportHasEnds_image hψ hinj hV hKbd hI₁K hI₁⟩,
    ⟨_, _, supportHasEnds_image hψ hinj hV hKbd hI₂K hI₂⟩, by rw [← image_union, hun], ?_,
    image_mono hsI₁, image_mono hsI₂⟩
  · rw [hV] at huV
    exact huV
  · rw [← (hinj.mono (union_subset hI₁K hI₂K)).image_inter subset_union_left
      subset_union_right, hint, image_singleton]

end Image

end CutLine
end GM21
end GraphMinor
