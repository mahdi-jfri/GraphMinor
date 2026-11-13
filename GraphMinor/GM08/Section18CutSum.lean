module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18ClopenComplexity
import GraphMinor.GM08.Section18Invariance
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM07.Section3
import GraphMinor.Surface.CutComp

/-!
# Cutting one part of a surface, and cuts in a row

The cuts of (18.2) for types (iv) and (v) on page 286 are made one arc at a
time. After the first cut the surface may have two components, and the next
arc lies in one of them. So we cut one open and closed part `W` and keep the
rest: the new surface is the cut of `W` next to `Wᶜ` (`isCutting_sum_compl`).
Its measure is the larger of the two measures (`surfaceComplexity_sum_le`).
Two cuts in a row make one cut along the union (`IsCutMap.comp`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- **Cutting one open and closed part.** A cut of `W` along `F ⊆ W`, put next
to the rest of the surface, is a cut of the whole surface along `F`. -/
theorem isCutting_sum_compl {S : Type w} [TopologicalSpace S] {W : Set S}
    {F : Set S} (hFW : F ⊆ W) {Y : Type w} [TopologicalSpace Y] {θ : Y → W}
    (hθ : IsCutting θ (Subtype.val ⁻¹' F)) :
    IsCutting (Sum.elim (Subtype.val ∘ θ) (Subtype.val : (Wᶜ : Set S) → S)) F := by
  set ψ : Y ⊕ (Wᶜ : Set S) → S := Sum.elim (Subtype.val ∘ θ) Subtype.val
  refine ⟨continuous_sum_dom.mpr ⟨continuous_subtype_val.comp hθ.1, continuous_subtype_val⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ W
    · obtain ⟨y, hy⟩ := hθ.2.1 ⟨x, hx⟩
      exact ⟨Sum.inl y, congrArg Subtype.val hy⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  · rintro (y₁ | y₁) hy₁ (y₂ | y₂) hy₂ heq
    · congr 1
      exact hθ.2.2.1 hy₁ hy₂ (Subtype.ext heq)
    · exfalso
      change (θ y₁).1 = y₂.1 at heq
      exact y₂.2 (heq ▸ (θ y₁).2)
    · exfalso
      change y₁.1 = (θ y₂).1 at heq
      exact y₁.2 (heq.symm ▸ (θ y₂).2)
    · congr 1
      exact Subtype.ext heq
  · intro x hx
    have hxW : x ∈ W := hFW hx
    have hpre_eq : ψ ⁻¹' {x} = Sum.inl '' (θ ⁻¹' {⟨x, hxW⟩}) := by
      ext (y | z)
      · simp only [ψ, Sum.elim_inl, Function.comp_apply, mem_preimage, mem_singleton_iff,
          mem_image, Subtype.ext_iff]
        constructor
        · intro h
          exact ⟨y, h, rfl⟩
        · rintro ⟨y', hy', h_eq⟩
          cases h_eq
          exact hy'
      · simp only [ψ, Sum.elim_inr, mem_preimage, mem_singleton_iff, mem_image, reduceCtorEq,
          and_false, exists_false, iff_false]
        intro hzx
        exact z.2 (hzx ▸ hxW)
    rw [hpre_eq, ncard_image_of_injective _ Sum.inl_injective]
    exact hθ.2.2.2.1 ⟨x, hxW⟩ hx
  · rintro (y | z) hy
    · exact GM07.mem_bd_inl (hθ.2.2.2.2 hy)
    · exfalso
      exact z.2 (hFW hy)

/-- A component inside an open and closed part `R` has `g` at most `g(R)`. -/
theorem connectedSurfaceComplexity_le_of_subset_clopen {T : Type w} [TopologicalSpace T]
    (hT : IsSurface T) {R : Set T} (hR : IsClopen R) {x : T} (hx : x ∈ R) :
    connectedSurfaceComplexity (connectedComponent x) ≤ surfaceComplexity R := by
  have hsub : connectedComponent x ⊆ R := hR.connectedComponent_subset hx
  obtain ⟨e⟩ := exists_homeo_sub (connectedComponent x) hsub
  rw [← connectedSurfaceComplexity_congr
    ((Homeomorph.setCongr (connectedComponent_subtype_eq hR ⟨x, hx⟩)).trans e)]
  exact connectedSurfaceComplexity_le_of_mem (isSurface_sub hT hR)
    (by rw [Surface.spaceComponents_eq]; exact ⟨⟨x, hx⟩, rfl⟩)

/-- The measure of a surface is at most the larger measure of the two sides of
an open and closed set. -/
theorem surfaceComplexity_le_max_of_isClopen {T : Type w} [TopologicalSpace T]
    (hT : IsSurface T) {R : Set T} (hR : IsClopen R) :
    surfaceComplexity T ≤ max (surfaceComplexity R) (surfaceComplexity (Rᶜ : Set T)) := by
  rcases ((fun C : Set T => connectedSurfaceComplexity C) '' spaceComponents T).eq_empty_or_nonempty
    with h | h
  · rw [surfaceComplexity, h, csSup_empty]
    exact bot_le
  refine csSup_le h ?_
  rintro n ⟨C, hC, rfl⟩
  rw [Surface.spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  by_cases hx : x ∈ R
  · exact (connectedSurfaceComplexity_le_of_subset_clopen hT hR hx).trans (le_max_left _ _)
  · exact (connectedSurfaceComplexity_le_of_subset_clopen hT hR.compl hx).trans
      (le_max_right _ _)

/-- The measure of a disjoint union is the larger of the two measures. -/
theorem surfaceComplexity_sum_le {A B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    (hA : IsSurface A) (hB : IsSurface B) :
    surfaceComplexity (A ⊕ B) ≤ max (surfaceComplexity A) (surfaceComplexity B) := by
  have hR : IsClopen (range (Sum.inl : A → A ⊕ B)) := ⟨isClosed_range_inl, isOpen_range_inl⟩
  have hRc : (range (Sum.inl : A → A ⊕ B))ᶜ = range Sum.inr := by
    rw [← Set.isCompl_range_inl_range_inr.compl_eq]
  have eA : A ≃ₜ range (Sum.inl : A → A ⊕ B) := IsEmbedding.inl.toHomeomorph
  have eB : B ≃ₜ ((range (Sum.inl : A → A ⊕ B))ᶜ : Set (A ⊕ B)) :=
    IsEmbedding.inr.toHomeomorph.trans (Homeomorph.setCongr hRc.symm)
  have h := surfaceComplexity_le_max_of_isClopen (GM07.isSurface_sum hA hB) hR
  rwa [← surfaceComplexity_congr eA, ← surfaceComplexity_congr eB] at h

/-- **Two cuts in a row.** Cut along `F₁`, and then along a closed set `F₂`
over `G`, which together with the old boundary covers the preimage of `G`. The
result is a cut along `F₁ ∪ G`. -/
theorem IsCutMap.comp {S S₁ S₂ : Type w} [TopologicalSpace S] [TopologicalSpace S₁]
    [TopologicalSpace S₂] [CompactSpace S₂] [T2Space S₁] {ψ₁ : S₁ → S} {ψ₂ : S₂ → S₁}
    {F₁ G : Set S} {F₂ : Set S₁} (h₁ : GM19.IsCutMap ψ₁ F₁) (h₂ : GM19.IsCutMap ψ₂ F₂)
    (hF₂ : IsClosed F₂) (hF₂G : F₂ ⊆ ψ₁ ⁻¹' G) (hG : ψ₁ ⁻¹' G ⊆ F₂ ∪ bd S₁) :
    GM19.IsCutMap (ψ₁ ∘ ψ₂) (F₁ ∪ G) := by
  refine ⟨h₁.1.comp h₂.1, h₁.2.1.comp h₂.2.1, ?_, fun x => ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : ψ₁ (ψ₂ x) ∉ F₁ ∪ G := hx
    have hy' : ψ₁ (ψ₂ y) ∉ F₁ ∪ G := hy
    have h1 : ψ₂ x = ψ₂ y :=
      h₁.2.2.1 (fun h => hx' (Or.inl h)) (fun h => hy' (Or.inl h)) hxy
    exact h₂.2.2.1 (fun h => hx' (Or.inr (hF₂G h))) (fun h => hy' (Or.inr (hF₂G h))) h1
  · have : (ψ₁ ∘ ψ₂) ⁻¹' {x} = ⋃ y ∈ ψ₁ ⁻¹' {x}, ψ₂ ⁻¹' {y} := by
      ext z
      simp
    rw [this]
    exact (h₁.2.2.2.1 x).biUnion fun y _ => h₂.2.2.2.1 y
  · intro x hx
    by_cases hx₂ : ψ₂ x ∈ F₂
    · exact h₂.2.2.2.2 hx₂
    · have hbd : ψ₂ x ∈ bd S₁ := by
        rcases hx with h | h
        · exact h₁.2.2.2.2 h
        · exact (hG h).resolve_left hx₂
      exact bd_lift_cutMap h₂ hF₂ hbd hx₂

end GraphMinor.GM08
