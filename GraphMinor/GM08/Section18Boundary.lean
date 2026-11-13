module

public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section18Cuff
import GraphMinor.Surface.Classification

/-!
# Aligning all boundary vertices

Match the finite boundary sets one cuff at a time. Each move preserves its
cuff and fixes all other cuffs, so it keeps the matches already made. This
provides the boundary alignment for the application of VII (9.1) in VIII
(18.1), page 285.
-/

public section

namespace GraphMinor.GM08

open Set Function GraphMinor.Surface

universe w

/-- Two finite boundary sets with the same number of points on every cuff
are carried to each other by a homeomorphism preserving every cuff. -/
theorem exists_homeomorph_match_boundary {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {A B : Set S} (hA : A.Finite) (hB : B.Finite)
    (hAbd : A ⊆ bd S) (hBbd : B ⊆ bd S)
    (hcard : ∀ C ∈ cuffs S, (A ∩ C).ncard = (B ∩ C).ncard) :
    ∃ α : S ≃ₜ S, α '' A = B ∧ ∀ C ∈ cuffs S, α '' C = C := by
  have hpartial : ∀ 𝓒 : Set (Set S), 𝓒.Finite → 𝓒 ⊆ cuffs S →
      ∃ α : S ≃ₜ S, (∀ C ∈ 𝓒, α '' (A ∩ C) = B ∩ C) ∧
        ∀ C ∈ cuffs S, α '' C = C := by
    intro 𝓒 hfin
    induction 𝓒, hfin using Set.Finite.induction_on with
    | empty =>
      intro _
      exact ⟨Homeomorph.refl S, fun _ h => h.elim, fun C _ => by simp⟩
    | @insert C 𝓒 hCnot hfin ih =>
      intro hsub
      have hCc : C ∈ cuffs S := hsub (mem_insert C 𝓒)
      obtain ⟨α, hα, hαc⟩ := ih (fun D hD => hsub (mem_insert_of_mem C hD))
      have hAC : α '' (A ∩ C) ⊆ C := by
        exact (image_mono (show A ∩ C ⊆ C from inter_subset_right)).trans
          (hαc C hCc).subset
      have hc : (α '' (A ∩ C)).ncard = (B ∩ C).ncard := by
        rw [ncard_image_of_injective _ α.injective, hcard C hCc]
      obtain ⟨β, hβ, hβC, hfix⟩ := exists_homeomorph_match_cuff hS hCc
        ((hA.inter_of_left C).image α) (hB.inter_of_left C) hAC inter_subset_right hc
      have hβD : ∀ D ∈ cuffs S, D ≠ C → ∀ E : Set S, E ⊆ D → β '' E = E := by
        intro D hD hDC E hED
        have hDb : D ⊆ bd S := by
          obtain ⟨x, hx, rfl⟩ := hD
          exact connectedComponentIn_subset _ _
        have hfx : ∀ x ∈ E, β x = x := fun x hx =>
          hfix x ⟨hDb (hED hx), disjoint_left.mp (cuffs_disjoint hD hCc hDC) (hED hx)⟩
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rwa [hfx y hy]
        · intro hx
          exact ⟨x, hx, hfx x hx⟩
      refine ⟨α.trans β, ?_, ?_⟩
      · intro D hD
        change (β ∘ α) '' (A ∩ D) = B ∩ D
        rw [image_comp]
        rcases hD with rfl | hD
        · exact hβ
        · rw [hα D hD]
          exact hβD D (hsub (mem_insert_of_mem C hD))
            (fun hDC => hCnot (hDC ▸ hD)) _ inter_subset_right
      · intro D hD
        change (β ∘ α) '' D = D
        rw [image_comp, hαc D hD]
        by_cases hDC : D = C
        · simpa only [hDC] using hβC
        · exact hβD D hD hDC D Subset.rfl
  obtain ⟨α, hα, hαc⟩ := hpartial (cuffs S) (cuff_statement S hS).2.1 Subset.rfl
  refine ⟨α, ?_, hαc⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    let C := connectedComponentIn (bd S) y
    have hC : C ∈ cuffs S := ⟨y, hAbd hy, rfl⟩
    have hyC : y ∈ C := mem_connectedComponentIn (hAbd hy)
    exact ((hα C hC).subset (mem_image_of_mem α ⟨hy, hyC⟩)).1
  · intro hx
    let C := connectedComponentIn (bd S) x
    have hC : C ∈ cuffs S := ⟨x, hBbd hx, rfl⟩
    have hxC : x ∈ C := mem_connectedComponentIn (hBbd hx)
    obtain ⟨y, hy, heq⟩ := (hα C hC).symm.subset ⟨hx, hxC⟩
    exact ⟨y, hy.1, heq⟩

end GraphMinor.GM08
