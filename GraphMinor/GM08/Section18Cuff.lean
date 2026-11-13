module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM08.Section18Circle
import GraphMinor.Surface.MoveCuff
import GraphMinor.Surface.Classification

/-!
# Aligning boundary vertices on one cuff

The orientation-preserving circle matching extends across a collar of the
cuff. Taking the collar away from the other cuffs leaves them fixed. This
is the local boundary alignment used in VIII (18.1), page 285.
-/

public section

namespace GraphMinor.GM08

open Set Function GraphMinor.Surface

universe w

/-- Match finite point sets on a cuff by a homeomorphism supported in an
open neighborhood of the cuff. The cuff itself is preserved. -/
theorem exists_homeomorph_match_cuff_in_open {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {C U A B : Set S} (hC : IsCuff C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hA : A.Finite) (hB : B.Finite) (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hcard : A.ncard = B.ncard) :
    ∃ α : S ≃ₜ S, α '' A = B ∧ α '' C = C ∧ ∀ x ∉ U, α x = x := by
  obtain ⟨φ⟩ := (cuff_statement S hS).2.2 C hC
  let f : Circle → S := fun z => (φ z).1
  have hf : Injective f := fun x y h => φ.injective (Subtype.ext h)
  have hr : range f = C := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (φ t).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩
  have hIA : f '' (f ⁻¹' A) = A := image_preimage_eq_of_subset (hr.symm ▸ hAC)
  have hIB : f '' (f ⁻¹' B) = B := image_preimage_eq_of_subset (hr.symm ▸ hBC)
  have hpreCard : (f ⁻¹' A).ncard = (f ⁻¹' B).ncard := by
    rw [← ncard_image_of_injective (f ⁻¹' A) hf,
      ← ncard_image_of_injective (f ⁻¹' B) hf, hIA, hIB, hcard]
  obtain ⟨τ, hτor, hτ⟩ := exists_circle_homeomorph_image_eq
    (hA.preimage hf.injOn) (hB.preimage hf.injOn) hpreCard
  obtain ⟨α, hα, hfix⟩ := move_cuff S C U φ τ hS hC hU hCU hτor
  have hcomm : (α : S → S) ∘ f = f ∘ τ := funext hα
  refine ⟨α, ?_, ?_, hfix⟩
  · rw [← hIA, ← image_comp, hcomm, image_comp, hτ, hIB]
  · rw [← hr, ← image_univ, ← image_comp, hcomm, image_comp,
      image_univ, τ.surjective.range_eq, image_univ, hr]

/-- The union of all cuffs other than a fixed cuff is closed. -/
theorem isClosed_other_cuffs {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {C : Set S} (hC : IsCuff C) : IsClosed (bd S \ C) := by
  have : T2Space S := hS.2.1
  have heq : bd S \ C = ⋃₀ (cuffs S \ {C}) := by
    ext x
    constructor
    · rintro ⟨hxbd, hxC⟩
      have hD : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hxbd, rfl⟩
      refine ⟨_, ⟨hD, ?_⟩, mem_connectedComponentIn hxbd⟩
      intro heq
      exact hxC (heq ▸ mem_connectedComponentIn hxbd)
    · rintro ⟨D, ⟨hD, hDC⟩, hxD⟩
      have hDsub : D ⊆ bd S := by
        obtain ⟨y, hy, rfl⟩ := hD
        exact connectedComponentIn_subset _ _
      refine ⟨hDsub hxD, ?_⟩
      intro hxC
      exact disjoint_left.mp (cuffs_disjoint hD hC hDC) hxD hxC
  rw [heq]
  apply ((cuff_statement S hS).2.1.subset sdiff_subset).isClosed_sUnion
  intro D hD
  obtain ⟨φ⟩ := (cuff_statement S hS).2.2 D hD.1
  have : CompactSpace D := φ.compactSpace
  exact (isCompact_iff_compactSpace.mpr this).isClosed

/-- Match equal-sized finite subsets of one cuff, while fixing every point
on the other cuffs. This is one step in the alignment for VIII (18.1). -/
theorem exists_homeomorph_match_cuff {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {C A B : Set S} (hC : IsCuff C)
    (hA : A.Finite) (hB : B.Finite) (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hcard : A.ncard = B.ncard) :
    ∃ α : S ≃ₜ S, α '' A = B ∧ α '' C = C ∧ ∀ x ∈ bd S \ C, α x = x := by
  let U := (bd S \ C)ᶜ
  obtain ⟨α, hAB, hCC, hfix⟩ := exists_homeomorph_match_cuff_in_open hS hC
    (isClosed_other_cuffs hS hC).isOpen_compl
    (fun x hx ⟨_, hnC⟩ => hnC hx) hA hB hAC hBC hcard
  exact ⟨α, hAB, hCC, fun x hx => hfix x (by simpa only [U, mem_compl_iff, not_not] using hx)⟩

end GraphMinor.GM08
