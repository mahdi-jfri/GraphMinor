module

public import GraphMinor.GM19.CutMap
public import GraphMinor.GM19.PullLift
import GraphMinor.GM08.Section18DiscLift

/-!
# Homeomorphic closures of lifts

A set off the cut has one lift. If it is connected near every point
of its frontier, the closure also has one lift over each of its points.
Compactness turns the resulting continuous bijection into a homeomorphism.
This treats the uncut edges and faces in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

universe w

open Set Topology

/-- A set off a finite-fibre cut lifts homeomorphically after taking
closure, provided it is connected near its frontier. This is the
closure-lifting step for the dissection in VIII (18.2), page 286. -/
theorem exists_homeo_closure_lift_of_cutMap {Y S : Type w} [TopologicalSpace Y]
    [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F A : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (hA : A ⊆ Fᶜ) (hloc : ∀ v ∈ closure A \ A, GM19.IsConnectedNear A v) :
    ∃ H : ↥(closure (ψ ⁻¹' A)) ≃ₜ ↥(closure A),
      ∀ x, (H x).1 = ψ x.1 := by
  have hsur : ψ '' (ψ ⁻¹' A) = A := hcm.2.1.image_preimage A
  have himg : ψ '' closure (ψ ⁻¹' A) = closure A := by
    apply subset_antisymm
    · simpa only [hsur] using image_closure_subset_closure_image (s := ψ ⁻¹' A) hcm.1
    · simpa only [hsur] using (GM19.isClosedMap_of_isCutMap hcm).closure_image_subset (ψ ⁻¹' A)
  have hinj : InjOn ψ (closure (ψ ⁻¹' A)) := by
    intro x hx y hy hxy
    by_cases hxi : ψ x ∈ A
    · exact hcm.2.2.1 (hA hxi) (hA (hxy ▸ hxi)) hxy
    · exact eq_of_mem_closure_preimage_of_cutMap hcm hF hA
        (hloc (ψ x) ⟨himg.subset (mem_image_of_mem ψ hx), hxi⟩) rfl hxy.symm hx hy
  have hbij : Function.Bijective (fun x : ↥(closure (ψ ⁻¹' A)) =>
      (⟨ψ x.1, himg.subset (mem_image_of_mem ψ x.2)⟩ : ↥(closure A))) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx, hψx⟩ := himg.symm.subset hz
      exact ⟨⟨x, hx⟩, Subtype.ext hψx⟩
  have : CompactSpace ↥(closure (ψ ⁻¹' A)) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij)
    ((hcm.1.comp continuous_subtype_val).subtype_mk _), fun _ => rfl⟩

end GraphMinor.GM08
