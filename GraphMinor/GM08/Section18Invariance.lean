module

public import GraphMinor.GM08.Section18Complexity
import GraphMinor.Surface.CutComp

/-!
# Invariance of the surface measure

A homeomorphism sends each connected component onto a connected component.
Its restriction gives a homeomorphism of the component spaces, preserving
their model measures. The maxima defining the general measure therefore
agree. This allows the cut surfaces in VIII (18.2) to be replaced by
homeomorphic models.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

private theorem image_mem_spaceComponents {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T) {C : Set S}
    (hC : C ∈ spaceComponents S) : e '' C ∈ spaceComponents T := by
  rw [spaceComponents_eq] at hC ⊢
  obtain ⟨x, rfl⟩ := hC
  refine ⟨e x, ?_⟩
  simpa only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] using
    (e.image_connectedComponentIn (s := univ) (mem_univ x)).symm

private theorem component_values_subset_of_homeomorph {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T) :
    (fun C : Set S => connectedSurfaceComplexity C) '' spaceComponents S ⊆
      (fun C : Set T => connectedSurfaceComplexity C) '' spaceComponents T := by
  rintro n ⟨C, hC, rfl⟩
  refine ⟨e '' C, image_mem_spaceComponents e hC, ?_⟩
  exact (connectedSurfaceComplexity_congr (e.isEmbedding.homeomorphImage C)).symm

/-- The measure defined in VIII Section 18, page 286, is invariant under
homeomorphisms, also for surfaces with more than one component. -/
theorem surfaceComplexity_congr {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T) :
    surfaceComplexity S = surfaceComplexity T := by
  apply congrArg sSup
  exact Subset.antisymm (component_values_subset_of_homeomorph e)
    (component_values_subset_of_homeomorph e.symm)

end GraphMinor.GM08
