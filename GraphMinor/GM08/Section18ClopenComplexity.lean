module

public import GraphMinor.GM08.Section18Complexity
import GraphMinor.GM08.Section18Maximum
import GraphMinor.Surface.CutComp

/-!
# The measure of an open and closed part of a surface

On page 288 of VIII, a graft drawn in a surface `Σ` is split along the
components of `Σ`. Each piece is drawn in an open and closed part `K` of `Σ`.
Here we show that `g(K) ≤ g(Σ)`: every component of `K` is a component of `Σ`,
and `g(Σ)` is the largest value of `g` over the components of `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- In an open and closed set `W`, the component of a point is the preimage of
its component in the whole space. -/
theorem connectedComponent_subtype_eq {S : Type w} [TopologicalSpace S] {W : Set S}
    (hW : IsClopen W) (x : W) :
    connectedComponent x = Subtype.val ⁻¹' connectedComponent (x : S) := by
  have hin : connectedComponentIn W (x : S) = connectedComponent (x : S) := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponent
        (mem_connectedComponentIn x.2)
    · exact isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent
        (hW.connectedComponent_subset x.2)
  rw [← hin, connectedComponentIn_eq_image x.2, Subtype.coe_eta,
    preimage_image_eq _ Subtype.val_injective]

/-- A component of a surface has `g` at most `g(Σ)`. -/
theorem connectedSurfaceComplexity_le_of_mem {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {C : Set S} (hC : C ∈ spaceComponents S) :
    connectedSurfaceComplexity C ≤ surfaceComplexity S :=
  le_csSup ((finite_spaceComponents_of_surface hS).image _).bddAbove ⟨C, hC, rfl⟩

/-- **An open and closed part of a surface has no larger measure.** -/
theorem surfaceComplexity_le_of_isClopen {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {W : Set S} (hW : IsClopen W) :
    surfaceComplexity W ≤ surfaceComplexity S := by
  rcases ((fun C : Set W => connectedSurfaceComplexity C) '' spaceComponents W).eq_empty_or_nonempty
    with h | h
  · rw [surfaceComplexity, h, csSup_empty]
    exact bot_le
  refine csSup_le h ?_
  rintro n ⟨C, hC, rfl⟩
  rw [Surface.spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  have hsub : connectedComponent (x : S) ⊆ W := hW.connectedComponent_subset x.2
  obtain ⟨e⟩ := exists_homeo_sub (connectedComponent (x : S)) hsub
  change connectedSurfaceComplexity (connectedComponent x) ≤ _
  rw [connectedSurfaceComplexity_congr
    ((Homeomorph.setCongr (connectedComponent_subtype_eq hW x)).trans e)]
  exact connectedSurfaceComplexity_le_of_mem hS (by rw [Surface.spaceComponents_eq]; exact ⟨x, rfl⟩)

end GraphMinor.GM08
