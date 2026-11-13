module

public import GraphMinor.GM08.Section18Complexity
import GraphMinor.Surface.CutComp
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The maximum over surface components

A compact surface is locally connected, so it has finitely many connected
components. Its measure from VIII Section 18 is therefore an attained
maximum when the surface is nonempty. Bounds on this measure can be checked
component by component, as in the final step of (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- A surface has finitely many connected components. -/
theorem finite_spaceComponents_of_surface {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) : (spaceComponents S).Finite := by
  let := hS.1
  let := hS.locallyConnected
  have heq : spaceComponents S =
      range (fun q : ConnectedComponents S => (ConnectedComponents.mk : S → ConnectedComponents S) ⁻¹' {q}) := by
    rw [spaceComponents_eq]
    ext C
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ConnectedComponents.mk x, connectedComponents_preimage_singleton⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
      exact ⟨x, connectedComponents_preimage_singleton.symm⟩
  rw [heq]
  exact finite_range _

private theorem component_values_nonempty {S : Type w} [TopologicalSpace S] [Nonempty S] :
    ((fun C : Set S => connectedSurfaceComplexity C) '' spaceComponents S).Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  exact ⟨_, _, ⟨x, mem_univ x, rfl⟩, rfl⟩

/-- The maximum in the definition on page 286 is attained at a component
of every nonempty surface. -/
theorem exists_component_surfaceComplexity_eq {S : Type w} [TopologicalSpace S]
    [Nonempty S] (hS : IsSurface S) :
    ∃ C ∈ spaceComponents S, connectedSurfaceComplexity C = surfaceComplexity S := by
  exact component_values_nonempty.csSup_mem
    ((finite_spaceComponents_of_surface hS).image _)

/-- The surface measure is at most a bound exactly when every component
measure is at most that bound. -/
theorem surfaceComplexity_le_iff {S : Type w} [TopologicalSpace S] [Nonempty S]
    (hS : IsSurface S) (n : ℕ) :
    surfaceComplexity S ≤ n ↔ ∀ C ∈ spaceComponents S, connectedSurfaceComplexity C ≤ n := by
  have hfin := (finite_spaceComponents_of_surface hS).image
    (fun C : Set S => connectedSurfaceComplexity C)
  constructor
  · intro h C hC
    exact (le_csSup hfin.bddAbove (mem_image_of_mem _ hC)).trans h
  · intro h
    exact csSup_le component_values_nonempty (by rintro _ ⟨C, hC, rfl⟩; exact h C hC)

/-- The strict componentwise bound used at the end of VIII (18.2), page 286. -/
theorem surfaceComplexity_lt_iff {S : Type w} [TopologicalSpace S] [Nonempty S]
    (hS : IsSurface S) (n : ℕ) :
    surfaceComplexity S < n ↔ ∀ C ∈ spaceComponents S, connectedSurfaceComplexity C < n := by
  exact ((finite_spaceComponents_of_surface hS).image _).csSup_lt_iff
    component_values_nonempty |>.trans (by simp only [forall_mem_image])

end GraphMinor.GM08
