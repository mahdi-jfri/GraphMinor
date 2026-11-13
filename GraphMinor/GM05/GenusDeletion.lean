module

public import GraphMinor.GM05.SurfaceGenus
public import GraphMinor.GM05.GenusListOrder
import GraphMinor.GM05.ClopenComplement
import GraphMinor.GM05.GenusSumGeneral
import GraphMinor.GM05.GenusSum
import GraphMinor.GM05.GenusHomeomorph

/-!
# Deleting an unused component decreases the genus multiset

The strict list order in GM V leaves prefixes incomparable. To choose
its minimal drawing surface without unused components, minimize instead
the well-founded multiset order already used to prove (8.9). Removing
one component deletes one genus entry, including a zero entry.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface
universe u

/-- Removing a connected clopen part deletes one entry of the component
genus multiset, and is a strict decrease in the multiset order. -/
theorem genus_multiset_delete_component {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) {U : Set S} (hU : IsClopen U) [ConnectedSpace U]
    (hUc : IsClosedSurface U) (hR : IsClosedSurface ↥(Uᶜ)) :
    Multiset.IsDershowitzMannaLT (surfaceGenusList ↥(Uᶜ) hR : Multiset ℕ)
      (surfaceGenusList S hS : Multiset ℕ) := by
  obtain ⟨e⟩ := clopen_sum_homeomorph hU
  have he : (surfaceGenusList S hS : Multiset ℕ) =
      {connectedGenus U} + (surfaceGenusList ↥(Uᶜ) hR : Multiset ℕ) := by
    rw [← surfaceGenusList_homeo e (isClosedSurface_sum hUc hR) hS,
      surfaceGenusList_sum hUc hR,surfaceGenusList_of_connected U hUc,Multiset.sort_eq]
    rfl
  refine ⟨(surfaceGenusList ↥(Uᶜ) hR : Multiset ℕ),0,{connectedGenus U},by simp,by simp,?_,by simp⟩
  simpa only [add_comm] using he

end GraphMinor.GM05
