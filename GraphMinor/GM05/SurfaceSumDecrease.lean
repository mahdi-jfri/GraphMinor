module

public import GraphMinor.GM05.SurfaceDescent
public import Mathlib.Topology.Constructions.SumProd
import GraphMinor.GM05.GenusReplacement
import GraphMinor.GM05.GenusSumGeneral
public import GraphMinor.GM05.GenusSum

/-!
# Keeping the other surface components unchanged

For GM V, (8.10), a strict genus decrease in the component containing
the circle remains strict after adding back all unchanged components.
The old connected component has a singleton genus list. Every genus
in the replacement is smaller than it, so the replacement lemma for
sorted multisets applies to the genera of the unchanged components.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v w

/-- A decrease in a connected component persists in a disjoint union
with any unchanged closed surface, including the empty surface. -/
theorem surfaceGenusLT_sum_of_connected {U : Type u} [TopologicalSpace U] [ConnectedSpace U]
    {T : Type v} [TopologicalSpace T] {R : Type w} [TopologicalSpace R]
    (hU : IsClosedSurface U) (hT : IsClosedSurface T) (hR : IsClosedSurface R)
    (h : SurfaceGenusLT hT hU) :
    SurfaceGenusLT (isClosedSurface_sum hT hR) (isClosedSurface_sum hU hR) := by
  have hlocal : GenusListLT (surfaceGenusList T hT) [connectedGenus U] := by
    change GenusListLT (surfaceGenusList T hT) (surfaceGenusList U hU) at h
    rwa [surfaceGenusList_of_connected U hU] at h
  have hsum := genusListLT_add_singleton (surfaceGenusList R hR : Multiset ℕ)
    (surfaceGenusList_sorted T hT) hlocal
  change GenusListLT (surfaceGenusList (T ⊕ R) _) (surfaceGenusList (U ⊕ R) _)
  rw [surfaceGenusList_sum hT hR,surfaceGenusList_sum hU hR,surfaceGenusList_of_connected U hU]
  simpa only [add_comm,Multiset.coe_singleton] using hsum

end GraphMinor.GM05
