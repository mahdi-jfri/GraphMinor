module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.SphereContainment
import GraphMinor.GM05.FlatDiscContainment

/-!
# Disc containment on a connected closed surface

This proves the connected-surface case of GM V, (8.11), with the
whole-sphere exception removed. On the sphere a missed point gives the
container. On other surfaces the maximal flat-set argument gives it.
-/

public section

namespace GraphMinor.GM05

open Set Surface

/-- The connected-surface version of GM V, (8.11), page 113, after
excluding the counterexample where the open set is the whole sphere.
The nonspherical case uses the proved GM VII, (11.2), and the maximal
flat-set construction of GM XI; the spherical case removes one point. -/
theorem lemma_8_11_connected_surface {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {r : Set S} (hr : IsConnected r) (hro : IsOpen r)
    (H : ∀ F : Set S, F ⊆ r → IsOArc F → ∃ D : Set S, IsClosedDisc D ∧ F = discBd D)
    (hex : ¬(IsSphere S ∧ r = univ)) :
    ∃ D : Set S, IsOpenDisc D ∧ r ⊆ D := by
  by_cases hs : IsSphere S
  · exact proper_sphere_set_openDisc_container hS hs (fun he ↦ hex ⟨hs,he⟩)
  · exact nonsphere_openDisc_container hS hs hr hro H

end GraphMinor.GM05
