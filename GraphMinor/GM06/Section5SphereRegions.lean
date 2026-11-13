module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM11.SphereRegion
import GraphMinor.Surface.OpenDisc
import GraphMinor.Surface.Cuffs

/-!
# Regions of a connected drawing in a sphere

For the boundary walk in VI (5.1), page 129, the drawing with cuff arcs
adjoined can be viewed in a sphere. Every circle in one of its regions
bounds a disc missing the connected drawing. That disc lies in the
same region. The open-disc theorem then makes each region an open
disc, allowing the region-walk construction.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- A nonempty drawing with a connected point set in a sphere has
open-disc regions. This justifies taking its region-boundary walks. -/
theorem isTwoCell_of_connected_drawing_in_sphere
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (hsph : IsSphere S) {G : Drawing S} (hGU : IsConnected G.U) : G.IsTwoCell := by
  let : T2Space S := hS.2.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine ⟨inferInstance, ?_⟩
  intro r hr
  have hrc : IsConnected r := ⟨region_nonempty hr, region_isPreconnected hr⟩
  have hcircles : ∀ F : Set S, F ⊆ r → IsOArc F →
      ∃ D : Set S, D ⊆ r ∧ IsClosedDisc D ∧ discBd D = F := by
    intro F hFr hF
    have hUF : Disjoint G.U F := disjoint_left.mpr fun x hxU hxF => region_subset hr (hFr hxF) hxU
    obtain ⟨D, hD, hDF, hDU⟩ := exists_disc_missing hS hsph hF hGU.isPreconnected hUF
    obtain ⟨e⟩ := hF
    let x := (e 1).1
    have hxF : x ∈ F := (e 1).2
    have hxD : x ∈ D := Surface.discBd_subset D (hDF.symm ▸ hxF)
    have hDr : D ⊆ r := subset_region hr hD.isPathConnected.isConnected.isPreconnected
      hDU hxD (hFr hxF)
    exact ⟨D, hDr, hD, hDF⟩
  rcases open_disc S r hS inferInstance hrc (region_isOpen hr) hcircles with hwhole | hdisc
  · obtain ⟨x, hx⟩ := hGU.nonempty
    have hxr : x ∈ r := hwhole.2.symm ▸ mem_univ x
    exact False.elim (region_subset hr hxr hx)
  · exact hdisc

end GraphMinor.GM06
