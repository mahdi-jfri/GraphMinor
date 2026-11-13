module

public import GraphMinor.Planar.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM03.Section2d
import GraphMinor.GM05.ComponentPlanar
import GraphMinor.GM05.ExpansionConnected
import GraphMinor.GM05.GraphComponents
import GraphMinor.GM05.PlanarDiscDrawing
import GraphMinor.GM09.DiscDrawing

/-!
# A graph disjoint from disc-contained regions is planar

This is the proof of GM V, (8.13), page 113. Suppose the graph is not
planar. Then it has a nonplanar component. Its drawing is connected and
misses the other drawing, so it lies in one region. That region lies in
an open disc, so the component is planar, a contradiction.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM06
universe u v

/-- The disc-region implication used in GM V, (8.13), on arbitrary
closed surfaces, including disconnected and empty ones. -/
theorem isPlanar_of_disjoint_disc_regions {α : Type u} {β : Type v}
    {H : Graph α β} {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Γ : GraphDrawing H S) (K : Drawing S)
    (hregions : ∀ r ∈ K.R, ∃ D : Set S, IsOpenDisc D ∧ r ⊆ D)
    (hdis : Disjoint Γ.drawing.U K.U) : GraphMinor.IsPlanar H := by
  classical
  by_contra hnp
  -- "Since H is non-planar, it has a non-planar component H*."
  obtain ⟨Hs,hHs,hnpHs⟩ := exists_nonplanar_component Γ.finite_V hnp
  let : T2Space S := hS.2.1
  let : CompactSpace S := hS.1
  obtain ⟨Γs,-,hUs,-⟩ := GM09.GraphDrawing.ofSubgraph Γ hHs.1
  -- The drawing of H* is connected and misses K, so it lies in one region.
  have hconn : IsGraphConnected Γs.drawing.toGraph :=
    (graphConnected_iff_isGraphConnected _).mp (graphConnected_of_iso Γs.iso
      ((graphConnected_iff_isGraphConnected _).mpr hHs.2.1))
  obtain ⟨⟨x,hx⟩,hpre⟩ := (GM03.isGraphConnected_iff_isPreconnected_U Γs.drawing).mp hconn
  have hxU : x ∈ Γs.drawing.U := Γs.drawing.V_subset_U hx
  have hK : Γs.drawing.U ⊆ univ \ K.U := fun y hy ↦
    ⟨mem_univ _,fun hyK ↦ disjoint_left.mp hdis (hUs hy) hyK⟩
  let r := connectedComponentIn (univ \ K.U) x
  have hr : r ∈ K.R := ⟨x,hK hxU,rfl⟩
  have hUr : Γs.drawing.U ⊆ r := hpre.subset_connectedComponentIn hxU hK
  -- By (8.12) the region lies in an open disc, so H* is planar.
  obtain ⟨D,hD,hrD⟩ := hregions r hr
  let : Nonempty S := ⟨x⟩
  exact hnpHs (isPlanar_of_drawing_in_open_disc Γs hD (hUr.trans hrD))

end GraphMinor.GM05
