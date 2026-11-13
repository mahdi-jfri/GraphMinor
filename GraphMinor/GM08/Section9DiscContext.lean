module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section11Inside
import GraphMinor.GM22.Section3Disc
import GraphMinor.GM07.CuffFrame
import GraphMinor.GM06.DiscRegions
import GraphMinor.Surface.Disc

/-!
# Disc and drawing conditions in VIII (9.3)

A space that is a closed disc is a compact Hausdorff surface with one
cuff, its boundary. A nest contains a circuit and hence an edge. These
facts supply the ambient and nonemptiness conditions when applying the
surface-digraph theorem to abstract graft drawings.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- A closed disc, regarded as the whole ambient space, is a surface.
This supplies the surface hypothesis of VII (9.4) in VIII (9.3). -/
theorem isSurface_of_closedDisc_univ {S : Type u} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) : IsSurface S := by
  obtain ⟨e⟩ := hΔ
  exact GM07.isSurface_of_homeo (e.trans (Homeomorph.Set.univ S))
    GM22.isSurface_closedUnitDisc

/-- The only cuff of a closed disc is its boundary, as used in the
application of VII (9.4) to VIII (9.3), page 270. -/
theorem cuffs_of_closedDisc_univ {S : Type u} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) : cuffs S = {bd S} := by
  obtain ⟨φ⟩ := hΔ.isOArc_discBd
  have hr : range (fun w => (φ w).1) = bd S := by
    rw [← GM06.discBd_univ S]
    ext x
    exact ⟨by rintro ⟨w, rfl⟩; exact (φ w).2,
      fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩⟩
  have hconn : IsConnected (bd S) := by
    rw [← hr]
    exact isConnected_range (continuous_subtype_val.comp φ.continuous)
  change componentsIn (bd S) = {bd S}
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_singleton_iff.mpr (hconn.isPreconnected.connectedComponentIn hx)
  · intro hC
    rw [mem_singleton_iff] at hC
    obtain ⟨x, hx⟩ := hconn.nonempty
    exact ⟨x, hx, (hconn.isPreconnected.connectedComponentIn hx).trans hC.symm⟩

/-- A drawing containing an `O`-arc has an edge. This ensures that the
host edge type is inhabited when the model in VIII (9.3) is transferred
from a surface drawing to the abstract graph. -/
theorem drawing_edges_nonempty_of_oArc {S : Type u} [TopologicalSpace S] [T1Space S]
    {D : Drawing S} {F : Set S} (hF : IsOArc F) (hFD : F ⊆ D.U) : D.E.Nonempty := by
  by_contra hnone
  have hE : D.E = ∅ := not_nonempty_iff_eq_empty.mp hnone
  have hU : D.U = D.V := by rw [D.U_eq, hE]; simp
  exact (GM07.isOArc_infinite_any hF).not_finite
    (D.finite_V.subset (hU ▸ hFD))

end GraphMinor.GM08
