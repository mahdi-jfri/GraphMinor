module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.CutStages
public import GraphMinor.Surface.SurfaceGraph
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18SchismGraph
import GraphMinor.GM08.Section18SchismFrame
import GraphMinor.GM08.Section18CutRegularFibres
import GraphMinor.GM08.Section18SchismBoundary
import GraphMinor.GM08.Section18CutBoundary

/-!
# Schism cuts with regular fibre counts

Choose a finite graph for the schism, marking its boundary contacts.
Its circle and line frame gives a cut whose nonvertex fibres have size
two. The boundary of the cut lies exactly over the old boundary and the
schism. This construction works in any universe and supplies the regular
edge count for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

/-- A schism cut with a finite graph subdivision and two lifts at every
nonvertex point, for the Euler calculation in VIII (18.2), page 286.
The measure decrease is not part of this construction theorem. -/
theorem exists_regular_cut_of_schism {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ (V : Set S) (E : Set (Set S)) (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsGraph V E ∧ gr V E = F ∧ F ∩ bd S ⊆ V ∧
      GM07.IsCutAlongSet F ψ ∧ GM19.IsCutMap ψ F ∧
      ∀ x ∈ F \ V, (ψ ⁻¹' {x}).ncard = 2 := by
  obtain ⟨V, E, hg, hno, hgr, hbd⟩ := exists_graph_of_schism hS hF
  obtain ⟨𝓐, 𝓛, hframe, hcover⟩ := exists_cutFrame_of_schism hS hF
  obtain ⟨Y, tY, ψ, hY, hcut, hregular⟩ :=
    exists_cutMap_of_graph_frame_with_regular_fibres hS hg hno
      (by rwa [hgr]) hframe (by rwa [hgr])
  let := tY
  have hcutF : GM19.IsCutMap ψ F := hgr ▸ hcut
  exact ⟨V, E, Y, tY, ψ, hg, hgr, hbd,
    isCutAlongSet_of_cutMap hS hY (isClosed_of_isSchism hS hF) hcutF,
    hcutF, hgr ▸ hregular⟩

end GraphMinor.GM08
