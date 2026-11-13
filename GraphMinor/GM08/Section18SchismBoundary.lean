module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section18SchismCut
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM07.Section8

/-!
# The exact boundary of a schism cut

Each schism is a finite union of circles and lines, hence closed. Its
constructed finite-fibre cut map consequently has new boundary exactly
over the old boundary together with the schism. This supplies the cut
along a set needed to pull drawings back in VIII Section 18.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Every schism is closed. The six cases are circles, proper arcs, or
finite unions of circles and joining lines (VIII Section 18, page 285). -/
theorem isClosed_of_isSchism {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) : IsClosed F := by
  have : T2Space S := hS.2.1
  rcases hF with hi | hii | hiii | hiv | hv | hvi
  · exact (GM07.IsOArc.isSolid hi.1).2
  · obtain ⟨u, v, _, _, hline⟩ := hii.1
    exact (GM07.IsLineWithEnds.isSolid hline).2
  · obtain ⟨u, v, _, _, hline⟩ := hiii.1
    exact (GM07.IsLineWithEnds.isSolid hline).2
  · rcases hiv.1 with hbar | hwedge
    · exact (GM07.IsX1Arc.isSolid_and_isConnected hS hbar).1.2
    · exact (GM07.IsX2Arc.isSolid_and_isConnected hS hwedge).1.2
  · exact (GM07.IsX3Arc.isSolid_and_isConnected hS hv.1).1.2
  · obtain ⟨w, A, P, C, D, u, hA, hP, _, _, rfl, _⟩ := hvi
    exact (GM07.IsOArc.isSolid hA).2.union (GM07.IsLineWithEnds.isSolid hP).2

/-- Every schism has a cut surface whose boundary lies exactly over the
old boundary together with the schism. This is the cut construction in
VIII Section 18, pages 285–286; the measure bound remains separate. -/
theorem exists_cutAlongSet_of_schism {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S), GM07.IsCutAlongSet F ψ := by
  obtain ⟨Y, tY, ψ, hY, hcut⟩ := exists_cutMap_of_schism hS hF
  let := tY
  exact ⟨Y, tY, ψ, isCutAlongSet_of_cutMap hS hY (isClosed_of_isSchism hS hF) hcut⟩

end GraphMinor.GM08
