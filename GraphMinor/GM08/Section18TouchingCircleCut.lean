module

public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18CircleGraph
import GraphMinor.GM08.Section18GraphCut

/-!
# Constructing a cut along a boundary-touching circle

Mark every boundary contact as a vertex in a finite graph representation
of the circle. Its edges are lines and miss the boundary in their
interiors. The proved cut construction for finite drawings therefore
applies, including at contacts with more than two lifts. This constructs
the surface needed for the boundary-touching circle case of VIII (18.2).
The decrease of its measure is a separate assertion.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- A circle with finitely many boundary contacts has a cut surface.
The cutting map allows more than two lifts at boundary contacts, as needed
for type (i) in VIII (18.2), page 286. This theorem constructs the cut;
it does not assert the measure decrease. -/
theorem exists_cutMap_of_oArc_finite_boundary {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {F : Set S} (hF : IsOArc F)
    (hFb : (F ∩ bd S).Finite) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S), IsSurface Y ∧ GM19.IsCutMap ψ F := by
  have : T2Space S := hS.2.1
  obtain ⟨V, E, hg, hno, hgr, hmarks⟩ :=
    exists_graph_oArc_with_finite_marks hF hFb inter_subset_left
  have hframe : GM19.IsCutFrame S (insert F (cuffs S)) ∅ := by
    refine ⟨((cuff_statement S hS).2.1).insert F, finite_empty, ?_, subset_insert _ _, ?_⟩
    · rintro C (rfl | hC)
      · exact hF
      · exact (cuff_statement S hS).2.2 C hC
    · simp
  have hcover : bd S ∪ gr V E = ⋃₀ insert F (cuffs S) ∪ ⋃₀ (∅ : Set (Set S)) := by
    rw [hgr, sUnion_insert, sUnion_cuffs, sUnion_empty, union_empty, union_comm]
  obtain ⟨Y, tY, ψ, hY, hcut⟩ := exists_cutMap_of_graph_frame hS hg hno
    (by rw [hgr]; exact hmarks) hframe hcover
  exact ⟨Y, tY, ψ, hY, hgr ▸ hcut⟩

end GraphMinor.GM08
