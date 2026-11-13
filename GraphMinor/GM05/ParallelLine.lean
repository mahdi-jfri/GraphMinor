module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.EdgeLens
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SurfaceGraph

/-!
# A parallel line on an arbitrary closed surface

To choose the drawings in GM V, (8.14), first place parallel edge
curves with common original endpoints. A thin lens around a line
avoids the forbidden closed set except at its ends. One arc of the
lens boundary is the required parallel line. This construction also
works when the closed surface is disconnected.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- A parallel line avoiding a prescribed closed set, for the edge
copy construction in GM V, (8.14), page 113. -/
theorem exists_parallel_line_closed_surface {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) {L Z : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) (huv : u ≠ v) (hZ : IsClosed Z)
    (hLZ : L ∩ Z ⊆ {u,v}) :
    ∃ P : Set S, IsLineWithEnds P u v ∧ P ∩ Z ⊆ {u,v} ∧ P ∩ L = {u,v} := by
  let : T2Space S := hS.2.1
  obtain ⟨D,A,B,hD,hLD,hDZ,hu,hv,hbdL,-⟩ := exists_edge_lens hS hL huv hZ hLZ
  obtain ⟨a,b,hab,ha0,ha1,hcov⟩ := hD.isOArc_discBd.exists_arcs hu hv huv
  have hsub : range a ⊆ discBd D := subset_union_left.trans hcov.subset
  have hPa : IsLineWithEnds (range a) u v := by
    simpa only [ha0,ha1] using hab.arc_left.isLineWithEnds
  refine ⟨range a,hPa,?_,?_⟩
  · exact (inter_subset_inter_left Z (hsub.trans (discBd_subset D))).trans hDZ
  · apply subset_antisymm
    · exact (inter_subset_inter_left L hsub).trans hbdL
    · rintro x (rfl | rfl)
      · exact ⟨hPa.left_mem,hL.left_mem⟩
      · exact ⟨hPa.right_mem,hL.right_mem⟩

end GraphMinor.GM05
