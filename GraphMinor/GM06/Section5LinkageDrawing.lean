module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5AdjoinedEdges
import GraphMinor.GM06.Section4SubgraphDrawing
import GraphMinor.GM11.Walks

/-!
# The drawing formed by the linkage alone

For the local boundary argument of VI (5.1), page 129, compare the
given drawing with just its linkage paths and the cuffs. The union
of the linkage paths is a subdrawing, with exactly the union vertices
and edges. It is proper and keeps all prescribed cuff vertices.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- The union of the linkage paths forms a proper Section 5 drawing
with exactly their union vertices, edges and point set. -/
theorem exists_linkage_union_drawing
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) :
    ∃ H : Drawing ClosedCylinder, H.IsSubdrawing G ∧
      H.U = ⋃ j : Fin k, (L.pathDrawing j).U ∧
      H.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      H.E = ⋃ j : Fin k, (L.pathDrawing j).E ∧
      IsCylinderSection5Drawing k H ∧
      ∀ j : Fin k, (L.pathDrawing j).IsSubdrawing H := by
  let X := ⋃ j : Fin k, (L.pathDrawing j).V
  let Y := ⋃ j : Fin k, (L.pathDrawing j).E
  let H := G.span X Y
  have hX : X ⊆ G.V := iUnion_subset (fun j => (L.isSubdrawing j).1.1)
  have hY : Y ⊆ G.E := iUnion_subset (fun j => (L.isSubdrawing j).1.2)
  have hHG : H.IsSubdrawing G := Drawing.span_isSubdrawing G X Y
  have hHV : H.V = X := by
    rw [Drawing.span_V, Drawing.spanV, inter_eq_left.mpr hX]
    apply union_eq_left.mpr
    rintro z hz
    obtain ⟨e, ⟨heY, _⟩, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨j, hej⟩ := mem_iUnion.mp heY
    have hzP : z ∈ (L.pathDrawing j).U := (L.pathDrawing j).closure_subset_U hej hz.1
    have hzV : z ∈ (L.pathDrawing j).V := by
      by_contra hn
      obtain ⟨f, hf, hzf⟩ := (L.pathDrawing j).exists_edge_of_mem hzP hn
      exact (((L.isSubdrawing j).1.2 hf).2.1 hzf).2 hz.2
    exact mem_iUnion.mpr ⟨j, hzV⟩
  have hHE : H.E = Y := by
    rw [Drawing.span_E, inter_eq_left.mpr hY]
  have hPH (j : Fin k) : (L.pathDrawing j).IsSubdrawing H := by
    constructor
    · rw [hHV]
      exact subset_iUnion (fun j => (L.pathDrawing j).V) j
    · rw [hHE]
      exact subset_iUnion (fun j => (L.pathDrawing j).E) j
  have hHU : H.U = ⋃ j : Fin k, (L.pathDrawing j).U := by
    apply subset_antisymm
    · rw [H.U_eq, hHV, hHE]
      rintro z (hz | hz)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨j, (L.pathDrawing j).V_subset_U hj⟩
      · obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hz
        obtain ⟨j, hej⟩ := mem_iUnion.mp he
        exact mem_iUnion.mpr ⟨j, (L.pathDrawing j).closure_subset_U hej hz⟩
    · exact iUnion_subset (fun j => (hPH j).U_subset)
  have hproper : H.IsProper := isProper_of_isSubdrawing hG.2.1 hHG
  have hboundary : H.V ∩ bd ClosedCylinder = cylinderM1 k ∪ cylinderM2 k := by
    apply subset_antisymm
    · intro z hz
      rw [← hG.2.2]
      exact ⟨hHG.1 hz.1, hz.2⟩
    · intro z hz
      refine ⟨L.boundary_vertices_subset hPH hz, ?_⟩
      rw [← hG.2.2] at hz
      exact hz.2
  exact ⟨H, hHG, hHU, hHV, hHE, ⟨hG.1, hproper, hboundary⟩, hPH⟩

/-- Adjoining the cuffs to the linkage alone gives the comparison
drawing in the local sector argument of VI (5.1). Its only edges are
linkage edges and cuff edges, and its vertices are the linkage vertices. -/
theorem exists_drawing_of_linkage_and_cuffs
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) :
    ∃ F : Drawing ClosedCylinder,
      F.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder ∧
      F.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      (∀ j : Fin k, (L.pathDrawing j).IsSubdrawing F) ∧
      ∀ e ∈ F.E, (∃ j : Fin k, e ∈ (L.pathDrawing j).E) ∨ e ⊆ bd ClosedCylinder := by
  obtain ⟨H, _, hHU, hHV, hHE, hH, hPH⟩ := exists_linkage_union_drawing L hG
  let M : CylinderLinkage k H := {
    pathDrawing := L.pathDrawing
    curve := L.curve
    isSubdrawing := fun j => ⟨hPH j, (hPH j).U_subset⟩
    isPath := L.isPath
    curve_parametrizes := L.curve_parametrizes
    curve_one_mem := L.curve_one_mem
    pairwise_disjoint := L.pairwise_disjoint }
  obtain ⟨F, hHF, hFU, hFV⟩ := exists_drawing_adjoining_boundary M hH
  refine ⟨F, hHU ▸ hFU, hHV ▸ hFV, fun j => (hPH j).trans hHF, ?_⟩
  intro e he
  rcases edge_mem_or_subset_boundary_of_adjoining hHF hFU hFV he with heH | heBd
  · exact Or.inl (mem_iUnion.mp (hHE ▸ heH))
  · exact Or.inr heBd

end GraphMinor.GM06
