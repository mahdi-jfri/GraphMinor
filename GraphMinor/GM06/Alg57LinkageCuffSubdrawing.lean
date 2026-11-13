module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Walks
public import GraphMinor.Surface.Cuffs
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5LinkageDrawing
import GraphMinor.GM06.Section5AdjoinedEdges

/-!
# Restricting the cuffed drawing to the linkage and cuffs

For the local side argument in VI (5.7), page 133, remove all ordinary
edges outside the linkage from the cuffed drawing. Taking a span
keeps its actual edge parametrizations and local charts. Its point
set is exactly the linkage together with both cuffs, and its vertices
are exactly the linkage vertices.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- The comparison drawing made of just the linkage and cuffs can
be chosen as a subdrawing of the supplied cuffed drawing. This is
the local comparison used in Lemma 10 of the proof of VI (5.7). -/
theorem exists_linkage_cuff_subdrawing {k : ℕ} {G F : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V) :
    ∃ H : Drawing ClosedCylinder, H.IsSubdrawing F ∧
      H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder ∧
      H.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      (∀ j : Fin k, (L.pathDrawing j).IsSubdrawing H) ∧
      ∀ e, e ∈ H.E ↔ e ∈ F.E ∧
        ((∃ j : Fin k, e ∈ (L.pathDrawing j).E) ∨ e ⊆ bd ClosedCylinder) := by
  let X := ⋃ j : Fin k, (L.pathDrawing j).V
  let Y := {e | (∃ j : Fin k, e ∈ (L.pathDrawing j).E) ∨ e ⊆ bd ClosedCylinder}
  let H := F.span X Y
  have hXF : X ⊆ F.V := iUnion_subset (fun j => ((L.isSubdrawing j).1.trans hGF).1)
  have hHG : H.IsSubdrawing F := Drawing.span_isSubdrawing F X Y
  have hboundX : G.V ∩ bd ClosedCylinder ⊆ X := by
    rw [hG.2.2]
    rintro z (hz | hz)
    · obtain ⟨j, rfl⟩ := hz
      exact mem_iUnion.mpr ⟨j, (isPathDrawing_end_vertices (L.isPath j)).1⟩
    · obtain ⟨j, rfl⟩ := L.curve_one_surjective hz
      exact mem_iUnion.mpr ⟨j, (isPathDrawing_end_vertices (L.isPath j)).2⟩
  have hVX : H.V = X := by
    rw [Drawing.span_V, Drawing.spanV, inter_eq_left.mpr hXF]
    apply union_eq_left.mpr
    rintro z hz
    obtain ⟨e, ⟨heY, heF⟩, hze, hzF⟩ := mem_iUnion₂.mp hz
    rcases heY with ⟨j, hej⟩ | heBd
    · have hzG : z ∈ G.V := hFV ▸ hzF
      have hzP : z ∈ (L.pathDrawing j).V := by
        have hh := (L.isSubdrawing j).1.closure_inter_V hej
        have hh' : z ∈ closure e ∩ G.V := ⟨hze, hzG⟩
        rw [← hh] at hh'
        exact hh'.2
      exact mem_iUnion.mpr ⟨j, hzP⟩
    · exact hboundX ⟨hFV ▸ hzF, closure_minimal heBd (isClosed_bd _) hze⟩
  have hPH (j : Fin k) : (L.pathDrawing j).IsSubdrawing H := by
    constructor
    · rw [hVX]
      exact subset_iUnion (fun i : Fin k => (L.pathDrawing i).V) j
    · intro e he
      rw [Drawing.span_E]
      exact ⟨Or.inl ⟨j, he⟩, hGF.2 ((L.isSubdrawing j).1.2 he)⟩
  have hHU : H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder := by
    apply subset_antisymm
    · rw [H.U_eq, hVX]
      rintro z (hzV | hzE)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hzV
        exact Or.inl (mem_iUnion.mpr ⟨j, (L.pathDrawing j).V_subset_U hj⟩)
      · obtain ⟨e, heH, hze⟩ := mem_iUnion₂.mp hzE
        obtain ⟨heY, _⟩ := (Drawing.span_E F X Y) ▸ heH
        rcases heY with ⟨j, hej⟩ | heBd
        · exact Or.inl (mem_iUnion.mpr ⟨j, (L.pathDrawing j).closure_subset_U hej hze⟩)
        · exact Or.inr (closure_minimal heBd (isClosed_bd _) hze)
    · rintro z (hzP | hzBd)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hzP
        exact (hPH j).U_subset hj
      · have hzF : z ∈ F.U := hFU.symm ▸ Or.inr hzBd
        by_cases hzV : z ∈ F.V
        · apply H.V_subset_U
          rw [hVX]
          exact hboundX ⟨hFV ▸ hzV, hzBd⟩
        · obtain ⟨e, heF, hze⟩ := F.exists_edge_of_mem hzF hzV
          have heBd : e ⊆ bd ClosedCylinder := by
            rcases edge_mem_or_subset_boundary_of_adjoining hGF hFU hFV heF with heG | heB
            · exfalso
              have hzGV := hG.2.1 ⟨hzBd, G.closure_subset_U heG (subset_closure hze)⟩
              exact (heG.2.1 hze).2 hzGV
            · exact heB
          apply H.closure_subset_U (e := e) _ (subset_closure hze)
          rw [Drawing.span_E]
          exact ⟨Or.inr heBd, heF⟩
  refine ⟨H, hHG, hHU, hVX, hPH, fun e => ?_⟩
  rw [Drawing.span_E]
  exact and_comm

end GraphMinor.GM06
