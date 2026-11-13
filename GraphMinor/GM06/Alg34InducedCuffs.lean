module

public import GraphMinor.GM06.Alg34InducedListImages
import GraphMinor.Compute.GM06Alg34InducedOrder

/-!
# Cuff representation after vertex deletion

The old surface cuffs remain the same. The computed cuff lists denote
exactly the surviving boundary vertices, contain no repetitions, and
preserve all geometric crossings through the new vertex labels. These
are the three cuff conditions of the updated drawing representation.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- A computed cuff list denotes exactly the induced drawing's vertices
on the original actual cuff. -/
theorem induced_cuff_vertices (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (i : Fin x.cuffs.length) :
    (fun v => (h.inducedVertex vs v).val) ''
        GM06DrawingData.block (x.relabelVertexList vs x.cuffs[i]) =
      (induceDrawing G (h.vertexImage vs)).V ∩ (h.cuff i).val := by
  rw [h.image_relabelVertexList vs _, h.cuff_vertices i,
    induceDrawing_V G (h.vertexImage_subset vs)]
  ext p
  constructor
  · exact fun hp => ⟨hp.2, hp.1.2⟩
  · exact fun hp => ⟨⟨h.vertexImage_subset vs hp.1, hp.2⟩, hp.1⟩

/-- Every computed cuff list contains no repeated new vertex label. -/
theorem induced_cuff_nodup (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    ∀ L ∈ (x.inducedData vs).cuffs, L.Nodup := by
  intro L hL
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hL
  exact x.relabelVertexList_nodup vs M (h.cuff_nodup M hM)

/-- The computed induced data has exactly the geometric crossing order
of the surviving vertices under its new vertex labels. -/
theorem induced_crossing_order (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (a c b d : Fin (x.activeVertices vs).length) :
    (x.inducedData vs).crosses a c b d = true ↔
      ∃ C ∈ Surface.cuffs S, CrossesOn C (h.inducedVertex vs a).val (h.inducedVertex vs c).val
        (h.inducedVertex vs b).val (h.inducedVertex vs d).val := by
  rw [x.inducedData_crosses vs h.cuff_nodup]
  exact h.order _ _ _ _

end GraphMinor.Compute.GM06DrawingRep
