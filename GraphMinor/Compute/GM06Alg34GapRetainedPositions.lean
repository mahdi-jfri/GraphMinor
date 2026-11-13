module

public import GraphMinor.Compute.GM06Alg34GapInducedData
public import GraphMinor.Compute.GM06Alg34GapFilterOrder

/-!
# Old cuff positions of the induced payload

The induced cuff list filters its old vertices and renumbers them
without changing their order. Its positions therefore identify an
increasing sequence of old cuff positions. Reading one selected old
vertex agrees with reading the new label through the active-vertex map.
-/

@[expose] public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- Renumbering does not change the number of retained list entries. -/
theorem gm06RelabelVertexList_length_filter (x : GM06DrawingData)
    (vs L : List (Fin x.n)) :
    (x.relabelVertexList vs L).length = (L.filter (fun v => decide (v ∈ vs))).length := by
  simp only [relabelVertexList, List.length_map, List.length_attach]

/-- The old cuff position paired with a new induced cuff position. -/
def gm06InducedGapPosition (x : GM06DrawingData) (vs L : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs L).length) : Fin L.length :=
  gm06FilterPosition L (fun v => decide (v ∈ vs))
    (Fin.cast (gm06RelabelVertexList_length_filter x vs L) i)

/-- The induced cuff positions occur in increasing old cuff order. -/
theorem gm06InducedGapPosition_strictMono (x : GM06DrawingData) (vs L : List (Fin x.n))
    (hL : L.Nodup) : StrictMono (gm06InducedGapPosition x vs L) := by
  intro i j hij
  apply gm06FilterPosition_strictMono L hL (fun v => decide (v ∈ vs))
  exact hij

/-- The selected old vertex is exactly the old label of the new cuff vertex. -/
theorem gm06InducedGapPosition_get (x : GM06DrawingData) (vs L : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs L).length) :
    L.get (gm06InducedGapPosition x vs L i) =
      (x.activeVertices vs).get ((x.relabelVertexList vs L).get i) := by
  rw [gm06InducedGapPosition, gm06FilterPosition_get]
  have hi : i.val < (L.filter (fun v => decide (v ∈ vs))).length := by
    rw [← gm06RelabelVertexList_length_filter x vs L]
    exact i.isLt
  have hh := congrArg (fun A : List (Fin x.n) => A[i.val]?) (x.map_relabelVertexList vs L)
  rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem hi] at hh
  exact (Option.some.inj hh).symm

end GraphMinor.Compute
