module

public import GraphMinor.Compute.GM06Alg34RelabelLists

/-!
# Word lists for filtered vertex labels

Filter old labels by the active set and replace each retained label by
its position in the ordered active list. This plain list operation is
the word form of the vertex-list field in the induced drawing payload.
It applies to cuff orders, division blocks, and region boundaries.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Filter and renumber a supplied vertex list as natural RAM words. -/
def gm06RelabelVertexWords (x : GM06DrawingData) (vs L : List (Fin x.n)) : List ℕ :=
  (L.filter (fun v => decide (v ∈ vs))).map (fun v => (x.activeVertices vs).idxOf v)

/-- The finite word operation is exactly the induced payload's relabelled list. -/
theorem gm06RelabelVertexWords_eq (x : GM06DrawingData) (vs L : List (Fin x.n)) :
    gm06RelabelVertexWords x vs L = (x.relabelVertexList vs L).map Fin.val := by
  simp only [gm06RelabelVertexWords, GM06DrawingData.relabelVertexList, List.map_map,
    Function.comp_def, gm06ListIndex]
  exact List.attach_map_val.symm

/-- A supplied head emits one new label exactly when it remains active. -/
theorem gm06RelabelVertexWords_cons (x : GM06DrawingData) (vs : List (Fin x.n))
    (v : Fin x.n) (L : List (Fin x.n)) :
    gm06RelabelVertexWords x vs (v :: L) =
      if v ∈ vs then (x.activeVertices vs).idxOf v :: gm06RelabelVertexWords x vs L
      else gm06RelabelVertexWords x vs L := by
  by_cases hv : v ∈ vs <;> simp [gm06RelabelVertexWords, hv]

/-- Filtering cannot increase a supplied list's reserved capacity. -/
theorem gm06RelabelVertexWords_length_le (x : GM06DrawingData) (vs L : List (Fin x.n)) :
    (gm06RelabelVertexWords x vs L).length ≤ L.length := by
  simp only [gm06RelabelVertexWords, List.length_map]
  exact List.length_filter_le _ _

/-- Every emitted word is a valid new vertex label. -/
theorem gm06RelabelVertexWords_lt (x : GM06DrawingData) (vs L : List (Fin x.n))
    (k : ℕ) (hk : k ∈ gm06RelabelVertexWords x vs L) : k < (x.activeVertices vs).length := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
  have hv' : v ∈ vs := of_decide_eq_true (List.mem_filter.mp hv).2
  exact List.idxOf_lt_length_iff.mpr ((x.mem_activeVertices_iff vs v).mpr hv')

end GraphMinor.Compute
