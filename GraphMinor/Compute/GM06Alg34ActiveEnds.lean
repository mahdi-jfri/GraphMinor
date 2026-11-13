module

public import GraphMinor.Compute.GM06Alg34RelabelLists

/-!
# Endpoint correctness for the finite deletion payload

The computed surviving endpoint list uses list indices as new vertex
labels. Reading those indices through the active vertex list recovers
both original ends of each surviving edge. These identities verify the
endpoint field of the updated drawing representation.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The first new endpoint label denotes the first original endpoint. -/
theorem activeEnds_fst (x : GM06DrawingData) (vs : List (Fin x.n))
    (i : Fin (x.activeEdges vs).length) :
    (x.activeVertices vs).get
      ((x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)).1 = x.ends[(x.activeEdges vs).get i].1 := by
  simp only [activeEnds, List.getElem_ofFn, gm06ListIndex_get]

/-- The second new endpoint label denotes the second original endpoint. -/
theorem activeEnds_snd (x : GM06DrawingData) (vs : List (Fin x.n))
    (i : Fin (x.activeEdges vs).length) :
    (x.activeVertices vs).get
      ((x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)).2 = x.ends[(x.activeEdges vs).get i].2 := by
  simp only [activeEnds, List.getElem_ofFn, gm06ListIndex_get]

end GraphMinor.Compute.GM06DrawingData
