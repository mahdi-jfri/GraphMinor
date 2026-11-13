module

public import GraphMinor.GM02.IncidenceAugment

/-!
# Deleting a newly attached edge vertex

When an edge vertex has just been added to the augmentation, deleting
it restores the preceding graph exactly. Old edges and the other edge
vertices are unchanged. The equality lets the leaf-bag construction use
the decomposition already built before this insertion.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Deleting a newly added edge vertex restores the previous augmentation. -/
theorem incidenceAugment_delete_vertex {α : Type u} {β : Type v}
    (G : Graph α β) (S : Set β) (e : β) (he : e ∉ S) :
    (incidenceAugment G (insert e S)).deleteVerts {Sum.inr e} = incidenceAugment G S := by
  refine Graph.ext ?_ fun g a b => ?_
  · rw [Graph.vertexSet_deleteVerts]
    change (incidenceAugmentVertices G (insert e S)) \ {Sum.inr e} = incidenceAugmentVertices G S
    ext a
    rcases a with a | f
    · simp [incidenceAugmentVertices]
    · by_cases hfe : f = e
      · subst f; simp [incidenceAugmentVertices, he]
      · simp [incidenceAugmentVertices, hfe]
  · rw [Graph.deleteVerts_isLink, incidenceAugment_isLink_iff, incidenceAugment_isLink_iff]
    rcases a with a | f <;> rcases b with b | h
    · simp [incidenceAugmentVertices, incidenceAugmentAdj]
    · by_cases hhe : h = e
      · subst h; simp [incidenceAugmentVertices, incidenceAugmentAdj, he]
      · simp [incidenceAugmentVertices, incidenceAugmentAdj, hhe]
    · by_cases hfe : f = e
      · subst f; simp [incidenceAugmentVertices, incidenceAugmentAdj, he]
      · simp [incidenceAugmentVertices, incidenceAugmentAdj, hfe]
    · simp [incidenceAugmentVertices, incidenceAugmentAdj]

end GraphMinor.GM02
