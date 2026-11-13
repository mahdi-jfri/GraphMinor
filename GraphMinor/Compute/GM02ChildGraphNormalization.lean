module

public import GraphMinor.Compute.GM02FilteredSideGraph

/-!
# Normalizing the actual induced child graphs

Deleting vertices from a vertex-induced side replaces its inducing set
by the surviving vertices. This also holds when separator edges have
already been assigned to the first side. These identities let the child
edge builder use its computed vertex bits directly.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Vertex deletion on an induced side is induction on the surviving set. -/
theorem gm02Induce_deleteVerts {α β : Type*} (G : Graph α β) (S D : Set α) :
    (G.induce S).deleteVerts D = G.induce (S \ D) := by
  apply Graph.ext (by rw [Graph.vertexSet_deleteVerts]; rfl)
  intro e u v
  simp only [Graph.deleteVerts_isLink, Graph.induce_isLink, Set.mem_sdiff]
  tauto

/-- The same normalization preserves the canonical assignment of separator edges. -/
theorem gm02Induce_deleteEdges_deleteVerts {α β : Type*} (G : Graph α β)
    (S D : Set α) (F : Set β) :
    ((G.induce S).deleteEdges F).deleteVerts D = (G.induce (S \ D)).deleteEdges F := by
  apply Graph.ext (by rw [Graph.vertexSet_deleteVerts]; rfl)
  intro e u v
  rw [Graph.deleteVerts_isLink]
  change (((G.induce S).IsLink e u v ∧ e ∉ F) ∧ u ∉ D ∧ v ∉ D) ↔
    ((G.induce (S \ D)).IsLink e u v ∧ e ∉ F)
  simp only [Graph.induce_isLink, Set.mem_sdiff]
  tauto

/-- The path shadow of a first-side child has the filter's empty exclusion set. -/
theorem gm02InducedSimple_pathGraph {n : ℕ} (F : SimpleGraph (Fin n))
    (B : Finset (Fin n)) :
    pathGraph ((Graph.ofSimpleGraph F).induce (B : Set (Fin n))) =
      gm02FilteredSide F ∅ B := by
  have he : E((Graph.ofSimpleGraph F).induce (∅ : Set (Fin n))) = ∅ := by
    ext e
    constructor
    · rintro ⟨u, v, h⟩
      exact h.2.1.elim
    · intro h
      exact h.elim
  have h := gm02FilteredSide_pathGraph F ∅ B
  simpa only [Finset.coe_empty, he, Graph.deleteEdges_empty] using h

end GraphMinor.Compute
