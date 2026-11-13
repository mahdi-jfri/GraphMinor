module

public import GraphMinor.Compute.Case3StepsPushGraph
import GraphMinor.Compute.Algorithm99TransportMove

/-!
# The original-label graph of a restored member

Restricting the compact member to its own vertices and then renaming gives
exactly the restored ambient multigraph restricted to the image of those
vertices. This retains isolated member vertices while excluding the added
ambient vertices from the member graph.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- Restoring a member's vertex restriction commutes with the ordered
renaming into the original ambient graph. -/
theorem case3PushMultigraph_relabel_induce {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (T : Finset (Fin S.card)) :
    relabelGraph (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (D.toGMDigraph.toGraph.induce T.toNatSet) =
        (case3PushMultigraph S D).toGMDigraph.toGraph.induce
          (T.image (S.orderEmbOfFin rfl)).toNatSet := by
  rw [relabelGraph_induce, case3PushMultigraph_relabel, ← toNatSet_image_orig]
  have hsub : (T.image (S.orderEmbOfFin rfl)).toNatSet ⊆ S.toNatSet := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨S.orderEmbOfFin rfl v, S.orderEmbOfFin_mem rfl v, rfl⟩
  refine Graph.ext rfl fun e u v => ?_
  change (( _ ∧ u ∈ S.toNatSet ∧ v ∈ S.toNatSet) ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, hsub h.2.1, hsub h.2.2⟩, h.2⟩

end GraphMinor.Compute
