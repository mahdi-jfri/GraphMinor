module

public import GraphMinor.GM06.Alg34InteriorComponentRep
import GraphMinor.GM06.Section3Basic

/-!
# Feasibility of the computed interior-component deletion

The finite cuff test identifies an actual component disjoint from the
boundary. Apply the proved reduction (3.3)(ii), then transport through
the computed induced drawing representation. This proves that deleting
that component preserves the exact finite input's feasibility answer.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The computed deletion of a cuff-disjoint component preserves
feasibility, exactly as in Graph Minors VI (3.3)(ii). -/
theorem interiorComponentData_feasible_iff (h : GM06DrawingRep x G Δ) (a : Fin x.n)
    (ha : x.isInteriorComponent a = true) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    IsFeasible x.graph x.divisionSet ↔
      IsFeasible (x.interiorComponentData a).graph (x.interiorComponentData a).divisionSet := by
  obtain ⟨hr⟩ := h.interiorComponentData_rep a ha hD hbd
  have heq : IsFeasible G.toGraph Δ ↔
      IsFeasible (induceDrawing G
        (G.V \ (GM06.compOf G.toGraph (h.vertex a).val).vertexSet)).toGraph Δ := by
    rw [induceDrawing_toGraph_deleteVerts]
    exact theorem_3_3_ii G (GM06.compOf G.toGraph (h.vertex a).val) Δ hD hbd
      (isGraphComponent_compOf (show (h.vertex a).val ∈ G.toGraph.vertexSet from (h.vertex a).property))
      ((h.isInteriorComponent_iff a).mp ha)
  exact (h.feasible_iff hD).symm.trans (heq.trans (hr.feasible_iff hD))

end GraphMinor.Compute.GM06DrawingRep
