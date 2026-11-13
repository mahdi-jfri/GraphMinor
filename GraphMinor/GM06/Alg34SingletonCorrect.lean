module

public import GraphMinor.GM06.Alg34SingletonRestriction
public import GraphMinor.Compute.GM06Alg34Graph
import GraphMinor.GM06.Section3Basic

/-!
# Feasibility of the computed singleton payload

The payload represents the actual induced drawing. Apply (3.3)(i) to
that drawing, then transport feasibility through the two finite label
bijections. Thus the finite update preserves exactly the answer that
the algorithm must return.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The computed singleton payload has the same feasibility answer as
the old finite payload, by Graph Minors VI (3.3)(i). -/
theorem singletonData_feasible_iff (h : GM06DrawingRep x G Δ) (v : Fin x.n)
    (hD : IsDivision Δ) (hsub : divisionUnion Δ ⊆ G.V) (hv : {(h.vertex v).val} ∈ Δ) :
    IsFeasible x.graph x.divisionSet ↔
      IsFeasible (x.singletonData v).graph (x.singletonData v).divisionSet := by
  obtain ⟨hr⟩ := h.singletonData_rep v hD hsub hv
  have hD' : IsDivision (Δ \ {{(h.vertex v).val}}) :=
    ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1,
      hD.2.2.subset sdiff_subset⟩
  have heq : IsFeasible G.toGraph Δ ↔
      IsFeasible (induceDrawing G (G.V \ {(h.vertex v).val})).toGraph
        (Δ \ {{(h.vertex v).val}}) := by
    rw [induceDrawing_toGraph_deleteVerts G {(h.vertex v).val}]
    exact theorem_3_3_i G.toGraph Δ (h.vertex v).val hD hsub hv
  exact (h.feasible_iff hD).symm.trans (heq.trans (hr.feasible_iff hD'))

end GraphMinor.Compute.GM06DrawingRep
