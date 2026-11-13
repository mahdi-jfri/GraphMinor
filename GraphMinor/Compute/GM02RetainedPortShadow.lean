module

public import GraphMinor.Compute.GM02FullPortGraphMap
public import GraphMinor.GM02.FeasibilityVertices

/-!
# The actual-vertex shadow of the abstract split graph

On retained vertices, abstract port adjacency already has distinct
endpoints. Thus restricting the path shadow to actual vertices gives
exactly the retained simple graph used in the numeric embedding. This
identity supports both feasibility and width transfer in II (4.6).
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Restricting the abstract split graph to actual vertices gives precisely the retained simple graph. -/
theorem gm02RetainedPortSimpleGraph_eq_shadow (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (assignment : GM02PortAssignment x) (hvalid : gm02PortAssignmentValid x gflags hflags assignment) :
    gm02RetainedPortSimpleGraph x gflags hflags edge assignment hvalid =
      (pathGraph (portGraph (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
        (gm02PortChoiceOfAssignment x gflags hflags edge assignment hvalid))).induce
        (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) := by
  ext a b
  change portAdj _ _ a.val b.val ↔ (_ ∧ a.val ≠ b.val)
  rw [portGraph_adj_iff]
  constructor
  · intro hab
    exact ⟨⟨a.property, b.property, hab⟩, (portSimpleGraph _ _).ne_of_adj hab⟩
  · exact fun h => h.1.2.2

end GraphMinor.Compute
