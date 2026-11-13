module

public import GraphMinor.Compute.GM02RetainedPortShadow
public import GraphMinor.GM02.PortTermination
import GraphMinor.GM02.FeasibilityEmbedding

/-!
# The terminal pairs and feasibility of the numeric split graph

Transport the abstract split terminals through the actual-vertex subtype
and numeric embedding. Rebase them onto the full numeric vertex set,
which includes unused isolated positions. The image theorem and the
feasibility transfer prove that this is exactly the same path problem.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The abstract split pairs with their finite numeric names. -/
@[expose] noncomputable def gm02FullPortTermination (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    Termination (Set.univ : Set (Fin (gm02FullPortSize x K))) :=
  (((portTermination (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
    (gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)).onVertices).mapEmbedding (gm02PortPositionEmbedding x gflags hflags edge hK)).rebase (Set.subset_univ _)

/-- Numeric naming retains exactly one prescribed pair per active pattern edge. -/
theorem gm02FullPortTermination_index (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    (gm02FullPortTermination x gflags hflags code K hK edge hvalid).index = k := by
  rw [gm02FullPortTermination, Termination.rebase_index]
  exact (Termination.mapEmbedding_index _ _).trans
    ((Termination.onVertices_index _).trans (portTermination_index _ _ _))

/-- Feasibility of the numeric split graph is exactly feasibility of the abstract split graph. -/
theorem gm02FullPortTermination_feasible_iff (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    (gm02FullPortTermination x gflags hflags code K hK edge hvalid).Feasible
      (Graph.ofSimpleGraph (gm02FullPortGraph x gflags hflags code K)) ↔
    (portTermination (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
      (gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)).Feasible
      (portGraph (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
        (gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)) := by
  let A : Termination (Set.univ : Set (portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k)) :=
    (portTermination (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
      (gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)).onVertices
  rw [gm02FullPortTermination, Termination.feasible_rebase_iff,
    gm02FullPortGraph_eq_map x gflags hflags code K hK edge hvalid]
  apply (feasible_mapEmbedding_iff
    (gm02RetainedPortSimpleGraph x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)
    A (gm02PortPositionEmbedding x gflags hflags edge hK)).trans
  rw [gm02RetainedPortSimpleGraph_eq_shadow]
  exact feasible_onVertices_iff _ _

end GraphMinor.Compute
