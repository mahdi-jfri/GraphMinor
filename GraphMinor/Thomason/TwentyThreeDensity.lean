module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialHubAverageDegreeCertificate
import GraphMinor.Thomason.TwentyThreePotential
import GraphMinor.Thomason.TwentyThreeCounts

/-!
# The 23-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 20 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 131 forces a 23-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyThree_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 131 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 23))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_hub_average_degree_certificate G 131 20 20 130
    twentyThreePotential twentyThreeRequired twentyThreeSelection twentyThreeCharge twentyThreeUncovered (by decide) (by decide)
    twentyThreePotential_monotone twentyThreeRequired_monotone twentyThreePotential_boundary
    twentyThreePotential_threshold twentyThreePotential_bounds twentyThree_degree_certificate hden

end GraphMinor.Thomason
