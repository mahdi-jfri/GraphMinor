module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialHubAverageDegreeCertificate
import GraphMinor.Thomason.TwentyFourPotential
import GraphMinor.Thomason.TwentyFourCounts

/-!
# The 24-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 21 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 137 forces a 24-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyFour_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 137 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 24))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_hub_average_degree_certificate G 137 21 21 135
    twentyFourPotential twentyFourRequired twentyFourSelection twentyFourCharge twentyFourUncovered (by decide) (by decide)
    twentyFourPotential_monotone twentyFourRequired_monotone twentyFourPotential_boundary
    twentyFourPotential_threshold twentyFourPotential_bounds twentyFour_degree_certificate hden

end GraphMinor.Thomason
