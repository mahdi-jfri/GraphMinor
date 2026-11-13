module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialHubAverageDegreeCertificate
import GraphMinor.Thomason.TwentyFivePotential
import GraphMinor.Thomason.TwentyFiveCounts

/-!
# The 25-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 22 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 144 forces a 25-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyFive_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 144 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 25))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_hub_average_degree_certificate G 144 22 22 143
    twentyFivePotential twentyFiveRequired twentyFiveSelection twentyFiveCharge twentyFiveUncovered (by decide) (by decide)
    twentyFivePotential_monotone twentyFiveRequired_monotone twentyFivePotential_boundary
    twentyFivePotential_threshold twentyFivePotential_bounds twentyFive_degree_certificate hden

end GraphMinor.Thomason
