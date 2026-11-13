module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialMixedAverageDegreeCertificate
import GraphMinor.Thomason.TwentyEightPotential
import GraphMinor.Thomason.TwentyEightCounts

/-!
# The 28-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 25 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 164 forces a 28-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyEight_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 164 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 28))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_mixed_average_degree_certificate G 164 25 25 149
    twentyEightPotential twentyEightRequired twentyEightSelection twentyEightCharge twentyEightUncovered twentyEightEdge (by decide) (by decide)
    twentyEightPotential_monotone twentyEightRequired_monotone twentyEightPotential_boundary
    twentyEightPotential_threshold twentyEightPotential_bounds twentyEight_degree_certificate hden

end GraphMinor.Thomason
