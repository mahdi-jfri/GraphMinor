module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialMixedAverageDegreeCertificate
import GraphMinor.Thomason.TwentySevenPotential
import GraphMinor.Thomason.TwentySevenCounts

/-!
# The 27-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 24 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 157 forces a 27-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentySeven_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 157 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 27))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_mixed_average_degree_certificate G 157 24 24 142
    twentySevenPotential twentySevenRequired twentySevenSelection twentySevenCharge twentySevenUncovered twentySevenEdge (by decide) (by decide)
    twentySevenPotential_monotone twentySevenRequired_monotone twentySevenPotential_boundary
    twentySevenPotential_threshold twentySevenPotential_bounds twentySeven_degree_certificate hden

end GraphMinor.Thomason
