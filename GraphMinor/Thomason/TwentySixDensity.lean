module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialMixedAverageDegreeCertificate
import GraphMinor.Thomason.TwentySixPotential
import GraphMinor.Thomason.TwentySixCounts

/-!
# The 26-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 23 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 151 forces a 26-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentySix_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 151 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 26))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_mixed_average_degree_certificate G 151 23 23 135
    twentySixPotential twentySixRequired twentySixSelection twentySixCharge twentySixUncovered twentySixEdge (by decide) (by decide)
    twentySixPotential_monotone twentySixRequired_monotone twentySixPotential_boundary
    twentySixPotential_threshold twentySixPotential_bounds twentySix_degree_certificate hden

end GraphMinor.Thomason
