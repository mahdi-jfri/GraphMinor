module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialStarAverageDegreeCertificate
import GraphMinor.Thomason.FortyFourPotential
import GraphMinor.Thomason.FortyFourCounts

/-!
# The 44-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 41 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 252 forces a 44-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_fortyFour_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 252 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 44))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_star_average_degree_certificate G 252 41 41 251
    fortyFourPotential fortyFourRequired fortyFourSelection fortyFourCharge fortyFourUncovered fortyFourEdge (by decide) (by decide)
    fortyFourPotential_monotone fortyFourRequired_monotone fortyFourPotential_boundary
    fortyFourPotential_threshold fortyFourPotential_bounds fortyFour_degree_certificate hden

end GraphMinor.Thomason
