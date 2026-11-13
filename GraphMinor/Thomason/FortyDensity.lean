module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialStarAverageDegreeCertificate
import GraphMinor.Thomason.FortyPotential
import GraphMinor.Thomason.FortyCounts

/-!
# The 40-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 37 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 222 forces a 40-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_forty_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 222 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 40))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_star_average_degree_certificate G 222 37 37 221
    fortyPotential fortyRequired fortySelection fortyCharge fortyUncovered fortyEdge (by decide) (by decide)
    fortyPotential_monotone fortyRequired_monotone fortyPotential_boundary
    fortyPotential_threshold fortyPotential_bounds forty_degree_certificate hden

end GraphMinor.Thomason
