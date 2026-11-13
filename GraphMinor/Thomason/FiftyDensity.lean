module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialStarAverageDegreeCertificate
import GraphMinor.Thomason.FiftyPotential
import GraphMinor.Thomason.FiftyCounts

/-!
# The 50-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 47 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 298 forces a 50-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_fifty_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 298 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 50))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_star_average_degree_certificate G 298 47 47 297
    fiftyPotential fiftyRequired fiftySelection fiftyCharge fiftyUncovered fiftyEdge (by decide) (by decide)
    fiftyPotential_monotone fiftyRequired_monotone fiftyPotential_boundary
    fiftyPotential_threshold fiftyPotential_bounds fifty_degree_certificate hden

end GraphMinor.Thomason
