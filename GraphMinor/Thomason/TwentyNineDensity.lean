module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialMixedAverageDegreeCertificate
import GraphMinor.Thomason.TwentyNinePotential
import GraphMinor.Thomason.TwentyNineCounts

/-!
# The 29-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 26 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 171 forces a 29-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyNine_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 171 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 29))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_mixed_average_degree_certificate G 171 26 26 157
    twentyNinePotential twentyNineRequired twentyNineSelection twentyNineCharge twentyNineUncovered twentyNineEdge (by decide) (by decide)
    twentyNinePotential_monotone twentyNineRequired_monotone twentyNinePotential_boundary
    twentyNinePotential_threshold twentyNinePotential_bounds twentyNine_degree_certificate hden

end GraphMinor.Thomason
