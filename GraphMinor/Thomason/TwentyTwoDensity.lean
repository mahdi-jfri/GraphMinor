module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialHubDegreeCertificate
import GraphMinor.Thomason.TwentyTwoPotential
import GraphMinor.Thomason.TwentyTwoCounts

/-!
# The 22-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 19 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 124 forces a 22-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyTwo_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 124 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 22))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_hub_degree_certificate G 124 19 19 122
    twentyTwoPotential twentyTwoRequired twentyTwoSelection twentyTwoCharge (by decide) (by decide)
    twentyTwoPotential_monotone twentyTwoRequired_monotone twentyTwoPotential_boundary
    twentyTwoPotential_threshold twentyTwoPotential_bounds twentyTwo_degree_certificate hden

end GraphMinor.Thomason
