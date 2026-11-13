module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.TwentyPotential
import GraphMinor.Thomason.TwentyCounts

/-!
# The 20-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 17 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 111 forces a 20-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twenty_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 111 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 20))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 111 17 17 108
    twentyPotential twentyRequired twentySelection (by decide) (by decide)
    twentyPotential_monotone twentyRequired_monotone twentyPotential_boundary
    twentyPotential_threshold twentyPotential_bounds twenty_degree_certificate hden

end GraphMinor.Thomason
