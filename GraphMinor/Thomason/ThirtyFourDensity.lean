module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialMixedAverageDegreeCertificate
import GraphMinor.Thomason.ThirtyFourPotential
import GraphMinor.Thomason.ThirtyFourCounts

/-!
# The 34-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 31 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 184 forces a 34-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_thirtyFour_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 184 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 34))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_mixed_average_degree_certificate G 184 31 31 183
    thirtyFourPotential thirtyFourRequired thirtyFourSelection thirtyFourCharge thirtyFourUncovered thirtyFourEdge (by decide) (by decide)
    thirtyFourPotential_monotone thirtyFourRequired_monotone thirtyFourPotential_boundary
    thirtyFourPotential_threshold thirtyFourPotential_bounds thirtyFour_degree_certificate hden

end GraphMinor.Thomason
