module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialMixedAverageDegreeCertificate
import GraphMinor.Thomason.ThirtyPotential
import GraphMinor.Thomason.ThirtyCounts

/-!
# The 30-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 27 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 178 forces a 30-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_thirty_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 178 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 30))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_mixed_average_degree_certificate G 178 27 27 164
    thirtyPotential thirtyRequired thirtySelection thirtyCharge thirtyUncovered thirtyEdge (by decide) (by decide)
    thirtyPotential_monotone thirtyRequired_monotone thirtyPotential_boundary
    thirtyPotential_threshold thirtyPotential_bounds thirty_degree_certificate hden

end GraphMinor.Thomason
