module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialStarAverageDegreeCertificate
import GraphMinor.Thomason.FortySevenPotential
import GraphMinor.Thomason.FortySevenCounts

/-!
# The 47-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 44 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 274 forces a 47-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_fortySeven_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 274 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 47))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_star_average_degree_certificate G 274 44 44 273
    fortySevenPotential fortySevenRequired fortySevenSelection fortySevenCharge fortySevenUncovered fortySevenEdge (by decide) (by decide)
    fortySevenPotential_monotone fortySevenRequired_monotone fortySevenPotential_boundary
    fortySevenPotential_threshold fortySevenPotential_bounds fortySeven_degree_certificate hden

end GraphMinor.Thomason
