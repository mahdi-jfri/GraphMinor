module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialStarAverageDegreeCertificate
import GraphMinor.Thomason.ThirtySixPotential
import GraphMinor.Thomason.ThirtySixCounts

/-!
# The 36-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 33 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 193 forces a 36-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_thirtySix_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 193 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 36))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_star_average_degree_certificate G 193 33 33 192
    thirtySixPotential thirtySixRequired thirtySixSelection thirtySixCharge thirtySixUncovered thirtySixEdge (by decide) (by decide)
    thirtySixPotential_monotone thirtySixRequired_monotone thirtySixPotential_boundary
    thirtySixPotential_threshold thirtySixPotential_bounds thirtySix_degree_certificate hden

end GraphMinor.Thomason
