module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.FifteenPotential
import GraphMinor.Thomason.FifteenCounts

/-!
# The 15-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 12 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 79 forces a 15-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_fifteen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 79 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 15))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 79 12 12 68
    fifteenPotential fifteenRequired fifteenSelection (by decide) (by decide)
    fifteenPotential_monotone fifteenRequired_monotone fifteenPotential_boundary
    fifteenPotential_threshold fifteenPotential_bounds fifteen_degree_certificate hden

end GraphMinor.Thomason
