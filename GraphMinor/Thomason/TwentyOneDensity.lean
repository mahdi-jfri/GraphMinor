module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.TwentyOnePotential
import GraphMinor.Thomason.TwentyOneCounts

/-!
# The 21-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 18 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 117 forces a 21-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_twentyOne_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 117 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 21))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 117 18 18 116
    twentyOnePotential twentyOneRequired twentyOneSelection (by decide) (by decide)
    twentyOnePotential_monotone twentyOneRequired_monotone twentyOnePotential_boundary
    twentyOnePotential_threshold twentyOnePotential_bounds twentyOne_degree_certificate hden

end GraphMinor.Thomason
