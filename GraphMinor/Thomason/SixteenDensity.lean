module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.SixteenPotential
import GraphMinor.Thomason.SixteenCounts

/-!
# The 16-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 13 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 85 forces a 16-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_sixteen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 85 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 16))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 85 13 13 76
    sixteenPotential sixteenRequired sixteenSelection (by decide) (by decide)
    sixteenPotential_monotone sixteenRequired_monotone sixteenPotential_boundary
    sixteenPotential_threshold sixteenPotential_bounds sixteen_degree_certificate hden

end GraphMinor.Thomason
