module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.ThirteenPotential
import GraphMinor.Thomason.ThirteenCounts

/-!
# The 13-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 10 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 67 forces a 13-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_thirteen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 67 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 13))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 67 10 10 54
    thirteenPotential thirteenRequired thirteenSelection (by decide) (by decide)
    thirteenPotential_monotone thirteenRequired_monotone thirteenPotential_boundary
    thirteenPotential_threshold thirteenPotential_bounds thirteen_degree_certificate hden

end GraphMinor.Thomason
