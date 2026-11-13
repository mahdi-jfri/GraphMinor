module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.EighteenPotential
import GraphMinor.Thomason.EighteenCounts

/-!
# The 18-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 15 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 98 forces a 18-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_eighteen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 98 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 18))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 98 15 15 92
    eighteenPotential eighteenRequired eighteenSelection (by decide) (by decide)
    eighteenPotential_monotone eighteenRequired_monotone eighteenPotential_boundary
    eighteenPotential_threshold eighteenPotential_bounds eighteen_degree_certificate hden

end GraphMinor.Thomason
