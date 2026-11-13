module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.FourteenPotential
import GraphMinor.Thomason.FourteenCounts

/-!
# The 14-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 11 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 73 forces a 14-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_fourteen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 73 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 14))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 73 11 11 60
    fourteenPotential fourteenRequired fourteenSelection (by decide) (by decide)
    fourteenPotential_monotone fourteenRequired_monotone fourteenPotential_boundary
    fourteenPotential_threshold fourteenPotential_bounds fourteen_degree_certificate hden

end GraphMinor.Thomason
