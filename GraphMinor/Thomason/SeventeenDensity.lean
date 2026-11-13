module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.SeventeenPotential
import GraphMinor.Thomason.SeventeenCounts

/-!
# The 17-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 14 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 92 forces a 17-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_seventeen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 92 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 17))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 92 14 14 84
    seventeenPotential seventeenRequired seventeenSelection (by decide) (by decide)
    seventeenPotential_monotone seventeenRequired_monotone seventeenPotential_boundary
    seventeenPotential_threshold seventeenPotential_bounds seventeen_degree_certificate hden

end GraphMinor.Thomason
