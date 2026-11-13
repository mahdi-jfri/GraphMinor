module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.NineteenPotential
import GraphMinor.Thomason.NineteenCounts

/-!
# The 19-vertex density bound

The proved potential and degree certificates provide the numeric inputs
to the uniform graph reduction. The 16 selected branches, the residual
branch, and both neighbourhood centres give the complete minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Density 104 forces a 19-vertex clique minor in every non-null finite
simple graph, by the verified integer potential and selection counts. -/
theorem clique_nineteen_of_density {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 104 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 19))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 104 16 16 99
    nineteenPotential nineteenRequired nineteenSelection (by decide) (by decide)
    nineteenPotential_monotone nineteenRequired_monotone nineteenPotential_boundary
    nineteenPotential_threshold nineteenPotential_bounds nineteen_degree_certificate hden

end GraphMinor.Thomason
