module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeCertificate
import GraphMinor.Thomason.TwelvePotential
import GraphMinor.Thomason.TwelveCounts

/-!
# The twelve-vertex density bound

Use the verified integer potential, required-degree table, and branch
selection certificate in the uniform potential reduction. The resulting
clique has the nine selected branches, the final residual branch, and
the two neighbourhood centres.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Every non-null finite simple graph of density at least sixty has
a twelve-vertex clique minor. All finite numeric certificates are proved
by kernel-checked integer computations. -/
theorem clique_twelve_of_density_sixty {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 60 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 12))) (Graph.ofSimpleGraph G) := by
  exact clique_isIsoMinor_of_potential_degree_certificate G 60 9 9 46
    twelvePotential twelveRequired twelveSelection (by decide) (by decide)
    twelvePotential_monotone twelveRequired_monotone twelvePotential_boundary
    twelvePotential_threshold twelvePotential_bounds twelve_degree_certificate hden

end GraphMinor.Thomason
