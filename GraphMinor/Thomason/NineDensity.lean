module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.DensityReduction
import GraphMinor.Thomason.NumericConstant
import GraphMinor.Thomason.NineParameters
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The nine-vertex density case

At density forty-two, Thomason's two neighbourhood reductions produce
a graph of order at most forty-two with degree surplus at least eleven.
The proved mixed-selection construction gives a seven-vertex clique
minor there. The two neighbourhood centres yield a nine-vertex clique
minor in the original graph.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Every non-null finite simple graph of density at least forty-two
has a nine-vertex clique minor. -/
theorem clique_nine_of_density_forty_two {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 42 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 9))) (Graph.ofSimpleGraph G) := by
  let a : ℝ := 2679 / 1000
  let r : ℝ := 42000 / 2679
  apply clique_isIsoMinor_of_dense_class G a r 42 7 (by norm_num [r]) (by norm_num [a])
    logarithmic_reduction_constant (by norm_num [a, r]) hden
  intro W _ _ J _ hsize hgap
  apply clique_seven_of_order_le_forty_two J hsize
  intro v
  have hh := hgap v
  have hr : (11 : ℝ) ≤ r - 4 := by norm_num [r]
  have hd : (Fintype.card W : ℝ) + 11 ≤ 2 * (J.degree v : ℝ) := by linarith only [hh, hr]
  exact_mod_cast hd

end GraphMinor.Thomason
