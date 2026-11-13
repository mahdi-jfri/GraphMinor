module
public import GraphMinor.Thomason.CliqueCriterion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.PositiveGapMinor
import GraphMinor.Minor.Basic
import Mathlib.Tactic.Linarith

/-!
# The class-to-density reduction retaining both neighbourhood centres

Combine the dense-minor reduction, the logarithmic-potential reduction,
and the connected-branch construction. All graph steps are proved here;
the remaining hypotheses are explicit inequalities on numeric parameters.
This follows the reductions and counting argument of Thomason (1984),
Lemma 1 and the main theorem, pp. 262–264.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- The class-to-density reduction of Thomason's Lemma 1 (1984), p. 262.
The hypothesis on the reduced class is the hypothesis printed in that
lemma. Both neighbourhood centres supply the extra two clique vertices. -/
theorem clique_isIsoMinor_of_dense_class {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a r : ℝ) (d q : ℕ)
    (hr : 1 < r) (ha : 1 < a) (halog : 1 + Real.log (2 * a) ≤ a)
    (hd : (d : ℝ) = a * r)
    (hden : d * Fintype.card V ≤ G.edgeFinset.card)
    (hclass : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj], Fintype.card W ≤ d →
      (∀ x, r - 4 < 2 * (J.degree x : ℝ) - (Fintype.card W : ℝ)) →
      IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph J)) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 2)))) (Graph.ofSimpleGraph G) := by
  classical
  have hdposR : 0 < (d : ℝ) := by rw [hd]; exact mul_pos (lt_trans zero_lt_one ha) (lt_trans zero_lt_one hr)
  have hdpos : 0 < d := by exact_mod_cast hdposR
  obtain ⟨W, hW, H, hH, hneH, _, hHsize, hHdegree, hHG⟩ := exists_small_dense_minor_with_clique_extension G d hdpos hden
  let := hW
  let := hH
  let := hneH
  obtain ⟨X, hX, J, hJ, hneJ, _, hJsize, hJdegree, hJH⟩ :=
    exists_minor_with_degree_gap_and_clique_extension H a r d hr ha halog hd hHsize hHdegree
  let := hX
  let := hJ
  let := hneJ
  exact hHG (q + 1) (hJH q (hclass J hJsize hJdegree))

end GraphMinor.Thomason
