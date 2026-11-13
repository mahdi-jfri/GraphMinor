module
public import GraphMinor.Thomason.CliqueCriterion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GraphMinor.Thomason.CliqueCriterionSharp
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.PositiveGapMinor
import GraphMinor.Minor.Basic
import Mathlib.Tactic.Linarith

/-!
# A density criterion retaining both neighbourhood centres

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

/-- Thomason's Lemma 1 and main construction (1984), pp. 262–264,
with explicit finite numeric conditions. A `K_q` minor in the final
neighbourhood yields a `K_(q+2)` minor in the original graph by retaining
the centres of both neighbourhood reductions. -/
theorem clique_isIsoMinor_of_density_counting_with_centres {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a r : ℝ) (d b k q : ℕ)
    (hr : 1 < r) (ha : 1 < a) (halog : 1 + Real.log (2 * a) ≤ a)
    (hd : (d : ℝ) = a * r) (hb : (b : ℝ) ≤ r - 4)
    (hden : d * Fintype.card V ≤ G.edgeFinset.card) (hk : 0 < k)
    (hroom : (q - 1) * (k + 2 * Nat.log 2 k + 1) + Nat.log 2 k ≤ b)
    (hcount : (q - 1) * (d / 2 ^ k).choose k <
      (b - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 3).choose k) :
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
  have hsurplus : ∀ x, Fintype.card X + b ≤ 2 * J.degree x := by
    intro x
    have hh := hJdegree x
    have hh' : (Fintype.card X : ℝ) + (b : ℝ) ≤ 2 * (J.degree x : ℝ) := by linarith
    exact_mod_cast hh'
  exact hHG (q + 1) (hJH q
    (clique_isIsoMinor_of_counting_exact J b k q d hk hJsize hsurplus hroom hcount))

end GraphMinor.Thomason
