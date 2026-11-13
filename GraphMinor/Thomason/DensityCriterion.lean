module
public import GraphMinor.Thomason.CliqueCriterion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.PositiveGapMinor
import GraphMinor.Minor.Basic
import Mathlib.Tactic.Linarith

/-!
# A density criterion for a clique minor

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

/-- A finite-parameter density-to-clique-minor bound. The integer `b`
is a lower bound for the positive degree surplus obtained by the
logarithmic-potential reduction. -/
theorem clique_isIsoMinor_of_density_counting {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a r : ℝ) (d b k q : ℕ)
    (hr : 1 < r) (ha : 1 < a) (halog : 1 + Real.log (2 * a) ≤ a)
    (hd : (d : ℝ) = a * r) (hb : (b : ℝ) ≤ r - 4)
    (hden : d * Fintype.card V ≤ G.edgeFinset.card) (hk : 0 < k)
    (hroom : (q - 1) * (k + 2 * Nat.log 2 k + 1) + (Nat.log 2 k + 3) ≤ b)
    (hcount : (q - 1) * (d / 2 ^ k).choose k <
      (b - (q - 1) * (k + 2 * Nat.log 2 k + 1)).choose k) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  classical
  have hdposR : 0 < (d : ℝ) := by rw [hd]; exact mul_pos (lt_trans zero_lt_one ha) (lt_trans zero_lt_one hr)
  have hdpos : 0 < d := by exact_mod_cast hdposR
  obtain ⟨W, hW, H, hH, hneH, hmHG, hHsize, hHdegree⟩ := exists_small_dense_minor G d hdpos hden
  let := hW
  let := hH
  let := hneH
  obtain ⟨X, hX, J, hJ, hneJ, hmJH, hJsize, hJdegree⟩ :=
    exists_minor_with_degree_gap H a r d hr ha halog hd hHsize hHdegree
  let := hX
  let := hJ
  let := hneJ
  have hsurplus : ∀ x, Fintype.card X + b ≤ 2 * J.degree x := by
    intro x
    have hh := hJdegree x
    have hh' : (Fintype.card X : ℝ) + (b : ℝ) ≤ 2 * (J.degree x : ℝ) := by linarith
    exact_mod_cast hh'
  have hbsize : b ≤ Fintype.card X := by
    let x := Classical.arbitrary X
    have hs := hsurplus x
    have hx := J.degree_lt_card_verts x
    omega
  exact (clique_isIsoMinor_of_counting J b k q d hk hbsize hJsize hsurplus hroom hcount).trans
    (hmJH.trans hmHG)

end GraphMinor.Thomason
