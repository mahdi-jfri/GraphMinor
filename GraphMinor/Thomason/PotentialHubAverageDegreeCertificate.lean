module

public import GraphMinor.Thomason.FiniteHubAverageDegreeCriterion
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.PotentialNeighborhood
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-!
# Density bounds from finite averaged central-vertex degree certificates

The graph argument is uniform: reduce to a small graph of high minimum
degree, minimize an integer edge potential, pass to a neighbourhood,
and construct mixed-size clique branches. The inputs below are only
integer inequalities for the potential and the selected branch sizes.
Both neighbourhood centres and the final residual branch are retained.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- An entirely numeric certificate implies a density-to-clique-minor
bound. It specifies an integer potential and branch selection sizes for
each possible minimal-minor order and neighbourhood order. -/
theorem clique_isIsoMinor_of_potential_hub_average_degree_certificate
    {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d q m L : ℕ) (f r : ℕ → ℕ) (k cost t : ℕ → ℕ → ℕ)
    (hmpos : 0 < m) (hmd : m ≤ d) (hf : Monotone f)
    (hr : Monotone r)
    (hboundary : m.choose 2 < f m)
    (hthreshold : ∀ n, d < n → n ≤ 2 * d → 2 * f n ≤ d * n)
    (hparam : ∀ n, m < n → n ≤ 2 * d → f n ≤ n.choose 2 →
      2 * f n / n ≤ L ∧ r (2 * f n / n) ≤ f n - f (n - 1))
    (hcert : ∀ N, N ≤ L → N ≤ r N ∨
      (N ≤ 2 * r N ∧
       (∀ j < q, 0 < k N j ∧ chargedBudget (cost N) j ≤ 2 * r N - N + 1 ∧
        chargedBudget (cost N) j < N ∧
        hubSelectionCost (N - chargedBudget (cost N) j) (N - r N - 1) (k N j) ≤ cost N j ∧
        t N j ≤ N - r N - 1 ∧
        (N * (N - r N - 1).choose (k N j) <
          ((N - chargedBudget (cost N) j).choose (k N j) -
            ∑ i ∈ range j, (t N i).choose (k N j)) * (t N j + 1) ∨
          (N - r N - 1 ≤ t N j ∧ (∑ i ∈ range j, (t N i).choose (k N j)) <
            (N - chargedBudget (cost N) j).choose (k N j)))) ∧
       chargedBudget (cost N) q ≤ 2 * r N - N + 1 ∧
       N - r N - 1 + chargedBudget (cost N) q < N))
    (hden : d * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 3)))) (Graph.ofSimpleGraph G) := by
  classical
  have hdpos : 0 < d := hmpos.trans_le hmd
  obtain ⟨W, hW, H, hH, hneH, _, hHsize, hHdegree, hHG⟩ :=
    exists_small_dense_minor_with_clique_extension G d hdpos hden
  let := hW
  let := hH
  let := hneH
  have hlarge : d < Fintype.card W := by
    let v := Classical.arbitrary W
    exact (hHdegree v).trans_lt (H.degree_lt_card_verts v)
  have hsum : d * Fintype.card W ≤ 2 * H.edgeFinset.card := by
    calc
      d * Fintype.card W = ∑ _ : W, d := by simp [Nat.mul_comm]
      _ ≤ ∑ v : W, H.degree v := sum_le_sum (fun v _ => hHdegree v)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hthreshold' : f (Fintype.card W) ≤ H.edgeFinset.card := by
    have ht := hthreshold _ hlarge hHsize
    omega
  obtain ⟨n, X, hX, J, hJ, hneJ, hn, hn', he, _, hJsize, hJdegree, hJH⟩ :=
    exists_potential_neighborhood H f hf m hmpos (hmd.trans hlarge.le) hboundary hthreshold'
  let := hX
  let := hJ
  let := hneJ
  obtain ⟨hL, hrequired⟩ := hparam n hn (hn'.trans hHsize) he
  have hdegree : ∀ v, r (Fintype.card X) ≤ J.degree v := by
    intro v
    exact (hr hJsize).trans (hrequired.trans (hJdegree v))
  have hm := clique_isIsoMinor_of_finite_hub_average_degree_certificate J q L r k cost t hcert
    (hJsize.trans hL) hdegree
  exact hHG (q + 2) (hJH (q + 1) hm)

end GraphMinor.Thomason
