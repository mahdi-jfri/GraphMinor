module

public import GraphMinor.Thomason.HubAverageCliqueCriterion
import Lean.Elab.Tactic.Omega

/-!
# Finite degree certificates with central-vertex connection charges

A degree threshold and a list of selection sizes depend only on the
order of the graph. For each order, either the threshold is impossible
or the explicit mixed-selection inequalities construct a clique minor.
The certificate contains numeric inequalities and no graph conclusions.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- A finite numeric certificate for order-dependent degree thresholds
produces a clique minor in every graph meeting the threshold. -/
theorem clique_isIsoMinor_of_finite_hub_average_degree_certificate
    {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q L : ℕ) (r : ℕ → ℕ) (k cost t : ℕ → ℕ → ℕ)
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
    (hN : Fintype.card V ≤ L) (hdegree : ∀ v, r (Fintype.card V) ≤ G.degree v) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  classical
  let N := Fintype.card V
  have hr : r N < N := by
    let v := Classical.arbitrary V
    exact (hdegree v).trans_lt (G.degree_lt_card_verts v)
  rcases hcert N hN with himpossible | ⟨hhalf, hsteps, hfinal, hroom⟩
  · exact (not_le_of_gt hr himpossible).elim
  · let B := 2 * r N - N
    let D := N - r N - 1
    have hnonneighbors : ∀ v, Fintype.card V ≤ G.degree v + D + 1 := by
      intro v
      have hh := hdegree v
      change r N ≤ G.degree v at hh
      dsimp only [D]
      change N ≤ _
      omega
    have hgap : ∀ v, Fintype.card V + B ≤ 2 * G.degree v := by
      intro v
      have hh := hdegree v
      change r N ≤ G.degree v at hh
      dsimp only [B]
      change N + _ ≤ _
      omega
    exact clique_isIsoMinor_of_hub_average_parameters G B D q (k N) (cost N) (t N)
      hnonneighbors hgap hsteps hfinal hroom

end GraphMinor.Thomason
