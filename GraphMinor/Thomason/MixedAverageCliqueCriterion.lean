module

public import GraphMinor.Thomason.MixedAverageBranchFamily
public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Thomason.RemainingBranch

/-!
# A clique criterion with central-vertex charges and a final branch

Construct the earlier connected branches with varying selection sizes
and a individual uncovered bounds. If the final residual graph is large
enough and its degree is near half its order, use it as one more branch.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Numeric conditions for mixed-size selections and a final residual
branch give a clique minor of order `q+1`. -/
theorem clique_isIsoMinor_of_mixed_average_parameters (d D q : ℕ) (k cost t : ℕ → ℕ) (edge : ℕ → Bool)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q, (edge j = true → k j = 2) ∧ 0 < k j ∧ chargedBudget cost j ≤ d + 1 ∧
      chargedBudget cost j < Fintype.card V ∧
      candidateCost (Fintype.card V - chargedBudget cost j) D (k j) (edge j) ≤ cost j ∧
      t j ≤ D ∧
      (Fintype.card V * D.choose (k j) <
        (candidateCount (Fintype.card V - chargedBudget cost j) D (k j) (edge j) -
          ∑ i ∈ range j, (t i).choose (k j)) * (t j + 1) ∨
        (D ≤ t j ∧ (∑ i ∈ range j, (t i).choose (k j)) <
          candidateCount (Fintype.card V - chargedBudget cost j) D (k j) (edge j))))
    (hfinal : chargedBudget cost q ≤ d + 1)
    (hroom : D + chargedBudget cost q < Fintype.card V) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  obtain ⟨T, hcard, hconn, hdis, hadj, hundom⟩ :=
    exists_mixed_average_branch_family G d D q k cost t edge hdegree hdeg (by
      intro j hj
      obtain ⟨he, hk, hbudget, hremaining, hcost, _, hcount⟩ := hparam j hj
      exact ⟨he, hk, hbudget, hremaining, hcost, hcount⟩)
  exact clique_isIsoMinor_with_remaining_branch G T d D hdeg hconn hdis hadj
    (hcard.trans hfinal) ((Nat.add_le_add_left hcard D).trans_lt hroom) (fun i => (hundom i).trans (hparam i.val i.isLt).2.2.2.2.2.1)

end GraphMinor.Thomason
