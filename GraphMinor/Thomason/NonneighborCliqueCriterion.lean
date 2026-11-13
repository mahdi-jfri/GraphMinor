module

public import GraphMinor.Thomason.NonneighborBranchFamily
public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Thomason.RemainingBranch

/-!
# A clique criterion with a final residual branch

Construct the earlier connected branches with varying selection sizes
and a fixed non-neighbour bound. If the final residual graph is large
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
theorem clique_isIsoMinor_of_nonneighbor_parameters (d D q : ℕ) (k : ℕ → ℕ)
    (hd : d ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q, 0 < k j ∧ selectionBudget k j < d ∧
      j * D.choose (k j) < (Fintype.card V - selectionBudget k j).choose (k j))
    (hfinal : selectionBudget k q ≤ d + 1)
    (hroom : D + selectionBudget k q < Fintype.card V) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  obtain ⟨T, hcard, hconn, hdis, hadj, hundom⟩ :=
    exists_nonneighbor_branch_family G d D q k hd hdegree hdeg hparam
  exact clique_isIsoMinor_with_remaining_branch G T d D hdeg hconn hdis hadj
    (hcard.trans hfinal) ((Nat.add_le_add_left hcard D).trans_lt hroom) hundom

end GraphMinor.Thomason
