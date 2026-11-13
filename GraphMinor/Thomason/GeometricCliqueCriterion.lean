module

public import GraphMinor.Thomason.GeometricBranchFamily
public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Thomason.GeometricDeletionBound

/-!
# A finite geometric criterion for a clique minor

The degree-sensitive branch induction has numeric conditions at each
stage. A uniform bound over allowed deletion counts removes the
quantifier over remaining orders. The resulting disjoint connected
branches give the clique-minor witness.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Explicit numeric conditions for the geometric branch construction
imply a clique minor. Selection sizes and residual bounds may vary. -/
theorem clique_isIsoMinor_of_geometric_parameters (d D q : ℕ) (k M t : ℕ → ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q,
      0 < k j ∧ selectionBudget k j < d ∧
      M j + selectionBudget k j ≤ Fintype.card V ∧ t j ≤ t (j + 1) ∧
      j * (t j).choose (k j) < (M j).choose (k j) ∧
      Fintype.card V * D ^ k j /
        (Fintype.card V - selectionBudget k j + 1 - M j) ^ k j ≤ t (j + 1)) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  obtain ⟨T, _, hconn, hdis, hadj, _⟩ :=
    exists_geometric_branch_family G d D q k M t hdegree hdeg (fun j hj => by
      obtain ⟨hk, hroom, hM, htmono, hcount, hdecay⟩ := hparam j hj
      refine ⟨hk, hroom, hM, htmono, hcount, ?_⟩
      intro x hx
      exact (geometric_bound_after_deletion_le _ _ _ _ _ _ hx hM).trans hdecay)
  exact clique_isIsoMinor_of_branches G T hconn hdis hadj

end GraphMinor.Thomason
