module

public import GraphMinor.Thomason.ConnectedDominators
import GraphMinor.Thomason.HubConnection
import Lean.Elab.Tactic.Omega

/-!
# Integer connection costs using a central vertex

This is the integer form of the costs in Wood (2026),
arXiv:2610.41060v1, Lemma 6, p. 5. A singleton needs no extra vertex.
For larger selections, the central-vertex argument adds at most one
plus the selected size times the non-neighbour proportion, rounded down.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset

/-- The order bound for connecting a selection in a graph of order `N`
with non-neighbour bound `D`, as in Wood's Lemma 6. -/
def hubSelectionCost (N D k : ℕ) : ℕ :=
  if k = 1 then 1 else k + 1 + k * D / N

/-- Enlarging the available graph order decreases the connection cost
when the non-neighbour bound and selection size stay fixed. -/
theorem hubSelectionCost_antitone_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (hpos : 0 < N₀)
    (D k : ℕ) : hubSelectionCost N₁ D k ≤ hubSelectionCost N₀ D k := by
  by_cases hk : k = 1
  · simp only [hubSelectionCost, hk, ite_true, le_refl]
  · simp only [hubSelectionCost, hk, ite_false]
    have hdiv : k * D / N₁ ≤ k * D / N₀ := by
      apply (Nat.le_div_iff_mul_le hpos).mpr
      exact (Nat.mul_le_mul_left (k * D / N₁) hN).trans (Nat.div_mul_le_self _ _)
    omega

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every nonempty selected set extends to a connected set with the
central-vertex order bound. This includes the exact singleton case. -/
theorem exists_connected_superset_hub (Y : Finset V) (hne : Y.Nonempty) (D : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1) :
    ∃ X : Finset V, Y ⊆ X ∧ X.card ≤ hubSelectionCost (Fintype.card V) D Y.card ∧
      (G.induce (X : Set V)).Connected := by
  by_cases hY : Y.card = 1
  · obtain ⟨y, hy⟩ := card_eq_one.mp hY
    refine ⟨Y, subset_refl _, ?_, ?_⟩
    · simp only [hubSelectionCost, hY, ite_true, le_refl]
    · have heq : (Y : Set V) = {y} := by rw [hy]; ext x; simp
      rw [heq]
      exact (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := y)).induce_verts
  · obtain ⟨Z, hZ, hconn⟩ := exists_hub_connecting_set G Y hne D hdegree hnear
    refine ⟨Y ∪ Z, subset_union_left, ?_, hconn⟩
    have hc := card_union_le Y Z
    simp only [hubSelectionCost, hY, ite_false]
    omega

end GraphMinor.Thomason
