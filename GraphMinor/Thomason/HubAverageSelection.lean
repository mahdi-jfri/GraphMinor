module

public import GraphMinor.Thomason.HubSelectionCost
public import GraphMinor.Thomason.AverageSubsetSelection
import GraphMinor.Thomason.NonemptyDominationBound
import Lean.Elab.Tactic.Omega

/-!
# Connecting selections obtained by finite averaging

The average uncovered count yields a selected set that avoids all earlier
exceptional families. The central-vertex construction connects this set.
Enlarging the set preserves its uncovered bound and its avoidance properties.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A selection obtained by finite averaging extends to a connected set
with the central-vertex order bound and the same uncovered bound. -/
theorem exists_connected_hubAverageSet_avoiding
    {I : Type v} [DecidableEq I] (S : Finset I) (B : I → Finset V) (t : I → ℕ) (D k T : ℕ)
    (hk : 0 < k)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    (hB : ∀ i ∈ S, (B i).card ≤ t i)
    (hcount : Fintype.card V * D.choose k <
      ((Fintype.card V).choose k - ∑ i ∈ S, (t i).choose k) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ S, (t i).choose k) < (Fintype.card V).choose k)) :
    ∃ X : Finset V, X.card ≤ hubSelectionCost (Fintype.card V) D k ∧
      (G.induce (X : Set V)).Connected ∧
      (undominatedVertices G X).card ≤
        T ∧
      ∀ i ∈ S, ¬ X ⊆ B i := by
  have hex : ∃ Y ∈ (univ : Finset V).powersetCard k,
      (undominatedVertices G Y).card ≤ T ∧ ∀ i ∈ S, ¬ Y ⊆ B i := by
    rcases hcount with hcount | ⟨hDT, hcount⟩
    · exact exists_subset_avoiding_of_average G S B t k D T hdegree hB hcount
    · obtain ⟨Y, hY, havoid⟩ := exists_subset_avoiding_of_count S B t k hB hcount
      have hne : Y.Nonempty := card_pos.mp (by rw [(mem_powersetCard.mp hY).2]; exact hk)
      exact ⟨Y, hY, (card_undominatedVertices_le_of_nonempty G Y hne D hdegree).trans hDT, havoid⟩
  obtain ⟨Y, hY, hYundom, havoid⟩ := hex
  have hYcard := (mem_powersetCard.mp hY).2
  have hYne : Y.Nonempty := card_pos.mp (by omega)
  obtain ⟨X, hYX, hXcard, hconn⟩ := exists_connected_superset_hub G Y hYne D hdegree hnear
  refine ⟨X, ?_, hconn, ?_, ?_⟩
  · simpa only [hYcard] using hXcard
  · apply le_trans (card_le_card ?_) hYundom
    intro x hx
    obtain ⟨hxuniv, hxdom⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hxuniv, fun h => hxdom (dominatedVertices_mono G hYX h)⟩
  · intro i hi hsub
    exact havoid i hi (hYX.trans hsub)

end GraphMinor.Thomason
