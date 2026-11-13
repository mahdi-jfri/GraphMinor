module

public import GraphMinor.Thomason.HubAverageSelection
import GraphMinor.Thomason.EdgeSelections
import GraphMinor.Thomason.FamilyAverageSelection
import GraphMinor.Thomason.NonemptyDominationBound
import Lean.Elab.Tactic.Omega

/-!
# Choosing between edge branches and connected larger selections

For a two-vertex selection, an edge is already connected. Its candidate
count follows from the degree sum. For larger selections, finite averaging
and the central-vertex connection bound apply. Both choices retain the
same uncovered-vertex and exceptional-family estimates.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v

/-- A lower bound on the number of candidate selections. -/
def candidateCount (N D k : ℕ) (edge : Bool) : ℕ :=
  if edge then N * (N - D - 1) / 2 else N.choose k

/-- The number of vertices charged to a connected selection. -/
def candidateCost (N D k : ℕ) (edge : Bool) : ℕ :=
  if edge then 2 else hubSelectionCost N D k

/-- More available vertices give at least as many candidates. -/
theorem candidateCount_monotone {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (D k : ℕ) (edge : Bool) :
    candidateCount N₀ D k edge ≤ candidateCount N₁ D k edge := by
  cases edge
  · exact Nat.choose_le_choose k hN
  · exact Nat.div_le_div_right (Nat.mul_le_mul hN
      (Nat.sub_le_sub_right (Nat.sub_le_sub_right hN D) 1))

/-- The connection charge decreases with the available order. -/
theorem candidateCost_antitone_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (hpos : 0 < N₀)
    (D k : ℕ) (edge : Bool) : candidateCost N₁ D k edge ≤ candidateCost N₀ D k edge := by
  cases edge
  · exact hubSelectionCost_antitone_order hN hpos D k
  · exact Nat.le_refl 2

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A connected selection exists with either the edge charge or the
central-vertex charge, under the corresponding finite count bound. -/
theorem exists_connected_average_candidate_avoiding
    {I : Type v} [DecidableEq I] (S : Finset I) (B : I → Finset V) (t : I → ℕ)
    (D k T : ℕ) (edge : Bool) (he : edge = true → k = 2) (hk : 0 < k)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    (hB : ∀ i ∈ S, (B i).card ≤ t i)
    (hcount : Fintype.card V * D.choose k <
      (candidateCount (Fintype.card V) D k edge - ∑ i ∈ S, (t i).choose k) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ S, (t i).choose k) < candidateCount (Fintype.card V) D k edge)) :
    ∃ X : Finset V, X.card ≤ candidateCost (Fintype.card V) D k edge ∧
      (G.induce (X : Set V)).Connected ∧ (undominatedVertices G X).card ≤ T ∧
      ∀ i ∈ S, ¬ X ⊆ B i := by
  cases edge with
  | false =>
    exact exists_connected_hubAverageSet_avoiding G S B t D k T hk hdegree hnear hB hcount
  | true =>
    have hk2 := he rfl
    subst k
    have hmin : ∀ v, Fintype.card V - D - 1 ≤ G.degree v := by
      intro v
      have hh := hdegree v
      omega
    have hM : candidateCount (Fintype.card V) D 2 true ≤ (edgeSelections G).card := by
      have hh := twice_card_edgeSelections G (Fintype.card V - D - 1) hmin
      change Fintype.card V * (Fintype.card V - D - 1) / 2 ≤ _
      omega
    have hbound (Y : Finset V) (hY : Y ∈ edgeSelections G) :
        (undominatedVertices G Y).card ≤ D := by
      have hc := (mem_powersetCard.mp (edgeSelections_subset_powersetCard G hY)).2
      exact card_undominatedVertices_le_of_nonempty G Y (card_pos.mp (by omega)) D hdegree
    obtain ⟨Y, hY, hYT, havoid⟩ := exists_selection_avoiding_in_family G (edgeSelections G)
      S B t 2 (candidateCount (Fintype.card V) D 2 true) (Fintype.card V * D.choose 2) D T
      (edgeSelections_subset_powersetCard G) hM
      (sum_card_undominatedVertices_edgeSelections_le G D hdegree) hbound hB hcount
    exact ⟨Y, ((mem_powersetCard.mp (edgeSelections_subset_powersetCard G hY)).2).le,
      connected_of_mem_edgeSelections G Y hY, hYT, havoid⟩

end GraphMinor.Thomason
