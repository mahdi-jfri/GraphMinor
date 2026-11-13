module

public import GraphMinor.Thomason.HubAverageSelection
import GraphMinor.Thomason.StarSelections
import GraphMinor.Thomason.FamilyAverageSelection
import GraphMinor.Thomason.NonemptyDominationBound
import Lean.Elab.Tactic.Omega

/-!
# Averaged selections with a centre inside or outside the selection

A selection containing a centre is already connected. Count these
candidates by their possible centres. Alternatively use the unrestricted
subset family and add connecting vertices. Both methods preserve the
same uncovered and exceptional-family bounds.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v

/-- A lower bound on the number of candidate selections. -/
def starCandidateCount (N D k : ℕ) (internal : Bool) : ℕ :=
  if internal then N * (N - D - 1).choose (k - 1) / k else N.choose k

/-- The number of vertices charged to a connected selection. -/
def starCandidateCost (N D k : ℕ) (internal : Bool) : ℕ :=
  if internal then k else hubSelectionCost N D k

/-- More available vertices give at least as many candidates. -/
theorem starCandidateCount_monotone {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (D k : ℕ) (internal : Bool) :
    starCandidateCount N₀ D k internal ≤ starCandidateCount N₁ D k internal := by
  cases internal
  · exact Nat.choose_le_choose k hN
  · exact Nat.div_le_div_right (Nat.mul_le_mul hN
      (Nat.choose_le_choose _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hN D) 1)))

/-- The connection charge decreases with the available order. -/
theorem starCandidateCost_antitone_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (hpos : 0 < N₀)
    (D k : ℕ) (internal : Bool) : starCandidateCost N₁ D k internal ≤ starCandidateCost N₀ D k internal := by
  cases internal
  · exact hubSelectionCost_antitone_order hN hpos D k
  · exact Nat.le_refl k

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A connected selection exists with either an internal-centre charge or
the external-centre charge, under the corresponding finite count bound. -/
theorem exists_connected_star_candidate_avoiding
    {I : Type v} [DecidableEq I] (S : Finset I) (B : I → Finset V) (t : I → ℕ)
    (D k T : ℕ) (internal : Bool) (hk : 0 < k)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    (hB : ∀ i ∈ S, (B i).card ≤ t i)
    (hcount : Fintype.card V * D.choose k <
      (starCandidateCount (Fintype.card V) D k internal - ∑ i ∈ S, (t i).choose k) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ S, (t i).choose k) < starCandidateCount (Fintype.card V) D k internal)) :
    ∃ X : Finset V, X.card ≤ starCandidateCost (Fintype.card V) D k internal ∧
      (G.induce (X : Set V)).Connected ∧ (undominatedVertices G X).card ≤ T ∧
      ∀ i ∈ S, ¬ X ⊆ B i := by
  cases internal with
  | false =>
    exact exists_connected_hubAverageSet_avoiding G S B t D k T hk hdegree hnear hB hcount
  | true =>
    have hmin : ∀ v, Fintype.card V - D - 1 ≤ G.degree v := by
      intro v
      have hh := hdegree v
      omega
    have hM : starCandidateCount (Fintype.card V) D k true ≤ (starSelections G k).card :=
      Nat.div_le_of_le_mul (card_starSelections_lower G k (Fintype.card V - D - 1) hk hmin)
    have hbound (Y : Finset V) (hY : Y ∈ starSelections G k) :
        (undominatedVertices G Y).card ≤ D := by
      have hc := (mem_powersetCard.mp (starSelections_subset_powersetCard G k hY)).2
      exact card_undominatedVertices_le_of_nonempty G Y (card_pos.mp (by omega)) D hdegree
    have hsum : (∑ Y ∈ starSelections G k, (undominatedVertices G Y).card) ≤
        Fintype.card V * D.choose k :=
      (sum_le_sum_of_subset_of_nonneg (starSelections_subset_powersetCard G k)
        (fun _ _ _ => Nat.zero_le _)).trans
        (sum_card_undominatedVertices_powersetCard_le G k D hdegree)
    obtain ⟨Y, hY, hYT, havoid⟩ := exists_selection_avoiding_in_family G (starSelections G k)
      S B t k (starCandidateCount (Fintype.card V) D k true) (Fintype.card V * D.choose k) D T
      (starSelections_subset_powersetCard G k) hM hsum hbound hB hcount
    exact ⟨Y, ((mem_powersetCard.mp (starSelections_subset_powersetCard G k hY)).2).le,
      connected_of_mem_starSelections G k Y hY, hYT, havoid⟩

end GraphMinor.Thomason
