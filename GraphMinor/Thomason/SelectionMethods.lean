module

public import GraphMinor.Thomason.StarAverageSelection
public import GraphMinor.Thomason.OneMissedSelection

/-!
# Numeric bounds for three proved selection methods

A branch can be formed from an unrestricted subset with an external
centre, a subset containing its centre, or a rooted sequence with one
missed adjacency. Keep the candidate counts, exceptional counts, total
uncovered bounds, and connection charges separate, since the sequence
method counts ordered samples rather than subsets.
-/

@[expose] public section
namespace GraphMinor.Thomason

/-- The choice of candidate family and connection construction. -/
inductive SelectionMethod
  | hub
  | star
  | oneMissed
  deriving DecidableEq

/-- A lower bound on the size of a candidate family. -/
def selectionCount (N D k : ℕ) : SelectionMethod → ℕ
  | .hub => N.choose k
  | .star => starCandidateCount N D k true
  | .oneMissed => rootedOneMissedCount N D (k - 1)

/-- The order charged to a connected selection. -/
def selectionCost (N D k : ℕ) : SelectionMethod → ℕ
  | .hub => hubSelectionCost N D k
  | .star => k
  | .oneMissed => k + 1

/-- The number of candidate samples inside an exceptional set of size `t`. -/
def selectionExceptionBound (t k : ℕ) : SelectionMethod → ℕ
  | .hub | .star => t.choose k
  | .oneMissed => t ^ k

/-- An upper bound on the total uncovered count over a candidate family. -/
def selectionUncoveredBound (N D k : ℕ) : SelectionMethod → ℕ
  | .hub | .star => N * D.choose k
  | .oneMissed => N * D ^ k

private theorem rootedOneMissedCount_mono_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (D m : ℕ) :
    rootedOneMissedCount N₀ D m ≤ rootedOneMissedCount N₁ D m := by
  apply Nat.mul_le_mul hN
  apply Nat.add_le_add
  · exact Nat.pow_le_pow_left (Nat.sub_le_sub_right hN D) m
  · exact Nat.mul_le_mul_left (m * D) (Nat.pow_le_pow_left (Nat.sub_le_sub_right hN D) (m - 1))

/-- More available vertices give at least as many candidates. -/
theorem selectionCount_mono_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (D k : ℕ)
    (method : SelectionMethod) : selectionCount N₀ D k method ≤ selectionCount N₁ D k method := by
  cases method with
  | hub => exact Nat.choose_le_choose k hN
  | star => exact starCandidateCount_monotone hN D k true
  | oneMissed => exact rootedOneMissedCount_mono_order hN D (k - 1)

/-- The connection charge decreases with the available order. -/
theorem selectionCost_antitone_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (hpos : 0 < N₀)
    (D k : ℕ) (method : SelectionMethod) : selectionCost N₁ D k method ≤ selectionCost N₀ D k method := by
  cases method with
  | hub => exact hubSelectionCost_antitone_order hN hpos D k
  | star => exact Nat.le_refl _
  | oneMissed => exact Nat.le_refl _

/-- The total uncovered bound increases with the order. -/
theorem selectionUncoveredBound_mono_order {N₀ N₁ : ℕ} (hN : N₀ ≤ N₁) (D k : ℕ)
    (method : SelectionMethod) :
    selectionUncoveredBound N₀ D k method ≤ selectionUncoveredBound N₁ D k method := by
  cases method <;> exact Nat.mul_le_mul_right _ hN

/-- Enlarging an exceptional set enlarges its sample bound. -/
theorem selectionExceptionBound_mono {t₀ t₁ : ℕ} (ht : t₀ ≤ t₁) (k : ℕ)
    (method : SelectionMethod) :
    selectionExceptionBound t₀ k method ≤ selectionExceptionBound t₁ k method := by
  cases method with
  | hub | star => exact Nat.choose_le_choose k ht
  | oneMissed => exact Nat.pow_le_pow_left ht k

end GraphMinor.Thomason
