module

public import GraphMinor.Thomason.ResidualFamilies
import GraphMinor.Thomason.ResidualExtensions
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Counting selected sets with degree-sensitive uncovered bounds

The inclusion count of Thomason's Lemma 5 (1984), p. 263, works with
any sequence of uncovered-vertex bounds satisfying the missing-pair
inequality. Every selected set has enough extensions, and every larger
set has at most its own order many parents.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The subset-count induction of Thomason's Lemma 5 with explicit
uncovered bounds and the graph's actual non-neighbour bound. -/
theorem card_residualBoundedSets (M D : ℕ) (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (f : ℕ → ℕ) (hfzero : Fintype.card V ≤ f 0)
    (hbudget : ∀ j, f j * D < (Fintype.card V + 1 - M) * (f (j + 1) + 1)) (k : ℕ) :
    M.choose k ≤ (residualBoundedSets G k (f k)).card := by
  induction k with
  | zero =>
    have hmem : (∅ : Finset V) ∈ residualBoundedSets G 0 (f 0) := by
      rw [mem_residualBoundedSets_iff]
      simpa using hfzero
    simpa using (one_le_card.mpr ⟨∅, hmem⟩)
  | succ k ih =>
    by_cases hk : k + 1 ≤ M
    · let A := residualBoundedSets G k (f k)
      let B := residualBoundedSets G (k + 1) (f (k + 1))
      let R : Finset V → Finset V → Prop := (· ⊆ ·)
      have hrow : ∀ Y ∈ A, M - k ≤ (B.bipartiteAbove R Y).card := by
        intro Y hY
        exact card_residualBounded_extensions G M D hM hdegree (hbudget k) hY
      have hcol : ∀ Z ∈ B, (A.bipartiteBelow R Z).card ≤ k + 1 := by
        intro Z hZ
        have hZcard := ((mem_residualBoundedSets_iff G (k + 1) (f (k + 1)) Z).mp hZ).1
        have hsub : A.bipartiteBelow R Z ⊆ Z.powersetCard k := by
          intro Y hY
          obtain ⟨hYA, hYZ⟩ := (mem_bipartiteBelow R).mp hY
          exact mem_powersetCard.mpr ⟨hYZ,
            ((mem_residualBoundedSets_iff G k (f k) Y).mp hYA).1⟩
        calc
          (A.bipartiteBelow R Z).card ≤ (Z.powersetCard k).card := card_le_card hsub
          _ = (k + 1).choose k := by rw [card_powersetCard, hZcard]
          _ = k + 1 := Nat.choose_succ_self_right k
      have hcount : A.card * (M - k) ≤ B.card * (k + 1) := by
        calc
          A.card * (M - k) = ∑ _Y ∈ A, (M - k) := by simp
          _ ≤ ∑ Y ∈ A, (B.bipartiteAbove R Y).card := sum_le_sum hrow
          _ = ∑ Z ∈ B, (A.bipartiteBelow R Z).card :=
            sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
          _ ≤ ∑ _Z ∈ B, (k + 1) := sum_le_sum hcol
          _ = B.card * (k + 1) := by simp
      apply (mul_le_mul_iff_of_pos_right (by omega : 0 < k + 1)).mp
      calc
        (M).choose (k + 1) * (k + 1) =
            (M).choose k * (M - k) := Nat.choose_succ_right_eq _ _
        _ ≤ A.card * (M - k) := Nat.mul_le_mul_right _ ih
        _ ≤ B.card * (k + 1) := hcount
    · rw [Nat.choose_eq_zero_of_lt (by omega : M < k + 1)]
      exact Nat.zero_le _

end GraphMinor.Thomason
