module

public import GraphMinor.Thomason.AlmostDominatingSets
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Counting almost-dominating subsets

Thomason's Lemma 5, page 263 (1984), counts subsets by inserting a vertex
which covers half of the vertices still uncovered. We count the possible
insertions and then count the same inclusions from their larger endpoint.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each almost-dominating `k`-set has at least `m+3-k` extensions under
the degree hypothesis of Thomason's Lemma 5, p. 263. -/
theorem card_almostDominating_extensions (m : ℕ) (hm : m + 3 ≤ Fintype.card V)
    (hdeg : ∀ v, Fintype.card V + m ≤ 2 * G.degree v)
    {k : ℕ} {Y : Finset V} (hY : Y ∈ almostDominatingSets G k) :
    m + 3 - k ≤ ((almostDominatingSets G (k + 1)).filter (Y ⊆ ·)).card := by
  let C := verticesDominatingHalf G (undominatedVertices G Y) \ Y
  have hcardY := ((mem_almostDominatingSets_iff G k Y).mp hY).1
  have hlarge := card_verticesDominatingHalf G m hm hdeg (undominatedVertices G Y)
  have hC : m + 3 - k ≤ C.card := by
    have hsplit := card_sdiff_add_card_inter
      (verticesDominatingHalf G (undominatedVertices G Y)) Y
    have hsmall := card_le_card (inter_subset_right :
      verticesDominatingHalf G (undominatedVertices G Y) ∩ Y ⊆ Y)
    dsimp only [C]
    omega
  have hinj : Set.InjOn (fun v => insert v Y) (↑C : Set V) := by
    intro v hv w hw heq
    dsimp only at heq
    have hvY := (mem_sdiff.mp hv).2
    have hmem : v ∈ insert w Y := by
      rw [← heq]
      exact mem_insert_self v Y
    exact (mem_insert.mp hmem).resolve_right hvY
  have hsub : C.image (fun v => insert v Y) ⊆
      (almostDominatingSets G (k + 1)).filter (Y ⊆ ·) := by
    intro Z hZ
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hZ
    obtain ⟨hgood, hvY⟩ := mem_sdiff.mp hv
    exact mem_filter.mpr ⟨insert_mem_almostDominatingSets G hY hvY hgood,
      subset_insert v Y⟩
  calc
    m + 3 - k ≤ C.card := hC
    _ = (C.image (fun v => insert v Y)).card := (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub

/-- Thomason (1984), Lemma 5, p. 263: at least `choose(m+3,k)`
`k`-subsets leave at most `floor(n/2^k)` vertices undominated. -/
theorem card_almostDominatingSets (m : ℕ) (hm : m + 3 ≤ Fintype.card V)
    (hdeg : ∀ v, Fintype.card V + m ≤ 2 * G.degree v) (k : ℕ) :
    (m + 3).choose k ≤ (almostDominatingSets G k).card := by
  induction k with
  | zero =>
    simpa using (one_le_card.mpr ⟨∅, empty_mem_almostDominatingSets G⟩)
  | succ k ih =>
    by_cases hk : k + 1 ≤ m + 3
    · let A := almostDominatingSets G k
      let B := almostDominatingSets G (k + 1)
      let R : Finset V → Finset V → Prop := (· ⊆ ·)
      have hrow : ∀ Y ∈ A, m + 3 - k ≤ (B.bipartiteAbove R Y).card := by
        intro Y hY
        exact card_almostDominating_extensions G m hm hdeg hY
      have hcol : ∀ Z ∈ B, (A.bipartiteBelow R Z).card ≤ k + 1 := by
        intro Z hZ
        have hZcard := ((mem_almostDominatingSets_iff G (k + 1) Z).mp hZ).1
        have hsub : A.bipartiteBelow R Z ⊆ Z.powersetCard k := by
          intro Y hY
          obtain ⟨hYA, hYZ⟩ := (mem_bipartiteBelow R).mp hY
          exact mem_powersetCard.mpr ⟨hYZ,
            ((mem_almostDominatingSets_iff G k Y).mp hYA).1⟩
        calc
          (A.bipartiteBelow R Z).card ≤ (Z.powersetCard k).card := card_le_card hsub
          _ = (k + 1).choose k := by rw [card_powersetCard, hZcard]
          _ = k + 1 := Nat.choose_succ_self_right k
      have hcount : A.card * (m + 3 - k) ≤ B.card * (k + 1) := by
        calc
          A.card * (m + 3 - k) = ∑ _Y ∈ A, (m + 3 - k) := by simp
          _ ≤ ∑ Y ∈ A, (B.bipartiteAbove R Y).card := sum_le_sum hrow
          _ = ∑ Z ∈ B, (A.bipartiteBelow R Z).card :=
            sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
          _ ≤ ∑ _Z ∈ B, (k + 1) := sum_le_sum hcol
          _ = B.card * (k + 1) := by simp
      apply (mul_le_mul_iff_of_pos_right (by omega : 0 < k + 1)).mp
      calc
        (m + 3).choose (k + 1) * (k + 1) =
            (m + 3).choose k * (m + 3 - k) := Nat.choose_succ_right_eq _ _
        _ ≤ A.card * (m + 3 - k) := Nat.mul_le_mul_right _ ih
        _ ≤ B.card * (k + 1) := hcount
    · rw [Nat.choose_eq_zero_of_lt (by omega : m + 3 < k + 1)]
      exact Nat.zero_le _

end GraphMinor.Thomason
