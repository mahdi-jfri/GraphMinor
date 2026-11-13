module

public import GraphMinor.Thomason.SubsetMissingCount
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Selecting a set by its total uncovered count

Remove all selected sets lying inside an earlier exceptional set. If
all remaining selections left more than the desired number of vertices
uncovered, their total uncovered count would exceed the proved double
count. This combines the finite averaging and exceptional-family count
without introducing a probability space or assuming a selection step.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fewer exceptional selections than all selections leave a set outside
every exceptional family, even when their bounds differ. -/
theorem exists_subset_avoiding_of_count {I : Type v} [DecidableEq I]
    (indices : Finset I) (B : I → Finset V) (t : I → ℕ) (k : ℕ)
    (hB : ∀ i ∈ indices, (B i).card ≤ t i)
    (hcount : (∑ i ∈ indices, (t i).choose k) < (Fintype.card V).choose k) :
    ∃ Y ∈ (univ : Finset V).powersetCard k, ∀ i ∈ indices, ¬ Y ⊆ B i := by
  let F := indices.biUnion (fun i => (B i).powersetCard k)
  have hF : F.card ≤ ∑ i ∈ indices, (t i).choose k := by
    calc
      F.card ≤ ∑ i ∈ indices, ((B i).powersetCard k).card := card_biUnion_le
      _ ≤ ∑ i ∈ indices, (t i).choose k := by
        apply sum_le_sum
        intro i hi
        rw [card_powersetCard]
        exact Nat.choose_le_choose k (hB i hi)
  have htotal : ((univ : Finset V).powersetCard k).card = (Fintype.card V).choose k := by
    simp only [card_powersetCard, card_univ]
  obtain ⟨Y, hY, hYF⟩ := exists_mem_notMem_of_card_lt_card
    (htotal ▸ hF.trans_lt hcount)
  refine ⟨Y, hY, ?_⟩
  intro i hi hsub
  exact hYF (mem_biUnion.mpr ⟨i, hi, mem_powersetCard.mpr
    ⟨hsub, (mem_powersetCard.mp hY).2⟩⟩)

/-- A strict bound on the total uncovered count yields a selected set
which leaves at most `T` vertices uncovered and avoids every earlier
exceptional family. Exceptional bounds may differ between branches. -/
theorem exists_subset_avoiding_of_average {I : Type v} [DecidableEq I]
    (indices : Finset I) (B : I → Finset V) (t : I → ℕ) (k D T : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hB : ∀ i ∈ indices, (B i).card ≤ t i)
    (hcount : Fintype.card V * D.choose k <
      ((Fintype.card V).choose k - ∑ i ∈ indices, (t i).choose k) * (T + 1)) :
    ∃ Y ∈ (univ : Finset V).powersetCard k,
      (undominatedVertices G Y).card ≤ T ∧ ∀ i ∈ indices, ¬ Y ⊆ B i := by
  let F := indices.biUnion (fun i => (B i).powersetCard k)
  let S := (univ : Finset V).powersetCard k
  let A := S \ F
  let C := ∑ i ∈ indices, (t i).choose k
  have hF : F.card ≤ C := by
    calc
      F.card ≤ ∑ i ∈ indices, ((B i).powersetCard k).card := card_biUnion_le
      _ ≤ ∑ i ∈ indices, (t i).choose k := by
        apply sum_le_sum
        intro i hi
        rw [card_powersetCard]
        exact Nat.choose_le_choose k (hB i hi)
  have hScard : S.card = (Fintype.card V).choose k := by
    simp only [S, card_powersetCard, card_univ]
  have hAcard : (Fintype.card V).choose k - C ≤ A.card := by
    have hsplit := card_sdiff_add_card_inter S F
    have hsmall := card_le_card (inter_subset_right : S ∩ F ⊆ F)
    change A.card + (S ∩ F).card = S.card at hsplit
    rw [hScard] at hsplit
    omega
  have havg : (∑ Y ∈ S, (undominatedVertices G Y).card) ≤ Fintype.card V * D.choose k :=
    sum_card_undominatedVertices_powersetCard_le G k D hdegree
  have hex : ∃ Y ∈ A, (undominatedVertices G Y).card ≤ T := by
    by_contra hnone
    have hbad (Y : Finset V) (hY : Y ∈ A) : T + 1 ≤ (undominatedVertices G Y).card := by
      have hh : ¬ (undominatedVertices G Y).card ≤ T := fun h => hnone ⟨Y, hY, h⟩
      omega
    have hlower : A.card * (T + 1) ≤ ∑ Y ∈ S, (undominatedVertices G Y).card := by
      calc
        A.card * (T + 1) = ∑ _Y ∈ A, (T + 1) := by simp
        _ ≤ ∑ Y ∈ A, (undominatedVertices G Y).card := sum_le_sum hbad
        _ ≤ ∑ Y ∈ S, (undominatedVertices G Y).card :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.zero_le _)
    have hbound := (Nat.mul_le_mul_right (T + 1) hAcard).trans (hlower.trans havg)
    exact (not_lt_of_ge hbound) hcount
  obtain ⟨Y, hY, hdom⟩ := hex
  obtain ⟨hYS, hYF⟩ := mem_sdiff.mp hY
  refine ⟨Y, hYS, hdom, ?_⟩
  intro i hi hsub
  apply hYF
  exact mem_biUnion.mpr ⟨i, hi, mem_powersetCard.mpr
    ⟨hsub, (mem_powersetCard.mp hYS).2⟩⟩

end GraphMinor.Thomason
