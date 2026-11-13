module

public import GraphMinor.Thomason.SubsetMissingCount
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Averaging within a family of branch candidates

A family of equally sized vertex sets may be smaller than the full
family of subsets. A lower bound on its size and an upper bound on its
total uncovered count still yield a candidate outside all exceptional
families. This permits connected candidates such as edge endpoint sets.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Remove all exceptional selections and apply the total uncovered
bound to the remaining family. A direct bound also suffices when the
number of exceptional selections is smaller than the family size. -/
theorem exists_selection_avoiding_in_family {I : Type v} [DecidableEq I]
    (S : Finset (Finset V)) (indices : Finset I) (B : I → Finset V)
    (t : I → ℕ) (k M U D T : ℕ)
    (hS : S ⊆ (univ : Finset V).powersetCard k) (hM : M ≤ S.card)
    (htotal : (∑ Y ∈ S, (undominatedVertices G Y).card) ≤ U)
    (hbound : ∀ Y ∈ S, (undominatedVertices G Y).card ≤ D)
    (hB : ∀ i ∈ indices, (B i).card ≤ t i)
    (hcount : U < (M - ∑ i ∈ indices, (t i).choose k) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ indices, (t i).choose k) < M)) :
    ∃ Y ∈ S,
      (undominatedVertices G Y).card ≤ T ∧ ∀ i ∈ indices, ¬ Y ⊆ B i := by
  let F := indices.biUnion (fun i => (B i).powersetCard k)
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
  have hAcard : M - C ≤ A.card := by
    have hsplit := card_sdiff_add_card_inter S F
    have hsmall := card_le_card (inter_subset_right : S ∩ F ⊆ F)
    change A.card + (S ∩ F).card = S.card at hsplit
    omega
  have hex : ∃ Y ∈ A, (undominatedVertices G Y).card ≤ T := by
    rcases hcount with havg | ⟨hDT, hcount⟩
    swap
    · have hpos : 0 < A.card := lt_of_lt_of_le (Nat.sub_pos_of_lt hcount) hAcard
      obtain ⟨Y, hY⟩ := card_pos.mp hpos
      exact ⟨Y, hY, (hbound Y (mem_sdiff.mp hY).1).trans hDT⟩
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
    have hbound := (Nat.mul_le_mul_right (T + 1) hAcard).trans (hlower.trans htotal)
    exact (not_lt_of_ge hbound) havg
  obtain ⟨Y, hY, hdom⟩ := hex
  obtain ⟨hYS, hYF⟩ := mem_sdiff.mp hY
  refine ⟨Y, hYS, hdom, ?_⟩
  intro i hi hsub
  apply hYF
  exact mem_biUnion.mpr ⟨i, hi, mem_powersetCard.mpr
    ⟨hsub, (mem_powersetCard.mp (hS hYS)).2⟩⟩

end GraphMinor.Thomason
