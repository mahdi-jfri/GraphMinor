module

public import GraphMinor.Compute.Case3StepsBucketLists
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Total size of all pair buckets

Each positive input pair has one owner label. Filtering by all possible
labels therefore lists each pair exactly once. The sum of bucket lengths
is the number of stored pairs, so copying all member records has linear
pair cost.
-/

public section

namespace GraphMinor.Compute

open Classical
open scoped BigOperators

private theorem bucket_length_card {A : ℕ} (owner : Fin A → ℕ) (label : ℕ) :
    (case3BucketIndices owner label 0).length =
      (Finset.univ.filter (fun j : Fin A => owner j = label)).card := by
  let js := (List.finRange A).filter (fun j => owner j = label)
  have hnd : js.Nodup := (List.nodup_finRange A).filter _
  have hs : js.toFinset = Finset.univ.filter (fun j : Fin A => owner j = label) := by
    ext j
    simp only [js, List.mem_toFinset, List.mem_filter, List.mem_finRange,
      true_and, Finset.mem_filter, Finset.mem_univ, decide_eq_true_eq]
  simp only [case3BucketIndices, List.drop_zero, List.length_map]
  exact (List.toFinset_card_of_nodup hnd).symm.trans (congrArg Finset.card hs)

/-- Every positive pair contributes to exactly one owner bucket. -/
theorem case3BucketIndices_sum_length {A L : ℕ} (owner : Fin A → ℕ)
    (howner : ∀ j, owner j < L) :
    (∑ b : Fin L, (case3BucketIndices owner b.1 0).length) = A := by
  simp only [bucket_length_card, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hone (j : Fin A) : (∑ b : Fin L, if owner j = b.1 then 1 else 0) = 1 := by
    have he (b : Fin L) : (owner j = b.1) ↔ b = (⟨owner j, howner j⟩ : Fin L) := by
      constructor
      · intro h
        exact Fin.ext h.symm
      · rintro rfl
        rfl
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one]

end GraphMinor.Compute
