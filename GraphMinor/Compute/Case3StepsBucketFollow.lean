module

public import GraphMinor.Compute.Case3StepsBucketTables
import Mathlib.Data.List.GetD

/-!
# Following an ordered owner bucket

A bucket's count bounds its traversal. Each next pointer leads to the first
later pair with the same owner. Following exactly the stored count therefore
recovers the ordered filtered list of pair indices, without visiting the
missing sentinel.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Follow a fixed number of next pointers, starting at the bucket head. -/
def case3FollowBucket (next : List ℕ) (head : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 => head :: case3FollowBucket next (next.getD head 0) count

/-- A processed next pointer leads to the first later pair of the same owner. -/
theorem case3BucketNext_getD {A : ℕ} (owner : Fin A → ℕ) (k : ℕ) (j : Fin A)
    (hj : k ≤ j.1) :
    (case3BucketNext owner k).getD j.1 0 =
      (case3BucketIndices owner (owner j) (j.1 + 1)).headD A := by
  rw [List.getD_eq_getElem _ 0 (by simp only [case3BucketNext, List.length_ofFn]; exact j.2)]
  simp only [case3BucketNext, List.getElem_ofFn, hj, ↓reduceIte]

private theorem followBucket_suffix {A : ℕ} (owner : Fin A → ℕ) (label rem k : ℕ)
    (hrem : k + rem = A) :
    case3FollowBucket (case3BucketNext owner 0)
      ((case3BucketIndices owner label k).headD A) (case3BucketIndices owner label k).length =
      case3BucketIndices owner label k := by
  classical
  induction rem generalizing k with
  | zero =>
    have hk : k = A := by omega
    simp only [hk, case3BucketIndices_done, List.length_nil, case3FollowBucket]
  | succ rem ih =>
    have hk : k < A := by omega
    have hs := case3BucketIndices_step owner label k hk
    have hi := ih (k + 1) (by omega)
    by_cases h : owner ⟨k, hk⟩ = label
    · simp only [h, ↓reduceIte, List.cons_append, List.nil_append] at hs
      rw [hs]
      simp only [List.headD_cons, List.length_cons, case3FollowBucket]
      rw [case3BucketNext_getD owner 0 ⟨k, hk⟩ (by omega)]
      simpa only [h] using congrArg (List.cons k) hi
    · simp only [h, ↓reduceIte, List.nil_append] at hs
      simpa only [hs] using hi

/-- The head and count recover exactly the owner's ordered pair-index list. -/
theorem case3FollowBucket_eq_indices {A : ℕ} (owner : Fin A → ℕ) (label : ℕ) :
    case3FollowBucket (case3BucketNext owner 0)
      ((case3BucketIndices owner label 0).headD A) (case3BucketIndices owner label 0).length =
      case3BucketIndices owner label 0 :=
  followBucket_suffix owner label A 0 (by omega)

end GraphMinor.Compute
