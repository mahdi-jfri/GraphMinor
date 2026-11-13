module

public import GraphMinor.Compute.Case3StepsBucketTables

/-!
# Bounds for bucket pointer and count words

A head or next pointer is a stored pair index or the missing sentinel, and
each bucket count is at most the number of stored pairs. These bounds check
the arithmetic of reverse insertion independently of edge multiplicities.
-/

public section

namespace GraphMinor.Compute

/-- A bucket head is either a valid pair index or the missing sentinel. -/
theorem case3BucketIndices_head_le {A : ℕ} (owner : Fin A → ℕ) (label k : ℕ) :
    (case3BucketIndices owner label k).headD A ≤ A := by
  cases hs : case3BucketIndices owner label k with
  | nil => simp only [List.headD_nil, le_refl]
  | cons j js =>
    have hj : j ∈ case3BucketIndices owner label k := by rw [hs]; exact List.mem_cons_self
    obtain ⟨hjA, _, _⟩ := case3BucketIndices_mem owner label k j hj
    exact hjA.le

/-- All head words fit under the pair-count sentinel. -/
theorem case3BucketHeads_words {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) :
    ∀ z ∈ case3BucketHeads owner L k, z ≤ A := by
  intro z hz
  obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hz
  exact case3BucketIndices_head_le owner b.1 k

/-- All count words are bounded by the number of stored pairs. -/
theorem case3BucketCounts_words {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) :
    ∀ z ∈ case3BucketCounts owner L k, z ≤ A := by
  intro z hz
  obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hz
  exact case3BucketIndices_length_le owner b.1 k

/-- Next words are pair indices, the sentinel, or unprocessed zeroes. -/
theorem case3BucketNext_words {A : ℕ} (owner : Fin A → ℕ) (k : ℕ) :
    ∀ z ∈ case3BucketNext owner k, z ≤ A := by
  classical
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  split_ifs
  · exact case3BucketIndices_head_le owner (owner j) (j.1 + 1)
  · exact Nat.zero_le _

end GraphMinor.Compute
