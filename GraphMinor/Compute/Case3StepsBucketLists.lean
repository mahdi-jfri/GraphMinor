module

public import GraphMinor.Compute.BitSet
import Mathlib.Data.List.GetD

/-!
# Ordered buckets of stored pair indices

The multigraph encoding stores each positive directed pair once, together
with its full multiplicity. Reverse insertion into owner buckets keeps the
original order within every bucket. These lists describe the pair records
used to encode the members in XIII (9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- Indices at least `k` whose stored pair belongs to the specified owner. -/
noncomputable def case3BucketIndices {A : ℕ} (owner : Fin A → ℕ) (label k : ℕ) : List ℕ :=
  (((List.finRange A).drop k).filter (fun j => owner j = label)).map Fin.val

/-- After the last pair, every owner bucket is empty. -/
theorem case3BucketIndices_done {A : ℕ} (owner : Fin A → ℕ) (label : ℕ) :
    case3BucketIndices owner label A = [] := by
  have hd : (List.finRange A).drop A = [] := List.drop_eq_nil_of_le (by simp only [List.length_finRange]; exact le_rfl)
  simp only [case3BucketIndices, hd, List.filter_nil, List.map_nil]

/-- Reverse insertion prepends the current index just to its own bucket. -/
theorem case3BucketIndices_step {A : ℕ} (owner : Fin A → ℕ) (label k : ℕ) (hk : k < A) :
    case3BucketIndices owner label k =
      (if owner ⟨k, hk⟩ = label then [k] else []) ++ case3BucketIndices owner label (k + 1) := by
  have hget : (List.finRange A)[k]'(by simpa only [List.length_finRange] using hk) = ⟨k, hk⟩ := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  unfold case3BucketIndices
  rw [List.drop_eq_getElem_cons (show k < (List.finRange A).length by simpa only [List.length_finRange] using hk), hget]
  by_cases h : owner ⟨k, hk⟩ = label <;>
    simp only [List.filter_cons, h, decide_true, decide_false, ↓reduceIte,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, Bool.false_eq_true]

/-- Every bucket index is a valid stored pair index belonging to its owner. -/
theorem case3BucketIndices_mem {A : ℕ} (owner : Fin A → ℕ) (label k j : ℕ)
    (hj : j ∈ case3BucketIndices owner label k) :
    ∃ h : j < A, k ≤ j ∧ owner ⟨j, h⟩ = label := by
  obtain ⟨u, hu, heq⟩ := List.mem_map.mp hj
  have hf := List.mem_filter.mp hu
  subst j
  refine ⟨u.2, ?_, of_decide_eq_true hf.2⟩
  have hindex : k ≤ u.1 := by
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hf.1
    have hv := congrArg Fin.val hget
    simp only [List.getElem_drop, List.getElem_finRange, Fin.val_cast] at hv
    omega
  exact hindex

/-- No pair is listed twice in a bucket. -/
theorem case3BucketIndices_nodup {A : ℕ} (owner : Fin A → ℕ) (label k : ℕ) :
    (case3BucketIndices owner label k).Nodup := by
  exact ((show ((List.finRange A).drop k).Nodup from (List.nodup_finRange A).drop).filter _).map Fin.val_injective

/-- A bucket never contains more records than the whole encoding. -/
theorem case3BucketIndices_length_le {A : ℕ} (owner : Fin A → ℕ) (label k : ℕ) :
    (case3BucketIndices owner label k).length ≤ A := by
  unfold case3BucketIndices
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans
    ((List.drop_sublist k (List.finRange A)).length_le.trans (show (List.finRange A).length = A from List.length_finRange).le)

end GraphMinor.Compute
