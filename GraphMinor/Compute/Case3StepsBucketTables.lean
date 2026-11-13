module

public import GraphMinor.Compute.Case3StepsBucketLists
import Mathlib.Data.List.GetD

/-!
# Heads, counts, and next pointers for reverse bucket insertion

Each owner stores the first pair index in its bucket and the number of its
records. Each processed pair stores the next index for the same owner. A
reverse insertion writes one next pointer, replaces one head, and increases
one count. The list identities keep these three tables exact.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Head pointers for all owner buckets after processing indices at least `k`. -/
noncomputable def case3BucketHeads {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) : List ℕ :=
  List.ofFn (fun b : Fin L => (case3BucketIndices owner b.1 k).headD A)

/-- Record counts for all owner buckets after processing indices at least `k`. -/
noncomputable def case3BucketCounts {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) : List ℕ :=
  List.ofFn (fun b : Fin L => (case3BucketIndices owner b.1 k).length)

/-- Next pointers at processed indices, with zero in unprocessed slots. -/
noncomputable def case3BucketNext {A : ℕ} (owner : Fin A → ℕ) (k : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin A => if k ≤ j.1 then
    (case3BucketIndices owner (owner j) (j.1 + 1)).headD A else 0)

/-- The head-table lookup is the first index of the corresponding ordered bucket. -/
theorem case3BucketHeads_getD {A : ℕ} (owner : Fin A → ℕ) (L k b : ℕ) (hb : b < L) :
    (case3BucketHeads owner L k).getD b 0 = (case3BucketIndices owner b k).headD A := by
  rw [List.getD_eq_getElem _ 0 (by simp only [case3BucketHeads, List.length_ofFn]; exact hb)]
  simp only [case3BucketHeads, List.getElem_ofFn]

/-- The count-table lookup is the corresponding ordered bucket's length. -/
theorem case3BucketCounts_getD {A : ℕ} (owner : Fin A → ℕ) (L k b : ℕ) (hb : b < L) :
    (case3BucketCounts owner L k).getD b 0 = (case3BucketIndices owner b k).length := by
  rw [List.getD_eq_getElem _ 0 (by simp only [case3BucketCounts, List.length_ofFn]; exact hb)]
  simp only [case3BucketCounts, List.getElem_ofFn]

/-- Initially all owner buckets are missing. -/
theorem case3BucketHeads_done {A : ℕ} (owner : Fin A → ℕ) (L : ℕ) :
    case3BucketHeads owner L A = List.replicate L A := by
  apply List.ext_getElem (by simp [case3BucketHeads])
  intro j hj hj'
  simp only [case3BucketHeads, List.getElem_ofFn, case3BucketIndices_done,
    List.headD_nil, List.getElem_replicate]

/-- Initially all owner counts are zero. -/
theorem case3BucketCounts_done {A : ℕ} (owner : Fin A → ℕ) (L : ℕ) :
    case3BucketCounts owner L A = List.replicate L 0 := by
  apply List.ext_getElem (by simp [case3BucketCounts])
  intro j hj hj'
  simp only [case3BucketCounts, List.getElem_ofFn, case3BucketIndices_done,
    List.length_nil, List.getElem_replicate]

/-- Initially no next pointer has been written. -/
theorem case3BucketNext_done {A : ℕ} (owner : Fin A → ℕ) :
    case3BucketNext owner A = List.replicate A 0 := by
  apply List.ext_getElem (by simp [case3BucketNext])
  intro j hj hj'
  have hjA : j < A := by simpa only [case3BucketNext, List.length_ofFn] using hj
  simp only [case3BucketNext, List.getElem_ofFn, List.getElem_replicate,
    show ¬ A ≤ j by omega, ↓reduceIte]

/-- Inserting a pair replaces its owner's head by its own index. -/
theorem case3BucketHeads_set {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) (hk : k < A)
    (howner : owner ⟨k, hk⟩ < L) :
    (case3BucketHeads owner L (k + 1)).set (owner ⟨k, hk⟩) k = case3BucketHeads owner L k := by
  classical
  apply List.ext_getElem (by simp [case3BucketHeads])
  intro b hb hb'
  simp only [List.getElem_set, case3BucketHeads, List.getElem_ofFn]
  rw [case3BucketIndices_step owner b k hk]
  by_cases h : owner ⟨k, hk⟩ = b <;>
    simp only [h, ↓reduceIte, List.cons_append, List.nil_append, List.headD_cons]

/-- Inserting a pair increases its owner's count by one. -/
theorem case3BucketCounts_set {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) (hk : k < A)
    (howner : owner ⟨k, hk⟩ < L) :
    (case3BucketCounts owner L (k + 1)).set (owner ⟨k, hk⟩)
      ((case3BucketCounts owner L (k + 1)).getD (owner ⟨k, hk⟩) 0 + 1) =
      case3BucketCounts owner L k := by
  classical
  rw [case3BucketCounts_getD owner L (k + 1) _ howner]
  apply List.ext_getElem (by simp [case3BucketCounts])
  intro b hb hb'
  simp only [List.getElem_set, case3BucketCounts, List.getElem_ofFn]
  rw [case3BucketIndices_step owner b k hk]
  by_cases h : owner ⟨k, hk⟩ = b
  · simp only [h, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons]
  · simp only [h, ↓reduceIte, List.nil_append]

/-- The inserted pair points to the owner's previous bucket head. -/
theorem case3BucketNext_set {A : ℕ} (owner : Fin A → ℕ) (L k : ℕ) (hk : k < A)
    (howner : owner ⟨k, hk⟩ < L) :
    (case3BucketNext owner (k + 1)).set k
      ((case3BucketHeads owner L (k + 1)).getD (owner ⟨k, hk⟩) 0) = case3BucketNext owner k := by
  classical
  rw [case3BucketHeads_getD owner L (k + 1) _ howner]
  apply List.ext_getElem (by simp [case3BucketNext])
  intro j hj hj'
  simp only [List.getElem_set, case3BucketNext, List.getElem_ofFn]
  by_cases h : k = j
  · subst j
    simp only [le_refl, ↓reduceIte]
  · have he : k + 1 ≤ j ↔ k ≤ j := by omega
    simp only [h, ↓reduceIte, he]

end GraphMinor.Compute
