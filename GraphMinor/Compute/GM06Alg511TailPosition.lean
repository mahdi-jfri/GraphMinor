module

public import GraphMinor.Compute.GM06FindLabel
import Mathlib.Tactic

/-!
# Recognizing noninitial cuff positions from a label scan

The reference correction in VI (5.11), page 134, is one for a
vertex listed after the first cuff position. In a row with no repeated
labels, a successful scan finds a positive position exactly for these
vertices. The missing-label sentinel is the row length and is excluded.
-/

public section
namespace GraphMinor.Compute

/-- A genuine matching position in a row with no repeated labels is
positive exactly when the label belongs to the tail of the row. -/
theorem gm06Alg511Tail_mem_iff (xs : List ℕ) (hnd : xs.Nodup) (v q : ℕ)
    (hresult : (q = xs.length ∧ v ∉ xs) ∨ ∃ hq : q < xs.length, xs[q] = v) :
    v ∈ xs.tail ↔ 0 < q ∧ q < xs.length := by
  rcases hresult with hnone | hsome
  · have htail : v ∉ xs.tail := fun h => hnone.2 (List.mem_of_mem_tail h)
    simp only [htail, false_iff]
    omega
  · obtain ⟨hq, hval⟩ := hsome
    cases xs with
    | nil => simp at hq
    | cons a rest =>
      cases q with
      | zero =>
        have hav : a = v := hval
        have hnot : v ∉ rest := hav ▸ (List.nodup_cons.mp hnd).1
        simp [hnot]
      | succ j =>
        have hj : j < rest.length := by simpa using hq
        have hmem : v ∈ rest := hval ▸ List.getElem_mem hj
        simp only [List.tail_cons, hmem, true_iff]
        exact ⟨Nat.zero_lt_succ _, hq⟩

/-- The generic scan result gives exactly the positive-position
membership test needed for the finite reference correction. -/
theorem gm06Alg511Tail_mem_iff_of_scan (xs : List ℕ) (hnd : xs.Nodup) (v q : ℕ)
    (hscan : (q = xs.length ∧ ∀ j (hj : j < xs.length), xs[j] ≠ v) ∨
      ∃ (j : ℕ) (hj : j < xs.length), q = j ∧ xs[j] = v) :
    v ∈ xs.tail ↔ 0 < q ∧ q < xs.length := by
  apply gm06Alg511Tail_mem_iff xs hnd v q
  rcases hscan with hnone | hsome
  · refine Or.inl ⟨hnone.1, ?_⟩
    intro hm
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    exact hnone.2 j hj heq
  · obtain ⟨j, hj, rfl, hval⟩ := hsome
    exact Or.inr ⟨hj, hval⟩

end GraphMinor.Compute
