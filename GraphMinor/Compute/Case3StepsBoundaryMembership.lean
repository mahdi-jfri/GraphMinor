module

public import GraphMinor.Compute.Case3StepsBoundaryKeys

/-!
# Membership tests in a small boundary key

The key's size word says which of its three vertex slots are occupied.
Checking that a slot is occupied before comparing its value prevents zero
padding from being mistaken for vertex zero. This yields a constant-size
membership test for the selected member's core vertices.
-/

public section

namespace GraphMinor.Compute

open Classical

/-- The key's first word is its boundary size. -/
theorem case3BoundaryKey_getD_zero {n : ℕ} (S : Finset (Fin n)) :
    (case3BoundaryKey S).getD 0 0 = S.card := rfl

/-- Any key read fits the word bound, including a default zero past its end. -/
theorem case3BoundaryKey_getD_lt {n w : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (j : ℕ) :
    (case3BoundaryKey S).getD j 0 < 2 ^ w := by
  by_cases hj : j < (case3BoundaryKey S).length
  · rw [List.getD_eq_getElem _ 0 hj]
    exact case3BoundaryKey_words S hS hw hn _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ 0 (by omega)]
    omega

/-- An occupied key slot contains the corresponding increasing boundary vertex. -/
theorem case3BoundaryKey_slot {n : ℕ} (S : Finset (Fin n)) (j : ℕ) (hj : j < S.card) :
    (case3BoundaryKey S).getD (j + 1) 0 =
      ((case3BoundaryVertices S)[j]'(by rw [case3BoundaryVertices_length]; exact hj)).1 := by
  unfold case3BoundaryKey
  rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by
    rw [List.length_map, case3BoundaryVertices_length]
    exact hj)]
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_map, case3BoundaryVertices_length]; exact hj)]
  simp only [List.getElem_map]

/-- A boundary vertex appears in one of the occupied slots. -/
theorem case3BoundaryKey_mem_iff_slot {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (v : Fin n) :
    v ∈ S ↔ ∃ j : Fin 3, j.1 < S.card ∧ (case3BoundaryKey S).getD (j.1 + 1) 0 = v.1 := by
  constructor
  · intro hv
    have hm : v ∈ case3BoundaryVertices S := by simp [case3BoundaryVertices, hv]
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    have hjc : j < S.card := by rw [← case3BoundaryVertices_length S]; exact hj
    refine ⟨⟨j, by omega⟩, hjc, ?_⟩
    rw [case3BoundaryKey_slot S j hjc, heq]
  · rintro ⟨j, hj, heq⟩
    rw [case3BoundaryKey_slot S j.1 hj] at heq
    have hvEq : (case3BoundaryVertices S)[j.1]'(by rw [case3BoundaryVertices_length]; exact hj) = v :=
      Fin.ext heq
    have hm := List.getElem_mem (l := case3BoundaryVertices S)
      (n := j.1) (by rw [case3BoundaryVertices_length]; exact hj)
    rw [hvEq] at hm
    simpa only [case3BoundaryVertices, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using hm

/-- Three occupied-slot tests decide membership in a boundary of size at most three. -/
theorem case3BoundaryKey_mem_iff_three_slots {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (v : Fin n) :
    v ∈ S ↔
      (0 < S.card ∧ (case3BoundaryKey S).getD 1 0 = v.1) ∨
      (1 < S.card ∧ (case3BoundaryKey S).getD 2 0 = v.1) ∨
      (2 < S.card ∧ (case3BoundaryKey S).getD 3 0 = v.1) := by
  rw [case3BoundaryKey_mem_iff_slot S hS v]
  constructor
  · rintro ⟨j, hj, heq⟩
    fin_cases j
    · exact Or.inl ⟨hj, heq⟩
    · exact Or.inr (Or.inl ⟨hj, heq⟩)
    · exact Or.inr (Or.inr ⟨hj, heq⟩)
  · rintro (h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

end GraphMinor.Compute
