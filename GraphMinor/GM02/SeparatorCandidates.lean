module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Polynomially many candidate separators

For a fixed separator bound, enumerate tuples of that many optional
vertices. Ignore empty slots and repetitions. Every small vertex set is
represented by its vertex list followed by empty slots. Thus this
version of the exhaustive search in II (3.1) has at most one plus the
number of vertices, raised to the fixed separator bound, candidates.
-/

@[expose] public section
namespace GraphMinor.GM02
open Finset Classical
open scoped BigOperators

/-- The vertex set represented by a tuple with empty slots allowed. -/
def separatorOfTuple {α : Type*} [DecidableEq α] {w : ℕ} (f : Fin w → Option α) : Finset α :=
  Finset.univ.biUnion (fun i => (f i).toFinset)

/-- A tuple of length `w` represents at most `w` distinct vertices. -/
theorem separatorOfTuple_card_le {α : Type*} [DecidableEq α] {w : ℕ}
    (f : Fin w → Option α) : (separatorOfTuple f).card ≤ w := by
  calc
    _ ≤ ∑ i : Fin w, (f i).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin w, 1 := Finset.sum_le_sum (fun i _ => by cases f i <;> simp)
    _ = w := by simp

/-- Padding a vertex list by empty slots represents any set of size at most `w`. -/
theorem exists_separator_tuple {α : Type*} [DecidableEq α] (s : Finset α) {w : ℕ}
    (hs : s.card ≤ w) : ∃ f : Fin w → Option α, separatorOfTuple f = s := by
  refine ⟨fun i => s.toList[i.val]?, ?_⟩
  ext a
  simp only [separatorOfTuple, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨i, hi⟩
    exact Finset.mem_toList.1 (List.mem_of_getElem? hi)
  · intro ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 ha)
    have hiw : i < w := by simpa only [Finset.length_toList] using lt_of_lt_of_le hi (by simpa using hs)
    exact ⟨⟨i, hiw⟩, by simp only [List.getElem?_eq_getElem hi, he]⟩

/-- All separator candidates, with repeated representations removed. -/
noncomputable def separatorCandidates (n w : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.image (separatorOfTuple (α := Fin n) (w := w))

/-- The enumeration contains exactly the permitted vertex subsets. -/
theorem mem_separatorCandidates {n w : ℕ} {s : Finset (Fin n)} :
    s ∈ separatorCandidates n w ↔ s.card ≤ w := by
  constructor
  · rintro hs
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 hs
    exact separatorOfTuple_card_le f
  · intro hs
    obtain ⟨f, hf⟩ := exists_separator_tuple s hs
    exact Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩

/-- The candidate count is polynomial in the vertex count for fixed `w`. -/
theorem separatorCandidates_card_le (n w : ℕ) :
    (separatorCandidates n w).card ≤ (n + 1) ^ w := by
  calc
    _ ≤ (Finset.univ : Finset (Fin w → Option (Fin n))).card := Finset.card_image_le
    _ = (n + 1) ^ w := by simp

end GraphMinor.GM02
