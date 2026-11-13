module

public import GraphMinor.Compute.SpecsCrossingRec

/-!
# The splice positions in Lemma 1's reverse rule

The replacement lift removes the path segment from its first boundary visit through its
last boundary visit. This file expresses those two cuts as numerical indices and identifies
the resulting prefix and suffix with `spliceBetween`. It also gives the update rules used by
the RAM scan of path vertices.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The first boundary position, with the list length as sentinel if there is no visit. -/
def liftFirstBoundaryIndex {V : Type*} [DecidableEq V] (B L : List V) : ℕ :=
  L.findIdx (fun x => decide (x ∈ B))

/-- The cut just after the last boundary visit, or zero if there is no visit. -/
def liftAfterLastBoundaryIndex {V : Type*} [DecidableEq V] (B L : List V) : ℕ :=
  L.length - (L.reverse.takeWhile (fun x => decide (x ∉ B))).length

/-- The first cut gives exactly the prefix used in Lemma 1's splice. -/
theorem liftFirstBoundaryIndex_prefix {V : Type*} [DecidableEq V] (B L : List V) :
    L.take (liftFirstBoundaryIndex B L) = L.takeWhile (fun x => decide (x ∉ B)) := by
  rw [List.takeWhile_eq_take_findIdx_not]
  have hp : (fun x : V => !decide (x ∉ B)) = (fun x => decide (x ∈ B)) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [hp]
  rfl

/-- The last cut gives exactly the suffix used in Lemma 1's splice. -/
theorem liftAfterLastBoundaryIndex_suffix {V : Type*} [DecidableEq V] (B L : List V) :
    L.drop (liftAfterLastBoundaryIndex B L) =
      (L.reverse.takeWhile (fun x => decide (x ∉ B))).reverse := by
  have hp := List.prefix_iff_eq_take.mp (List.takeWhile_prefix (l := L.reverse) (fun x => decide (x ∉ B)))
  calc
    L.drop (liftAfterLastBoundaryIndex B L) =
        (L.reverse.take (L.reverse.takeWhile (fun x => decide (x ∉ B))).length).reverse := by
      rw [List.take_reverse, List.reverse_reverse]
      rfl
    _ = (L.reverse.takeWhile (fun x => decide (x ∉ B))).reverse := congrArg List.reverse hp.symm

/-- The index-based RAM splice is the replacement splice from Lemma 1. -/
theorem liftBoundaryCuts_spliceBetween {V : Type*} [DecidableEq V]
    (B L Y : List V) (S : Finset V) (hB : ∀ x, x ∈ B ↔ x ∈ S) :
    L.take (liftFirstBoundaryIndex B L) ++ Y ++ L.drop (liftAfterLastBoundaryIndex B L) =
      spliceBetween S L Y := by
  have hp : (fun x : V => decide (x ∉ B)) = (fun x => decide (x ∉ S)) := by
    funext x
    simp only [hB]
  rw [liftFirstBoundaryIndex_prefix, liftAfterLastBoundaryIndex_suffix, hp]
  rfl

/-- Both cuts lie within the path array. -/
theorem liftBoundaryIndices_le_length {V : Type*} [DecidableEq V] (B L : List V) :
    liftFirstBoundaryIndex B L ≤ L.length ∧ liftAfterLastBoundaryIndex B L ≤ L.length :=
  ⟨List.findIdx_le_length, Nat.sub_le _ _⟩

/-- Visiting a boundary vertex at position `j` bounds the first cut by `j`. -/
theorem liftFirstBoundaryIndex_le_of_mem {V : Type*} [DecidableEq V] (B L : List V)
    {j : ℕ} (hj : j < L.length) (hm : L[j] ∈ B) : liftFirstBoundaryIndex B L ≤ j := by
  by_contra h
  have hi : j < L.findIdx (fun x => decide (x ∈ B)) := by change j < liftFirstBoundaryIndex B L; omega
  have hn := List.not_of_lt_findIdx hi
  simp only [hm, decide_true] at hn
  contradiction

/-- At a position outside the boundary, the first cut is not that position. -/
theorem liftFirstBoundaryIndex_ne_of_not_mem {V : Type*} [DecidableEq V] (B L : List V)
    {j : ℕ} (hj : j < L.length) (hm : L[j] ∉ B) : liftFirstBoundaryIndex B L ≠ j := by
  intro heq
  have hi : L.findIdx (fun x => decide (x ∈ B)) < L.length := by
    change liftFirstBoundaryIndex B L < L.length
    omega
  have hn := @List.findIdx_getElem V (fun x => decide (x ∈ B)) L hi
  change decide (L[liftFirstBoundaryIndex B L]'hi ∈ B) = true at hn
  simp only [heq, hm, decide_false] at hn
  contradiction

/-- A boundary visit moves the last cut to the following position. Otherwise the last cut
stays where it was. This is the update rule of the path scan. -/
theorem liftAfterLastBoundaryIndex_take_step {V : Type*} [DecidableEq V] (B L : List V)
    {j : ℕ} (hj : j < L.length) :
    liftAfterLastBoundaryIndex B (L.take (j + 1)) =
      if L[j] ∈ B then j + 1 else liftAfterLastBoundaryIndex B (L.take j) := by
  have hjtake : (L.take j).length = j := List.length_take_of_le (by omega)
  unfold liftAfterLastBoundaryIndex
  rw [List.take_succ_eq_append_getElem hj]
  by_cases hm : L[j] ∈ B <;>
    simp only [List.length_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.takeWhile_cons, hm,
      not_true_eq_false, not_false_eq_true, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte,
      List.length_nil, List.length_cons, hjtake] <;> omega

end GraphMinor.Compute.Crossing
