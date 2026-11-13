module

public import GraphMinor.Compute.CrossingLiftCuts

/-!
# Reading the endpoints at the replacement cuts

The first cut is the first boundary vertex, and the last cut lies just after the last
boundary vertex. These identities let the program read exactly the two endpoints used
in Lemma 1's reverse search, without a second scan of the path.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The first boundary vertex is the entry at the first cut, including the no-visit case. -/
theorem liftFirstBoundaryIndex_getElem? {V : Type*} [DecidableEq V]
    (B L : List V) (S : Finset V) (hB : ∀ x, x ∈ B ↔ x ∈ S) :
    L[liftFirstBoundaryIndex B L]? = firstIn S L := by
  unfold firstIn
  rw [List.dropWhile_eq_drop_findIdx_not, List.head?_drop]
  have hp : (fun x : V => !decide (x ∉ S)) = (fun x => decide (x ∈ B)) := by
    funext x
    simp only [hB]
    by_cases hx : x ∈ S <;> simp [hx]
  rw [hp]
  rfl

/-- The last cut is complementary to the first cut in the reversed list. -/
theorem liftAfterLastBoundaryIndex_eq_reverse {V : Type*} [DecidableEq V] (B L : List V) :
    liftAfterLastBoundaryIndex B L = L.length - liftFirstBoundaryIndex B L.reverse := by
  have h := congrArg List.length (liftFirstBoundaryIndex_prefix B L.reverse)
  rw [List.length_take, min_eq_left (liftBoundaryIndices_le_length B L.reverse).1] at h
  exact congrArg (fun n => L.length - n) h.symm

/-- Existing first and last boundary vertices can be read at the two numerical cuts.
The cut bounds make both reads valid and make the final subtraction exact. -/
theorem liftBoundaryCuts_endpoints {V : Type*} [DecidableEq V]
    (B L : List V) (S : Finset V) (hB : ∀ x, x ∈ B ↔ x ∈ S)
    (p q : V) (hp : firstIn S L = some p) (hq : lastIn S L = some q) :
    liftFirstBoundaryIndex B L < L.length ∧
      0 < liftAfterLastBoundaryIndex B L ∧
      L[liftFirstBoundaryIndex B L]? = some p ∧
      L[liftAfterLastBoundaryIndex B L - 1]? = some q := by
  have hp' := (liftFirstBoundaryIndex_getElem? B L S hB).trans hp
  have hq' := (liftFirstBoundaryIndex_getElem? B L.reverse S hB).trans hq
  have hi := (List.getElem?_eq_some_iff.mp hp').1
  have hj := (List.getElem?_eq_some_iff.mp hq').1
  have hj' : liftFirstBoundaryIndex B L.reverse < L.length := by simpa using hj
  refine ⟨hi, ?_, hp', ?_⟩
  · rw [liftAfterLastBoundaryIndex_eq_reverse]; omega
  · rw [liftAfterLastBoundaryIndex_eq_reverse]
    rw [List.getElem?_reverse hj'] at hq'
    simpa only [Nat.sub_right_comm] using hq'

end GraphMinor.Compute.Crossing
