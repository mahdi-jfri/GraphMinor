module

public import GraphMinor.Compute.GM06Alg34GapInducedData
public import GraphMinor.Compute.GM06Alg34BoundaryFilterData

/-!
# Exact reference words for the retained-gap scan

The scan uses consecutive finite positions of the supplied cuff list.
Selecting positions whose vertices survive and mapping their region
numbers gives exactly the finite augmented gap update. Consecutive
selection writes compose across list prefixes, which supplies the loop
invariant for the RAM scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Selection words concatenate when the scanned list concatenates. -/
theorem gm06BoundaryWords_append_lists {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (A B : List α) :
    gm06BoundaryWords selected labels (A ++ B) =
      gm06BoundaryWords selected labels A ++ gm06BoundaryWords selected labels B := by
  simp only [gm06BoundaryWords, List.filter_append, List.map_append]

/-- Scanning two lists in succession gives exactly the concatenated selection writes. -/
theorem gm06BoundaryWrites_append_lists {α : Type*} (selected : α → Bool) (labels : α → ℕ)
    (A B : List α) (k : ℕ) (dst : List ℕ) :
    gm06BoundaryWrites selected labels (A ++ B) k dst =
      gm06BoundaryWrites selected labels B (k + (gm06BoundaryWords selected labels A).length)
        (gm06BoundaryWrites selected labels A k dst) := by
  induction A generalizing k dst with
  | nil => simp [gm06BoundaryWrites, gm06BoundaryWords]
  | cons a A ih =>
    cases ha : selected a <;>
      simp [gm06BoundaryWrites, gm06BoundaryWords, ha, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The region-number words selected in cuff position order. -/
def gm06GapUpdatedWords (x : GM06DrawingData) (vs L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) : List ℕ :=
  gm06BoundaryWords (fun i => decide (L.get i ∈ vs))
    (fun i => (x.regionAfterDeletion vs (g i)).val) (List.finRange L.length)

private theorem zip_ofFn {α β : Type*} (L : List α) (g : Fin L.length → β) :
    L.zip (List.ofFn g) = (List.finRange L.length).map (fun i => (L.get i, g i)) := by
  apply List.ext_getElem (by simp only [List.length_zip, List.length_ofFn,
    List.length_map, List.length_finRange, Nat.min_self])
  intro i hi hj
  simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_map, List.getElem_finRange,
    List.get_eq_getElem]
  rfl

/-- The position scan emits exactly the region labels of the finite induced gap list. -/
theorem gm06GapUpdatedWords_eq (x : GM06DrawingData) (vs L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) :
    gm06GapUpdatedWords x vs L g =
      (x.gapRegionsAfterDeletion vs L (List.ofFn g)).map Fin.val := by
  rw [GM06DrawingData.gapRegionsAfterDeletion, zip_ofFn]
  simp only [List.filter_map, List.map_map, Function.comp_def, gm06GapUpdatedWords, gm06BoundaryWords]

end GraphMinor.Compute
