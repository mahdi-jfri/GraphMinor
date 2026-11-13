module

public import GraphMinor.Compute.GM06Alg34RegionRecordProg

/-!
# The region stream selected by canonical root flags

Scan all supplied cell labels in increasing order. Emit a region record
at a canonical root and no words at other labels. This produces exactly
the induced region section because the canonical root list is the
increasing finite label list filtered by the same predicate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Words emitted for a supplied label during the canonical root scan. -/
def gm06RootRecordWords (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : List ℕ :=
  if x.isRegionRoot vs a then gm06RegionRecordWords x vs a else []

private theorem filter_records {α : Type*} (L : List α) (p : α → Bool) (f : α → List ℕ) :
    (L.filter p).flatMap f = L.flatMap (fun a => if p a then f a else []) := by
  induction L with
  | nil => rfl
  | cons a L ih => cases hp : p a <;> simp [List.filter_cons, hp, ih]

/-- Scanning every old label and selecting the root flags produces the
exact induced region section in the specified canonical order. -/
theorem gm06Induced_regionWords_eq_root_scan (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).regionWords = (List.finRange x.cellCount).flatMap (gm06RootRecordWords x vs) := by
  rw [gm06Induced_regionWords_eq_records]
  exact filter_records (List.finRange x.cellCount) (x.isRegionRoot vs) (gm06RegionRecordWords x vs)

/-- A root-selected record obeys the same size bound, including skipped labels. -/
theorem gm06RootRecordWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : (gm06RootRecordWords x vs a).length ≤ 2 + x.n + x.ends.length := by
  unfold gm06RootRecordWords
  split
  · exact gm06RegionRecordWords_length_le x vs a
  · simp

end GraphMinor.Compute
