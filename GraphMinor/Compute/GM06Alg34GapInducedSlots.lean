module

public import GraphMinor.Compute.GM06Alg34GapInducedData

/-!
# Reading updated cuff gap groups

The augmented update maps the old cuff/gap zip. Reading its group at a
cuff position therefore gives precisely that cuff's retained and
reindexed old region list. Matching old group counts justify every read.
-/

public section
namespace GraphMinor.Compute.GM06GapInput

/-- Each updated gap group is the finite update of the matching old cuff and group. -/
theorem inducedGapInput_gap_get (X : GM06GapInput) (vs : List (Fin X.drawing.n))
    (hc : X.gapRegions.length = X.drawing.cuffs.length)
    (c : Fin (X.drawing.inducedData vs).cuffs.length) :
    (X.inducedGapInput vs).gapRegions[c.val]'(by
      rw [X.inducedGapInput_gap_count vs hc]; exact c.isLt) =
    X.drawing.gapRegionsAfterDeletion vs
      X.drawing.cuffs[Fin.cast (X.drawing.inducedData_cuffs_length vs) c]
      (X.gapRegions[c.val]'(by rw [hc, ← X.drawing.inducedData_cuffs_length vs]; exact c.isLt)) := by
  change ((X.drawing.cuffs.zip X.gapRegions).map
    (fun p => X.drawing.gapRegionsAfterDeletion vs p.1 p.2))[c.val]'
    (by simpa only [List.length_map, List.length_zip, hc, Nat.min_self,
      X.drawing.inducedData_cuffs_length vs] using c.isLt) = _
  rw [List.getElem_map, List.getElem_zip]
  rfl

end GraphMinor.Compute.GM06GapInput
