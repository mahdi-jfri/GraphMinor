module

public import GraphMinor.Compute.GM06Alg34ClosureRowLists

/-!
# Enumerating supplied rows by finite indices

A supplied list paired with consecutive row numbers is also a list
indexed by its finite positions. This identity lets the closure-row
proof use the input's typed vertex, edge, and region labels without
changing the executable natural-number representation.
-/

public section
namespace GraphMinor.Compute

/-- Consecutively numbered entries are their finite-index enumeration. -/
theorem gm06ZipIdx_eq_finRange {α : Type*} (L : List α) (start : ℕ) :
    L.zipIdx start = (List.finRange L.length).map (fun i => (L[i], start + i.val)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_finRange]
  rfl

/-- Consecutive vertex row numbers are their finite-index enumeration. -/
theorem gm06Range_eq_finRange (n : ℕ) :
    List.range' 0 n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_range', List.getElem_map, List.getElem_finRange]
  simp

end GraphMinor.Compute
