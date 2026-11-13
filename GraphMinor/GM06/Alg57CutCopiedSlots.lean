module

public import GraphMinor.Compute.GM06CutOriginFacts

/-!
# Exact slots of the computed cut rows

For VI (5.7), page 133, each old vertex contributes its left row
and then its right row. Reading either permanent copied slot
therefore gives exactly the local selected row. The proof follows
the finite row scan, including empty slots.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

private theorem splitRowsFrom_getD (marks : GM06CutTables) (rows : List (List ℕ))
    (base v : ℕ) (hv : v < rows.length) (left : Bool) :
    (gm06SplitRotationRowsFrom marks base rows).getD (gm06CutVertex v left) [] =
      gm06CutSelectedRow (gm06CutPositionAt marks (base + v)) (rows.getD v []) left := by
  induction rows generalizing base v with
  | nil => simp at hv
  | cons row rows ih =>
    rw [gm06SplitRotationRowsFrom_cons, gm06SplitVertexRows_eq_selected]
    simp only [List.cons_append, List.nil_append]
    cases v with
    | zero => cases left <;> simp [gm06CutVertex]
    | succ v =>
      have hv' : v < rows.length := by simp only [List.length_cons] at hv; omega
      have he : gm06CutVertex (v + 1) left = gm06CutVertex v left + 2 := by
        unfold gm06CutVertex
        omega
      rw [he]
      simp only [show gm06CutVertex v left + 2 = (gm06CutVertex v left + 1) + 1 by omega,
        List.getD_cons_succ]
      have hh := ih (base + 1) v hv'
      simpa only [show base + 1 + v = base + (v + 1) by omega] using hh

/-- Each permanent copied vertex slot reads its prescribed local
selected row. -/
theorem splitRows_getD (marks : GM06CutTables) (rows : List (List ℕ))
    (v : ℕ) (hv : v < rows.length) (left : Bool) :
    (gm06SplitRotationRows marks rows).getD (gm06CutVertex v left) [] =
      gm06CutSelectedRow (gm06CutPositionAt marks v) (rows.getD v []) left := by
  simpa only [Nat.zero_add, gm06SplitRotationRowsFrom_zero] using splitRowsFrom_getD marks rows 0 v hv left

/-- At a marked vertex, its copied slot reads the induced cut row. -/
theorem splitRows_getD_of_position {marks : GM06CutTables} {rows : List (List ℕ)}
    {v : ℕ} (hv : v < rows.length) {p : GM06CutPosition}
    (hp : gm06CutPositionAt marks v = some p) (left : Bool) :
    (gm06SplitRotationRows marks rows).getD (gm06CutVertex v left) [] =
      gm06CutRotation p (rows.getD v []) left := by
  rw [splitRows_getD marks rows v hv left, hp]
  rfl

end GraphMinor.GM06
