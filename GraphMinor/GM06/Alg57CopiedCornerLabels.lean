module

public import GraphMinor.GM06.Alg57CutBlockCornerLabels
public import GraphMinor.GM06.Alg57CutCopiedSlots
public import GraphMinor.GM06.Alg57CutOrbitAvoidLast
import all GraphMinor.GM06.Alg57CutFaceLink

/-!
# Reading a corner label in a copied row slot

For Lemma 10 of VI (5.7), page 133, a copied end in a marked
vertex slot belongs to that slot's local block. When it is not a
last block end, its projected corner has the first end's label.
This joins the exact slot calculation to local corner constancy.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- The last end specified by a decoded local position belongs to
the global set of copied last ends. -/
theorem cutLastDarts_of_position {marks : GM06CutTables} {rows : List (List ℕ)}
    {v : ℕ} {row : List ℕ} {p : GM06CutPosition}
    (hv : rows[v]? = some row) (hp : gm06CutPositionAt marks v = some p) (left : Bool) :
    gm06CutRowDart p left (cutLast p left) ∈ cutLastDarts marks rows :=
  ⟨v, row, p, left, hv, hp, rfl⟩

/-- A nonlast end in a copied slot has the corner label of the
first end of that slot's local block. -/
theorem copied_corner_label {β : Type*} {marks : GM06CutTables} {rows : List (List ℕ)}
    {v : ℕ} (hv : v < rows.length) {p : GM06CutPosition}
    (hp : gm06CutPositionAt marks v = some p) (hn : (rows.getD v []).Nodup)
    (hok : CutBlockOK p (rows.getD v [])) (g : ℕ → β)
    (hskip : ∀ d ∈ rows.getD v [], d ∉ cutBoundaryEnds p →
      g ((rows.getD v []).formPerm.symm d) = g d)
    (left : Bool) {q : ℕ}
    (hq : q ∈ (gm06SplitRotationRows marks rows).getD (gm06CutVertex v left) [])
    (hnot : q ∉ cutLastDarts marks rows) :
    g (gm06UncutDart q) = g (cutFirst p left) := by
  rw [splitRows_getD_of_position hv hp left] at hq
  rw [gm06CutRotation_eq_map_filter] at hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hd, hkeep⟩ := List.mem_filter.mp hd
  rw [gm06CutRowDart_project]
  apply cutBlock_corner_label hn hok g hskip left hd hkeep
  intro he
  apply hnot
  rw [he]
  exact cutLastDarts_of_position (row := rows.getD v []) (by
    simp only [List.getElem?_eq_getElem hv, List.getD_eq_getElem _ _ hv]) hp left

end GraphMinor.GM06
