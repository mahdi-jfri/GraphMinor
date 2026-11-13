module

public import GraphMinor.GM01.GridDiagramCoordinates
import GraphMinor.GM01.ConnectedInducedSets

/-!
# Connected crosses in the grid diagram

The two children of the root in Figure 3 of Graph Minors I, page 52,
are represented by a horizontal interval joined to a vertical interval.
Their common vertex connects the two intervals. The four smaller tree
models will attach to the ends of the vertical intervals.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- A horizontal interval and a vertical interval form a connected
cross whenever their intersection point lies in both intervals. -/
theorem gridGraph_cross_connected {n : ℕ}
    (row col rowLo rowHi colLo colHi : Fin n)
    (hr : rowLo ≤ row ∧ row ≤ rowHi)
    (hc : colLo ≤ col ∧ col ≤ colHi) :
    GraphConnected ((gridGraph n).induce
      (((fun c : Fin n ↦ (row, c)) '' Icc colLo colHi) ∪
       ((fun r : Fin n ↦ (r, col)) '' Icc rowLo rowHi))) := by
  apply graphConnected_induce_union
    (gridGraph_horizontal_interval_connected row colLo colHi (hc.1.trans hc.2))
    (gridGraph_vertical_interval_connected col rowLo rowHi (hr.1.trans hr.2))
  exact ⟨(row, col), ⟨col, hc, rfl⟩, ⟨row, hr, rfl⟩⟩

end GraphMinor.GM01
