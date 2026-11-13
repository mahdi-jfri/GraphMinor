module

public import GraphMinor.Compute.GM13WallCertificate

/-!
# Integer thresholds in Graph Minors XIII, (7.1)

The threshold in (7.1) is a rational number. Since widths are integers, its
ceiling is the minor threshold, whereas its floor is the parameter of (3.3).
If the wall test fails, the ceiling threshold bounds the width by the floor.
-/

public section
namespace GraphMinor.Compute
open GraphMinor GM13

/-- The failed wall test in XIII (7.1), page 89, bounds the input width.
This accounts for integer rounding before applying (3.3). -/
theorem width_of_no_wall71 {h Ω n : ℕ} (G : MultiDigraph n)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ((Ω + 2) / 3))
    (hno : ¬ HasDigraphModel (elemWallEdges h) G) :
    GraphBranchWidthLE G.toGMDigraph.toGraph (Ω / 3) := by
  classical
  by_contra hbw
  apply hno
  apply h71
  constructor
  · by_contra he
    have he' : G.numEdges ≤ 1 := by omega
    exact hbw (HasBranchDecompOfWidthLe.graphBranchWidthLE (Or.inl he'))
  · intro B hB hdec
    have hBk : B ≤ Ω / 3 := by omega
    exact hbw (graphBranchWidthLE_mono_width hBk hdec.graphBranchWidthLE)

/-- The hypothesis of XIII (7.1) forces the search parameter of (3.3) to
be at least two. A pair of parallel edges excludes smaller thresholds. -/
theorem two_le_search_parameter71 {h Ω : ℕ} (hh : 2 ≤ h)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ((Ω + 2) / 3)) :
    2 ≤ Ω / 3 := by
  have := three_le_wall_threshold71 hh h71
  omega

end GraphMinor.Compute
