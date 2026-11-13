module

public import GraphMinor.GM13.Section7Choice

/-!
# Graph Minors XIII, (7.3) with `r = 0`, on cells

This file proves (7.3) with `r = 0` for walls drawn on the cells of the grid inside the wall of
Fig. 1 (`theorem_7_3_cellWall`). (7.6) uses (7.3) only with `r = 0`.

For every element `mv` of the elementary wall of height `h' + 2` there is a shape that deletes
`mv` and passes the depth test (`exists_deleting_shape`). The depth test gives `KI 4`
(`Shape.DepthTest.ki`), so the new cell wall has `d' ≥ d - 4` (`CellWall.transform_distGeSub`).
The cells of `mv` are not in the new drawing (`CellWall.not_mem_t𝒰`), so no point of the new
drawing is at distance 0 from a point of `mv`.
-/

public section

namespace GraphMinor.GM13

open Set

/-- **Graph Minors XIII, (7.3) with `r = 0`, for a wall drawn on cells.** "*Let $H$ be a wall of
height $h$ with distance function $d$ and let $v \in V(H)$. Let $r \ge 0$
be an integer with $h \ge 2r + 4$. Then there is a subgraph $H'$ of $H$, which is a wall of
height $h - 2r - 2$, such that*

*(i) $d' \ge d - 4r - 4$, where $d'$ is the distance function in $H'$*

*(ii) there is no vertex $u$ of $H'$ with $d(u, v) \le r$.*" Here `r = 0`, the wall `H` is a cell
wall `C` of height
`h' + 2 ≥ 4`, the vertex `v` lies in the cells of an element `mv`, and `H'` is the cell wall
`C.transform τ` of height `h'`. -/
theorem theorem_7_3_cellWall {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') (C : CellWall (h' + 2))
    {mv : ℤ × ℤ} (hmv : mv ∈ fig1WallCells (h' + 2)) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own mv = none ∧
      DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet (C.transform τ hh' he').𝒰))
        (planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰)) 4 ∧
      ∀ c ∈ C.cells mv, c ∉ (C.transform τ hh' he').𝒰 := by
  obtain ⟨τ, hT, hown, -⟩ := exists_deleting_shape hh' he' hmv
  exact ⟨τ, hT, hown, C.transform_distGeSub τ hh' he' (by norm_num) hT.ki, fun c hc => C.not_mem_t𝒰 τ hmv hown hc⟩

end GraphMinor.GM13
