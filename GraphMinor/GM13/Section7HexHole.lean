module

public import GraphMinor.GM13.Section7Hole

/-!
# Graph Minors XIII, (7.3): a hexagonal hole

This file starts the proof of (7.3) of *Graph Minors XIII* (page 90) for a vertex `v` deep inside
the wall. For `r ≥ 1` we write `k = r + 1` and `b = k - 1 = r`. A wall of height `h'` is found
inside a wall of height `h' + 2k = h' + 2b + 2` with a hole around `v`. The hole is a hexagon of
bricks; every brick at hex distance at most `b` from its centre lies in one face of the new wall.

The new wall is drawn as follows. Its vertex `(x, y)` is the old vertex `(x + sL, y)` when
`x < c0` and `(x + sL + 2b, y)` when `x ≥ c0`, and the old row is `y` below the new row `Y0` and
`y + 2b` from row `Y0` on. So `sL` columns are lost at the left side, `2b` columns are cut out at
`c0`, `2b + 4 - sL` columns are lost at the right side, and the two top rows of the old wall are
not used. The `2b` old rows `Y0, …, Y0 + 2b - 1` form a band. A vertical edge of the new wall
from row `Y0 - 1` to row `Y0` becomes a staircase through the band: left of the cut it goes up,
moves one step to the left, and so on `b` times, then it moves back to the right `b` times; right
of the cut it does the mirror image. Between the last staircase left of the cut and the first one
right of it lies the hole.

We describe the hole on unit squares, as `Hole.newSq` does for the hole of `Section7Hole.lean`:
the square `(u, v)` is the cell `(2u + 1, 2v + 1)`. In the band row `v = Y0 + t`, the left
staircases sit `off b t` columns from their place below the band (`HexHole.off`), and the map
`HexHole.newSq` sends each old square to a square of the new wall in the same new face. The new
element that contains each old element is given by `HexHole.vertexCell`, `HexHole.horizCell` and
`HexHole.vertCell`. These formulas were found by a computer search before the proof. The Lean
proof does not rely on the search.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

namespace HexHole

/-- The column offset of a left staircase in the band row `Y0 + t`: it moves one step left in each
of the first `b` rows and one step back in each of the last `b` rows. Below the band (`t = -1`) it
is `0`. -/
def off (b : ℕ) (t : ℤ) : ℤ := if t + 1 ≤ b then -(t + 1) else -(2 * b - t - 1)

/-- The new column of an old column `u` of squares in a row where the left staircases are `o`
columns from their place: left of the hole, right of it, or the column `c0 - 1` of the hole. -/
def side (b : ℕ) (c0 sL : ℤ) (o u : ℤ) : ℤ :=
  if u - sL - o ≤ c0 - 1 then u - sL - o
  else if c0 ≤ u - sL - 2 * b + o then u - sL - 2 * b + o else c0 - 1

/-- The new square that contains an old unit square `s`. -/
def newSq (b : ℕ) (Y0 c0 sL : ℤ) (s : ℤ × ℤ) : ℤ × ℤ :=
  if s.2 ≤ Y0 - 1 then (side b c0 sL 0 s.1, s.2)
  else if Y0 + 2 * b ≤ s.2 then (side b c0 sL 0 s.1, s.2 - 2 * b)
  else (side b c0 sL (off b (s.2 - Y0)) s.1, Y0 - 1)

/-- The face of the new wall (height `h'`) that contains the face `F` of the old wall (height
`h' + 2b + 2`). -/
def pi (h' b : ℕ) (Y0 c0 sL : ℤ) (F : ℤ × ℤ) : ℤ × ℤ :=
  if IsBrick (h' + 2 * b + 2) F then sqFace h' (newSq b Y0 c0 sL F) else outFace

/-- The new element that contains the old vertex `(x, y)`. In the band row `Y0 + t` the vertex
lies on the staircase of the new column `x'`, which depends on the parity `(x + y) % 2`. -/
def vertexCell (b : ℕ) (Y0 c0 sL x y : ℤ) : ℤ × ℤ :=
  if y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y then
    (if x - sL ≤ c0 - 1 then (2 * (x - sL), 2 * (if y ≤ Y0 - 1 then y else y - 2 * b))
      else if c0 ≤ x - sL - 2 * b then
        (2 * (x - sL - 2 * b), 2 * (if y ≤ Y0 - 1 then y else y - 2 * b))
      else (2 * (c0 - 1) + 1, 2 * (if y ≤ Y0 - 1 then y else y - 2 * b)))
  else if y - Y0 + 1 ≤ b then
    (if x - sL + (y - Y0) + (x + y) % 2 ≤ c0 - 1 then
        (2 * (x - sL + (y - Y0) + (x + y) % 2), 2 * (Y0 - 1) + 1)
      else if c0 ≤ x - sL - 2 * b - (y - Y0) - (x + y) % 2 then
        (2 * (x - sL - 2 * b - (y - Y0) - (x + y) % 2), 2 * (Y0 - 1) + 1)
      else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))
  else
    (if x - sL + 2 * b - (y - Y0) - (x + y) % 2 ≤ c0 - 1 then
        (2 * (x - sL + 2 * b - (y - Y0) - (x + y) % 2), 2 * (Y0 - 1) + 1)
      else if c0 ≤ x - sL - 4 * b + (y - Y0) + (x + y) % 2 then
        (2 * (x - sL - 4 * b + (y - Y0) + (x + y) % 2), 2 * (Y0 - 1) + 1)
      else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))

/-- The new element that contains the old horizontal edge from `(x, y)` to `(x + 1, y)`. In the
band it is a step of a staircase, or it is deleted and goes to the new square above it. -/
def horizCell (b : ℕ) (Y0 c0 sL x y : ℤ) : ℤ × ℤ :=
  if y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y then
    (if x + 1 - sL ≤ c0 - 1 then (2 * (x - sL) + 1, 2 * (if y ≤ Y0 - 1 then y else y - 2 * b))
      else if c0 ≤ x - sL - 2 * b then
        (2 * (x - sL - 2 * b) + 1, 2 * (if y ≤ Y0 - 1 then y else y - 2 * b))
      else (2 * (c0 - 1) + 1, 2 * (if y ≤ Y0 - 1 then y else y - 2 * b)))
  else if y - Y0 + 1 ≤ b then
    (if (x + y) % 2 = 1 ∧ x - sL + (y - Y0) + 1 ≤ c0 - 1 then
        (2 * (x - sL + (y - Y0) + 1), 2 * (Y0 - 1) + 1)
      else if (x + y) % 2 = 0 ∧ c0 ≤ x - sL - 2 * b - (y - Y0) then
        (2 * (x - sL - 2 * b - (y - Y0)), 2 * (Y0 - 1) + 1)
      else (2 * (newSq b Y0 c0 sL (x, y)).1 + 1, 2 * (Y0 - 1) + 1))
  else
    (if (x + y) % 2 = 0 ∧ x - sL + 2 * b - (y - Y0) ≤ c0 - 1 then
        (2 * (x - sL + 2 * b - (y - Y0)), 2 * (Y0 - 1) + 1)
      else if (x + y) % 2 = 1 ∧ c0 ≤ x - sL - 4 * b + (y - Y0) + 1 then
        (2 * (x - sL - 4 * b + (y - Y0) + 1), 2 * (Y0 - 1) + 1)
      else (2 * (newSq b Y0 c0 sL (x, y)).1 + 1, 2 * (Y0 - 1) + 1))

/-- The new element that contains the old vertical edge from `(x, y)` to `(x, y + 1)`. In the band
every such edge lies on a staircase, except in the hole. -/
def vertCell (b : ℕ) (Y0 c0 sL x y : ℤ) : ℤ × ℤ :=
  if y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y then
    (if x - sL ≤ c0 - 1 then (2 * (x - sL), 2 * (if y ≤ Y0 - 1 then y else y - 2 * b) + 1)
      else if c0 ≤ x - sL - 2 * b then
        (2 * (x - sL - 2 * b), 2 * (if y ≤ Y0 - 1 then y else y - 2 * b) + 1)
      else (2 * (c0 - 1) + 1, 2 * (if y ≤ Y0 - 1 then y else y - 2 * b) + 1))
  else
    (if x - sL - off b (y - Y0) ≤ c0 - 1 then (2 * (x - sL - off b (y - Y0)), 2 * (Y0 - 1) + 1)
      else if c0 ≤ x - sL - 2 * b + off b (y - Y0) then
        (2 * (x - sL - 2 * b + off b (y - Y0)), 2 * (Y0 - 1) + 1)
      else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))

/-- The new element that contains the old element with cell `m`, before the test that it is an
element of the new wall. For an element that is not kept, it is a cell outside the new wall in
the new face that contains the element. -/
def cell (b : ℕ) (Y0 c0 sL : ℤ) (m : ℤ × ℤ) : ℤ × ℤ :=
  if m.2 % 2 = 0 then
    (if m.1 % 2 = 0 then vertexCell b Y0 c0 sL (m.1 / 2) (m.2 / 2)
      else horizCell b Y0 c0 sL (m.1 / 2) (m.2 / 2))
  else vertCell b Y0 c0 sL (m.1 / 2) (m.2 / 2)

/-- The new element that contains the old element with cell `m`, if it is kept. -/
def own (h' b : ℕ) (Y0 c0 sL : ℤ) (m : ℤ × ℤ) : Option (ℤ × ℤ) :=
  if IsWallCell h' (cell b Y0 c0 sL m) then some (cell b Y0 c0 sL m) else none

/-- The range of the parameters of a hexagonal hole: the band starts at a row `Y0` of the new
wall, the cut at a column `c0` of it, and the staircases fit between the sides. -/
structure Params (h' b : ℕ) (Y0 c0 sL : ℤ) : Prop where
  Y1 : 1 ≤ Y0
  Y2 : Y0 ≤ h'
  c1 : 1 ≤ c0
  c2 : c0 ≤ 2 * h' + 1
  sL1 : b ≤ sL
  sL2 : sL ≤ b + 4
  sLe : sL % 2 = 0
  b1 : 1 ≤ b

theorem cell_vertex (b : ℕ) (Y0 c0 sL x y : ℤ) :
    cell b Y0 c0 sL (2 * x, 2 * y) = vertexCell b Y0 c0 sL x y := by
  unfold cell
  rw [if_pos (by simp), if_pos (by simp)]
  congr 1 <;> simp

theorem cell_horiz (b : ℕ) (Y0 c0 sL x y : ℤ) :
    cell b Y0 c0 sL (2 * x + 1, 2 * y) = horizCell b Y0 c0 sL x y := by
  unfold cell
  rw [if_pos (by omega), if_neg (by omega)]
  congr 1 <;> omega

theorem cell_vert (b : ℕ) (Y0 c0 sL x y : ℤ) :
    cell b Y0 c0 sL (2 * x, 2 * y + 1) = vertCell b Y0 c0 sL x y := by
  unfold cell
  rw [if_neg (by omega)]
  congr 1 <;> omega

/-- Cleans the logic constants from all hypotheses and the goal, then calls `omega`. -/
macro "hex_omega" : tactic => `(tactic| ((try simp only [Prod.mk.injEq, true_and, and_true, not_true_eq_false, false_and, and_false, or_false, false_or, not_false_eq_true, true_or, or_true, not_and, not_le, not_lt, true_iff, iff_true, imp_false, true_implies, implies_true] at *) <;> first | done | trivial | omega))

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- Two squares of one old brick have new squares in one new face. -/
theorem newSq_bk (hp : Params h' b Y0 c0 sL) (s : ℤ × ℤ) (hb : IsBrick (h' + 2 * b + 2) (bk s)) :
    bk (newSq b Y0 c0 sL (bk s)) = bk (newSq b Y0 c0 sL s) ∨
      (¬ IsBrick h' (bk (newSq b Y0 c0 sL (bk s))) ∧ ¬ IsBrick h' (bk (newSq b Y0 c0 sL s))) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  obtain ⟨x, y⟩ := s
  rcases Int.emod_two_eq_zero_or_one (x + y) with hp | hp
  · have : bk (x, y) = (x, y) := by simp [bk, hp]
    rw [this]; exact Or.inl rfl
  have e : bk (x, y) = (x + 1, y) := by simp [bk, hp]
  rw [e]
  rw [e] at hb
  simp only [IsBrick] at hb
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 - y := ⟨(x + y) / 2, by omega⟩
  simp only [newSq, side, off]
  split_ifs <;> simp only [bk, IsBrick] <;> hex_omega

/-- A square outside the old wall has its new square outside the new wall. -/
theorem newSq_out (hp : Params h' b Y0 c0 sL) (s : ℤ × ℤ) (hb : ¬ IsBrick (h' + 2 * b + 2) (bk s)) :
    ¬ IsBrick h' (bk (newSq b Y0 c0 sL s)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  obtain ⟨x, y⟩ := s
  simp only [IsBrick, bk] at hb
  simp only [newSq, side, off]
  split_ifs <;> simp only [bk, IsBrick] <;> hex_omega

/-- **The face map on squares.** -/
theorem pi_sqFace (hp : Params h' b Y0 c0 sL) (s : ℤ × ℤ) :
    pi h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) s) = sqFace h' (newSq b Y0 c0 sL s) := by
  rw [sqFace_eq (h' + 2 * b + 2) s]
  split_ifs with hb
  · unfold pi
    rw [if_pos hb]
    exact sqFace_eq_iff.mpr (newSq_bk hp s hb)
  · unfold pi
    rw [if_neg (not_isBrick_outFace _)]
    exact (sqFace_eq_out_iff.mpr (newSq_out hp s hb)).symm

theorem even_add_two_mul_add_two {h' : ℕ} (he' : Even h') (b : ℕ) : Even (h' + 2 * b + 2) := by
  obtain ⟨a, ha⟩ := he'
  exact ⟨a + b + 1, by omega⟩

theorem own_mem (hh' : 1 ≤ h') (he' : Even h') {m m' : ℤ × ℤ}
    (hm : own h' b Y0 c0 sL m = some m') : m' ∈ fig1WallCells h' := by
  unfold own at hm
  split_ifs at hm with h1
  cases hm
  exact (mem_fig1WallCells_iff hh' he' _).mpr h1

theorem own_eq_some {m m' : ℤ × ℤ} (h1 : cell b Y0 c0 sL m = m') (h2 : IsWallCell h' m') :
    own h' b Y0 c0 sL m = some m' := by
  subst h1
  unfold own
  rw [if_pos h2]

theorem pi_face (F : ℤ × ℤ) : IsWallFace h' (pi h' b Y0 c0 sL F) := by
  unfold pi
  split_ifs
  · exact isWallFace_sqFace h' _
  · exact Or.inr rfl

theorem pi_outFace : pi h' b Y0 c0 sL outFace = outFace := by
  unfold pi
  rw [if_neg (not_isBrick_outFace _)]

/-- The old square whose new square is `s'`. -/
def sqInv (b : ℕ) (Y0 c0 sL : ℤ) (s' : ℤ × ℤ) : ℤ × ℤ :=
  (if s'.1 ≤ c0 - 1 then s'.1 + sL else s'.1 + sL + 2 * b,
    if s'.2 ≤ Y0 - 1 then s'.2 else s'.2 + 2 * b)

theorem newSq_sqInv (s' : ℤ × ℤ) : newSq b Y0 c0 sL (sqInv b Y0 c0 sL s') = s' := by
  obtain ⟨x, y⟩ := s'
  simp only [newSq, sqInv, side]
  split_ifs <;> hex_omega

theorem pi_surj (hp : Params h' b Y0 c0 sL) {F' : ℤ × ℤ} (hF' : IsWallFace h' F') :
    ∃ F, IsWallFace (h' + 2 * b + 2) F ∧ pi h' b Y0 c0 sL F = F' := by
  rcases hF' with hb | rfl
  · refine ⟨sqFace (h' + 2 * b + 2) (sqInv b Y0 c0 sL F'), isWallFace_sqFace _ _, ?_⟩
    rw [pi_sqFace hp, newSq_sqInv, sqFace_eq_brick_iff hb]
    obtain ⟨X, Y⟩ := F'
    simp only [IsBrick] at hb
    simp only [bk]
    hex_omega
  · exact ⟨outFace, Or.inr rfl, pi_outFace⟩

theorem vertexCell_inv (hb : 1 ≤ b) (x y : ℤ) :
    vertexCell b Y0 c0 sL (if x ≤ c0 - 1 then x + sL else x + sL + 2 * b)
      (if y ≤ Y0 - 1 then y else y + 2 * b) = (2 * x, 2 * y) := by
  unfold vertexCell
  split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

theorem horizCell_inv (hb : 1 ≤ b) (x y : ℤ) :
    horizCell b Y0 c0 sL (if x ≤ c0 - 1 then x + sL else x + sL + 2 * b)
      (if y ≤ Y0 - 1 then y else y + 2 * b) = (2 * x + 1, 2 * y) := by
  unfold horizCell
  split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

theorem vertCell_inv (hb : 1 ≤ b) (x y : ℤ) :
    vertCell b Y0 c0 sL (if x ≤ c0 - 1 then x + sL else x + sL + 2 * b)
      (if y ≤ Y0 - 1 then y else y + 2 * b) = (2 * x, 2 * y + 1) := by
  unfold vertCell
  split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

theorem own_surj (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {m' : ℤ × ℤ}
    (hm' : m' ∈ fig1WallCells h') :
    ∃ m ∈ fig1WallCells (h' + 2 * b + 2), own h' b Y0 c0 sL m = some m' := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  have hw := (mem_fig1WallCells_iff hh' he' _).mp hm'
  have hw' := hw
  simp only [mem_fig1WallCells_iff (by omega : 1 ≤ h' + 2 * b + 2)
    (even_add_two_mul_add_two he' b)]
  rcases Hole.cell_cases hw with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · -- a vertex
    unfold IsWallCell at hw
    simp only at hw
    refine ⟨(2 * (if x ≤ c0 - 1 then x + sL else x + sL + 2 * b),
      2 * (if y ≤ Y0 - 1 then y else y + 2 * b)), ?_, own_eq_some ?_ hw'⟩
    · unfold IsWallCell; simp only; push_cast; split_ifs <;> hex_omega
    · rw [cell_vertex]; exact vertexCell_inv (by omega) x y
  · -- a horizontal edge
    unfold IsWallCell at hw
    simp only at hw
    refine ⟨(2 * (if x ≤ c0 - 1 then x + sL else x + sL + 2 * b) + 1,
      2 * (if y ≤ Y0 - 1 then y else y + 2 * b)), ?_, own_eq_some ?_ hw'⟩
    · unfold IsWallCell; simp only; push_cast; split_ifs <;> hex_omega
    · rw [cell_horiz]; exact horizCell_inv (by omega) x y
  · -- a vertical edge
    unfold IsWallCell at hw
    simp only at hw
    refine ⟨(2 * (if x ≤ c0 - 1 then x + sL else x + sL + 2 * b),
      2 * (if y ≤ Y0 - 1 then y else y + 2 * b) + 1), ?_, own_eq_some ?_ hw'⟩
    · unfold IsWallCell; simp only; push_cast; split_ifs <;> hex_omega
    · rw [cell_vert]; exact vertCell_inv (by omega) x y

end HexHole

end GraphMinor.GM13
