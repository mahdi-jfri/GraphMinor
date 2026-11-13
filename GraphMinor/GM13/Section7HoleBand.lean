module

public import GraphMinor.GM13.Section7Hole

/-!
# Graph Minors XIII, (7.3): the faces of the hole along its band

The hole `Hole(Y0, c0)` of `Section7Hole.lean` merges the old rows `Y0` and `Y0 + 1` into the new
row `Y0 - 1`. This file computes, for every element of the old wall in the band (the cells
`(a, b)` with `2 Y0 ≤ b ≤ 2 Y0 + 2`), the faces of the new wall that contain its faces. They are
the faces of the new wall at the element `Hole.cell Y0 c0 m`. For an element that is not kept,
`Hole.cell` is a square, and the faces collapse to one.

The squares around a cell are listed explicitly (`cellFaces_vertex` and its companions). The
proof splits the column of the element into the part left of the cut, the five columns of the
cut, and the part right of it, and splits the parities of the column and of `c0` against `Y0`.
In each case every `if` in the formulas is decided, and the remaining statement is linear, which
`omega` proves.
-/

public section

namespace GraphMinor.GM13

open Set

/-! ## The squares around a cell, listed -/

theorem cellFaces_vertex (h : ℕ) (x y : ℤ) : cellFaces h (2 * x, 2 * y) =
    {sqFace h (x - 1, y - 1), sqFace h (x, y - 1), sqFace h (x - 1, y), sqFace h (x, y)} := by
  ext F
  rw [mem_cellFaces_iff_sq]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨u, v, h1, h2, h3, h4, rfl⟩
    have hu : u = x - 1 ∨ u = x := by omega
    have hv : v = y - 1 ∨ v = y := by omega
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨x - 1, y - 1, by omega, by omega, by omega, by omega, rfl⟩
    · exact ⟨x, y - 1, by omega, by omega, by omega, by omega, rfl⟩
    · exact ⟨x - 1, y, by omega, by omega, by omega, by omega, rfl⟩
    · exact ⟨x, y, by omega, by omega, by omega, by omega, rfl⟩

theorem cellFaces_horiz (h : ℕ) (x y : ℤ) : cellFaces h (2 * x + 1, 2 * y) =
    {sqFace h (x, y - 1), sqFace h (x, y)} := by
  ext F
  rw [mem_cellFaces_iff_sq]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨u, v, h1, h2, h3, h4, rfl⟩
    have hu : u = x := by omega
    have hv : v = y - 1 ∨ v = y := by omega
    subst hu
    rcases hv with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨x, y - 1, by omega, by omega, by omega, by omega, rfl⟩
    · exact ⟨x, y, by omega, by omega, by omega, by omega, rfl⟩

theorem cellFaces_vert (h : ℕ) (x y : ℤ) : cellFaces h (2 * x, 2 * y + 1) =
    {sqFace h (x - 1, y), sqFace h (x, y)} := by
  ext F
  rw [mem_cellFaces_iff_sq]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨u, v, h1, h2, h3, h4, rfl⟩
    have hu : u = x - 1 ∨ u = x := by omega
    have hv : v = y := by omega
    subst hv
    rcases hu with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨x - 1, y, by omega, by omega, by omega, by omega, rfl⟩
    · exact ⟨x, y, by omega, by omega, by omega, by omega, rfl⟩

theorem cellFaces_square (h : ℕ) (x y : ℤ) : cellFaces h (2 * x + 1, 2 * y + 1) =
    {sqFace h (x, y)} := by
  ext F
  rw [mem_cellFaces_iff_sq]
  simp only [mem_singleton_iff]
  constructor
  · rintro ⟨u, v, h1, h2, h3, h4, rfl⟩
    have hu : u = x := by omega
    have hv : v = y := by omega
    subst hu hv
    rfl
  · rintro rfl
    exact ⟨x, y, by omega, by omega, by omega, by omega, rfl⟩

/-- A square whose two coordinates have odd sum lies in the brick of the square to its right. -/
theorem sqFace_odd {h : ℕ} {u v : ℤ} (hp : (u + v) % 2 = 1) :
    sqFace h (u, v) = sqFace h (u + 1, v) := by
  rw [sqFace_eq_iff]
  left
  rw [bk_eq_iff]
  omega

theorem sqFace_congr_true {h : ℕ} {u v u' v' : ℤ} (hu : u = u') (hv : v = v') :
    (sqFace h (u, v) = sqFace h (u', v')) = True := by
  subst hu hv
  simp

namespace Hole

/-- Computes both sides of an equation between the new faces at an element and the faces at a
new element. Every square is moved to the square of its brick with even coordinate sum, so two
squares lie in one brick exactly when they are equal, which `omega` decides. -/
macro "band_tac" hp:term : tactic => `(tactic| (
  simp (disch := omega) only [cell_vertex, cell_horiz, cell_vert, vertexCell, horizCell,
    vertCell, if_pos, if_neg, ↓reduceIte, cellFaces_vertex, cellFaces_horiz, cellFaces_vert,
    cellFaces_square, image_insert_eq, image_singleton, pi_sqFace $hp, newSq];
  (try simp (disch := omega) only [sqFace_odd]);
  (try (apply Subset.antisymm <;>
    simp (disch := omega) only [insert_subset_iff, singleton_subset_iff, mem_insert_iff,
      mem_singleton_iff, sqFace_congr_true, true_or, or_true, true_and, and_true, and_self]))))

set_option hygiene false in
/-- Splits the parity of `x` against `Y0`. -/
macro "par_x" x:ident : tactic => `(tactic|
  obtain ⟨t, rfl | rfl⟩ : ∃ t, $x = Y0 + 2 * t ∨ $x = Y0 + 2 * t + 1 :=
    ⟨($x - Y0) / 2, by omega⟩)

set_option hygiene false in
/-- Splits the parity of `c0` against `Y0`. -/
macro "par_c" : tactic => `(tactic|
  obtain ⟨w, rfl | rfl⟩ : ∃ w, c0 = Y0 + 2 * w ∨ c0 = Y0 + 2 * w + 1 :=
    ⟨(c0 - Y0) / 2, by omega⟩)

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- The vertices of the old row `Y0`. -/
theorem band_vertex0 (hp : Params h' Y0 c0) (x : ℤ) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (2 * x, 2 * Y0) =
      cellFaces h' (cell Y0 c0 (2 * x, 2 * Y0)) := by
  rcases (by omega : x ≤ c0 - 1 ∨ c0 + 5 ≤ x ∨ x = c0 ∨ x = c0 + 1 ∨ x = c0 + 2 ∨
    x = c0 + 3 ∨ x = c0 + 4) with hx | hx | hx | hx | hx | hx | hx
  · par_x x <;> band_tac hp
  · par_x x <;> band_tac hp
  all_goals (rw [hx]; par_c <;> band_tac hp)

/-- The horizontal edges of the old row `Y0`. -/
theorem band_horiz0 (hp : Params h' Y0 c0) (x : ℤ) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (2 * x + 1, 2 * Y0) =
      cellFaces h' (cell Y0 c0 (2 * x + 1, 2 * Y0)) := by
  rcases (by omega : x ≤ c0 - 1 ∨ c0 + 3 ≤ x ∨ x = c0 ∨ x = c0 + 1 ∨ x = c0 + 2) with
    hx | hx | hx | hx | hx
  · par_x x <;> band_tac hp
  · par_x x <;> band_tac hp
  all_goals (rw [hx]; par_c <;> band_tac hp)

/-- The vertical edges between the old rows `Y0` and `Y0 + 1`. -/
theorem band_vert (hp : Params h' Y0 c0) (x : ℤ) (hx2 : (x + Y0) % 2 = 1) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (2 * x, 2 * Y0 + 1) =
      cellFaces h' (cell Y0 c0 (2 * x, 2 * Y0 + 1)) := by
  rcases (by omega : x ≤ c0 ∨ c0 + 3 ≤ x ∨ x = c0 + 1 ∨ x = c0 + 2) with hx | hx | hx | hx
  · par_x x <;> first | omega | band_tac hp
  · par_x x <;> first | omega | band_tac hp
  all_goals (rw [hx]; par_c <;> first | omega | band_tac hp)

/-- The vertices of the old row `Y0 + 1`. -/
theorem band_vertex1 (hp : Params h' Y0 c0) (x : ℤ) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (2 * x, 2 * (Y0 + 1)) =
      cellFaces h' (cell Y0 c0 (2 * x, 2 * (Y0 + 1))) := by
  rcases (by omega : x ≤ c0 ∨ c0 + 3 ≤ x ∨ x = c0 + 1 ∨ x = c0 + 2) with hx | hx | hx | hx
  · par_x x <;> band_tac hp
  · par_x x <;> band_tac hp
  all_goals (rw [hx]; par_c <;> band_tac hp)

/-- The horizontal edges of the old row `Y0 + 1`. -/
theorem band_horiz1 (hp : Params h' Y0 c0) (x : ℤ) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (2 * x + 1, 2 * (Y0 + 1)) =
      cellFaces h' (cell Y0 c0 (2 * x + 1, 2 * (Y0 + 1))) := by
  rcases (by omega : x ≤ c0 ∨ c0 + 2 ≤ x ∨ x = c0 + 1) with hx | hx | hx
  · par_x x <;> band_tac hp
  · par_x x <;> band_tac hp
  all_goals (rw [hx]; par_c <;> band_tac hp)

end Hole

end GraphMinor.GM13
