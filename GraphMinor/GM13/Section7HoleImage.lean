module

public import GraphMinor.GM13.Section7HoleBand

/-!
# Graph Minors XIII, (7.3): the faces of the hole at each element

For every element `m` of the old wall (height `h' + 2`), the faces of the new wall that contain
the faces at `m` are exactly the faces of the new wall at `Hole.cell Y0 c0 m`
(`Hole.pi_image_cellFaces`). When `m` is kept, `Hole.cell Y0 c0 m` is the new element that
contains it. When `m` is not kept, it is a cell outside the new wall, so all faces at `m` go to
one face.

Off the band the hole moves squares without changing their shape: by `(0, 0)` left of the cut,
by `(-4, 0)` right of it, by `(-2, -2)` above the band, and it sends the five columns of the cut
to the single column `c0 - 1`. In these regions the claim holds square by square
(`image_of_newSq_eq`, `image_of_newSq_col`). The band is done in `Section7HoleBand.lean`.
-/

public section

namespace GraphMinor.GM13

open Set

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- Where the hole moves every square around `m` by `(-i, -j)`, it moves the faces at `m` to the
faces at the moved cell. -/
theorem image_of_newSq_eq (hp : Params h' Y0 c0) {a b i j : ℤ}
    (hv : ∀ x y : ℤ, 2 * x ≤ a → a ≤ 2 * x + 2 → 2 * y ≤ b → b ≤ 2 * y + 2 →
      newSq Y0 c0 (x, y) = (x - i, y - j)) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (a, b) = cellFaces h' (a - 2 * i, b - 2 * j) := by
  ext F
  simp only [mem_image]
  rw [mem_cellFaces_iff_sq]
  constructor
  · rintro ⟨G, hG, rfl⟩
    obtain ⟨x, y, h1, h2, h3, h4, rfl⟩ := mem_cellFaces_iff_sq.mp hG
    refine ⟨x - i, y - j, by omega, by omega, by omega, by omega, ?_⟩
    rw [pi_sqFace hp, hv x y h1 h2 h3 h4]
  · rintro ⟨x, y, h1, h2, h3, h4, rfl⟩
    refine ⟨sqFace (h' + 2) (x + i, y + j),
      mem_cellFaces_iff_sq.mpr ⟨x + i, y + j, by omega, by omega, by omega, by omega, rfl⟩, ?_⟩
    rw [pi_sqFace hp, hv (x + i) (y + j) (by omega) (by omega) (by omega) (by omega)]
    simp

/-- Where the hole sends every square around `m` to the column `k` of the same row, it sends the
faces at `m` to the faces at the cell of column `2 k + 1` in the same row. -/
theorem image_of_newSq_col (hp : Params h' Y0 c0) {a b k : ℤ}
    (hv : ∀ x y : ℤ, 2 * x ≤ a → a ≤ 2 * x + 2 → 2 * y ≤ b → b ≤ 2 * y + 2 →
      newSq Y0 c0 (x, y) = (k, y)) :
    pi h' Y0 c0 '' cellFaces (h' + 2) (a, b) = cellFaces h' (2 * k + 1, b) := by
  ext F
  simp only [mem_image]
  rw [mem_cellFaces_iff_sq]
  constructor
  · rintro ⟨G, hG, rfl⟩
    obtain ⟨x, y, h1, h2, h3, h4, rfl⟩ := mem_cellFaces_iff_sq.mp hG
    refine ⟨k, y, by omega, by omega, by omega, by omega, ?_⟩
    rw [pi_sqFace hp, hv x y h1 h2 h3 h4]
  · rintro ⟨x, y, h1, h2, h3, h4, rfl⟩
    refine ⟨sqFace (h' + 2) (a / 2, y),
      mem_cellFaces_iff_sq.mpr ⟨a / 2, y, by omega, by omega, by omega, by omega, rfl⟩, ?_⟩
    rw [pi_sqFace hp, hv (a / 2) y (by omega) (by omega) (by omega) (by omega)]
    congr 2
    omega

/-- Evaluates `newSq` on a square whose position is fixed by the hypotheses. -/
macro "newSq_tac" : tactic => `(tactic| (
  intro u v h1 h2 h3 h4
  simp (disch := omega) only [newSq, if_pos, if_neg, ↓reduceIte]
  all_goals (try split_ifs) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega))

/-- Proves that `Hole.cell` has a given value, with the position fixed by the hypotheses. -/
macro "cell_tac" : tactic => `(tactic| (
  simp (disch := omega) only [cell_vertex, cell_horiz, cell_vert, vertexCell, horizCell, vertCell,
    if_pos, if_neg, ↓reduceIte]
  all_goals (try split_ifs) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega))

/-- **The faces of the hole at each element.** -/
theorem pi_image_cellFaces (hp : Params h' Y0 c0) {m : ℤ × ℤ} (hm : IsWallCell (h' + 2) m) :
    pi h' Y0 c0 '' cellFaces (h' + 2) m = cellFaces h' (cell Y0 c0 m) := by
  rcases Hole.cell_cases hm with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · -- a vertex
    rcases (by omega : Y0 + 2 ≤ y ∨ y = Y0 ∨ y = Y0 + 1 ∨ (y ≤ Y0 - 1 ∧ x ≤ c0 - 1) ∨
      (y ≤ Y0 - 1 ∧ c0 + 4 ≤ x) ∨ (y ≤ Y0 - 1 ∧ c0 ≤ x ∧ x ≤ c0 + 3)) with
      hy | rfl | rfl | ⟨hy, hx⟩ | ⟨hy, hx⟩ | ⟨hy, hx, hx'⟩
    · rw [image_of_newSq_eq hp (i := 2) (j := 2) (by newSq_tac)]
      congr 1; cell_tac
    · exact band_vertex0 hp x
    · exact band_vertex1 hp x
    · rw [image_of_newSq_eq hp (i := 0) (j := 0) (by newSq_tac)]
      congr 1; cell_tac
    · rw [image_of_newSq_eq hp (i := 4) (j := 0) (by newSq_tac)]
      congr 1; cell_tac
    · rw [image_of_newSq_col hp (k := c0 - 1) (by newSq_tac)]
      congr 1; cell_tac
  · -- a horizontal edge
    rcases (by omega : Y0 + 2 ≤ y ∨ y = Y0 ∨ y = Y0 + 1 ∨ (y ≤ Y0 - 1 ∧ x ≤ c0 - 1) ∨
      (y ≤ Y0 - 1 ∧ c0 + 3 ≤ x) ∨ (y ≤ Y0 - 1 ∧ c0 ≤ x ∧ x ≤ c0 + 2)) with
      hy | rfl | rfl | ⟨hy, hx⟩ | ⟨hy, hx⟩ | ⟨hy, hx, hx'⟩
    · rw [image_of_newSq_eq hp (i := 2) (j := 2) (by newSq_tac)]
      congr 1; cell_tac
    · exact band_horiz0 hp x
    · exact band_horiz1 hp x
    · rw [image_of_newSq_eq hp (i := 0) (j := 0) (by newSq_tac)]
      congr 1; cell_tac
    · rw [image_of_newSq_eq hp (i := 4) (j := 0) (by newSq_tac)]
      congr 1; cell_tac
    · rw [image_of_newSq_col hp (k := c0 - 1) (by newSq_tac)]
      congr 1; cell_tac
  · -- a vertical edge
    have hpar : (x + y) % 2 = 1 := by
      have := (isWallCell_vert_iff (h := h' + 2) (x := x) (y := y)).mp hm
      omega
    rcases (by omega : Y0 + 1 ≤ y ∨ y = Y0 ∨ (y ≤ Y0 - 1 ∧ x ≤ c0 - 1) ∨
      (y ≤ Y0 - 1 ∧ c0 + 4 ≤ x) ∨ (y ≤ Y0 - 1 ∧ c0 ≤ x ∧ x ≤ c0 + 3)) with
      hy | rfl | ⟨hy, hx⟩ | ⟨hy, hx⟩ | ⟨hy, hx, hx'⟩
    · rw [image_of_newSq_eq hp (i := 2) (j := 2) (by newSq_tac)]
      congr 1; cell_tac
    · exact band_vert hp x (by omega)
    · rw [image_of_newSq_eq hp (i := 0) (j := 0) (by newSq_tac)]
      congr 1; cell_tac
    · rw [image_of_newSq_eq hp (i := 4) (j := 0) (by newSq_tac)]
      congr 1; cell_tac
    · rw [image_of_newSq_col hp (k := c0 - 1) (by newSq_tac)]
      congr 1; cell_tac

/-- A kept element keeps its faces: they go onto the faces at its owner. -/
theorem image_cellFaces_of_own (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h')
    {m m' : ℤ × ℤ}
    (hm : m ∈ fig1WallCells (h' + 2)) (hown : own h' Y0 c0 m = some m') :
    pi h' Y0 c0 '' cellFaces (h' + 2) m = cellFaces h' m' := by
  have hm' : IsWallCell (h' + 2) m :=
    (mem_fig1WallCells_iff (by omega) (even_succ_succ he') _).mp hm
  unfold own at hown
  split_ifs at hown
  cases hown
  exact pi_image_cellFaces hp hm'

/-- All faces at an element that is not kept go to one face. -/
theorem pi_eq_of_own_none (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') {m : ℤ × ℤ}
    (hm : m ∈ fig1WallCells (h' + 2)) (hown : own h' Y0 c0 m = none) {F G : ℤ × ℤ}
    (hF : F ∈ cellFaces (h' + 2) m) (hG : G ∈ cellFaces (h' + 2) m) :
    pi h' Y0 c0 F = pi h' Y0 c0 G := by
  have hm' : IsWallCell (h' + 2) m :=
    (mem_fig1WallCells_iff (by omega) (even_succ_succ he') _).mp hm
  have hn : cell Y0 c0 m ∉ fig1WallCells h' := by
    rw [mem_fig1WallCells_iff hh' he']
    intro hc
    unfold own at hown
    rw [if_pos hc] at hown
    exact absurd hown (by simp)
  have h1 : pi h' Y0 c0 F ∈ cellFaces h' (cell Y0 c0 m) := by
    rw [← pi_image_cellFaces hp hm']; exact mem_image_of_mem _ hF
  have h2 : pi h' Y0 c0 G ∈ cellFaces h' (cell Y0 c0 m) := by
    rw [← pi_image_cellFaces hp hm']; exact mem_image_of_mem _ hG
  obtain ⟨q, hq, e⟩ := h1
  obtain ⟨q', hq', e'⟩ := h2
  rw [← e, ← e']
  exact wallFace_eq_of_not_mem hh' he' hn hq hq'

end Hole

end GraphMinor.GM13
