module

public import GraphMinor.GM13.Section7HexHole
public import GraphMinor.GM13.Section7HoleBand

/-!
# Graph Minors XIII, (7.3): the faces of the hexagonal hole at each element

For every element `m` of the old wall (height `h' + 2b + 2`), the faces of the new wall that
contain the faces at `m` are exactly the faces of the new wall at `HexHole.cell b Y0 c0 sL m`
(`HexHole.pi_image_cellFaces`). When `m` is kept, this cell is the new element that contains
`m`. When `m` is not kept, it is a cell outside the new wall, so all faces at `m` go to one face
(`HexHole.pi_eq_of_own_none`).

Each proof writes the faces at `m` as the faces of its two or four unit squares
(`cellFaces_vertex`, `cellFaces_horiz`, `cellFaces_vert`), moves each square with `newSq`, and
then splits by the column of `m`, so that every `if` in `newSq` and in the cell is decided. In
each case the two sides are equal sets of at most four faces; `sqFace_odd` moves each square to
the square of its brick, after which equal faces have equal coordinates.

Off the band (`off_vertex`, `off_horiz`, `off_vert`) the hole only shifts columns. In the band we
split by the half of the band (the staircases move left in the first `b` rows and back in the
last `b` rows) and by the parity of the vertex.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

theorem newSq_band {u v : ℤ} (h1 : Y0 - 1 ≤ v) (h2 : v ≤ Y0 + 2 * b - 1) :
    newSq b Y0 c0 sL (u, v) = (side b c0 sL (off b (v - Y0)) u, Y0 - 1) := by
  unfold newSq
  by_cases hv : v ≤ Y0 - 1
  · have hv' : v = Y0 - 1 := by omega
    subst hv'
    simp only [hv, ite_true, Prod.mk.injEq, and_true]
    congr 1
    unfold off
    rw [if_pos (by omega)]
    ring
  · rw [if_neg hv, if_neg (by simp only; omega)]

/-- Decides every `if` of the new squares and of the new cell from the hypotheses, moves every
square to the square of its brick with even coordinate sum, and compares the two sets of faces. -/
macro "band_case" : tactic => `(tactic| (
  simp (disch := omega) only [side, if_pos, if_neg, ↓reduceIte, true_and, and_true, false_and,
    and_false]
  (try rw [cellFaces_vertex])
  (try rw [cellFaces_horiz])
  (try rw [cellFaces_vert])
  (try rw [cellFaces_square])
  (try simp (disch := omega) only [sqFace_odd])
  first
  | done
  | (apply Subset.antisymm <;>
      simp (disch := omega) only [insert_subset_iff, singleton_subset_iff, mem_insert_iff,
        mem_singleton_iff, sqFace_congr_true, true_or, or_true, true_and, and_true, and_self])))

set_option linter.unusedSimpArgs false

theorem band_vertex_first (hp : Params h' b Y0 c0 sL) (x t : ℤ) (ht1 : 0 ≤ t)
    (ht2 : t + 1 ≤ b) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x, 2 * (Y0 + t)) =
      cellFaces h' (vertexCell b Y0 c0 sL x (Y0 + t)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rw [cellFaces_vertex, image_insert_eq, image_insert_eq, image_insert_eq, image_singleton,
    pi_sqFace hp, pi_sqFace hp, pi_sqFace hp, pi_sqFace hp, newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega), newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega)]
  have e1 : ¬ (Y0 + t ≤ Y0 - 1 ∨ Y0 + 2 * (b : ℤ) ≤ Y0 + t) := by omega
  unfold vertexCell
  rw [if_neg e1]
  simp only [add_sub_cancel_left, show Y0 + t - 1 - Y0 = t - 1 by ring]
  have oa : off b (t - 1) = -t := by unfold off; rw [if_pos (by omega)]; ring
  have ob : off b t = -(t + 1) := by unfold off; rw [if_pos ht2]
  rw [oa, ob, if_pos ht2]
  rcases Int.emod_two_eq_zero_or_one (x + (Y0 + t)) with hq | hq <;> rw [hq] <;>
  rcases (by omega : x ≤ c0 + sL - t - 2 ∨ x = c0 + sL - t - 1 ∨ x = c0 + sL - t ∨
      (c0 + sL - t + 1 ≤ x ∧ x ≤ c0 + sL + 2 * b + t - 1) ∨ x = c0 + sL + 2 * b + t ∨
      x = c0 + sL + 2 * b + t + 1 ∨ c0 + sL + 2 * b + t + 2 ≤ x) with
    hx | hx | hx | hx | hx | hx | hx <;> band_case

theorem band_vertex_second (hp : Params h' b Y0 c0 sL) (x t : ℤ) (ht1 : b ≤ t)
    (ht2 : t ≤ 2 * b - 1) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x, 2 * (Y0 + t)) =
      cellFaces h' (vertexCell b Y0 c0 sL x (Y0 + t)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rw [cellFaces_vertex, image_insert_eq, image_insert_eq, image_insert_eq, image_singleton,
    pi_sqFace hp, pi_sqFace hp, pi_sqFace hp, pi_sqFace hp, newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega), newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega)]
  have e1 : ¬ (Y0 + t ≤ Y0 - 1 ∨ Y0 + 2 * (b : ℤ) ≤ Y0 + t) := by omega
  unfold vertexCell
  rw [if_neg e1]
  simp only [add_sub_cancel_left, show Y0 + t - 1 - Y0 = t - 1 by ring]
  have oa : off b (t - 1) = t - 2 * b := by
    unfold off; split_ifs <;> omega
  have ob : off b t = t - 2 * b + 1 := by unfold off; rw [if_neg (by omega)]; ring
  rw [oa, ob, if_neg (by omega)]
  rcases Int.emod_two_eq_zero_or_one (x + (Y0 + t)) with hq | hq <;> rw [hq] <;>
  rcases (by omega : x ≤ c0 - 1 + sL + t - 2 * b ∨ x = c0 + sL + t - 2 * b ∨
      x = c0 + sL + t - 2 * b + 1 ∨
      (c0 + sL + t - 2 * b + 2 ≤ x ∧ x ≤ c0 + sL + 4 * b - t - 2) ∨
      x = c0 + sL + 4 * b - t - 1 ∨ x = c0 + sL + 4 * b - t ∨ c0 + sL + 4 * b - t + 1 ≤ x) with
    hx | hx | hx | hx | hx | hx | hx <;> band_case

theorem band_horiz_first (hp : Params h' b Y0 c0 sL) (x t : ℤ) (ht1 : 0 ≤ t)
    (ht2 : t + 1 ≤ b) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x + 1, 2 * (Y0 + t)) =
      cellFaces h' (horizCell b Y0 c0 sL x (Y0 + t)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rw [cellFaces_horiz, image_insert_eq, image_singleton,
    pi_sqFace hp, pi_sqFace hp, newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega)]
  have e1 : ¬ (Y0 + t ≤ Y0 - 1 ∨ Y0 + 2 * (b : ℤ) ≤ Y0 + t) := by omega
  unfold horizCell
  rw [if_neg e1, newSq_band (by omega) (by omega)]
  simp only [add_sub_cancel_left, show Y0 + t - 1 - Y0 = t - 1 by ring]
  have oa : off b (t - 1) = -t := by unfold off; rw [if_pos (by omega)]; ring
  have ob : off b t = -(t + 1) := by unfold off; rw [if_pos ht2]
  rw [oa, ob, if_pos ht2]
  rcases Int.emod_two_eq_zero_or_one (x + (Y0 + t)) with hq | hq <;> rw [hq] <;>
  rcases (by omega : x ≤ c0 + sL - t - 2 ∨ x = c0 + sL - t - 1 ∨
      (c0 + sL - t ≤ x ∧ x ≤ c0 + sL + 2 * b + t - 1) ∨ x = c0 + sL + 2 * b + t ∨
      c0 + sL + 2 * b + t + 1 ≤ x) with
    hx | hx | hx | hx | hx <;> band_case

theorem band_horiz_second (hp : Params h' b Y0 c0 sL) (x t : ℤ) (ht1 : b ≤ t)
    (ht2 : t ≤ 2 * b - 1) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x + 1, 2 * (Y0 + t)) =
      cellFaces h' (horizCell b Y0 c0 sL x (Y0 + t)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rw [cellFaces_horiz, image_insert_eq, image_singleton,
    pi_sqFace hp, pi_sqFace hp, newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega)]
  have e1 : ¬ (Y0 + t ≤ Y0 - 1 ∨ Y0 + 2 * (b : ℤ) ≤ Y0 + t) := by omega
  unfold horizCell
  rw [if_neg e1, newSq_band (by omega) (by omega)]
  simp only [add_sub_cancel_left, show Y0 + t - 1 - Y0 = t - 1 by ring]
  have oa : off b (t - 1) = t - 2 * b := by
    unfold off; split_ifs <;> omega
  have ob : off b t = t - 2 * b + 1 := by unfold off; rw [if_neg (by omega)]; ring
  rw [oa, ob, if_neg (by omega)]
  rcases Int.emod_two_eq_zero_or_one (x + (Y0 + t)) with hq | hq <;> rw [hq] <;>
  rcases (by omega : x ≤ c0 - 1 + sL + t - 2 * b ∨ x = c0 + sL + t - 2 * b ∨
      (c0 + sL + t - 2 * b + 1 ≤ x ∧ x ≤ c0 + sL + 4 * b - t - 2) ∨
      x = c0 + sL + 4 * b - t - 1 ∨ c0 + sL + 4 * b - t ≤ x) with
    hx | hx | hx | hx | hx <;> band_case

theorem off_bounds {t : ℤ} (ht1 : 0 ≤ t) (ht2 : t ≤ 2 * b - 1) :
    -(b : ℤ) ≤ off b t ∧ off b t ≤ 0 := by
  unfold off; split_ifs <;> omega

theorem band_vert (hp : Params h' b Y0 c0 sL) (x t : ℤ) (ht1 : 0 ≤ t)
    (ht2 : t ≤ 2 * b - 1) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x, 2 * (Y0 + t) + 1) =
      cellFaces h' (vertCell b Y0 c0 sL x (Y0 + t)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rw [cellFaces_vert, image_insert_eq, image_singleton,
    pi_sqFace hp, pi_sqFace hp, newSq_band (by omega) (by omega),
    newSq_band (by omega) (by omega)]
  have e1 : ¬ (Y0 + t ≤ Y0 - 1 ∨ Y0 + 2 * (b : ℤ) ≤ Y0 + t) := by omega
  unfold vertCell
  rw [if_neg e1]
  simp only [add_sub_cancel_left]
  obtain ⟨o1, o2⟩ := off_bounds (b := b) ht1 ht2
  generalize off b t = o at *
  rcases (by omega : x ≤ c0 - 1 + sL + o ∨ x = c0 + sL + o ∨
      (c0 + sL + o + 1 ≤ x ∧ x ≤ c0 + sL + 2 * b - o - 1) ∨
      x = c0 + sL + 2 * b - o ∨ c0 + sL + 2 * b - o + 1 ≤ x) with
    hx | hx | hx | hx | hx <;> band_case

theorem newSq_below {u v : ℤ} (hv : v ≤ Y0 - 1) :
    newSq b Y0 c0 sL (u, v) = (side b c0 sL 0 u, v) := by
  unfold newSq
  rw [if_pos hv]

theorem newSq_above (hb : 1 ≤ b) {u v : ℤ} (hv : Y0 + 2 * b - 1 ≤ v) :
    newSq b Y0 c0 sL (u, v) = (side b c0 sL 0 u, v - 2 * b) := by
  unfold newSq
  rw [if_neg (by simp only; omega)]
  by_cases hv' : Y0 + 2 * (b : ℤ) ≤ v
  · rw [if_pos hv']
  · rw [if_neg hv']
    simp only [Prod.mk.injEq]
    constructor
    · congr 1
      unfold off
      rw [if_neg (by omega)]
      omega
    · omega

theorem off_vertex_core (hp : Params h' b Y0 c0 sL) (x y' : ℤ) :
    ({sqFace h' (side b c0 sL 0 (x - 1), y' - 1), sqFace h' (side b c0 sL 0 x, y' - 1),
      sqFace h' (side b c0 sL 0 (x - 1), y'), sqFace h' (side b c0 sL 0 x, y')} : Set (ℤ × ℤ)) =
      cellFaces h' (if x - sL ≤ c0 - 1 then (2 * (x - sL), 2 * y')
        else if c0 ≤ x - sL - 2 * b then (2 * (x - sL - 2 * b), 2 * y')
        else (2 * (c0 - 1) + 1, 2 * y')) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rcases Int.emod_two_eq_zero_or_one (x + y') with hq | hq <;>
  rcases (by omega : x ≤ c0 - 1 + sL ∨ x = c0 + sL ∨
      (c0 + sL + 1 ≤ x ∧ x ≤ c0 + sL + 2 * b - 1) ∨ x = c0 + sL + 2 * b ∨
      c0 + sL + 2 * b + 1 ≤ x) with
    hx | hx | hx | hx | hx <;> band_case

theorem off_horiz_core (hp : Params h' b Y0 c0 sL) (x y' : ℤ) :
    ({sqFace h' (side b c0 sL 0 x, y' - 1), sqFace h' (side b c0 sL 0 x, y')} : Set (ℤ × ℤ)) =
      cellFaces h' (if x + 1 - sL ≤ c0 - 1 then (2 * (x - sL) + 1, 2 * y')
        else if c0 ≤ x - sL - 2 * b then (2 * (x - sL - 2 * b) + 1, 2 * y')
        else (2 * (c0 - 1) + 1, 2 * y')) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rcases Int.emod_two_eq_zero_or_one (x + y') with hq | hq <;>
  rcases (by omega : x ≤ c0 - 2 + sL ∨ x = c0 - 1 + sL ∨
      (c0 + sL ≤ x ∧ x ≤ c0 + sL + 2 * b - 1) ∨ c0 + sL + 2 * b ≤ x) with
    hx | hx | hx | hx <;> band_case

theorem off_vert_core (hp : Params h' b Y0 c0 sL) (x y' : ℤ) :
    ({sqFace h' (side b c0 sL 0 (x - 1), y'), sqFace h' (side b c0 sL 0 x, y')} :
        Set (ℤ × ℤ)) =
      cellFaces h' (if x - sL ≤ c0 - 1 then (2 * (x - sL), 2 * y' + 1)
        else if c0 ≤ x - sL - 2 * b then (2 * (x - sL - 2 * b), 2 * y' + 1)
        else (2 * (c0 - 1) + 1, 2 * y' + 1)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp'
  rcases Int.emod_two_eq_zero_or_one (x + y') with hq | hq <;>
  rcases (by omega : x ≤ c0 - 1 + sL ∨ x = c0 + sL ∨
      (c0 + sL + 1 ≤ x ∧ x ≤ c0 + sL + 2 * b - 1) ∨ x = c0 + sL + 2 * b ∨
      c0 + sL + 2 * b + 1 ≤ x) with
    hx | hx | hx | hx | hx <;> band_case

theorem off_vertex (hp : Params h' b Y0 c0 sL) (x y : ℤ) (hy : y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x, 2 * y) =
      cellFaces h' (vertexCell b Y0 c0 sL x y) := by
  rw [cellFaces_vertex, image_insert_eq, image_insert_eq, image_insert_eq, image_singleton,
    pi_sqFace hp, pi_sqFace hp, pi_sqFace hp, pi_sqFace hp]
  unfold vertexCell
  rw [if_pos hy]
  rcases hy with hy | hy
  · rw [newSq_below (by omega), newSq_below (by omega), newSq_below (by omega),
      newSq_below (by omega)]
    simp only [hy, ↓reduceIte]
    exact off_vertex_core hp x y
  · rw [newSq_above hp.b1 (by omega), newSq_above hp.b1 (by omega), newSq_above hp.b1 (by omega),
      newSq_above hp.b1 (by omega),
      show y - 1 - 2 * (b : ℤ) = y - 2 * b - 1 by ring]
    simp only [show ¬ y ≤ Y0 - 1 by omega, ↓reduceIte]
    exact off_vertex_core hp x (y - 2 * b)

theorem off_horiz (hp : Params h' b Y0 c0 sL) (x y : ℤ) (hy : y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x + 1, 2 * y) =
      cellFaces h' (horizCell b Y0 c0 sL x y) := by
  rw [cellFaces_horiz, image_insert_eq, image_singleton, pi_sqFace hp, pi_sqFace hp]
  unfold horizCell
  rw [if_pos hy]
  rcases hy with hy | hy
  · rw [newSq_below (by omega), newSq_below (by omega)]
    simp only [hy, ↓reduceIte]
    exact off_horiz_core hp x y
  · rw [newSq_above hp.b1 (by omega), newSq_above hp.b1 (by omega),
      show y - 1 - 2 * (b : ℤ) = y - 2 * b - 1 by ring]
    simp only [show ¬ y ≤ Y0 - 1 by omega, ↓reduceIte]
    exact off_horiz_core hp x (y - 2 * b)

theorem off_vert (hp : Params h' b Y0 c0 sL) (x y : ℤ) (hy : y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) (2 * x, 2 * y + 1) =
      cellFaces h' (vertCell b Y0 c0 sL x y) := by
  rw [cellFaces_vert, image_insert_eq, image_singleton, pi_sqFace hp, pi_sqFace hp]
  unfold vertCell
  rw [if_pos hy]
  rcases hy with hy | hy
  · rw [newSq_below (by omega), newSq_below (by omega)]
    simp only [hy, ↓reduceIte]
    exact off_vert_core hp x y
  · rw [newSq_above hp.b1 (by omega), newSq_above hp.b1 (by omega)]
    simp only [show ¬ y ≤ Y0 - 1 by omega, ↓reduceIte]
    exact off_vert_core hp x (y - 2 * b)

/-- **The faces of the hexagonal hole at each element.** -/
theorem pi_image_cellFaces (hp : Params h' b Y0 c0 sL) {m : ℤ × ℤ}
    (hm : IsWallCell (h' + 2 * b + 2) m) :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) m = cellFaces h' (cell b Y0 c0 sL m) := by
  rcases Hole.cell_cases hm with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · rw [cell_vertex]
    by_cases hy : y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y
    · exact off_vertex hp x y hy
    · obtain ⟨t, rfl⟩ : ∃ t, y = Y0 + t := ⟨y - Y0, by ring⟩
      by_cases ht : t + 1 ≤ b
      · exact band_vertex_first hp x t (by omega) ht
      · exact band_vertex_second hp x t (by omega) (by omega)
  · rw [cell_horiz]
    by_cases hy : y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y
    · exact off_horiz hp x y hy
    · obtain ⟨t, rfl⟩ : ∃ t, y = Y0 + t := ⟨y - Y0, by ring⟩
      by_cases ht : t + 1 ≤ b
      · exact band_horiz_first hp x t (by omega) ht
      · exact band_horiz_second hp x t (by omega) (by omega)
  · rw [cell_vert]
    by_cases hy : y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ y
    · exact off_vert hp x y hy
    · obtain ⟨t, rfl⟩ : ∃ t, y = Y0 + t := ⟨y - Y0, by ring⟩
      exact band_vert hp x t (by omega) (by omega)

/-- A kept element keeps its faces: they go onto the faces at its owner. -/
theorem image_cellFaces_of_own (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h')
    {m m' : ℤ × ℤ} (hm : m ∈ fig1WallCells (h' + 2 * b + 2))
    (hown : own h' b Y0 c0 sL m = some m') :
    pi h' b Y0 c0 sL '' cellFaces (h' + 2 * b + 2) m = cellFaces h' m' := by
  have hm' : IsWallCell (h' + 2 * b + 2) m :=
    (mem_fig1WallCells_iff (by omega) (even_add_two_mul_add_two he' b) _).mp hm
  unfold own at hown
  split_ifs at hown
  cases hown
  exact pi_image_cellFaces hp hm'

/-- All faces at an element that is not kept go to one face. -/
theorem pi_eq_of_own_none (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h')
    {m : ℤ × ℤ} (hm : m ∈ fig1WallCells (h' + 2 * b + 2)) (hown : own h' b Y0 c0 sL m = none)
    {F G : ℤ × ℤ} (hF : F ∈ cellFaces (h' + 2 * b + 2) m)
    (hG : G ∈ cellFaces (h' + 2 * b + 2) m) :
    pi h' b Y0 c0 sL F = pi h' b Y0 c0 sL G := by
  have hm' : IsWallCell (h' + 2 * b + 2) m :=
    (mem_fig1WallCells_iff (by omega) (even_add_two_mul_add_two he' b) _).mp hm
  have hn : cell b Y0 c0 sL m ∉ fig1WallCells h' := by
    rw [mem_fig1WallCells_iff hh' he']
    intro hc
    unfold own at hown
    rw [if_pos hc] at hown
    exact absurd hown (by simp)
  have h1 : pi h' b Y0 c0 sL F ∈ cellFaces h' (cell b Y0 c0 sL m) := by
    rw [← pi_image_cellFaces hp hm']; exact mem_image_of_mem _ hF
  have h2 : pi h' b Y0 c0 sL G ∈ cellFaces h' (cell b Y0 c0 sL m) := by
    rw [← pi_image_cellFaces hp hm']; exact mem_image_of_mem _ hG
  obtain ⟨q, hq, e⟩ := h1
  obtain ⟨q', hq', e'⟩ := h2
  rw [← e, ← e']
  exact wallFace_eq_of_not_mem hh' he' hn hq hq'

end HexHole

end GraphMinor.GM13
