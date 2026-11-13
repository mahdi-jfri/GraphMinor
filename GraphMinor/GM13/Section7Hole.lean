module

public import GraphMinor.GM13.Section7Translate

/-!
# Graph Minors XIII, (7.3): a hole in the wall

On page 90 of *Graph Minors. XIII* a wall of height `h - 2` is found inside a wall of height `h`
by making a hole (Fig. 2). This file builds the version of the hole that we use, as a `Shape`.
Write `h = h' + 2` for the old height and `h'` for the new one. The hole has a row `Y0` and a
column `c0`, and the new wall is drawn as follows.

- Below row `Y0` (old rows `0 .. Y0 - 1`) the new wall is the old one with the four columns
  `c0 .. c0 + 3` cut out: their vertical edges are deleted and the horizontal edges across them
  are stretched.
- Above (old rows `Y0 + 2 .. h`) the new wall is the old one moved by `(2, 2)`.
- The vertical edges of the new wall between its rows `Y0 - 1` and `Y0` become staircases
  through the old rows `Y0` and `Y0 + 1`: two steps to the right left of the cut, and two steps
  to the left right of it.

We work with unit squares of the grid, in square coordinates: the square `(x, y)` is the cell
`(2 x + 1, 2 y + 1)`. Each square lies in one brick (`bk`), and the map `Hole.sq` sends an old
square to a new square in the same new face. So the faces of the new wall at an element are the
faces of the new squares of the old squares around it.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## Squares and their faces -/

/-- The brick that contains the unit square `s` (it may lie outside the wall). -/
def bk (s : ℤ × ℤ) : ℤ × ℤ := (s.1 + (s.1 + s.2) % 2, s.2)

/-- The face of the wall of height `h` that contains the unit square `s`. -/
def sqFace (h : ℕ) (s : ℤ × ℤ) : ℤ × ℤ := wallFace h (2 * s.1 + 1, 2 * s.2 + 1)

theorem sqFace_eq (h : ℕ) (s : ℤ × ℤ) :
    sqFace h s = if IsBrick h (bk s) then bk s else outFace := by
  unfold sqFace
  rw [wallFace_square]
  congr 1
  apply propext
  simp only [IsBrick, bk]
  omega

theorem bk_ne_outFace_of_isBrick {h : ℕ} {s : ℤ × ℤ} (hs : IsBrick h (bk s)) : bk s ≠ outFace := by
  intro e
  rw [e] at hs
  exact not_isBrick_outFace h hs

/-- Two squares lie in the same face exactly when they lie in the same brick or both lie
outside the wall. -/
theorem sqFace_eq_iff {h : ℕ} {s t : ℤ × ℤ} :
    sqFace h s = sqFace h t ↔
      bk s = bk t ∨ (¬ IsBrick h (bk s) ∧ ¬ IsBrick h (bk t)) := by
  rw [sqFace_eq, sqFace_eq]
  split_ifs with h1 h2 h2
  · constructor
    · exact Or.inl
    · rintro (e | ⟨e, -⟩)
      · exact e
      · exact absurd h1 e
  · constructor
    · intro e; exact absurd e (bk_ne_outFace_of_isBrick h1)
    · rintro (e | ⟨e, -⟩)
      · exact absurd (e ▸ h1) h2
      · exact absurd h1 e
  · constructor
    · intro e; exact absurd e.symm (bk_ne_outFace_of_isBrick h2)
    · rintro (e | ⟨-, e⟩)
      · exact absurd (by rw [e]; exact h2) h1
      · exact absurd h2 e
  · exact ⟨fun _ => Or.inr ⟨h1, h2⟩, fun _ => rfl⟩

theorem sqFace_eq_out_iff {h : ℕ} {s : ℤ × ℤ} : sqFace h s = outFace ↔ ¬ IsBrick h (bk s) := by
  rw [sqFace_eq]
  split_ifs with h1
  · exact ⟨fun e => absurd e (bk_ne_outFace_of_isBrick h1), fun e => absurd h1 e⟩
  · exact ⟨fun _ => h1, fun _ => rfl⟩

theorem sqFace_eq_brick_iff {h : ℕ} {s F : ℤ × ℤ} (hF : IsBrick h F) :
    sqFace h s = F ↔ bk s = F := by
  rw [sqFace_eq]
  split_ifs with h1
  · rfl
  · constructor
    · intro e; rw [← e] at hF; exact absurd hF (not_isBrick_outFace h)
    · intro e; rw [e] at h1; exact absurd hF h1

theorem isWallFace_sqFace (h : ℕ) (s : ℤ × ℤ) : IsWallFace h (sqFace h s) :=
  isBrick_or_eq_outFace_wallFace h _

/-- The depth of the face of a square, without cases: outside the wall the formula is at most
zero. -/
theorem faceDepth_sqFace (h : ℕ) (s : ℤ × ℤ) :
    faceDepth h (sqFace h s) = max 0 (outDepth h (bk s)) := by
  rw [sqFace_eq]
  split_ifs with h1
  · rw [faceDepth_of_isBrick h1]
    have := one_le_outDepth h1
    omega
  · simp only [faceDepth, ite_true]
    unfold outDepth
    simp only [IsBrick, bk, not_and, not_lt] at h1 ⊢
    omega

/-- The squares around the cell `(a, b)`, in square coordinates. -/
theorem mem_squaresAbove_iff_sq {a b : ℤ} {q : ℤ × ℤ} :
    q ∈ squaresAbove (a, b) ↔
      ∃ x y : ℤ, q = (2 * x + 1, 2 * y + 1) ∧ 2 * x ≤ a ∧ a ≤ 2 * x + 2 ∧ 2 * y ≤ b ∧
        b ≤ 2 * y + 2 := by
  rw [mem_squaresAbove_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(q.1 - 1) / 2, (q.2 - 1) / 2, Prod.ext (by simp; omega) (by simp; omega), ?_⟩
    simp only at h3 h4
    omega
  · rintro ⟨x, y, rfl, h1, h2, h3, h4⟩
    simp only
    omega

/-- The faces at the cell `(a, b)` are the faces of the squares around it. -/
theorem mem_cellFaces_iff_sq {h : ℕ} {a b : ℤ} {F : ℤ × ℤ} :
    F ∈ cellFaces h (a, b) ↔
      ∃ x y : ℤ, 2 * x ≤ a ∧ a ≤ 2 * x + 2 ∧ 2 * y ≤ b ∧ b ≤ 2 * y + 2 ∧ sqFace h (x, y) = F := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, y, rfl, h1⟩ := mem_squaresAbove_iff_sq.mp hq
    exact ⟨x, y, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, rfl⟩
  · rintro ⟨x, y, h1, h2, h3, h4, rfl⟩
    exact ⟨_, mem_squaresAbove_iff_sq.mpr ⟨x, y, rfl, h1, h2, h3, h4⟩, rfl⟩

theorem isBrick_bk_iff {h : ℕ} {u v : ℤ} :
    IsBrick h (bk (u, v)) ↔ 0 ≤ v ∧ v < h ∧ 1 ≤ u + (u + v) % 2 ∧ u + (u + v) % 2 ≤ 2 * h := by
  simp only [IsBrick, bk]
  omega

theorem bk_eq_iff {u v u' v' : ℤ} :
    bk (u, v) = bk (u', v') ↔ u + (u + v) % 2 = u' + (u' + v') % 2 ∧ v = v' := by
  simp only [bk, Prod.mk.injEq]

/-- Two squares in the same brick, without `bk`: the parity appears only in equations. -/
theorem bk_eq_iff' {u v u' v' : ℤ} :
    bk (u, v) = bk (u', v') ↔ v = v' ∧ (u = u' ∨ (u' = u + 1 ∧ (u + v) % 2 = 1) ∨
      (u = u' + 1 ∧ (u' + v) % 2 = 1)) := by
  simp only [bk, Prod.mk.injEq]
  omega

/-- A square outside the wall, without `bk`. -/
theorem not_isBrick_bk_iff {h : ℕ} {u v : ℤ} :
    ¬ IsBrick h (bk (u, v)) ↔ v < 0 ∨ h ≤ v ∨ u < 0 ∨ (u = 0 ∧ v % 2 = 0) ∨ 2 * (h : ℤ) < u ∨
      (u = 2 * h ∧ v % 2 = 1) := by
  simp only [IsBrick, bk]
  omega

/-! ## The cells of the wall by type -/

theorem isWallCell_vertex_iff {h : ℕ} {x y : ℤ} :
    IsWallCell h (2 * x, 2 * y) ↔ 0 ≤ x ∧ x ≤ 2 * h + 1 ∧ 0 ≤ y ∧ y ≤ h ∧
      ¬ (x = 0 ∧ y = 0) ∧ ¬ (x = 2 * h + 1 ∧ y = h) := by
  unfold IsWallCell
  simp only
  omega

theorem isWallCell_horiz_iff {h : ℕ} {x y : ℤ} :
    IsWallCell h (2 * x + 1, 2 * y) ↔ 0 ≤ x ∧ x ≤ 2 * h ∧ 0 ≤ y ∧ y ≤ h ∧
      ¬ (x = 0 ∧ y = 0) ∧ ¬ (x = 2 * h ∧ y = h) := by
  unfold IsWallCell
  simp only
  omega

theorem isWallCell_vert_iff {h : ℕ} {x y : ℤ} :
    IsWallCell h (2 * x, 2 * y + 1) ↔ 0 ≤ x ∧ x ≤ 2 * h + 1 ∧ 0 ≤ y ∧ y ≤ h - 1 ∧
      (x + y) % 2 = 1 := by
  unfold IsWallCell
  simp only
  omega

/-! ## The hole -/

namespace Hole

/-- The new square that contains an old unit square `s`: the cut below row `Y0`, the middle of
the staircases in row `Y0`, and the move by `(2, 2)` above. -/
def newSq (Y0 c0 : ℤ) (s : ℤ × ℤ) : ℤ × ℤ :=
  if s.2 ≤ Y0 - 1 then
    (if s.1 ≤ c0 - 1 then s else if c0 + 3 ≤ s.1 then (s.1 - 4, s.2) else (c0 - 1, s.2))
  else if s.2 = Y0 then
    (if s.1 ≤ c0 then (s.1 - 1, Y0 - 1) else if c0 + 2 ≤ s.1 then (s.1 - 3, Y0 - 1)
      else (c0 - 1, Y0 - 1))
  else (s.1 - 2, s.2 - 2)

/-- The face of the new wall (height `h'`) that contains the face `F` of the old wall (height
`h' + 2`). -/
def pi (h' : ℕ) (Y0 c0 : ℤ) (F : ℤ × ℤ) : ℤ × ℤ :=
  if IsBrick (h' + 2) F then sqFace h' (newSq Y0 c0 F) else outFace

/-- The new element that contains the old vertex `(x, y)`. -/
def vertexCell (Y0 c0 x y : ℤ) : ℤ × ℤ :=
  if y ≤ Y0 - 1 then
    (if x ≤ c0 - 1 then (2 * x, 2 * y) else if c0 + 4 ≤ x then (2 * (x - 4), 2 * y)
      else (2 * (c0 - 1) + 1, 2 * y))
  else if y = Y0 then
    (if (x - Y0) % 2 = 0 then
      (if x < c0 then (2 * x, 2 * (Y0 - 1) + 1)
        else if c0 + 4 ≤ x then (2 * (x - 4), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))
    else
      (if x - 1 < c0 then (2 * (x - 1), 2 * (Y0 - 1) + 1)
        else if c0 + 3 ≤ x then (2 * (x - 3), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1)))
  else if y = Y0 + 1 then
    (if (x - Y0) % 2 = 0 then (2 * (x - 2), 2 * (Y0 - 1) + 1)
    else
      (if x - 1 < c0 then (2 * (x - 1), 2 * (Y0 - 1) + 1)
        else if c0 + 3 ≤ x then (2 * (x - 3), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1)))
  else (2 * (x - 2), 2 * (y - 2))

/-- The new element that contains the old horizontal edge from `(x, y)` to `(x + 1, y)`. -/
def horizCell (Y0 c0 x y : ℤ) : ℤ × ℤ :=
  if y ≤ Y0 - 1 then
    (if x ≤ c0 - 2 then (2 * x + 1, 2 * y) else if c0 + 4 ≤ x then (2 * (x - 4) + 1, 2 * y)
      else (2 * (c0 - 1) + 1, 2 * y))
  else if y = Y0 then
    (if x < c0 then (2 * x, 2 * (Y0 - 1) + 1)
      else if c0 + 3 ≤ x then (2 * (x - 3), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))
  else if y = Y0 + 1 then
    (if x - 1 < c0 then (2 * (x - 1), 2 * (Y0 - 1) + 1)
      else if c0 + 2 ≤ x then (2 * (x - 2), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))
  else (2 * (x - 2) + 1, 2 * (y - 2))

/-- The new element that contains the old vertical edge from `(x, y)` to `(x, y + 1)`. -/
def vertCell (Y0 c0 x y : ℤ) : ℤ × ℤ :=
  if y ≤ Y0 - 2 then
    (if x ≤ c0 - 1 then (2 * x, 2 * y + 1) else if c0 + 4 ≤ x then (2 * (x - 4), 2 * y + 1)
      else (2 * (c0 - 1) + 1, 2 * y + 1))
  else if y = Y0 - 1 then
    (if x < c0 then (2 * x, 2 * (Y0 - 1) + 1)
      else if c0 + 4 ≤ x then (2 * (x - 4), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))
  else if y = Y0 then
    (if x - 1 < c0 then (2 * (x - 1), 2 * (Y0 - 1) + 1)
      else if c0 + 3 ≤ x then (2 * (x - 3), 2 * (Y0 - 1) + 1) else (2 * (c0 - 1) + 1, 2 * (Y0 - 1) + 1))
  else if y = Y0 + 1 then (2 * (x - 2), 2 * (Y0 - 1) + 1)
  else (2 * (x - 2), 2 * (y - 2) + 1)

/-- The new element that contains the old element with cell `m`, before the test that it is an
element of the new wall. For an element that is not kept, it is a square of the new face that
contains the element: the square in column `c0 - 1` of its row below the band, and the square
`(c0 - 1, Y0 - 1)` in the band. -/
def cell (Y0 c0 : ℤ) (m : ℤ × ℤ) : ℤ × ℤ :=
  if m.2 % 2 = 0 then
    (if m.1 % 2 = 0 then vertexCell Y0 c0 (m.1 / 2) (m.2 / 2)
      else horizCell Y0 c0 (m.1 / 2) (m.2 / 2))
  else vertCell Y0 c0 (m.1 / 2) (m.2 / 2)

/-- The new element that contains the old element with cell `m`, if it is kept. -/
def own (h' : ℕ) (Y0 c0 : ℤ) (m : ℤ × ℤ) : Option (ℤ × ℤ) :=
  if IsWallCell h' (cell Y0 c0 m) then some (cell Y0 c0 m) else none

theorem cell_vertex (Y0 c0 x y : ℤ) : cell Y0 c0 (2 * x, 2 * y) = vertexCell Y0 c0 x y := by
  unfold cell
  rw [if_pos (by simp), if_pos (by simp)]
  congr 1 <;> simp

theorem cell_horiz (Y0 c0 x y : ℤ) : cell Y0 c0 (2 * x + 1, 2 * y) = horizCell Y0 c0 x y := by
  unfold cell
  rw [if_pos (by omega), if_neg (by omega)]
  congr 1 <;> omega

theorem cell_vert (Y0 c0 x y : ℤ) : cell Y0 c0 (2 * x, 2 * y + 1) = vertCell Y0 c0 x y := by
  unfold cell
  rw [if_neg (by omega)]
  congr 1 <;> omega

/-- Every cell of the old wall is a vertex, a horizontal edge or a vertical edge. -/
theorem cell_cases {h : ℕ} {m : ℤ × ℤ} (hm : IsWallCell h m) :
    (∃ x y, m = (2 * x, 2 * y)) ∨ (∃ x y, m = (2 * x + 1, 2 * y)) ∨
      (∃ x y, m = (2 * x, 2 * y + 1)) := by
  obtain ⟨a, b⟩ := m
  unfold IsWallCell at hm
  simp only at hm
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
  rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · exact Or.inl ⟨a / 2, b / 2, Prod.ext (by simp; omega) (by simp; omega)⟩
  · exact Or.inr (Or.inr ⟨a / 2, b / 2, Prod.ext (by simp; omega) (by simp; omega)⟩)
  · exact Or.inr (Or.inl ⟨a / 2, b / 2, Prod.ext (by simp; omega) (by simp; omega)⟩)
  · omega

/-- The range of the parameters of a hole. -/
structure Params (h' : ℕ) (Y0 c0 : ℤ) : Prop where
  Y1 : 1 ≤ Y0
  Y2 : Y0 ≤ h'
  c1 : 1 ≤ c0
  c2 : c0 ≤ 2 * h' + 1

/-- Cleans the logic constants from all hypotheses and the goal, then calls `omega`. -/
macro "hole_omega" : tactic => `(tactic| ((try simp only [Prod.mk.injEq, true_and, and_true, not_true_eq_false, false_and, and_false, or_false, false_or, not_false_eq_true, true_or, or_true, not_and, not_le, not_lt, true_iff, iff_true, imp_false, true_implies, implies_true] at *) <;> first | done | trivial | omega))

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- Two squares of one old brick have new squares in one new face. -/
theorem newSq_bk (hp : Params h' Y0 c0) (s : ℤ × ℤ) (hb : IsBrick (h' + 2) (bk s)) :
    bk (newSq Y0 c0 (bk s)) = bk (newSq Y0 c0 s) ∨
      (¬ IsBrick h' (bk (newSq Y0 c0 (bk s))) ∧ ¬ IsBrick h' (bk (newSq Y0 c0 s))) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  obtain ⟨x, y⟩ := s
  rcases Int.emod_two_eq_zero_or_one (x + y) with hp | hp
  · have : bk (x, y) = (x, y) := by simp [bk, hp]
    rw [this]; exact Or.inl rfl
  have e : bk (x, y) = (x + 1, y) := by simp [bk, hp]
  rw [e]
  rw [e] at hb
  simp only [IsBrick] at hb
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 - y := ⟨(x + y) / 2, by omega⟩
  simp only [newSq]
  split_ifs <;> simp only [bk, IsBrick] <;> hole_omega

/-- A square outside the old wall has its new square outside the new wall. -/
theorem newSq_out (hp : Params h' Y0 c0) (s : ℤ × ℤ) (hb : ¬ IsBrick (h' + 2) (bk s)) :
    ¬ IsBrick h' (bk (newSq Y0 c0 s)) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  obtain ⟨x, y⟩ := s
  simp only [IsBrick, bk] at hb
  simp only [newSq]
  split_ifs <;> simp only [bk, IsBrick] <;> hole_omega

/-- **The face map on squares.** -/
theorem pi_sqFace (hp : Params h' Y0 c0) (s : ℤ × ℤ) :
    pi h' Y0 c0 (sqFace (h' + 2) s) = sqFace h' (newSq Y0 c0 s) := by
  rw [sqFace_eq (h' + 2) s]
  split_ifs with hb
  · unfold pi
    rw [if_pos hb]
    exact sqFace_eq_iff.mpr (newSq_bk hp s hb)
  · unfold pi
    rw [if_neg (not_isBrick_outFace _)]
    exact (sqFace_eq_out_iff.mpr (newSq_out hp s hb)).symm

theorem even_succ_succ {h' : ℕ} (he' : Even h') : Even (h' + 2) := by
  obtain ⟨k, hk⟩ := he'; exact ⟨k + 1, by omega⟩

theorem own_mem (hh' : 1 ≤ h') (he' : Even h') {m m' : ℤ × ℤ} (hm : own h' Y0 c0 m = some m') :
    m' ∈ fig1WallCells h' := by
  unfold own at hm
  split_ifs at hm with h1
  cases hm
  exact (mem_fig1WallCells_iff hh' he' _).mpr h1

theorem own_eq_some {m m' : ℤ × ℤ} (h1 : cell Y0 c0 m = m') (h2 : IsWallCell h' m') :
    own h' Y0 c0 m = some m' := by
  subst h1
  unfold own
  rw [if_pos h2]

theorem own_surj (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') {m' : ℤ × ℤ}
    (hm' : m' ∈ fig1WallCells h') : ∃ m ∈ fig1WallCells (h' + 2), own h' Y0 c0 m = some m' := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hw := (mem_fig1WallCells_iff hh' he' _).mp hm'
  have hw' := hw
  simp only [mem_fig1WallCells_iff (by omega : 1 ≤ h' + 2) (even_succ_succ he')]
  rcases cell_cases hw with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · -- a vertex
    unfold IsWallCell at hw
    simp only at hw
    by_cases hy : y ≤ Y0 - 1
    · by_cases hx : x ≤ c0 - 1
      · refine ⟨(2 * x, 2 * y), ?_, own_eq_some ?_ hw'⟩
        · unfold IsWallCell; simp only; push_cast; hole_omega
        · rw [cell_vertex]; unfold vertexCell; split_ifs <;> hole_omega
      · refine ⟨(2 * (x + 4), 2 * y), ?_, own_eq_some ?_ hw'⟩
        · unfold IsWallCell; simp only; push_cast; hole_omega
        · rw [cell_vertex]; unfold vertexCell; split_ifs <;> hole_omega
    · refine ⟨(2 * (x + 2), 2 * (y + 2)), ?_, own_eq_some ?_ hw'⟩
      · unfold IsWallCell; simp only; push_cast; hole_omega
      · rw [cell_vertex]; unfold vertexCell; split_ifs <;> hole_omega
  · -- a horizontal edge
    unfold IsWallCell at hw
    simp only at hw
    by_cases hy : y ≤ Y0 - 1
    · by_cases hx : x ≤ c0 - 1
      · refine ⟨(2 * x + 1, 2 * y), ?_, own_eq_some ?_ hw'⟩
        · unfold IsWallCell; simp only; push_cast; hole_omega
        · rw [cell_horiz]; unfold horizCell; split_ifs <;> hole_omega
      · refine ⟨(2 * (x + 4) + 1, 2 * y), ?_, own_eq_some ?_ hw'⟩
        · unfold IsWallCell; simp only; push_cast; hole_omega
        · rw [cell_horiz]; unfold horizCell; split_ifs <;> hole_omega
    · refine ⟨(2 * (x + 2) + 1, 2 * (y + 2)), ?_, own_eq_some ?_ hw'⟩
      · unfold IsWallCell; simp only; push_cast; hole_omega
      · rw [cell_horiz]; unfold horizCell; split_ifs <;> hole_omega
  · -- a vertical edge
    unfold IsWallCell at hw
    simp only at hw
    by_cases hy : y ≤ Y0 - 1
    · by_cases hx : x ≤ c0 - 1
      · refine ⟨(2 * x, 2 * y + 1), ?_, own_eq_some ?_ hw'⟩
        · unfold IsWallCell; simp only; push_cast; hole_omega
        · rw [cell_vert]; unfold vertCell; split_ifs <;> hole_omega
      · refine ⟨(2 * (x + 4), 2 * y + 1), ?_, own_eq_some ?_ hw'⟩
        · unfold IsWallCell; simp only; push_cast; hole_omega
        · rw [cell_vert]; unfold vertCell; split_ifs <;> hole_omega
    · refine ⟨(2 * (x + 2), 2 * (y + 2) + 1), ?_, own_eq_some ?_ hw'⟩
      · unfold IsWallCell; simp only; push_cast; hole_omega
      · rw [cell_vert]; unfold vertCell; split_ifs <;> hole_omega

theorem pi_face (F : ℤ × ℤ) : IsWallFace h' (pi h' Y0 c0 F) := by
  unfold pi
  split_ifs
  · exact isWallFace_sqFace h' _
  · exact Or.inr rfl

theorem pi_outFace : pi h' Y0 c0 outFace = outFace := by
  unfold pi
  rw [if_neg (not_isBrick_outFace _)]

/-- The old square whose new square is `s'`. -/
def sqInv (Y0 c0 : ℤ) (s' : ℤ × ℤ) : ℤ × ℤ :=
  if s'.2 ≤ Y0 - 1 then (if s'.1 ≤ c0 - 1 then s' else (s'.1 + 4, s'.2)) else (s'.1 + 2, s'.2 + 2)

theorem newSq_sqInv (s' : ℤ × ℤ) : newSq Y0 c0 (sqInv Y0 c0 s') = s' := by
  obtain ⟨x, y⟩ := s'
  simp only [newSq, sqInv]
  split_ifs <;> hole_omega

theorem pi_surj (hp : Params h' Y0 c0) {F' : ℤ × ℤ} (hF' : IsWallFace h' F') :
    ∃ F, IsWallFace (h' + 2) F ∧ pi h' Y0 c0 F = F' := by
  rcases hF' with hb | rfl
  · refine ⟨sqFace (h' + 2) (sqInv Y0 c0 F'), isWallFace_sqFace _ _, ?_⟩
    rw [pi_sqFace hp, newSq_sqInv, sqFace_eq_brick_iff hb]
    obtain ⟨X, Y⟩ := F'
    simp only [IsBrick] at hb
    simp only [bk]
    hole_omega
  · exact ⟨outFace, Or.inr rfl, pi_outFace⟩

end Hole

end GraphMinor.GM13
