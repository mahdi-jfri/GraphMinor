module

public import GraphMinor.GM13.Section7HexHoleImage
public import GraphMinor.GM13.Section7Translate

/-!
# Graph Minors XIII, (7.3): the hexagonal hole as a shape

This file finishes the hexagonal hole as a `Shape (h' + 2b + 2) h'` (`HexHole.shape`). What is
left after `Section7HexHoleImage.lean` is the condition `conn`: two old faces in the same new
face are joined by steps across elements that the hole deletes.

The proof works with unit squares. Two squares side by side either lie in one old face, or an
old edge lies between them. If such an edge is kept, it goes to an element of the new wall, and
an edge or a vertex of the new wall lies on two different new faces. So if the two squares lie
in one new face, the edge between them is deleted, and there is a step between their old faces
(`HexHole.rel_vert`, `HexHole.rel_horiz`). It remains to walk from each old face to a face fixed
by its new face, one square at a time, without leaving the new face:

* a square whose new face is the outer face walks straight to the outside of the old wall, up,
  left or right (`HexHole.reach_out`);
* an old brick whose new face is a brick walks left or down to the favourite old brick of its
  new face, `HexHole.kappa` (`HexHole.reach_kappa`). Which step to take in each region was found
  by a computer search before the proof. The Lean proof does not use the search:
  `HexHole.reach_kappa` proves that the steps reach the favourite brick, for all parameters.
-/

public section

namespace GraphMinor.GM13

open Set

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- Old faces joined by steps across elements that the hole deletes. -/
abbrev Rel (h' b : ℕ) (Y0 c0 sL : ℤ) : ℤ × ℤ → ℤ × ℤ → Prop :=
  Relation.ReflTransGen (DelStep (h := h' + 2 * b + 2) (own h' b Y0 c0 sL))

/-! ## Two squares side by side -/

/-- The two squares on the sides of a vertical edge of a wall lie in different faces. -/
theorem sqFace_ne_vert {h : ℕ} {x y : ℤ} (hw : IsWallCell h (2 * x, 2 * y + 1)) :
    sqFace h (x - 1, y) ≠ sqFace h (x, y) := by
  rw [Ne, sqFace_eq_iff]
  unfold IsWallCell at hw
  simp only [bk, IsBrick, Prod.mk.injEq] at hw ⊢
  omega

/-- The two squares below and above a horizontal edge of a wall of even height lie in different
faces. -/
theorem sqFace_ne_horiz {h : ℕ} (he : Even h) {x y : ℤ} (hw : IsWallCell h (2 * x + 1, 2 * y)) :
    sqFace h (x, y - 1) ≠ sqFace h (x, y) := by
  obtain ⟨n, rfl⟩ := he
  rw [Ne, sqFace_eq_iff]
  unfold IsWallCell at hw
  simp only [bk, IsBrick, Prod.mk.injEq] at hw ⊢
  push_cast at hw ⊢
  omega

/-- Two squares side by side with no vertical edge of the wall between them lie in one face. -/
theorem sqFace_eq_of_not_vert {h : ℕ} {x y : ℤ} (hw : ¬ IsWallCell h (2 * x, 2 * y + 1)) :
    sqFace h (x - 1, y) = sqFace h (x, y) := by
  rw [sqFace_eq_iff]
  unfold IsWallCell at hw
  simp only [show 2 * x / 2 = x by omega, show (2 * y + 1 - 1) / 2 = y by omega,
    show (2 * y + 1) % 2 = 1 by omega, show 2 * x % 2 = 0 by omega, true_and] at hw
  simp only [bk, IsBrick, Prod.mk.injEq, and_true]
  by_cases hp : (x + y) % 2 = 1
  · right
    omega
  · left
    omega

/-- Two squares one above the other with no horizontal edge of the wall between them lie in one
face, when the height of the wall is even. -/
theorem sqFace_eq_of_not_horiz {h : ℕ} (he : Even h) {x y : ℤ}
    (hw : ¬ IsWallCell h (2 * x + 1, 2 * y)) : sqFace h (x, y - 1) = sqFace h (x, y) := by
  obtain ⟨n, rfl⟩ := he
  rw [sqFace_eq_iff]
  unfold IsWallCell at hw
  simp only [bk, IsBrick, Prod.mk.injEq] at hw ⊢
  push_cast at hw ⊢
  omega

/-- The new cell of an old vertical edge has an odd second coordinate. -/
theorem vertCell_snd (x y : ℤ) : (vertCell b Y0 c0 sL x y).2 % 2 = 1 := by
  unfold vertCell
  split_ifs <;> simp only <;> omega

/-- The new cell of an old horizontal edge has an odd coordinate. -/
theorem horizCell_odd (x y : ℤ) :
    (horizCell b Y0 c0 sL x y).1 % 2 = 1 ∨ (horizCell b Y0 c0 sL x y).2 % 2 = 1 := by
  unfold horizCell
  split_ifs <;> simp only <;> omega

/-- An edge or a vertex of a wall of even height lies on two different faces, so the faces at a
kept element are never all equal. Here for the cells that the hole gives to old edges: cells
with an odd coordinate. -/
theorem not_cellFaces_eq_singleton {h : ℕ} (he : Even h) {m : ℤ × ℤ} (hm : IsWallCell h m)
    (hodd : m.1 % 2 = 1 ∨ m.2 % 2 = 1) (F : ℤ × ℤ) : cellFaces h m ≠ {F} := by
  intro e
  have hm' := hm
  unfold IsWallCell at hm'
  rcases hodd with hodd | hodd
  · obtain ⟨x, y, rfl⟩ : ∃ x y, m = (2 * x + 1, 2 * y) :=
      ⟨m.1 / 2, m.2 / 2, Prod.ext (by simp only; omega) (by simp only; omega)⟩
    have h1 : sqFace h (x, y - 1) ∈ cellFaces h (2 * x + 1, 2 * y) := by
      rw [cellFaces_horiz]; exact mem_insert _ _
    have h2 : sqFace h (x, y) ∈ cellFaces h (2 * x + 1, 2 * y) := by
      rw [cellFaces_horiz]; exact mem_insert_of_mem _ rfl
    rw [e, mem_singleton_iff] at h1 h2
    exact sqFace_ne_horiz he hm (h1.trans h2.symm)
  · obtain ⟨x, y, rfl⟩ : ∃ x y, m = (2 * x, 2 * y + 1) :=
      ⟨m.1 / 2, m.2 / 2, Prod.ext (by simp only; omega) (by simp only; omega)⟩
    have h1 : sqFace h (x - 1, y) ∈ cellFaces h (2 * x, 2 * y + 1) := by
      rw [cellFaces_vert]; exact mem_insert _ _
    have h2 : sqFace h (x, y) ∈ cellFaces h (2 * x, 2 * y + 1) := by
      rw [cellFaces_vert]; exact mem_insert_of_mem _ rfl
    rw [e, mem_singleton_iff] at h1 h2
    exact sqFace_ne_vert hm (h1.trans h2.symm)

/-- If the two squares at an old vertical edge lie in one new face, the edge is deleted. -/
theorem own_vert_eq_none (hp : Params h' b Y0 c0 sL) (he' : Even h') {u v : ℤ}
    (hw : IsWallCell (h' + 2 * b + 2) (2 * u, 2 * v + 1))
    (he : sqFace h' (newSq b Y0 c0 sL (u - 1, v)) = sqFace h' (newSq b Y0 c0 sL (u, v))) :
    own h' b Y0 c0 sL (2 * u, 2 * v + 1) = none := by
  unfold own
  rw [if_neg]
  intro hc
  have himg := pi_image_cellFaces hp hw
  rw [cellFaces_vert, image_insert_eq, image_singleton, pi_sqFace hp, pi_sqFace hp, he,
    pair_eq_singleton] at himg
  refine not_cellFaces_eq_singleton he' hc (Or.inr ?_) _ himg.symm
  rw [cell_vert]
  exact vertCell_snd u v

/-- If the two squares at an old horizontal edge lie in one new face, the edge is deleted. -/
theorem own_horiz_eq_none (hp : Params h' b Y0 c0 sL) (he' : Even h') {u v : ℤ}
    (hw : IsWallCell (h' + 2 * b + 2) (2 * u + 1, 2 * v))
    (he : sqFace h' (newSq b Y0 c0 sL (u, v - 1)) = sqFace h' (newSq b Y0 c0 sL (u, v))) :
    own h' b Y0 c0 sL (2 * u + 1, 2 * v) = none := by
  unfold own
  rw [if_neg]
  intro hc
  have himg := pi_image_cellFaces hp hw
  rw [cellFaces_horiz, image_insert_eq, image_singleton, pi_sqFace hp, pi_sqFace hp, he,
    pair_eq_singleton] at himg
  refine not_cellFaces_eq_singleton he' hc ?_ _ himg.symm
  rw [cell_horiz]
  exact horizCell_odd u v

/-- **Two squares side by side in one new face have old faces joined by steps.** -/
theorem rel_vert (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {u v : ℤ}
    (he : sqFace h' (newSq b Y0 c0 sL (u - 1, v)) = sqFace h' (newSq b Y0 c0 sL (u, v))) :
    Rel h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) (u - 1, v)) (sqFace (h' + 2 * b + 2) (u, v)) := by
  by_cases hw : IsWallCell (h' + 2 * b + 2) (2 * u, 2 * v + 1)
  · refine .single (delStep_of
      ((mem_fig1WallCells_iff (by omega) (even_add_two_mul_add_two he' b) _).mpr hw)
      (own_vert_eq_none hp he' hw he) (q := (2 * (u - 1) + 1, 2 * v + 1))
      (q' := (2 * u + 1, 2 * v + 1)) ?_ ?_ rfl rfl) <;>
    · rw [mem_squaresAbove_iff]; omega
  · rw [sqFace_eq_of_not_vert hw]

/-- **Two squares one above the other in one new face have old faces joined by steps.** -/
theorem rel_horiz (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {u v : ℤ}
    (he : sqFace h' (newSq b Y0 c0 sL (u, v - 1)) = sqFace h' (newSq b Y0 c0 sL (u, v))) :
    Rel h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) (u, v - 1)) (sqFace (h' + 2 * b + 2) (u, v)) := by
  by_cases hw : IsWallCell (h' + 2 * b + 2) (2 * u + 1, 2 * v)
  · refine .single (delStep_of
      ((mem_fig1WallCells_iff (by omega) (even_add_two_mul_add_two he' b) _).mpr hw)
      (own_horiz_eq_none hp he' hw he) (q := (2 * u + 1, 2 * (v - 1) + 1))
      (q' := (2 * u + 1, 2 * v + 1)) ?_ ?_ rfl rfl) <;>
    · rw [mem_squaresAbove_iff]; omega
  · rw [sqFace_eq_of_not_horiz (even_add_two_mul_add_two he' b) hw]

/-! ## Squares whose new face is the outer face -/

/-- Going up never lowers the new row. -/
theorem newSq_snd_le (u v : ℤ) :
    (newSq b Y0 c0 sL (u, v)).2 ≤ (newSq b Y0 c0 sL (u, v + 1)).2 := by
  unfold newSq
  split_ifs <;> simp only <;> omega

/-- Going left never moves the new brick to the right. -/
theorem bk_newSq_fst_le (u v : ℤ) :
    (bk (newSq b Y0 c0 sL (u - 1, v))).1 ≤ (bk (newSq b Y0 c0 sL (u, v))).1 := by
  simp only [newSq]
  generalize off b (v - Y0) = o
  simp only [side]
  split_ifs <;> simp only [bk] <;> omega

theorem sqFace_out_of_row {h : ℕ} {s : ℤ × ℤ} (hs : h ≤ s.2 ∨ s.2 < 0) : sqFace h s = outFace := by
  rw [sqFace_eq_out_iff]
  simp only [IsBrick, bk]
  omega

theorem sqFace_out_of_col {h : ℕ} {s : ℤ × ℤ} (hs : (bk s).1 ≤ 0 ∨ 2 * (h : ℤ) + 1 ≤ (bk s).1) :
    sqFace h s = outFace := by
  rw [sqFace_eq_out_iff]
  simp only [IsBrick]
  omega

/-- A square whose new row is above the new wall walks up to the outside of the old wall. -/
theorem reach_out_up (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') :
    ∀ n : ℕ, ∀ u v : ℤ, ((h' + 2 * b + 2 : ℕ) - v).toNat = n →
      (h' : ℤ) ≤ (newSq b Y0 c0 sL (u, v)).2 →
      Rel h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) (u, v)) outFace := by
  intro n
  induction n with
  | zero =>
    intro u v hn _
    rw [sqFace_out_of_row (by simp only; omega)]
  | succ n ih =>
    intro u v hn hv
    have hv' := (newSq_snd_le (b := b) (Y0 := Y0) (c0 := c0) (sL := sL) u v).trans' hv
    have hs := rel_horiz hp hh' he' (u := u) (v := v + 1)
      (by rw [add_sub_cancel_right, sqFace_out_of_row (Or.inl hv), sqFace_out_of_row (Or.inl hv')])
    rw [add_sub_cancel_right] at hs
    exact hs.trans (ih u (v + 1) (by omega) hv')

/-- A square whose new brick is left of the new wall walks left to the outside of the old wall. -/
theorem reach_out_left (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') :
    ∀ n : ℕ, ∀ u v : ℤ, (u + 1).toNat = n → (bk (newSq b Y0 c0 sL (u, v))).1 ≤ 0 →
      Rel h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) (u, v)) outFace := by
  intro n
  induction n with
  | zero =>
    intro u v hn _
    rw [sqFace_out_of_col (by simp only [bk]; omega)]
  | succ n ih =>
    intro u v hn hu
    have hu' := (bk_newSq_fst_le (b := b) (Y0 := Y0) (c0 := c0) (sL := sL) u v).trans hu
    have hs := rel_vert hp hh' he' (u := u) (v := v)
      (by rw [sqFace_out_of_col (Or.inl hu), sqFace_out_of_col (Or.inl hu')])
    exact (reflTransGen_delStep_symm hs).trans (ih (u - 1) v (by omega) hu')

/-- A square whose new brick is right of the new wall walks right to the outside of the old
wall. -/
theorem reach_out_right (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') :
    ∀ n : ℕ, ∀ u v : ℤ, (2 * ((h' + 2 * b + 2 : ℕ) : ℤ) + 1 - u).toNat = n →
      2 * (h' : ℤ) + 1 ≤ (bk (newSq b Y0 c0 sL (u, v))).1 →
      Rel h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) (u, v)) outFace := by
  intro n
  induction n with
  | zero =>
    intro u v hn _
    rw [sqFace_out_of_col (by simp only [bk]; omega)]
  | succ n ih =>
    intro u v hn hu
    have hm := bk_newSq_fst_le (b := b) (Y0 := Y0) (c0 := c0) (sL := sL) (u + 1) v
    rw [add_sub_cancel_right] at hm
    have hu' := hu.trans hm
    have hs := rel_vert hp hh' he' (u := u + 1) (v := v)
      (by rw [add_sub_cancel_right, sqFace_out_of_col (Or.inr hu), sqFace_out_of_col (Or.inr hu')])
    rw [add_sub_cancel_right] at hs
    exact hs.trans (ih (u + 1) v (by omega) hu')

/-- **A square whose new face is the outer face reaches the outer face.** -/
theorem reach_out (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {u v : ℤ}
    (hπ : sqFace h' (newSq b Y0 c0 sL (u, v)) = outFace) :
    Rel h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) (u, v)) outFace := by
  rw [sqFace_eq_out_iff] at hπ
  have hlow : 0 ≤ v ∨ sqFace (h' + 2 * b + 2) (u, v) = outFace := by
    by_cases hv : 0 ≤ v
    · exact Or.inl hv
    · exact Or.inr (sqFace_out_of_row (by simp only; omega))
  rcases hlow with hv | hv
  · have hrow : 0 ≤ (newSq b Y0 c0 sL (u, v)).2 := by
      have := hp.Y1
      unfold newSq
      split_ifs <;> simp only <;> omega
    simp only [IsBrick, not_and] at hπ
    have e2 : (bk (newSq b Y0 c0 sL (u, v))).2 = (newSq b Y0 c0 sL (u, v)).2 := rfl
    have epar : ((bk (newSq b Y0 c0 sL (u, v))).1 - (bk (newSq b Y0 c0 sL (u, v))).2) % 2 = 0 := by
      simp only [bk]; omega
    rcases (by omega : (h' : ℤ) ≤ (newSq b Y0 c0 sL (u, v)).2 ∨
        (bk (newSq b Y0 c0 sL (u, v))).1 ≤ 0 ∨
        2 * (h' : ℤ) + 1 ≤ (bk (newSq b Y0 c0 sL (u, v))).1) with h1 | h1 | h1
    · exact reach_out_up hp hh' he' _ u v rfl h1
    · exact reach_out_left hp hh' he' _ u v rfl h1
    · exact reach_out_right hp hh' he' _ u v rfl h1
  · rw [hv]

/-! ## Bricks whose new face is a brick -/

/-- The favourite old brick of a new brick `F'`: the brick at the place of `F'` in the old wall,
with the cut and the band put back. -/
def kappa (b : ℕ) (Y0 c0 sL : ℤ) (F' : ℤ × ℤ) : ℤ × ℤ :=
  (F'.1 + sL + (if c0 + 1 ≤ F'.1 then 2 * (b : ℤ) else 0),
    F'.2 + (if Y0 ≤ F'.2 then 2 * (b : ℤ) else 0))

theorem sqFace_brick {h : ℕ} {X Y : ℤ} (hF : IsBrick h (X, Y)) : sqFace h (X, Y) = (X, Y) := by
  rw [sqFace_eq_brick_iff hF]
  simp only [IsBrick] at hF
  simp only [bk, Prod.mk.injEq, and_true]
  omega

theorem sqFace_brick_left {h : ℕ} {X Y : ℤ} (hF : IsBrick h (X, Y)) :
    sqFace h (X - 1, Y) = (X, Y) := by
  rw [sqFace_eq_brick_iff hF]
  simp only [IsBrick] at hF
  simp only [bk, Prod.mk.injEq, and_true]
  omega

theorem sqFace_eq_of_bk {h : ℕ} {s t : ℤ × ℤ} (e : bk s = bk t) : sqFace h s = sqFace h t :=
  sqFace_eq_iff.mpr (Or.inl e)

/-- Steps keep the new face. -/
theorem pi_eq_of_rel (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {F G : ℤ × ℤ}
    (hs : Rel h' b Y0 c0 sL F G) : pi h' b Y0 c0 sL F = pi h' b Y0 c0 sL G := by
  induction hs with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨m, hm, hown, hF, hG⟩ := hst
    exact ih.trans (pi_eq_of_own_none hp hh' he' hm hown hF hG)

/-- The new face of an old brick, from the new square of its right square. -/
theorem pi_brick (hp : Params h' b Y0 c0 sL) {X Y : ℤ} (hF : IsBrick (h' + 2 * b + 2) (X, Y)) :
    pi h' b Y0 c0 sL (X, Y) = sqFace h' (newSq b Y0 c0 sL (X, Y)) := by
  rw [← pi_sqFace hp, sqFace_brick hF]

set_option hygiene false in
/-- Decides the `if`s of `side` from the hypotheses, then the `if`s of `kappa`, and finishes with
`omega`. -/
macro "step_tac" : tactic => `(tactic| (
  simp (disch := omega) only [side, if_pos, if_neg, ↓reduceIte, sub_zero, add_zero] at hb ⊢
  (try simp (disch := omega) only [side, if_pos, if_neg, ↓reduceIte, sub_zero, add_zero] at hl)
  simp only [bk, kappa, Prod.mk.injEq, and_true, true_and] at hb ⊢
  (try simp only [bk, kappa, Prod.mk.injEq, and_true, true_and] at hl)
  (try split_ifs) <;> omega))

set_option hygiene false in
/-- Splits every `if` of `side` and `bk` in the goal and in `hb`, and finishes with `omega`. -/
macro "band_step_tac" : tactic => `(tactic| (
  simp only [side, bk, Prod.mk.injEq, and_true, true_and] at hb ⊢
  split_ifs at hb ⊢ <;> omega))

/-- Off the band: a step to the left inside the new face, or the brick is the favourite brick. -/
theorem exists_step_off (hp : Params h' b Y0 c0 sL) {X Y : ℤ}
    (hF : IsBrick (h' + 2 * b + 2) (X, Y)) (hb : IsBrick h' (bk (newSq b Y0 c0 sL (X, Y))))
    (hY : Y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ Y) :
    kappa b Y0 c0 sL (bk (newSq b Y0 c0 sL (X, Y))) = (X, Y) ∨
      (3 ≤ X ∧ bk (newSq b Y0 c0 sL (X - 2, Y)) = bk (newSq b Y0 c0 sL (X - 1, Y))) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  by_cases hl : 3 ≤ X ∧ bk (newSq b Y0 c0 sL (X - 2, Y)) = bk (newSq b Y0 c0 sL (X - 1, Y))
  · exact Or.inr hl
  · left
    simp only [IsBrick] at hF hb
    push_cast at hF
    rcases hY with hY | hY
    · simp only [newSq_below hY] at hl hb ⊢
      rcases (by omega : X ≤ c0 - 1 + sL ∨ X = c0 + sL ∨ X = c0 + sL + 1 ∨
          (c0 + sL + 2 ≤ X ∧ X ≤ c0 + sL + 2 * b - 1) ∨ X = c0 + sL + 2 * b ∨
          X = c0 + sL + 2 * b + 1 ∨ c0 + sL + 2 * b + 2 ≤ X) with
        hx | hx | hx | hx | hx | hx | hx <;> step_tac
    · have hv : Y0 + 2 * (b : ℤ) - 1 ≤ Y := by omega
      simp only [newSq_above (Y0 := Y0) (c0 := c0) (sL := sL) b1 hv] at hl hb ⊢
      rcases (by omega : X ≤ c0 - 1 + sL ∨ X = c0 + sL ∨ X = c0 + sL + 1 ∨
          (c0 + sL + 2 ≤ X ∧ X ≤ c0 + sL + 2 * b - 1) ∨ X = c0 + sL + 2 * b ∨
          X = c0 + sL + 2 * b + 1 ∨ c0 + sL + 2 * b + 2 ≤ X) with
        hx | hx | hx | hx | hx | hx | hx <;> step_tac

/-- In the band: a step down to the left or down to the right inside the new face. -/
theorem exists_step_band (hp : Params h' b Y0 c0 sL) {X t : ℤ}
    (hF : IsBrick (h' + 2 * b + 2) (X, Y0 + t)) (hb : IsBrick h' (bk (newSq b Y0 c0 sL (X, Y0 + t))))
    (ht1 : 0 ≤ t) (ht2 : t ≤ 2 * b - 1) :
    (2 ≤ X ∧ bk (newSq b Y0 c0 sL (X - 1, Y0 + t - 1)) = bk (newSq b Y0 c0 sL (X - 1, Y0 + t))) ∨
      (X + 1 ≤ 2 * ((h' + 2 * b + 2 : ℕ) : ℤ) ∧
        bk (newSq b Y0 c0 sL (X, Y0 + t - 1)) = bk (newSq b Y0 c0 sL (X, Y0 + t))) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  simp only [IsBrick] at hF hb
  push_cast at hF ⊢
  have e1 : ∀ u, newSq b Y0 c0 sL (u, Y0 + t) = (side b c0 sL (off b t) u, Y0 - 1) := by
    intro u; rw [newSq_band (by omega) (by omega), add_sub_cancel_left]
  have e2 : ∀ u, newSq b Y0 c0 sL (u, Y0 + t - 1) = (side b c0 sL (off b (t - 1)) u, Y0 - 1) := by
    intro u; rw [newSq_band (by omega) (by omega)]; ring_nf
  simp only [e1, e2] at hb ⊢
  by_cases ht : t + 1 ≤ b
  · have oa : off b (t - 1) = -t := by unfold off; rw [if_pos (by omega)]; ring
    have ob : off b t = -(t + 1) := by unfold off; rw [if_pos ht]
    simp only [oa, ob] at hb ⊢
    by_cases hL : X - sL + t ≤ c0 - 1
    · right; band_step_tac
    · left; band_step_tac
  · have oa : off b (t - 1) = t - 2 * b := by unfold off; split_ifs <;> omega
    have ob : off b t = t - 2 * b + 1 := by unfold off; rw [if_neg (by omega)]; ring
    simp only [oa, ob] at hb ⊢
    by_cases hR : c0 ≤ X - sL - 4 * b + t
    · right; band_step_tac
    · left; band_step_tac

/-- One step of the walk to the favourite brick: a step to an old brick `G` in the same new face,
from which the walk goes on. -/
theorem reach_of_step (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {F G : ℤ × ℤ}
    (hF : IsBrick (h' + 2 * b + 2) F) (hbF : IsBrick h' (bk (newSq b Y0 c0 sL F)))
    (hG : IsBrick (h' + 2 * b + 2) G) (hs : Rel h' b Y0 c0 sL F G)
    (ih : IsBrick h' (bk (newSq b Y0 c0 sL G)) →
      Rel h' b Y0 c0 sL G (kappa b Y0 c0 sL (bk (newSq b Y0 c0 sL G)))) :
    Rel h' b Y0 c0 sL F (kappa b Y0 c0 sL (bk (newSq b Y0 c0 sL F))) := by
  have e := pi_eq_of_rel hp hh' he' hs
  obtain ⟨X, Y⟩ := F
  obtain ⟨X', Y'⟩ := G
  rw [pi_brick hp hF, pi_brick hp hG, (sqFace_eq_brick_iff hbF).mpr rfl] at e
  have e' := (sqFace_eq_brick_iff hbF).mp e.symm
  rw [e'] at ih
  exact hs.trans (ih hbF)

/-- **Every old brick whose new face is a brick reaches the favourite brick of its new face.**
The proof is by induction on `2 * Y + X`, which drops at each step. -/
theorem reach_kappa (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') :
    ∀ n : ℕ, ∀ X Y : ℤ, (2 * Y + X).toNat = n → IsBrick (h' + 2 * b + 2) (X, Y) →
      IsBrick h' (bk (newSq b Y0 c0 sL (X, Y))) →
      Rel h' b Y0 c0 sL (X, Y) (kappa b Y0 c0 sL (bk (newSq b Y0 c0 sL (X, Y)))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y hn hF hbF
  have hF' := hF
  simp only [IsBrick] at hF'
  have hY1 := hp.Y1
  by_cases hY : Y ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ Y
  · rcases exists_step_off hp hF hbF hY with hk | ⟨hX, he⟩
    · rw [hk]
    · have hG : IsBrick (h' + 2 * b + 2) (X - 2, Y) := by simp only [IsBrick]; omega
      have hs := rel_vert hp hh' he' (u := X - 1) (v := Y)
        (by rw [show X - 1 - 1 = X - 2 by ring]; exact sqFace_eq_of_bk he)
      rw [show X - 1 - 1 = X - 2 by ring, sqFace_brick hG, sqFace_brick_left hF] at hs
      exact reach_of_step hp hh' he' hF hbF hG (reflTransGen_delStep_symm hs)
        (ih _ (by omega) (X - 2) Y rfl hG)
  · obtain ⟨t, rfl⟩ : ∃ t, Y = Y0 + t := ⟨Y - Y0, by ring⟩
    rcases exists_step_band hp hF hbF (by omega) (by omega) with ⟨hX, he⟩ | ⟨hX, he⟩
    · have hG : IsBrick (h' + 2 * b + 2) (X - 1, Y0 + t - 1) := by
        simp only [IsBrick]; omega
      have hs := rel_horiz hp hh' he' (u := X - 1) (v := Y0 + t) (sqFace_eq_of_bk he)
      rw [sqFace_brick hG, sqFace_brick_left hF] at hs
      exact reach_of_step hp hh' he' hF hbF hG (reflTransGen_delStep_symm hs)
        (ih _ (by omega) (X - 1) (Y0 + t - 1) rfl hG)
    · have hG : IsBrick (h' + 2 * b + 2) (X + 1, Y0 + t - 1) := by
        simp only [IsBrick]; omega
      have hs := rel_horiz hp hh' he' (u := X) (v := Y0 + t) (sqFace_eq_of_bk he)
      have hl := sqFace_brick_left hG
      rw [add_sub_cancel_right] at hl
      rw [hl, sqFace_brick hF] at hs
      exact reach_of_step hp hh' he' hF hbF hG (reflTransGen_delStep_symm hs)
        (ih _ (by omega) (X + 1) (Y0 + t - 1) rfl hG)

/-- Every wall face reaches a face fixed by its new face: the outer face if the new face is the
outer face (`HexHole.reach_out`), and the favourite brick otherwise (`HexHole.reach_kappa`). -/
theorem reach_base (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {F : ℤ × ℤ}
    (hF : IsWallFace (h' + 2 * b + 2) F) :
    Rel h' b Y0 c0 sL F
      (if pi h' b Y0 c0 sL F = outFace then outFace else kappa b Y0 c0 sL (pi h' b Y0 c0 sL F)) := by
  rcases hF with hb | rfl
  · obtain ⟨X, Y⟩ := F
    rw [pi_brick hp hb]
    split_ifs with ho
    · have hs := reach_out hp hh' he' ho
      rwa [sqFace_brick hb] at hs
    · have hbF : IsBrick h' (bk (newSq b Y0 c0 sL (X, Y))) := by
        by_contra hn
        exact ho (sqFace_eq_out_iff.mpr hn)
      rw [(sqFace_eq_brick_iff hbF).mpr rfl]
      exact reach_kappa hp hh' he' _ X Y rfl hb hbF
  · rw [if_pos pi_outFace]

/-- **The condition `conn`.** Two old faces with the same new face both reach the face given by
`HexHole.reach_base`, and steps can be reversed (`delStep_symm`). -/
theorem conn (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {F G : ℤ × ℤ}
    (hF : IsWallFace (h' + 2 * b + 2) F) (hG : IsWallFace (h' + 2 * b + 2) G)
    (he : pi h' b Y0 c0 sL F = pi h' b Y0 c0 sL G) : Rel h' b Y0 c0 sL F G := by
  have h1 := reach_base hp hh' he' hF
  have h2 := reach_base hp hh' he' hG
  rw [he] at h1
  exact h1.trans (reflTransGen_delStep_symm h2)

end HexHole

/-- **The hexagonal hole of (7.3) as a shape.** -/
@[expose] def HexHole.shape {h' b : ℕ} {Y0 c0 sL : ℤ} (hp : HexHole.Params h' b Y0 c0 sL)
    (hh' : 1 ≤ h') (he' : Even h') : Shape (h' + 2 * b + 2) h' where
  own := HexHole.own h' b Y0 c0 sL
  π := HexHole.pi h' b Y0 c0 sL
  own_mem _ _ _ hm := HexHole.own_mem hh' he' hm
  own_surj _ hm' := HexHole.own_surj hp hh' he' hm'
  π_face F _ := HexHole.pi_face F
  π_surj _ hF' := HexHole.pi_surj hp hF'
  del _ hm hown _ hF _ hG := HexHole.pi_eq_of_own_none hp hh' he' hm hown hF hG
  keep _ hm _ hown := HexHole.image_cellFaces_of_own hp hh' he' hm hown
  conn _ _ hF hG he := HexHole.conn hp hh' he' hF hG he

@[simp] theorem HexHole.shape_own {h' b : ℕ} {Y0 c0 sL : ℤ} (hp : HexHole.Params h' b Y0 c0 sL)
    (hh' : 1 ≤ h') (he' : Even h') : (HexHole.shape hp hh' he').own = HexHole.own h' b Y0 c0 sL :=
  rfl

@[simp] theorem HexHole.shape_π {h' b : ℕ} {Y0 c0 sL : ℤ} (hp : HexHole.Params h' b Y0 c0 sL)
    (hh' : 1 ≤ h') (he' : Even h') : (HexHole.shape hp hh' he').π = HexHole.pi h' b Y0 c0 sL :=
  rfl

end GraphMinor.GM13
