module

public import GraphMinor.GM13.Section7HoleImage
public import GraphMinor.GM13.Section7Translate

/-!
# Graph Minors XIII, (7.3): the hole as a shape

This file finishes the hole `Hole(Y0, c0)` as a `Shape (h' + 2) h'` (`Hole.shape`). What is left
after `Section7HoleImage.lean` is the condition `conn`: two old faces in the same new face are
joined by steps across elements that the hole deletes.

First, the face map on bricks has a closed form without parities (`Hole.pi_brick`): a brick
`(X, Y)` below the band moves left by `0`, `2` or `4` according to its place against the cut, a
brick of the old row `Y0` goes to the new row `Y0 - 1` moving left by `1` or `3`, and a brick
above moves by `(-2, -2)`.

A new face that is a brick has a favourite old brick (`Hole.kappa`). Every old brick reaches the
favourite brick of its new face by steps: to the left across a deleted vertical edge of the cut,
or down across a deleted horizontal edge of the band (`Hole.reach_kappa`). An old brick whose new
face is the outer face is at most two steps from the outer face, across deleted vertical edges
at the side of the wall (`Hole.reach_out`).
-/

public section

namespace GraphMinor.GM13

open Set

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- The brick of the new wall that contains the old brick `F`, before the test that it is a
brick of the new wall. -/
@[expose] def bImg (Y0 c0 : ℤ) (F : ℤ × ℤ) : ℤ × ℤ :=
  if F.2 ≤ Y0 - 1 then
    (if F.1 ≤ c0 then F else if F.1 ≤ c0 + 2 then (F.1 - 2, F.2) else (F.1 - 4, F.2))
  else if F.2 = Y0 then
    (if F.1 ≤ c0 + 1 then (F.1 - 1, Y0 - 1) else (F.1 - 3, Y0 - 1))
  else (F.1 - 2, F.2 - 2)

theorem bk_newSq {X Y : ℤ} (hXY : (X - Y) % 2 = 0) :
    bk (newSq Y0 c0 (X, Y)) = bImg Y0 c0 (X, Y) := by
  obtain ⟨t, rfl⟩ : ∃ t, X = Y + 2 * t := ⟨(X - Y) / 2, by omega⟩
  simp only [newSq, bImg]
  split_ifs <;> simp only [bk, Prod.mk.injEq, and_true] <;> omega

/-- **The face map on bricks.** -/
theorem pi_brick {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y)) :
    pi h' Y0 c0 (X, Y) = if IsBrick h' (bImg Y0 c0 (X, Y)) then bImg Y0 c0 (X, Y) else outFace := by
  unfold pi
  rw [if_pos hF, sqFace_eq, bk_newSq hF.2.2.2.2]

theorem bImg_ne_outFace_of_isBrick {F : ℤ × ℤ} (hF : IsBrick h' (bImg Y0 c0 F)) :
    bImg Y0 c0 F ≠ outFace := fun e => not_isBrick_outFace h' (e ▸ hF)

/-- The favourite old face of a new face. -/
def kappa (Y0 c0 : ℤ) (F : ℤ × ℤ) : ℤ × ℤ :=
  if F = outFace then outFace
  else if F.2 ≤ Y0 - 1 then (if F.1 ≤ c0 then F else (F.1 + 4, F.2)) else (F.1 + 2, F.2 + 2)

/-! ## Steps across deleted elements -/

theorem own_none {m : ℤ × ℤ} (hd : ¬ IsWallCell h' (cell Y0 c0 m)) : own h' Y0 c0 m = none := by
  unfold own
  rw [if_neg hd]

/-- A step across a deleted vertical edge, between the squares on its two sides. -/
theorem delStep_vert (he' : Even h') {x y : ℤ} (hw : IsWallCell (h' + 2) (2 * x, 2 * y + 1))
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * x, 2 * y + 1))) :
    DelStep (h := h' + 2) (own h' Y0 c0) (sqFace (h' + 2) (x - 1, y)) (sqFace (h' + 2) (x, y)) := by
  refine delStep_of ((mem_fig1WallCells_iff (by omega) (even_succ_succ he') _).mpr hw)
    (own_none hd) (q := (2 * (x - 1) + 1, 2 * y + 1)) (q' := (2 * x + 1, 2 * y + 1)) ?_ ?_ rfl rfl <;>
  · rw [mem_squaresAbove_iff]; omega

/-- A step across a deleted horizontal edge, between the squares below and above it. -/
theorem delStep_horiz (he' : Even h') {x y : ℤ} (hw : IsWallCell (h' + 2) (2 * x + 1, 2 * y))
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * x + 1, 2 * y))) :
    DelStep (h := h' + 2) (own h' Y0 c0) (sqFace (h' + 2) (x, y - 1)) (sqFace (h' + 2) (x, y)) := by
  refine delStep_of ((mem_fig1WallCells_iff (by omega) (even_succ_succ he') _).mpr hw)
    (own_none hd) (q := (2 * x + 1, 2 * (y - 1) + 1)) (q' := (2 * x + 1, 2 * y + 1)) ?_ ?_ rfl rfl <;>
  · rw [mem_squaresAbove_iff]; omega

theorem sqFace_of_bk {h : ℕ} {s F : ℤ × ℤ} (hF : IsBrick h F) (hs : bk s = F) : sqFace h s = F :=
  (sqFace_eq_brick_iff hF).mpr hs

theorem sqFace_of_not_brick {h : ℕ} {s : ℤ × ℤ} (hs : ¬ IsBrick h (bk s)) : sqFace h s = outFace :=
  sqFace_eq_out_iff.mpr hs

/-- Decides that an element is deleted, from the position fixed by the hypotheses. -/
macro "del_tac" : tactic => `(tactic| (
  simp only [cell_vertex, cell_horiz, cell_vert, vertexCell, horizCell, vertCell];
  split_ifs <;> simp only [IsWallCell] <;> omega))

/-- Proves that a square lies in a given face. -/
macro "face_tac" : tactic => `(tactic| first
  | (apply sqFace_of_bk
     · simp only [IsBrick]; omega
     · simp only [bk, Prod.mk.injEq, and_true]; omega)
  | (apply sqFace_of_not_brick; simp only [bk, IsBrick]; omega))

/-- Proves a wall cell from coordinates. -/
macro "wcell_tac" : tactic => `(tactic| (simp only [IsWallCell]; push_cast; omega))

/-- Old faces joined by steps across elements that the hole deletes. -/
abbrev Rel (h' : ℕ) (Y0 c0 : ℤ) : ℤ × ℤ → ℤ × ℤ → Prop :=
  Relation.ReflTransGen (DelStep (h := h' + 2) (own h' Y0 c0))

/-! ## Bricks whose new face is the outer face -/

theorem out_L1 (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y)) (hX : X ≤ 2)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * (X - 1), 2 * Y + 1))) : Rel h' Y0 c0 (X, Y) outFace := by
  simp only [IsBrick] at hF
  have hs := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X - 1) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X - 1 - 1, Y) = outFace by face_tac,
    show sqFace (h' + 2) (X - 1, Y) = (X, Y) by face_tac] at hs
  exact .single (delStep_symm hs)

theorem out_L2 (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y)) (hX : X = 3 ∨ X = 4)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * (X - 1), 2 * Y + 1)))
    (hd' : ¬ IsWallCell h' (cell Y0 c0 (2 * (X - 3), 2 * Y + 1))) :
    Rel h' Y0 c0 (X, Y) outFace := by
  simp only [IsBrick] at hF
  have hs := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X - 1) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X - 1 - 1, Y) = (X - 2, Y) by face_tac,
    show sqFace (h' + 2) (X - 1, Y) = (X, Y) by face_tac] at hs
  have hs' := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X - 3) (y := Y) (by wcell_tac) hd'
  rw [show sqFace (h' + 2) (X - 3 - 1, Y) = outFace by face_tac,
    show sqFace (h' + 2) (X - 3, Y) = (X - 2, Y) by face_tac] at hs'
  exact (Relation.ReflTransGen.single (delStep_symm hs)).tail (delStep_symm hs')

theorem out_R1 (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y)) (hX : 2 * (h' : ℤ) + 3 ≤ X)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * (X + 1), 2 * Y + 1))) :
    Rel h' Y0 c0 (X, Y) outFace := by
  simp only [IsBrick] at hF
  push_cast at hF
  have hs := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X + 1) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X + 1 - 1, Y) = (X, Y) by face_tac,
    show sqFace (h' + 2) (X + 1, Y) = outFace by face_tac] at hs
  exact .single hs

theorem out_R2 (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y))
    (hX : X = 2 * (h' : ℤ) + 1 ∨ X = 2 * (h' : ℤ) + 2)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * (X + 1), 2 * Y + 1)))
    (hd' : ¬ IsWallCell h' (cell Y0 c0 (2 * (X + 3), 2 * Y + 1))) :
    Rel h' Y0 c0 (X, Y) outFace := by
  simp only [IsBrick] at hF
  push_cast at hF
  have hs := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X + 1) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X + 1 - 1, Y) = (X, Y) by face_tac,
    show sqFace (h' + 2) (X + 1, Y) = (X + 2, Y) by face_tac] at hs
  have hs' := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X + 3) (y := Y) (by wcell_tac) hd'
  rw [show sqFace (h' + 2) (X + 3 - 1, Y) = (X + 2, Y) by face_tac,
    show sqFace (h' + 2) (X + 3, Y) = outFace by face_tac] at hs'
  exact (Relation.ReflTransGen.single hs).tail hs'

theorem not_isBrick_bImg {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y))
    (hπ : pi h' Y0 c0 (X, Y) = outFace) : ¬ IsBrick h' (bImg Y0 c0 (X, Y)) := by
  rw [pi_brick hF] at hπ
  split_ifs at hπ with h1
  · exact absurd hπ (bImg_ne_outFace_of_isBrick h1)
  · exact h1

/-- Applies the right one of the four chains to the outer face. -/
macro "out_tac" he':term : tactic => `(tactic| first
  | omega
  | (refine out_L1 $he' (by assumption) (by assumption) ?_; del_tac)
  | (refine out_L2 $he' (by assumption) (by assumption) ?_ ?_ <;> del_tac)
  | (refine out_R1 $he' (by assumption) (by assumption) ?_; del_tac)
  | (refine out_R2 $he' (by assumption) (by assumption) ?_ ?_ <;> del_tac))

theorem reach_out_below (hp : Params h' Y0 c0) (he' : Even h') {X Y : ℤ}
    (hF : IsBrick (h' + 2) (X, Y)) (hb : ¬ IsBrick h' (bImg Y0 c0 (X, Y))) (hY : Y ≤ Y0 - 1) :
    Rel h' Y0 c0 (X, Y) outFace := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hk : ∃ k, h' = k + k := he'
  obtain ⟨k, hk⟩ := hk
  have hF' := hF
  simp only [IsBrick] at hF'
  push_cast at hF'
  simp only [bImg, if_pos hY] at hb
  split_ifs at hb <;> simp only [IsBrick, not_and] at hb <;>
  rcases (by omega : X ≤ 2 ∨ (X = 3 ∨ X = 4) ∨ 2 * (h' : ℤ) + 3 ≤ X ∨
    (X = 2 * (h' : ℤ) + 1 ∨ X = 2 * (h' : ℤ) + 2)) with hX | hX | hX | hX <;>
  out_tac he'

theorem reach_out_band (hp : Params h' Y0 c0) (he' : Even h') {X : ℤ}
    (hF : IsBrick (h' + 2) (X, Y0)) (hb : ¬ IsBrick h' (bImg Y0 c0 (X, Y0))) :
    Rel h' Y0 c0 (X, Y0) outFace := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hk : ∃ k, h' = k + k := he'
  obtain ⟨k, hk⟩ := hk
  have hF' := hF
  simp only [IsBrick] at hF'
  push_cast at hF'
  simp only [bImg, if_neg (show ¬ Y0 ≤ Y0 - 1 by omega), if_pos] at hb
  split_ifs at hb <;> simp only [IsBrick, not_and] at hb <;>
  rcases (by omega : X ≤ 2 ∨ (X = 3 ∨ X = 4) ∨ 2 * (h' : ℤ) + 3 ≤ X ∨
    (X = 2 * (h' : ℤ) + 1 ∨ X = 2 * (h' : ℤ) + 2)) with hX | hX | hX | hX <;>
  out_tac he'

theorem reach_out_above (hp : Params h' Y0 c0) (he' : Even h') {X Y : ℤ}
    (hF : IsBrick (h' + 2) (X, Y)) (hb : ¬ IsBrick h' (bImg Y0 c0 (X, Y))) (hY : Y0 + 1 ≤ Y) :
    Rel h' Y0 c0 (X, Y) outFace := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hk : ∃ k, h' = k + k := he'
  obtain ⟨k, hk⟩ := hk
  have hF' := hF
  simp only [IsBrick] at hF'
  push_cast at hF'
  simp only [bImg, if_neg (show ¬ Y ≤ Y0 - 1 by omega), if_neg (show ¬ Y = Y0 by omega),
    IsBrick, not_and] at hb
  rcases (by omega : X ≤ 2 ∨ 2 * (h' : ℤ) + 3 ≤ X) with hX | hX <;>
  out_tac he'

/-- **An old brick whose new face is the outer face reaches the outer face.** -/
theorem reach_out (hp : Params h' Y0 c0) (he' : Even h') {X Y : ℤ}
    (hF : IsBrick (h' + 2) (X, Y)) (hπ : pi h' Y0 c0 (X, Y) = outFace) :
    Rel h' Y0 c0 (X, Y) outFace := by
  have hb := not_isBrick_bImg hF hπ
  rcases (by omega : Y ≤ Y0 - 1 ∨ Y = Y0 ∨ Y0 + 1 ≤ Y) with hY | rfl | hY
  · exact reach_out_below hp he' hF hb hY
  · exact reach_out_band hp he' hF hb
  · exact reach_out_above hp he' hF hb hY

/-! ## Bricks whose new face is a brick -/

/-- A step across a deleted element keeps the new face. -/
theorem pi_eq_of_delStep (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') {F G : ℤ × ℤ}
    (hs : DelStep (h := h' + 2) (own h' Y0 c0) F G) : pi h' Y0 c0 F = pi h' Y0 c0 G := by
  obtain ⟨m, hm, hown, hF, hG⟩ := hs
  exact pi_eq_of_own_none hp hh' he' hm hown hF hG

theorem step_left (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y)) (hX : 3 ≤ X)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * (X - 1), 2 * Y + 1))) :
    DelStep (h := h' + 2) (own h' Y0 c0) (X, Y) (X - 2, Y) := by
  simp only [IsBrick] at hF
  have hs := delStep_vert (Y0 := Y0) (c0 := c0) he' (x := X - 1) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X - 1 - 1, Y) = (X - 2, Y) by face_tac,
    show sqFace (h' + 2) (X - 1, Y) = (X, Y) by face_tac] at hs
  exact delStep_symm hs

theorem step_downLeft (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y)) (hX : 2 ≤ X)
    (hY : 1 ≤ Y) (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * (X - 1) + 1, 2 * Y))) :
    DelStep (h := h' + 2) (own h' Y0 c0) (X, Y) (X - 1, Y - 1) := by
  simp only [IsBrick] at hF
  have hs := delStep_horiz (Y0 := Y0) (c0 := c0) he' (x := X - 1) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X - 1, Y - 1) = (X - 1, Y - 1) by face_tac,
    show sqFace (h' + 2) (X - 1, Y) = (X, Y) by face_tac] at hs
  exact delStep_symm hs

theorem step_downRight (he' : Even h') {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y))
    (hX : X ≤ 2 * (h' : ℤ) + 3) (hY : 1 ≤ Y)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * X + 1, 2 * Y))) :
    DelStep (h := h' + 2) (own h' Y0 c0) (X, Y) (X + 1, Y - 1) := by
  simp only [IsBrick] at hF
  push_cast at hF
  have hs := delStep_horiz (Y0 := Y0) (c0 := c0) he' (x := X) (y := Y) (by wcell_tac) hd
  rw [show sqFace (h' + 2) (X, Y - 1) = (X + 1, Y - 1) by face_tac,
    show sqFace (h' + 2) (X, Y) = (X, Y) by face_tac] at hs
  exact delStep_symm hs

theorem isBrick_bImg_of_pi_ne {X Y : ℤ} (hF : IsBrick (h' + 2) (X, Y))
    (hπ : pi h' Y0 c0 (X, Y) ≠ outFace) :
    IsBrick h' (bImg Y0 c0 (X, Y)) ∧ pi h' Y0 c0 (X, Y) = bImg Y0 c0 (X, Y) := by
  rw [pi_brick hF] at hπ ⊢
  split_ifs at hπ ⊢ with h1
  · exact ⟨h1, rfl⟩
  · exact absurd rfl hπ

set_option hygiene false in
/-- Shows that a brick is the favourite brick of its new face. -/
macro "kappa_tac" : tactic => `(tactic| (
  simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, kappa] at hb hne ⊢
  (try rw [if_neg hne])
  (try simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, Prod.mk.injEq, and_true])
  (try omega)))

/-- The step from a brick whose new face is a brick, towards the favourite brick. -/
theorem exists_step (hp : Params h' Y0 c0) (he' : Even h') {X Y : ℤ}
    (hF : IsBrick (h' + 2) (X, Y)) (hπ : pi h' Y0 c0 (X, Y) ≠ outFace) :
    kappa Y0 c0 (pi h' Y0 c0 (X, Y)) = (X, Y) ∨
      ∃ X₁ Y₁, DelStep (h := h' + 2) (own h' Y0 c0) (X, Y) (X₁, Y₁) ∧ 2 * Y₁ + X₁ < 2 * Y + X := by
  obtain ⟨hb, he⟩ := isBrick_bImg_of_pi_ne hF hπ
  rw [he]
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hk : ∃ k, h' = k + k := he'
  obtain ⟨k, hk⟩ := hk
  have hF' := hF
  simp only [IsBrick] at hF'
  push_cast at hF'
  have hne := bImg_ne_outFace_of_isBrick hb
  simp only [bImg] at hb hne ⊢
  rcases (by omega : Y0 + 2 ≤ Y ∨ Y = Y0 + 1 ∨ Y = Y0 ∨ (Y ≤ Y0 - 1 ∧ (X ≤ c0 ∨ c0 + 5 ≤ X)) ∨
    (Y ≤ Y0 - 1 ∧ c0 + 1 ≤ X ∧ X ≤ c0 + 4)) with hY | hY | hY | ⟨hY, hX⟩ | ⟨hY, hX⟩
  · left
    kappa_tac
  · right
    simp (disch := omega) only [if_pos, if_neg, IsBrick] at hb
    rcases (by omega : X ≤ c0 + 2 ∨ c0 + 3 ≤ X) with hX | hX
    · exact ⟨X - 1, Y - 1, step_downLeft he' hF (by omega) (by omega) (by del_tac), by omega⟩
    · exact ⟨X + 1, Y - 1, step_downRight he' hF (by omega) (by omega) (by del_tac), by omega⟩
  · right
    rcases (by omega : X ≤ c0 + 1 ∨ (c0 + 2 ≤ X ∧ X ≤ c0 + 3) ∨ c0 + 4 ≤ X) with hX | hX | hX
    · simp (disch := omega) only [if_pos, if_neg, IsBrick] at hb
      exact ⟨X - 1, Y - 1, step_downLeft he' hF (by omega) (by omega) (by del_tac), by omega⟩
    · simp (disch := omega) only [if_pos, if_neg, IsBrick] at hb
      exact ⟨X - 1, Y - 1, step_downLeft he' hF (by omega) (by omega) (by del_tac), by omega⟩
    · simp (disch := omega) only [if_pos, if_neg, IsBrick] at hb
      exact ⟨X + 1, Y - 1, step_downRight he' hF (by omega) (by omega) (by del_tac), by omega⟩
  · left
    rcases hX with hX | hX <;> kappa_tac
  · right
    rcases (by omega : X ≤ c0 + 2 ∨ c0 + 3 ≤ X) with hX' | hX' <;>
    · simp (disch := omega) only [if_pos, if_neg, IsBrick] at hb
      exact ⟨X - 2, Y, step_left he' hF (by omega) (by del_tac), by omega⟩

/-- **Every old brick reaches the favourite brick of its new face.** The proof is by induction on
`2 * Y + X`, which drops at each step of `Hole.exists_step`. -/
theorem reach_kappa (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') {F : ℤ × ℤ}
    (hF : IsBrick (h' + 2) F) (hπ : pi h' Y0 c0 F ≠ outFace) :
    Rel h' Y0 c0 F (kappa Y0 c0 (pi h' Y0 c0 F)) := by
  suffices H : ∀ n : ℕ, ∀ X Y : ℤ, (2 * Y + X).toNat = n → IsBrick (h' + 2) (X, Y) →
      pi h' Y0 c0 (X, Y) ≠ outFace → Rel h' Y0 c0 (X, Y) (kappa Y0 c0 (pi h' Y0 c0 (X, Y))) from
    H _ F.1 F.2 rfl hF hπ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y hn hb hne
  rcases exists_step hp he' hb hne with hk | ⟨X₁, Y₁, hs, hlt⟩
  · rw [hk]
  · -- The new brick `(X₁, Y₁)` has the same new face, so it is a brick and not the outer face.
    have he := pi_eq_of_delStep hp hh' he' hs
    have hne₁ : pi h' Y0 c0 (X₁, Y₁) ≠ outFace := he ▸ hne
    have hb₁ : IsBrick (h' + 2) (X₁, Y₁) := by
      obtain ⟨m, -, -, -, hG⟩ := hs
      rcases isWallFace_of_mem_cellFaces hG with hG' | hG'
      · exact hG'
      · exact absurd (by rw [hG', pi_outFace]) hne₁
    have hpos : 0 ≤ 2 * Y₁ + X₁ := by simp only [IsBrick] at hb₁; omega
    rw [he]
    exact Relation.ReflTransGen.head hs (ih _ (by omega) X₁ Y₁ rfl hb₁ hne₁)

/-- Every wall face reaches a face fixed by its new face: the outer face if the new face is the
outer face (`Hole.reach_out`), and the favourite brick otherwise (`Hole.reach_kappa`). -/
theorem reach_base (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') {F : ℤ × ℤ}
    (hF : IsWallFace (h' + 2) F) :
    Rel h' Y0 c0 F (if pi h' Y0 c0 F = outFace then outFace else kappa Y0 c0 (pi h' Y0 c0 F)) := by
  rcases hF with hb | rfl
  · split_ifs with ho
    · exact reach_out hp he' hb ho
    · exact reach_kappa hp hh' he' hb ho
  · rw [if_pos pi_outFace]

/-- **The condition `conn`.** Two old faces with the same new face both reach the face given by
`Hole.reach_base`, and steps can be reversed (`delStep_symm`). -/
theorem conn (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') {F G : ℤ × ℤ}
    (hF : IsWallFace (h' + 2) F) (hG : IsWallFace (h' + 2) G) (he : pi h' Y0 c0 F = pi h' Y0 c0 G) :
    Rel h' Y0 c0 F G := by
  have h1 := reach_base hp hh' he' hF
  have h2 := reach_base hp hh' he' hG
  rw [he] at h1
  haveI : Std.Symm (DelStep (h := h' + 2) (own h' Y0 c0)) := ⟨fun _ _ => delStep_symm⟩
  exact h1.trans (Relation.ReflTransGen.stdSymm.symm _ _ h2)

end Hole

/-- **The hole of (7.3) as a shape.** -/
@[expose] def Hole.shape {h' : ℕ} {Y0 c0 : ℤ} (hp : Hole.Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') : Shape (h' + 2) h' where
  own := Hole.own h' Y0 c0
  π := Hole.pi h' Y0 c0
  own_mem _ _ _ hm := Hole.own_mem hh' he' hm
  own_surj _ hm' := Hole.own_surj hp hh' he' hm'
  π_face F _ := Hole.pi_face F
  π_surj _ hF' := Hole.pi_surj hp hF'
  del _ hm hown _ hF _ hG := Hole.pi_eq_of_own_none hp hh' he' hm hown hF hG
  keep _ hm _ hown := Hole.image_cellFaces_of_own hp hh' he' hm hown
  conn _ _ hF hG he := Hole.conn hp hh' he' hF hG he

@[simp] theorem Hole.shape_own {h' : ℕ} {Y0 c0 : ℤ} (hp : Hole.Params h' Y0 c0) (hh' : 1 ≤ h')
    (he' : Even h') : (Hole.shape hp hh' he').own = Hole.own h' Y0 c0 := rfl

@[simp] theorem Hole.shape_π {h' : ℕ} {Y0 c0 : ℤ} (hp : Hole.Params h' Y0 c0) (hh' : 1 ≤ h')
    (he' : Even h') : (Hole.shape hp hh' he').π = Hole.pi h' Y0 c0 := rfl

end GraphMinor.GM13
