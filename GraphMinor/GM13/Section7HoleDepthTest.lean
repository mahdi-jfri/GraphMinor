module

public import GraphMinor.GM13.Section7HoleDepth

/-!
# Graph Minors XIII, (7.3): the hole passes the depth test

This file proves that the hole `Hole(Y0, c0)` passes `Shape.DepthTest` when its parameters are
good (`Hole.depthTest`), so that it has `KI 4` (`Hole.ki`).

The new face of an old brick `F` is `Hole.bImg F` when that is a brick, and `Hole.bImg` moves `F`
by one of `(0, 0)`, `(2, 0)`, `(4, 0)`, `(1, 1)`, `(3, 1)`, `(2, 2)`. These six moves lie in the
diamond of radius 2 around `(2, 0)` (`Hole.bImg_move`). So two bricks move apart by at most 4 in
the sum of the coordinates and by at most 2 in height, and their hex distance drops by at most 2
(`Hole.hex_le`). Each side of the wall comes closer by at most 2, so depths drop by at most 2
(`Hole.brick_le`). The deleted elements are in `Section7HoleDepth.lean`, except the vertical
edges, which are here (`Hole.del_vert`).
-/

public section

namespace GraphMinor.GM13

open Set

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- (S3) at a deleted vertical edge from `(x, y)`: the square `(x, y)`, or `(x - 1, y)` below
the band when `Y0` is even. -/
theorem del_vert (hg : Good h' Y0 c0) {x y : ℤ} {s : ℤ × ℤ}
    (hw : IsWallCell (h' + 2) (2 * x, 2 * y + 1))
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * x, 2 * y + 1)))
    (hs : s = if Y0 % 2 = 0 ∧ y ≤ Y0 - 1 then (x - 1, y) else (x, y)) :
    faceDepth (h' + 2) (sqFace (h' + 2) s) ≤
      faceDepth h' (pi h' Y0 c0 (sqFace (h' + 2) s)) + 1 := by
  s3_tac vertCell

/-- The move of a brick under the hole lies in the diamond of radius 2 around `(2, 0)`. -/
theorem bImg_move (F : ℤ × ℤ) :
    0 ≤ F.2 - (bImg Y0 c0 F).2 ∧
      max (F.1 - (bImg Y0 c0 F).1 - 2) (2 - (F.1 - (bImg Y0 c0 F).1)) +
        (F.2 - (bImg Y0 c0 F).2) ≤ 2 := by
  simp only [bImg]
  split_ifs <;> (try simp only) <;> omega

/-- The hex distance drops by at most 2 when the two differences move by at most 2 in height and
by at most 4 in the sum of both coordinates. -/
theorem hex_aux (u v u' v' : ℤ) (h1 : v - v' ≤ 2) (h2 : v' - v ≤ 2)
    (h3 : (u - u') + (v - v') ≤ 4) (h4 : (u - u') - (v - v') ≤ 4)
    (h5 : (u' - u) + (v - v') ≤ 4) (h6 : (u' - u) - (v - v') ≤ 4) :
    max (max v (-v)) ((max u (-u) + max v (-v)) / 2) ≤
      max (max v' (-v')) ((max u' (-u') + max v' (-v')) / 2) + 2 := by
  omega

/-- **(S1) for the hole.** -/
theorem hex_le (F G : ℤ × ℤ) :
    hexDist F G ≤ hexDist (bImg Y0 c0 F) (bImg Y0 c0 G) + 2 := by
  have h1 := bImg_move (Y0 := Y0) (c0 := c0) F
  have h2 := bImg_move (Y0 := Y0) (c0 := c0) G
  generalize bImg Y0 c0 F = P at *
  generalize bImg Y0 c0 G = Q at *
  unfold hexDist
  have := hex_aux (F.1 - G.1) (F.2 - G.2) (P.1 - Q.1) (P.2 - Q.2) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simp only [neg_sub] at this
  exact this

/-- A depth bound that loses `2`, checked side by side. -/
theorem depth_le_two {h h2 : ℕ} {F F' : ℤ × ℤ}
    (h1 : outDepth h F ≤ F'.2 + 1 + 2) (h2' : outDepth h F ≤ h2 - F'.2 + 2)
    (h3 : outDepth h F ≤ (F'.1 + 1) / 2 + 2) (h4 : outDepth h F ≤ (2 * h2 + 2 - F'.1) / 2 + 2) :
    outDepth h F ≤ max 0 (outDepth h2 F') + 2 := by
  unfold outDepth at *
  omega

/-- **(S2) for the hole.** -/
theorem brick_le {F : ℤ × ℤ} (hF : IsBrick (h' + 2) F) :
    faceDepth (h' + 2) F ≤ faceDepth h' (pi h' Y0 c0 F) + 2 := by
  rw [faceDepth_pi hF, faceDepth_of_isBrick hF]
  have h1 := bImg_move (Y0 := Y0) (c0 := c0) F
  generalize bImg Y0 c0 F = P at *
  apply depth_le_two <;> simp only [outDepth, min_le_iff] <;> push_cast <;> omega

theorem pi_ne_outFace_of_isBrick {F : ℤ × ℤ} (hF : IsBrick h' (pi h' Y0 c0 F)) :
    pi h' Y0 c0 F ≠ outFace := fun e => not_isBrick_outFace h' (e ▸ hF)

/-- **(S3) for the hole**: every deleted element has a face around it whose depth drops by at
most 1. -/
theorem del_depth (hg : Good h' Y0 c0) {m : ℤ × ℤ} (hm : IsWallCell (h' + 2) m)
    (hown : own h' Y0 c0 m = none) :
    ∃ q ∈ squaresAbove m, faceDepth (h' + 2) (wallFace (h' + 2) q) ≤
      faceDepth h' (pi h' Y0 c0 (wallFace (h' + 2) q)) + 1 := by
  have hd : ¬ IsWallCell h' (cell Y0 c0 m) := by
    intro h1
    unfold own at hown
    rw [ite_eq_left h1] at hown
    exact Option.some_ne_none _ hown
  rcases cell_cases hm with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · have hw := hm
    rw [isWallCell_vertex_iff] at hm
    refine ⟨(2 * (if y = Y0 + 1 then ((x, Y0) : ℤ × ℤ) else (x, y)).1 + 1,
      2 * (if y = Y0 + 1 then ((x, Y0) : ℤ × ℤ) else (x, y)).2 + 1), ?_,
      del_vertex hg hw hd rfl⟩
    rw [mem_squaresAbove_iff]
    split_ifs <;> simp only [true_or, true_and, and_true] <;> omega
  · have hw := hm
    rw [isWallCell_horiz_iff] at hm
    refine ⟨(2 * (if y = Y0 + 1 then ((x, Y0) : ℤ × ℤ) else (x, y)).1 + 1,
      2 * (if y = Y0 + 1 then ((x, Y0) : ℤ × ℤ) else (x, y)).2 + 1), ?_,
      del_horiz hg hw hd rfl⟩
    rw [mem_squaresAbove_iff]
    split_ifs <;> simp only [true_or, true_and, and_true] <;> omega
  · have hw := hm
    rw [isWallCell_vert_iff] at hm
    refine ⟨(2 * (if Y0 % 2 = 0 ∧ y ≤ Y0 - 1 then ((x - 1, y) : ℤ × ℤ) else (x, y)).1 + 1,
      2 * (if Y0 % 2 = 0 ∧ y ≤ Y0 - 1 then ((x - 1, y) : ℤ × ℤ) else (x, y)).2 + 1), ?_,
      del_vert hg hw hd rfl⟩
    rw [mem_squaresAbove_iff]
    split_ifs <;> simp only [true_or, true_and, and_true] <;> omega

/-- **The hole passes the depth test** when its parameters are good. -/
theorem depthTest (hg : Good h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') :
    (shape hg.toParams hh' he').DepthTest where
  out := by rw [shape_π]; exact pi_outFace
  hex F G hF hG hF' hG' := by
    rw [shape_π] at hF' hG' ⊢
    obtain ⟨X, Y⟩ := F
    obtain ⟨X', Y'⟩ := G
    rw [(isBrick_bImg_of_pi_ne hF (pi_ne_outFace_of_isBrick hF')).2,
      (isBrick_bImg_of_pi_ne hG (pi_ne_outFace_of_isBrick hG')).2]
    exact hex_le _ _
  brick _ hF := by rw [shape_π]; exact brick_le hF
  del m hm hown := by
    rw [shape_π]
    rw [shape_own] at hown
    exact del_depth hg ((mem_fig1WallCells_iff (by omega) (even_succ_succ he') m).mp hm) hown

/-- **The hole has `KI 4`** when its parameters are good. -/
theorem ki (hg : Good h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') :
    (shape hg.toParams hh' he').KI 4 :=
  (depthTest hg hh' he').ki

end Hole

end GraphMinor.GM13
