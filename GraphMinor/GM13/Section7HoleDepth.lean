module

public import GraphMinor.GM13.Section7HoleConn

/-!
# Graph Minors XIII, (7.3): depths under the hole

This file proves the depth bounds that `Shape.DepthTest` asks of the hole `Hole(Y0, c0)`, for
the elements that the hole deletes. The bounds on bricks, and the test itself, are in
`Section7HoleDepthTest.lean`.

The test (S3) asks that every deleted element has a face around it whose depth drops by at most
1. This is not true for every choice of `(Y0, c0)`. Below the band the hole moves the top side of
the wall two rows closer, so the depth of a face in the cut can drop by 2 when the top side is the
nearest side. We therefore ask that the cut is near a side that does not move (`Hole.Good`): near
the left side when `Y0` is even, and far from it when `Y0` is odd. These choices were found by
testing all walls of height at most 14, and every element of a wall is deleted by some shape with
such parameters.

The face chosen for a deleted element is the square above and to the right of it, with two
exceptions: the square one row lower for the elements on the top row of the band, and the square
to the left for the vertical edges of the cut when `Y0` is even (`Hole.del_vertex`,
`Hole.del_horiz`, `Hole.del_vert`).

The proofs reduce (S3) to a bound on the depth of the brick of that square
(`Hole.s3_of_brick`). The new face of a brick is `Hole.bImg`, which has no parities, so after
the cases of the cell formula every goal is linear.
-/

public section

namespace GraphMinor.GM13

open Set

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- The parameters of a hole for which the test (S3) holds: the parameters of `Hole.Params`, and
the cut is at most `2h' + 2 - 2Y0` when `Y0` is even, and at least `2Y0` when `Y0` is odd. -/
structure Good (h' : ℕ) (Y0 c0 : ℤ) : Prop extends Params h' Y0 c0 where
  even : Y0 % 2 = 0 → c0 ≤ 2 * h' + 2 - 2 * Y0
  odd : Y0 % 2 = 1 → 2 * Y0 ≤ c0

theorem not_isWallCell_odd_odd {h : ℕ} {a b : ℤ} : ¬ IsWallCell h (2 * a + 1, 2 * b + 1) := by
  simp only [IsWallCell]; omega

/-- A depth bound that loses `1`, checked side by side. -/
theorem depth_le {h h2 : ℕ} {F F' : ℤ × ℤ}
    (h1 : outDepth h F ≤ F'.2 + 1 + 1) (h2' : outDepth h F ≤ h2 - F'.2 + 1)
    (h3 : outDepth h F ≤ (F'.1 + 1) / 2 + 1) (h4 : outDepth h F ≤ (2 * h2 + 2 - F'.1) / 2 + 1) :
    outDepth h F ≤ max 0 (outDepth h2 F') + 1 := by
  unfold outDepth at *
  omega

/-- The depth of the new face of an old brick. -/
theorem faceDepth_pi {F : ℤ × ℤ} (hF : IsBrick (h' + 2) F) :
    faceDepth h' (pi h' Y0 c0 F) = max 0 (outDepth h' (bImg Y0 c0 F)) := by
  obtain ⟨X, Y⟩ := F
  rw [pi_brick hF]
  split_ifs with hb
  · rw [faceDepth_of_isBrick hb]
    have := one_le_outDepth hb
    omega
  · simp only [faceDepth, ite_true]
    simp only [IsBrick] at hF hb
    unfold outDepth
    simp only [bImg] at hb ⊢
    split_ifs at hb ⊢ <;> simp only at hb ⊢ <;> omega

/-- Reduces (S3) at a square to a bound on the depth of its brick: a square in the outer face has
depth 0, which cannot drop. -/
theorem s3_of_brick {s : ℤ × ℤ}
    (H : IsBrick (h' + 2) (bk s) →
      outDepth (h' + 2) (bk s) ≤ max 0 (outDepth h' (bImg Y0 c0 (bk s))) + 1) :
    faceDepth (h' + 2) (sqFace (h' + 2) s) ≤
      faceDepth h' (pi h' Y0 c0 (sqFace (h' + 2) s)) + 1 := by
  rw [sqFace_eq]
  split_ifs with hb
  · rw [faceDepth_pi hb, faceDepth_of_isBrick hb]
    exact H hb
  · rw [pi_outFace]
    simp only [faceDepth, ite_true]
    omega

set_option hygiene false in
/-- Proves (S3) at the square `s` of a deleted element, from the cell formula `f`. It splits on
the row of the element against the band, then on the cases of the cell formula and of
`Hole.bImg`, and checks each side of the depth. -/
macro "s3_tac " f:ident : tactic => `(tactic| (
  obtain ⟨⟨Y1, Y2, c1, c2⟩, ge, go⟩ := hg
  have hc : (Y0 % 2 = 0 ∧ c0 ≤ 2 * h' + 2 - 2 * Y0) ∨ (Y0 % 2 = 1 ∧ 2 * Y0 ≤ c0) := by
    rcases Int.emod_two_eq_zero_or_one Y0 with hY | hY
    · exact Or.inl ⟨hY, ge hY⟩
    · exact Or.inr ⟨hY, go hY⟩
  clear ge go
  simp only [cell_vertex, cell_horiz, cell_vert] at hd
  simp only [isWallCell_vertex_iff, isWallCell_horiz_iff, isWallCell_vert_iff] at hw
  apply s3_of_brick
  intro hb
  obtain ⟨p, hp, hbk⟩ : ∃ p, (p = 0 ∨ p = 1) ∧ bk s = (s.1 + p, s.2) :=
    ⟨(s.1 + s.2) % 2, by omega, rfl⟩
  rw [hbk] at hb ⊢
  clear hbk
  split_ifs at hs <;> subst hs <;> simp only [IsBrick] at hb ⊢ <;>
  rcases (by omega : y ≤ Y0 - 2 ∨ y = Y0 - 1 ∨ y = Y0 ∨ y = Y0 + 1 ∨ Y0 + 2 ≤ y) with
    hy' | hy' | hy' | hy' | hy' <;>
  simp (disch := omega) only [$f:ident, bImg, ite_eq_left, ite_eq_right] at hd ⊢ <;>
  (try split_ifs at hd ⊢) <;>
  simp only [isWallCell_vertex_iff, isWallCell_horiz_iff, isWallCell_vert_iff,
    not_isWallCell_odd_odd, not_false_eq_true] at hd <;>
  apply depth_le <;> simp only [outDepth, min_le_iff] <;> omega))

/-- (S3) at a deleted vertex `(x, y)`: the square `(x, y)`, or `(x, Y0)` on the top row of the
band. -/
theorem del_vertex (hg : Good h' Y0 c0) {x y : ℤ} {s : ℤ × ℤ}
    (hw : IsWallCell (h' + 2) (2 * x, 2 * y)) (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * x, 2 * y)))
    (hs : s = if y = Y0 + 1 then (x, Y0) else (x, y)) :
    faceDepth (h' + 2) (sqFace (h' + 2) s) ≤
      faceDepth h' (pi h' Y0 c0 (sqFace (h' + 2) s)) + 1 := by
  s3_tac vertexCell

/-- (S3) at a deleted horizontal edge from `(x, y)`: the square `(x, y)`, or `(x, Y0)` on the
top row of the band. -/
theorem del_horiz (hg : Good h' Y0 c0) {x y : ℤ} {s : ℤ × ℤ}
    (hw : IsWallCell (h' + 2) (2 * x + 1, 2 * y))
    (hd : ¬ IsWallCell h' (cell Y0 c0 (2 * x + 1, 2 * y)))
    (hs : s = if y = Y0 + 1 then (x, Y0) else (x, y)) :
    faceDepth (h' + 2) (sqFace (h' + 2) s) ≤
      faceDepth h' (pi h' Y0 c0 (sqFace (h' + 2) s)) + 1 := by
  s3_tac horizCell

end Hole

end GraphMinor.GM13
