module

public import GraphMinor.GM13.Section7HexHoleConn
public import GraphMinor.GM13.Section7Chain

/-!
# Graph Minors XIII, (7.3): the hexagonal hole passes the depth test

This file proves that the hexagonal hole passes `Shape.DepthTestK` with the constant `2k`,
`k = b + 1` (`HexHole.depthTestK`), so that it has `KI (4k)`.

The proof rests on one fact about the move of a brick (`HexHole.disp`). Write `P` for the new
brick of the old brick `F` (taken through the square of `F` with even coordinate sum). Then
`F - P - (sL + b, b)` lies in the hex ball of radius `b` around `0`: the move is `(sL, 0)` to
`(sL + 2b, 0)` below the band, `(sL, 2b)` to `(sL + 2b, 2b)` above it, and in band row `Y0 + t`
the staircases at the two sides of the hole move `t + 1` rows down and spread out sideways by
the same amount. A computer search found this set of moves before the proof, and `HexHole.disp`
proves that every move lies in it.

* The hex distance between two bricks drops by at most the diameter `2b` of that ball, which is
  less than the `4k - 2` allowed (`HexHole.hex_le`).
* Each side of the wall comes closer by at most `2b + 2`, so depths drop by at most `2k`
  (`HexHole.depth_le`). Here `b + 1 ≤ sL ≤ b + 2` is used.
* For (S3) the drop must be at most `2k - 1`. The top side comes `2b + 2` closer only for a brick
  below the band, and there the bottom side is nearer when the band starts in the lower half of
  the wall (`HexHole.Good`). The right side comes `2b + 2` closer only for a brick that moves by
  one column, which happens only in the band row `Y0 + b - 1`. So for each deleted element we
  take a face off that row, or, for a vertical edge on that row, the brick to its right, which
  moves by at least two columns or lies at the left side (`HexHole.del_depth`). This choice was
  found by a computer search, and `HexHole.del_depth` proves that it works.
-/

public section

namespace GraphMinor.GM13

open Set

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- The parameters of a hexagonal hole for which the depth test holds: the band starts in the
lower half of the old wall, and `b + 1 ≤ sL ≤ b + 2` (so `sL = k + k % 2`). -/
structure Good (h' b : ℕ) (Y0 c0 sL : ℤ) : Prop extends Params h' b Y0 c0 sL where
  low : 2 * Y0 ≤ h' + 2 * b + 2
  sL3 : b + 1 ≤ sL
  sL4 : sL ≤ b + 2

/-- **The move of a brick.** For a square with even coordinate sum (the right square of its
brick), the move to the new brick lies in the hex ball of radius `b` around `(sL + b, b)`, and
it keeps the row only below the band. -/
theorem disp (hp : Params h' b Y0 c0 sL) {X Y : ℤ} (he : (X + Y) % 2 = 0) :
    0 ≤ Y - (bk (newSq b Y0 c0 sL (X, Y))).2 ∧ Y - (bk (newSq b Y0 c0 sL (X, Y))).2 ≤ 2 * b ∧
      (Y - (bk (newSq b Y0 c0 sL (X, Y))).2 = 0 → Y ≤ Y0 - 1) ∧
      max (X - (bk (newSq b Y0 c0 sL (X, Y))).1 - sL - b)
          (-(X - (bk (newSq b Y0 c0 sL (X, Y))).1 - sL - b)) +
        max (Y - (bk (newSq b Y0 c0 sL (X, Y))).2 - b)
          (-(Y - (bk (newSq b Y0 c0 sL (X, Y))).2 - b)) ≤ 2 * b := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  simp only [newSq, side, off, bk]
  split_ifs <;> simp only <;> omega

/-- The new face of an old brick is the face of the new square of its right square. -/
theorem faceDepth_pi (hp : Params h' b Y0 c0 sL) {X Y : ℤ}
    (hF : IsBrick (h' + 2 * b + 2) (X, Y)) :
    faceDepth h' (pi h' b Y0 c0 sL (X, Y)) =
      max 0 (outDepth h' (bk (newSq b Y0 c0 sL (X, Y)))) := by
  rw [pi_brick hp hF, faceDepth_sqFace]

/-- The two row sides: the bottom side comes at most `2b` closer, and the top side at most
`2b + 1` closer except below the band, where the bottom side is the nearer one. -/
theorem rows_le (hg : Good h' b Y0 c0 sL) {Y Y' : ℤ} (h1 : 0 ≤ Y - Y') (h2 : Y - Y' ≤ 2 * b)
    (h3 : Y - Y' = 0 → Y ≤ Y0 - 1) :
    min (Y + 1) ((h' + 2 * b + 2 : ℕ) - Y) ≤ min (Y' + 1) ((h' : ℤ) - Y') + (2 * b + 1) := by
  have hlow := hg.low
  push_cast
  omega

/-- The two column sides come at most `2b + 2` closer, and at most `2b + 1` closer when the move
is at least two columns. -/
theorem cols_le {X X' D : ℤ} {b : ℕ} (h1 : 1 + D ≤ X - X') (h2 : X - X' ≤ 4 * b + 2) (hD : D = 0 ∨ D = 1) :
    min ((X + 1) / 2) ((2 * ((h' + 2 * b + 2 : ℕ) : ℤ) + 2 - X) / 2) ≤
      min ((X' + 1) / 2) ((2 * (h' : ℤ) + 2 - X') / 2) + (2 * b + 2 - D) := by
  push_cast
  omega

/-- **The depth of a brick drops by at most `2b + 2`.** -/
theorem depth_le (hg : Good h' b Y0 c0 sL) {F : ℤ × ℤ} (hF : IsBrick (h' + 2 * b + 2) F) :
    faceDepth (h' + 2 * b + 2) F ≤ faceDepth h' (pi h' b Y0 c0 sL F) + (2 * b + 2 : ℕ) := by
  obtain ⟨X, Y⟩ := F
  rw [faceDepth_pi hg.toParams hF, faceDepth_of_isBrick hF]
  have hF' := hF
  simp only [IsBrick] at hF'
  have hd := disp hg.toParams (X := X) (Y := Y) (by omega)
  generalize bk (newSq b Y0 c0 sL (X, Y)) = P at hd
  obtain ⟨X', Y'⟩ := P
  simp only at hd
  obtain ⟨d1, d2, d3, d4⟩ := hd
  have s3 := hg.sL3
  have s4 := hg.sL4
  have e1 : 1 + 0 ≤ X - X' := by omega
  have e2 : X - X' ≤ 4 * b + 2 := by omega
  have hr := rows_le hg d1 d2 d3
  have hc := cols_le (h' := h') e1 e2 (Or.inl rfl)
  have hm := le_max_right 0 (outDepth h' (X', Y'))
  clear d4 hF' hF
  unfold outDepth at hm ⊢
  simp only at hm ⊢
  push_cast at hc hr ⊢
  omega

/-- Moves that differ by at most `2B` in height and `4B` in all lower the hex distance by at most
`2B`. -/
theorem hex_aux (u v u' v' B : ℤ) (hf : max (v - v') (v' - v) ≤ 2 * B)
    (hef : max (u - u') (u' - u) + max (v - v') (v' - v) ≤ 4 * B) (hp : (u + v) % 2 = 0)
    (hp' : (u' + v') % 2 = 0) :
    max (max v (-v)) ((max u (-u) + max v (-v)) / 2) ≤
      max (max v' (-v')) ((max u' (-u') + max v' (-v')) / 2) + 2 * B := by
  omega

/-- **The hex distance between two bricks drops by at most `2b`.** -/
theorem hex_le (hp : Params h' b Y0 c0 sL) {X Y X₁ Y₁ : ℤ} (he : (X + Y) % 2 = 0)
    (he₁ : (X₁ + Y₁) % 2 = 0) :
    hexDist (X, Y) (X₁, Y₁) ≤
      hexDist (bk (newSq b Y0 c0 sL (X, Y))) (bk (newSq b Y0 c0 sL (X₁, Y₁))) + 2 * b := by
  have hd := disp hp he
  have hd₁ := disp hp he₁
  have hq : ∀ s : ℤ × ℤ, ((bk s).1 + (bk s).2) % 2 = 0 := by
    intro s; simp only [bk]; omega
  have hq1 := hq (newSq b Y0 c0 sL (X, Y))
  have hq2 := hq (newSq b Y0 c0 sL (X₁, Y₁))
  generalize bk (newSq b Y0 c0 sL (X, Y)) = P at hd hq1
  generalize bk (newSq b Y0 c0 sL (X₁, Y₁)) = Q at hd₁ hq2
  obtain ⟨X', Y'⟩ := P
  obtain ⟨X₁', Y₁'⟩ := Q
  simp only at hd hd₁ hq1 hq2
  obtain ⟨d1, d2, -, d4⟩ := hd
  obtain ⟨d1', d2', -, d4'⟩ := hd₁
  have hf : max ((Y - Y₁) - (Y' - Y₁')) ((Y' - Y₁') - (Y - Y₁)) ≤ 2 * b := by omega
  have hef : max ((X - X₁) - (X' - X₁')) ((X' - X₁') - (X - X₁)) +
      max ((Y - Y₁) - (Y' - Y₁')) ((Y' - Y₁') - (Y - Y₁)) ≤ 4 * b := by omega
  have := hex_aux (X - X₁) (Y - Y₁) (X' - X₁') (Y' - Y₁') b hf hef (by omega) (by omega)
  unfold hexDist
  simp only [neg_sub] at this ⊢
  exact this

/-- A brick that moves at least two columns, or lies at the left side, loses at most `2b + 1` in
depth. Only the right side can come `2b + 2` closer, and only for a move of one column. -/
theorem depth_le_of (hg : Good h' b Y0 c0 sL) {X Y : ℤ} (hF : IsBrick (h' + 2 * b + 2) (X, Y))
    (hx : 2 ≤ X - (bk (newSq b Y0 c0 sL (X, Y))).1 ∨ X ≤ 1) :
    faceDepth (h' + 2 * b + 2) (X, Y) ≤
      faceDepth h' (pi h' b Y0 c0 sL (X, Y)) + (2 * b + 1 : ℕ) := by
  rw [faceDepth_pi hg.toParams hF, faceDepth_of_isBrick hF]
  have hF' := hF
  simp only [IsBrick] at hF'
  have hd := disp hg.toParams (X := X) (Y := Y) (by omega)
  generalize bk (newSq b Y0 c0 sL (X, Y)) = P at hd hx
  obtain ⟨X', Y'⟩ := P
  simp only at hd hx
  have hm := le_max_right 0 (outDepth h' (X', Y'))
  have hm0 := le_max_left 0 (outDepth h' (X', Y'))
  rcases hx with hx | hx
  · obtain ⟨d1, d2, d3, d4⟩ := hd
    have s3 := hg.sL3
    have s4 := hg.sL4
    have e1 : 1 + 1 ≤ X - X' := by omega
    have e2 : X - X' ≤ 4 * b + 2 := by omega
    have hr := rows_le hg d1 d2 d3
    have hc := cols_le (h' := h') e1 e2 (Or.inr rfl)
    clear d4 hF' hF
    unfold outDepth at hm ⊢
    simp only at hm ⊢
    push_cast at hc hr ⊢
    omega
  · have : outDepth (h' + 2 * b + 2) (X, Y) ≤ 1 := by
      unfold outDepth; simp only; omega
    push_cast
    omega

/-- A brick moves at least one column, and exactly one only in the band row `Y0 + b - 1`. -/
theorem two_le_dX (hp : Params h' b Y0 c0 sL) {X Y : ℤ} (he : (X + Y) % 2 = 0)
    (hs : b + 1 ≤ sL) (hY : Y ≠ Y0 + b - 1) : 2 ≤ X - (bk (newSq b Y0 c0 sL (X, Y))).1 := by
  have hd := disp hp he
  have hrow : Y - (bk (newSq b Y0 c0 sL (X, Y))).2 = b → Y = Y0 + b - 1 := by
    have := hp.b1
    simp only [newSq, bk]
    split_ifs <;> simp only <;> omega
  omega

/-- A deleted vertical edge in the band row `Y0 + b - 1`: the brick to the right of it moves at
least two columns, or lies at the left side. -/
theorem vert_dX (hg : Good h' b Y0 c0 sL) {x : ℤ}
    (hw : IsWallCell (h' + 2 * b + 2) (2 * x, 2 * (Y0 + b - 1) + 1))
    (hd : ¬ IsWallCell h' (vertCell b Y0 c0 sL x (Y0 + b - 1))) :
    2 ≤ x + 1 - (bk (newSq b Y0 c0 sL (x + 1, Y0 + b - 1))).1 ∨ x + 1 ≤ 1 := by
  obtain ⟨⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩, low, s3, s4⟩ := hg
  rw [isWallCell_vert_iff] at hw
  have ho : off b (b - 1) = -b := by unfold off; rw [if_pos (by omega)]; ring
  rw [newSq_band (by omega) (by omega), show Y0 + b - 1 - Y0 = (b : ℤ) - 1 by ring, ho]
  unfold vertCell at hd
  rw [if_neg (by omega), show Y0 + b - 1 - Y0 = (b : ℤ) - 1 by ring, ho] at hd
  simp only [side, bk]
  split_ifs at hd ⊢ <;> simp only [not_and, IsWallCell] at hd ⊢ <;> omega

/-- (S3) at a square whose brick, if it is a brick, moves at least two columns or lies at the
left side. -/
theorem s3_of_square (hg : Good h' b Y0 c0 sL) (s : ℤ × ℤ)
    (H : IsBrick (h' + 2 * b + 2) (bk s) →
      2 ≤ (bk s).1 - (bk (newSq b Y0 c0 sL (bk s))).1 ∨ (bk s).1 ≤ 1) :
    faceDepth (h' + 2 * b + 2) (sqFace (h' + 2 * b + 2) s) ≤
      faceDepth h' (pi h' b Y0 c0 sL (sqFace (h' + 2 * b + 2) s)) + (2 * b + 1 : ℕ) := by
  rw [sqFace_eq]
  split_ifs with hb
  · have H' := H hb
    generalize bk s = F at hb H'
    obtain ⟨X, Y⟩ := F
    exact depth_le_of hg hb H'
  · rw [pi_outFace]
    simp only [faceDepth, ite_true]
    omega

theorem bk_snd (s : ℤ × ℤ) : (bk s).2 = s.2 := rfl

theorem bk_even (s : ℤ × ℤ) : ((bk s).1 + (bk s).2) % 2 = 0 := by
  simp only [bk]; omega

/-- **(S3) for the hexagonal hole**: every deleted element has a face around it whose depth drops
by at most `2b + 1`. The face is that of the square above and to the right of the element, or
of the square below it for a vertex or a horizontal edge on the band row `Y0 + b - 1`. -/
theorem del_depth (hg : Good h' b Y0 c0 sL) {m : ℤ × ℤ} (hm : IsWallCell (h' + 2 * b + 2) m)
    (hown : own h' b Y0 c0 sL m = none) :
    ∃ q ∈ squaresAbove m, faceDepth (h' + 2 * b + 2) (wallFace (h' + 2 * b + 2) q) ≤
      faceDepth h' (pi h' b Y0 c0 sL (wallFace (h' + 2 * b + 2) q)) + (2 * b + 1 : ℕ) := by
  have hd : ¬ IsWallCell h' (cell b Y0 c0 sL m) := by
    intro h1
    unfold own at hown
    rw [if_pos h1] at hown
    exact Option.some_ne_none _ hown
  have hs := hg.sL3
  have hdx : ∀ s : ℤ × ℤ, s.2 ≠ Y0 + b - 1 → IsBrick (h' + 2 * b + 2) (bk s) →
      2 ≤ (bk s).1 - (bk (newSq b Y0 c0 sL (bk s))).1 ∨ (bk s).1 ≤ 1 := by
    intro s hs2 _
    left
    have := two_le_dX hg.toParams (X := (bk s).1) (Y := (bk s).2) (bk_even s) hs
      (by rw [bk_snd]; exact hs2)
    exact this
  rcases Hole.cell_cases hm with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · by_cases hy : y = Y0 + b - 1
    · refine ⟨(2 * x + 1, 2 * (y - 1) + 1), ?_, s3_of_square hg (x, y - 1) (hdx _ ?_)⟩
      · rw [mem_squaresAbove_iff]; omega
      · simp only; omega
    · refine ⟨(2 * x + 1, 2 * y + 1), ?_, s3_of_square hg (x, y) (hdx _ hy)⟩
      rw [mem_squaresAbove_iff]; omega
  · by_cases hy : y = Y0 + b - 1
    · refine ⟨(2 * x + 1, 2 * (y - 1) + 1), ?_, s3_of_square hg (x, y - 1) (hdx _ ?_)⟩
      · rw [mem_squaresAbove_iff]; omega
      · simp only; omega
    · refine ⟨(2 * x + 1, 2 * y + 1), ?_, s3_of_square hg (x, y) (hdx _ hy)⟩
      rw [mem_squaresAbove_iff]; omega
  · refine ⟨(2 * x + 1, 2 * y + 1), ?_, s3_of_square hg (x, y) ?_⟩
    · rw [mem_squaresAbove_iff]; omega
    · by_cases hy : y = Y0 + b - 1
      · subst hy
        intro _
        have hw := hm
        rw [isWallCell_vert_iff] at hw
        have e : bk (x, Y0 + b - 1) = (x + 1, Y0 + b - 1) := by
          simp only [bk, Prod.mk.injEq, and_true]; omega
        rw [e]
        rw [cell_vert] at hd
        exact vert_dX hg hm hd
      · exact hdx _ hy

end HexHole

/-- **The hexagonal hole passes the depth test** with the constant `2k`, `k = b + 1`. -/
theorem HexHole.depthTestK {h' b : ℕ} {Y0 c0 sL : ℤ} (hg : HexHole.Good h' b Y0 c0 sL)
    (hh' : 1 ≤ h') (he' : Even h') :
    (HexHole.shape hg.toParams hh' he').DepthTestK (2 * (b + 1)) where
  one_le := by omega
  out := by rw [HexHole.shape_π]; exact HexHole.pi_outFace
  hex F G hF hG hF' hG' := by
    rw [HexHole.shape_π] at hF' hG' ⊢
    obtain ⟨X, Y⟩ := F
    obtain ⟨X₁, Y₁⟩ := G
    rw [HexHole.pi_brick hg.toParams hF] at hF' ⊢
    rw [HexHole.pi_brick hg.toParams hG] at hG' ⊢
    have h1 : IsBrick h' (bk (newSq b Y0 c0 sL (X, Y))) := by
      by_contra hn; rw [sqFace_eq, if_neg hn] at hF'; exact not_isBrick_outFace h' hF'
    have h2 : IsBrick h' (bk (newSq b Y0 c0 sL (X₁, Y₁))) := by
      by_contra hn; rw [sqFace_eq, if_neg hn] at hG'; exact not_isBrick_outFace h' hG'
    rw [sqFace_eq, if_pos h1, sqFace_eq, if_pos h2]
    have := HexHole.hex_le hg.toParams (X := X) (Y := Y) (X₁ := X₁) (Y₁ := Y₁)
      (by simp only [IsBrick] at hF; omega) (by simp only [IsBrick] at hG; omega)
    push_cast
    omega
  brick F hF := by
    rw [HexHole.shape_π]
    have := HexHole.depth_le hg hF
    push_cast at this ⊢
    omega
  del m hm hown := by
    rw [HexHole.shape_π]
    rw [HexHole.shape_own] at hown
    obtain ⟨q, hq, hle⟩ := HexHole.del_depth hg
      ((mem_fig1WallCells_iff (by omega) (HexHole.even_add_two_mul_add_two he' b) m).mp hm) hown
    refine ⟨q, hq, ?_⟩
    have e : (2 * (b + 1) - 1 : ℕ) = 2 * b + 1 := by omega
    rw [e]
    exact hle

/-- **The hexagonal hole has `KI (4k)`**, `k = b + 1`. -/
theorem HexHole.ki {h' b : ℕ} {Y0 c0 sL : ℤ} (hg : HexHole.Good h' b Y0 c0 sL)
    (hh' : 1 ≤ h') (he' : Even h') :
    (HexHole.shape hg.toParams hh' he').KI (2 * (2 * (b + 1))) :=
  (HexHole.depthTestK hg hh' he').ki

end GraphMinor.GM13
