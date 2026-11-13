module

public import GraphMinor.GM13.Section7HexHolePaths

/-!
# Graph Minors XIII, (7.3): the realization of the hexagonal hole

Each new vertex has an old vertex (`HexHole.vmap`) and each new edge an old path
(`HexHole.path`); `Section7HexHolePaths` checks that these paths are paths of the right owner.
This file checks the last condition of a realization: every kept old element is the old vertex
of a new vertex, or lies on one of these paths (`HexHole.covered`). The six `cover_*` lemmas
treat vertices, horizontal edges and vertical edges, off the band and in it. Then
`HexHole.realization` builds the realization with `Shape.Realization.ofPaths`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- The kept old element `m` is the old vertex of a new vertex, or an inner vertex or an edge of
the path of a new edge. -/
def Covered (h' b : ℕ) (Y0 c0 : ℤ) (s : ℕ) (m : ℤ × ℤ) : Prop :=
  (∃ p ∈ elementaryWallVerts h', m = vCell (vmap b Y0 c0 s p)) ∨
    ∃ p q, elementaryWallAdj h' p q ∧ p.1 + p.2 < q.1 + q.2 ∧
      ((∃ i, 1 ≤ i ∧ i < pathLen b Y0 c0 s p q ∧ m = vCell (path b Y0 c0 s p q i)) ∨
        ∃ i < pathLen b Y0 c0 s p q,
          m = eCell (path b Y0 c0 s p q i) (path b Y0 c0 s p q (i + 1)))

theorem path_horiz {s a y : ℕ} (j : ℕ) :
    path b Y0 c0 s (a, y) (a + 1, y) j =
      ((vmap b Y0 c0 s (a, y)).1 + j, (vmap b Y0 c0 s (a, y)).2) := by
  simp [path]

macro "verts_tac" : tactic => `(tactic| (simp only [elementaryWallVerts, Set.mem_setOf_eq, ne_eq,
  Prod.mk.injEq, not_and] at * <;> omega))

/-- A kept vertex outside the band, below it (row `y`) or above it (new row `y'`). -/
theorem cover_vertex_off (hp : Params h' b Y0 c0 sL) {s : ℕ} (hs : (s : ℤ) = sL) {x y y' : ℕ}
    (hy : ((y : ℤ) ≤ Y0 - 1 ∧ y' = y) ∨ (Y0 + 2 * b ≤ (y : ℤ) ∧ y' + 2 * b = y))
    (hc : IsWallCell h' (vertexCell b Y0 c0 sL x y)) : Covered h' b Y0 c0 s (vCell (x, y)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  have hoff : (y : ℤ) ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ (y : ℤ) := by omega
  have hrow : (if (y : ℤ) ≤ Y0 - 1 then (y : ℤ) else y - 2 * b) = y' := by
    split_ifs <;> omega
  unfold vertexCell at hc
  rw [if_pos hoff, hrow] at hc
  have hr : ((y' : ℤ) < Y0 ∧ y' = y) ∨ (¬ (y' : ℤ) < Y0 ∧ y' + 2 * b = y) := by omega
  by_cases hL : (x : ℤ) - sL ≤ c0 - 1
  · rw [if_pos hL, isWallCell_vertex_iff] at hc
    left
    refine ⟨(x - s, y'), by verts_tac, ?_⟩
    simp only [vCell, vmap, Prod.mk.injEq]
    rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte] <;>
      split_ifs <;> push_cast <;> omega
  by_cases hR : c0 ≤ (x : ℤ) - sL - 2 * b
  · rw [if_neg hL, if_pos hR, isWallCell_vertex_iff] at hc
    left
    refine ⟨(x - s - 2 * b, y'), by verts_tac, ?_⟩
    simp only [vCell, vmap, Prod.mk.injEq]
    rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte] <;>
      split_ifs <;> push_cast <;> omega
  rw [if_neg hL, if_neg hR, isWallCell_horiz_iff] at hc
  obtain ⟨c, hcc⟩ : ∃ c : ℕ, (c : ℤ) = c0 - 1 := ⟨(c0 - 1).toNat, by omega⟩
  right
  refine ⟨(c, y'), (c + 1, y'), ⟨by verts_tac, by verts_tac, Or.inl ⟨rfl, Or.inl rfl⟩⟩,
    by simp only; omega, Or.inl ⟨x - (c + s), ?_, ?_, ?_⟩⟩
  · omega
  · simp only [pathLen, if_true, vmap]
    split_ifs <;> push_cast at * <;> omega
  · rw [path_horiz]
    simp only [vCell, vmap, Prod.mk.injEq]
    rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte] <;>
      split_ifs <;> push_cast <;> omega

/-- The new vertical edge at a vertical wall cell of the new wall. -/
theorem adj_of_vert (he' : Even h') {x y : ℕ} (hw : IsWallCell h' (2 * (x : ℤ), 2 * (y : ℤ) + 1)) :
    elementaryWallAdj h' (x, y) (x, y + 1) := by
  rw [isWallCell_vert_iff] at hw
  obtain ⟨k, hk⟩ := he'
  refine ⟨by verts_tac, by verts_tac, Or.inr ⟨rfl, Or.inl ⟨rfl, Nat.odd_iff.mpr (by omega)⟩⟩⟩

/-- A point of a staircase covers its vertex. -/
theorem cover_stair_vertex (he' : Even h') {s x' y0 : ℕ} (hY : (y0 : ℤ) + 1 = Y0)
    (hw : IsWallCell h' (2 * (x' : ℤ), 2 * (y0 : ℤ) + 1)) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4 * b)
    {u : ℕ × ℕ} (he : path b Y0 c0 s (x', y0) (x', y0 + 1) i = u) :
    Covered h' b Y0 c0 s (vCell u) :=
  Or.inr ⟨(x', y0), (x', y0 + 1), adj_of_vert he' hw, by simp only; omega,
    Or.inl ⟨i, hi1, by rw [stair_len hY]; omega, by rw [he]⟩⟩

/-- A step of a staircase covers its edge. -/
theorem cover_stair_edge (he' : Even h') {s x' y0 : ℕ} (hY : (y0 : ℤ) + 1 = Y0)
    (hw : IsWallCell h' (2 * (x' : ℤ), 2 * (y0 : ℤ) + 1)) {i : ℕ} (hi : i ≤ 4 * b)
    {m : ℤ × ℤ}
    (he : eCell (path b Y0 c0 s (x', y0) (x', y0 + 1) i)
      (path b Y0 c0 s (x', y0) (x', y0 + 1) (i + 1)) = m) :
    Covered h' b Y0 c0 s m :=
  Or.inr ⟨(x', y0), (x', y0 + 1), adj_of_vert he' hw, by simp only; omega,
    Or.inr ⟨i, by rw [stair_len hY]; omega, he.symm⟩⟩

theorem not_isWallCell_odd_odd {h : ℕ} {a b : ℤ} : ¬ IsWallCell h (2 * a + 1, 2 * b + 1) := by
  simp only [IsWallCell]; omega

/-- A kept vertex in the band row `Y0 + t` lies on a staircase. -/
theorem cover_vertex_band (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ}
    (hs : (s : ℤ) = sL) {x y t : ℕ} (hy : (y : ℤ) = Y0 + t) (ht : t ≤ 2 * b - 1)
    (hc : IsWallCell h' (vertexCell b Y0 c0 sL x y)) : Covered h' b Y0 c0 s (vCell (x, y)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℕ, (y0 : ℤ) + 1 = Y0 := ⟨(Y0 - 1).toNat, by omega⟩
  have hoff : ¬ ((y : ℤ) ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ (y : ℤ)) := by omega
  unfold vertexCell at hc
  rw [if_neg hoff] at hc
  have hpar : ((x : ℤ) + y) % 2 = ((x + y) % 2 : ℕ) := by push_cast; rfl
  rw [hpar] at hc
  have hpar2 : (x + y) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize (x + y) % 2 = r at hc hpar2
  have hyt : (y : ℤ) - Y0 = t := by omega
  rw [hyt] at hc
  have e2 : (2 * (Y0 - 1) + 1 : ℤ) = 2 * (y0 : ℤ) + 1 := by omega
  by_cases h1 : (t : ℤ) + 1 ≤ b
  · rw [if_pos h1] at hc
    by_cases hL : (x : ℤ) - sL + t + r ≤ c0 - 1
    · rw [if_pos hL, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL + t + r := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL + t + r).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_vertex he' hy0 hc (i := 2 * t + 1 + r) (by omega) (by omega) ?_
      rw [stair_path hy0]
      simp only [show (2 * t + 1 + r) / 2 = t + r by omega,
        show (2 * t + 1 + r + 1) / 2 = t + 1 by omega, Prod.mk.injEq]
      rw [if_pos (by omega)]
      omega
    by_cases hR : c0 ≤ (x : ℤ) - sL - 2 * b - t - r
    · rw [if_neg hL, if_pos hR, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - 2 * b - t - r := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - 2 * b - t - r).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_vertex he' hy0 hc (i := 2 * t + 1 + r) (by omega) (by omega) ?_
      rw [stair_path hy0]
      simp only [show (2 * t + 1 + r) / 2 = t + r by omega,
        show (2 * t + 1 + r + 1) / 2 = t + 1 by omega, Prod.mk.injEq]
      rw [if_neg (by omega)]
      omega
    · rw [if_neg hL, if_neg hR] at hc
      exact absurd hc not_isWallCell_odd_odd
  · rw [if_neg h1] at hc
    by_cases hL : (x : ℤ) - sL + 2 * b - t - r ≤ c0 - 1
    · rw [if_pos hL, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL + 2 * b - t - r := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL + 2 * b - t - r).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_vertex he' hy0 hc (i := 2 * t + 1 + r) (by omega) (by omega) ?_
      rw [stair_path hy0]
      simp only [show (2 * t + 1 + r) / 2 = t + r by omega,
        show (2 * t + 1 + r + 1) / 2 = t + 1 by omega, Prod.mk.injEq]
      rw [if_pos (by omega)]
      omega
    by_cases hR : c0 ≤ (x : ℤ) - sL - 4 * b + t + r
    · rw [if_neg hL, if_pos hR, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - 4 * b + t + r := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - 4 * b + t + r).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_vertex he' hy0 hc (i := 2 * t + 1 + r) (by omega) (by omega) ?_
      rw [stair_path hy0]
      simp only [show (2 * t + 1 + r) / 2 = t + r by omega,
        show (2 * t + 1 + r + 1) / 2 = t + 1 by omega, Prod.mk.injEq]
      rw [if_neg (by omega)]
      omega
    · rw [if_neg hL, if_neg hR] at hc
      exact absurd hc not_isWallCell_odd_odd

/-- A kept horizontal edge outside the band. -/
theorem cover_horiz_off (hp : Params h' b Y0 c0 sL) {s : ℕ} (hs : (s : ℤ) = sL) {x y y' : ℕ}
    (hy : ((y : ℤ) ≤ Y0 - 1 ∧ y' = y) ∨ (Y0 + 2 * b ≤ (y : ℤ) ∧ y' + 2 * b = y))
    (hc : IsWallCell h' (horizCell b Y0 c0 sL x y)) :
    Covered h' b Y0 c0 s (eCell (x, y) (x + 1, y)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  have hoff : (y : ℤ) ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ (y : ℤ) := by omega
  have hrow : (if (y : ℤ) ≤ Y0 - 1 then (y : ℤ) else y - 2 * b) = y' := by
    split_ifs <;> omega
  unfold horizCell at hc
  rw [if_pos hoff, hrow] at hc
  have hr : ((y' : ℤ) < Y0 ∧ y' = y) ∨ (¬ (y' : ℤ) < Y0 ∧ y' + 2 * b = y) := by omega
  right
  by_cases hL : (x : ℤ) + 1 - sL ≤ c0 - 1
  · rw [if_pos hL, isWallCell_horiz_iff] at hc
    refine ⟨(x - s, y'), (x - s + 1, y'), ⟨by verts_tac, by verts_tac, Or.inl ⟨rfl, Or.inl rfl⟩⟩,
      by simp only; omega, Or.inr ⟨0, ?_, ?_⟩⟩
    · simp only [pathLen, if_true, vmap]; split_ifs <;> push_cast at * <;> omega
    · rw [path_horiz, path_horiz]
      simp only [eCell, vmap, Prod.mk.injEq]
      rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte] <;>
        split_ifs <;> push_cast <;> omega
  by_cases hR : c0 ≤ (x : ℤ) - sL - 2 * b
  · rw [if_neg hL, if_pos hR, isWallCell_horiz_iff] at hc
    refine ⟨(x - s - 2 * b, y'), (x - s - 2 * b + 1, y'),
      ⟨by verts_tac, by verts_tac, Or.inl ⟨rfl, Or.inl rfl⟩⟩, by simp only; omega,
      Or.inr ⟨0, ?_, ?_⟩⟩
    · simp only [pathLen, if_true, vmap]; split_ifs <;> push_cast at * <;> omega
    · rw [path_horiz, path_horiz]
      simp only [eCell, vmap, Prod.mk.injEq]
      rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte] <;>
        split_ifs <;> push_cast <;> omega
  rw [if_neg hL, if_neg hR, isWallCell_horiz_iff] at hc
  obtain ⟨c, hcc⟩ : ∃ c : ℕ, (c : ℤ) = c0 - 1 := ⟨(c0 - 1).toNat, by omega⟩
  refine ⟨(c, y'), (c + 1, y'), ⟨by verts_tac, by verts_tac, Or.inl ⟨rfl, Or.inl rfl⟩⟩,
    by simp only; omega, Or.inr ⟨x - (c + s), ?_, ?_⟩⟩
  · simp only [pathLen, if_true, vmap]
    split_ifs <;> push_cast at * <;> omega
  · rw [path_horiz, path_horiz]
    simp only [eCell, vmap, Prod.mk.injEq]
    rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte] <;>
      split_ifs <;> push_cast <;> omega

/-- A kept horizontal edge in the band row `Y0 + t` is a sideways step of a staircase. -/
theorem cover_horiz_band (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ}
    (hs : (s : ℤ) = sL) {x y t : ℕ} (hy : (y : ℤ) = Y0 + t) (ht : t ≤ 2 * b - 1)
    (hc : IsWallCell h' (horizCell b Y0 c0 sL x y)) :
    Covered h' b Y0 c0 s (eCell (x, y) (x + 1, y)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℕ, (y0 : ℤ) + 1 = Y0 := ⟨(Y0 - 1).toNat, by omega⟩
  have hoff : ¬ ((y : ℤ) ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ (y : ℤ)) := by omega
  unfold horizCell at hc
  rw [if_neg hoff] at hc
  have hpar : ((x : ℤ) + y) % 2 = ((x + y) % 2 : ℕ) := by push_cast; rfl
  rw [hpar] at hc
  have hpar2 : (x + y) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize (x + y) % 2 = r at hc hpar2
  have hyt : (y : ℤ) - Y0 = t := by omega
  rw [hyt] at hc
  have e2 : (2 * (Y0 - 1) + 1 : ℤ) = 2 * (y0 : ℤ) + 1 := by omega
  have hsq : ∀ z : ℤ, ¬ IsWallCell h' (2 * z + 1, 2 * (Y0 - 1) + 1) := fun z =>
    not_isWallCell_odd_odd
  by_cases h1 : (t : ℤ) + 1 ≤ b
  · rw [if_pos h1] at hc
    by_cases hL : ((r : ℕ) : ℤ) = 1 ∧ (x : ℤ) - sL + t + 1 ≤ c0 - 1
    · rw [if_pos hL, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL + t + 1 := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL + t + 1).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_edge he' hy0 hc (i := 2 * t + 1) (by omega) ?_
      rw [stair_path hy0, stair_path hy0]
      simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega,
        show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega, eCell, Prod.mk.injEq]
      rw [if_pos (by omega)]
      push_cast
      omega
    by_cases hR : ((r : ℕ) : ℤ) = 0 ∧ c0 ≤ (x : ℤ) - sL - 2 * b - t
    · rw [if_neg hL, if_pos hR, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - 2 * b - t := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - 2 * b - t).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_edge he' hy0 hc (i := 2 * t + 1) (by omega) ?_
      rw [stair_path hy0, stair_path hy0]
      simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega,
        show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega, eCell, Prod.mk.injEq]
      rw [if_neg (by omega)]
      push_cast
      omega
    · rw [if_neg hL, if_neg hR] at hc
      exact absurd hc (hsq _)
  · rw [if_neg h1] at hc
    by_cases hL : ((r : ℕ) : ℤ) = 0 ∧ (x : ℤ) - sL + 2 * b - t ≤ c0 - 1
    · rw [if_pos hL, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL + 2 * b - t := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL + 2 * b - t).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_edge he' hy0 hc (i := 2 * t + 1) (by omega) ?_
      rw [stair_path hy0, stair_path hy0]
      simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega,
        show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega, eCell, Prod.mk.injEq]
      rw [if_pos (by omega)]
      push_cast
      omega
    by_cases hR : ((r : ℕ) : ℤ) = 1 ∧ c0 ≤ (x : ℤ) - sL - 4 * b + t + 1
    · rw [if_neg hL, if_pos hR, e2] at hc
      obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - 4 * b + t + 1 := by
        rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - 4 * b + t + 1).toNat, by omega⟩
      rw [← hx'] at hc
      refine cover_stair_edge he' hy0 hc (i := 2 * t + 1) (by omega) ?_
      rw [stair_path hy0, stair_path hy0]
      simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega,
        show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega, eCell, Prod.mk.injEq]
      rw [if_neg (by omega)]
      push_cast
      omega
    · rw [if_neg hL, if_neg hR] at hc
      exact absurd hc (hsq _)

/-- A kept vertical edge outside the band is the first edge of the path of a new vertical
edge. -/
theorem cover_vert_off (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL)
    {x y y' : ℕ}
    (hy : ((y : ℤ) ≤ Y0 - 1 ∧ y' = y) ∨ (Y0 + 2 * b ≤ (y : ℤ) ∧ y' + 2 * b = y))
    (hc : IsWallCell h' (vertCell b Y0 c0 sL x y)) :
    Covered h' b Y0 c0 s (eCell (x, y) (x, y + 1)) := by
  have hp' := hp
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  have hoff : (y : ℤ) ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ (y : ℤ) := by omega
  have hrow : (if (y : ℤ) ≤ Y0 - 1 then (y : ℤ) else y - 2 * b) = y' := by
    split_ifs <;> omega
  unfold vertCell at hc
  rw [if_pos hoff, hrow] at hc
  have hr : ((y' : ℤ) < Y0 ∧ y' = y) ∨ (¬ (y' : ℤ) < Y0 ∧ y' + 2 * b = y) := by omega
  -- the new edge and its first old edge
  have key : ∀ x' : ℕ, IsWallCell h' (2 * (x' : ℤ), 2 * (y' : ℤ) + 1) →
      (vmap b Y0 c0 s (x', y')).1 = x → Covered h' b Y0 c0 s (eCell (x, y) (x, y + 1)) := by
    intro x' hw hx
    have hadj := adj_of_vert he' hw
    obtain ⟨-, h0, -, -, -⟩ := vert_path hp' hs hadj
    right
    refine ⟨(x', y'), (x', y' + 1), hadj, by simp only; omega,
      Or.inr ⟨0, (vert_path hp' hs hadj).1, ?_⟩⟩
    rw [h0]
    have h1 : path b Y0 c0 s (x', y') (x', y' + 1) 1 =
        ((vmap b Y0 c0 s (x', y')).1, (vmap b Y0 c0 s (x', y')).2 + 1) := by
      simp only [path, show y' ≠ y' + 1 by omega, ↓reduceIte, vmap, Nat.reduceDiv,
        Nat.zero_le, min_eq_left]
      split_ifs <;> simp
    rw [h1]
    simp only [eCell, Prod.mk.injEq]
    rw [hx]
    simp only [vmap]
    rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, ↓reduceIte, true_and, and_true] <;>
      push_cast <;> omega
  by_cases hL : (x : ℤ) - sL ≤ c0 - 1
  · rw [if_pos hL] at hc
    obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL := by
      rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL).toNat, by omega⟩
    rw [← hx'] at hc
    exact key x' hc (by simp only [vmap]; split_ifs <;> omega)
  by_cases hR : c0 ≤ (x : ℤ) - sL - 2 * b
  · rw [if_neg hL, if_pos hR] at hc
    obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - 2 * b := by
      rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - 2 * b).toNat, by omega⟩
    rw [← hx'] at hc
    exact key x' hc (by simp only [vmap]; split_ifs <;> omega)
  · rw [if_neg hL, if_neg hR] at hc
    exact absurd hc not_isWallCell_odd_odd

/-- A kept vertical edge in the band row `Y0 + t` is an upward step of a staircase. -/
theorem cover_vert_band (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ}
    (hs : (s : ℤ) = sL) {x y t : ℕ} (hy : (y : ℤ) = Y0 + t) (ht : t ≤ 2 * b - 1)
    (hc : IsWallCell h' (vertCell b Y0 c0 sL x y)) :
    Covered h' b Y0 c0 s (eCell (x, y) (x, y + 1)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℕ, (y0 : ℤ) + 1 = Y0 := ⟨(Y0 - 1).toNat, by omega⟩
  have hoff : ¬ ((y : ℤ) ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ (y : ℤ)) := by omega
  unfold vertCell at hc
  rw [if_neg hoff] at hc
  have hyt : (y : ℤ) - Y0 = t := by omega
  rw [hyt] at hc
  have ho : off b t = if (t : ℤ) + 1 ≤ b then -((t : ℤ) + 1) else -(2 * b - t - 1) := rfl
  have e2 : (2 * (Y0 - 1) + 1 : ℤ) = 2 * (y0 : ℤ) + 1 := by omega
  by_cases hL : (x : ℤ) - sL - off b t ≤ c0 - 1
  · rw [if_pos hL, e2] at hc
    obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - off b t := by
      rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - off b t).toNat, by omega⟩
    rw [← hx'] at hc
    refine cover_stair_edge he' hy0 hc (i := 2 * t + 2) (by omega) ?_
    rw [stair_path hy0, stair_path hy0]
    simp only [show (2 * t + 2) / 2 = t + 1 by omega, show (2 * t + 2 + 1) / 2 = t + 1 by omega,
      show (2 * t + 2 + 1 + 1) / 2 = t + 2 by omega, eCell, Prod.mk.injEq]
    rw [if_pos (by omega)]
    rw [ho] at hx'
    split_ifs at hx' <;> push_cast <;> omega
  by_cases hR : c0 ≤ (x : ℤ) - sL - 2 * b + off b t
  · rw [if_neg hL, if_pos hR, e2] at hc
    obtain ⟨x', hx'⟩ : ∃ x' : ℕ, (x' : ℤ) = x - sL - 2 * b + off b t := by
      rw [isWallCell_vert_iff] at hc; exact ⟨(x - sL - 2 * b + off b t).toNat, by omega⟩
    rw [← hx'] at hc
    refine cover_stair_edge he' hy0 hc (i := 2 * t + 2) (by omega) ?_
    rw [stair_path hy0, stair_path hy0]
    simp only [show (2 * t + 2) / 2 = t + 1 by omega, show (2 * t + 2 + 1) / 2 = t + 1 by omega,
      show (2 * t + 2 + 1 + 1) / 2 = t + 2 by omega, eCell, Prod.mk.injEq]
    have hR' : c0 ≤ (x' : ℤ) := by omega
    rw [if_neg (by omega)]
    rw [ho] at hx'
    split_ifs at hx' <;> push_cast <;> omega
  · rw [if_neg hL, if_neg hR, e2] at hc
    exact absurd hc not_isWallCell_odd_odd

/-- **Every kept old element lies on the old vertex of a new vertex or on a path.** -/
theorem covered (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL)
    {m : ℤ × ℤ} (hm : m ∈ fig1WallCells (h' + 2 * b + 2)) (hown : own h' b Y0 c0 sL m ≠ none) :
    Covered h' b Y0 c0 s m := by
  have hm' := (mem_fig1WallCells_iff (by omega) (even_add_two_mul_add_two he' b) m).mp hm
  have hc : IsWallCell h' (cell b Y0 c0 sL m) := by
    unfold own at hown
    split_ifs at hown with h1
    · exact h1
    · exact absurd rfl hown
  have Y1 := hp.Y1
  have rows : ∀ y : ℕ, (((y : ℤ) ≤ Y0 - 1 ∧ y = y) ∨ (Y0 + 2 * b ≤ (y : ℤ) ∧ y - 2 * b + 2 * b = y))
      ∨ ∃ t : ℕ, (y : ℤ) = Y0 + t ∧ t ≤ 2 * b - 1 := by
    intro y
    by_cases h1 : (y : ℤ) ≤ Y0 - 1
    · exact Or.inl (Or.inl ⟨h1, rfl⟩)
    by_cases h2 : Y0 + 2 * b ≤ (y : ℤ)
    · exact Or.inl (Or.inr ⟨h2, by omega⟩)
    · exact Or.inr ⟨(y - Y0).toNat, by omega, by omega⟩
  rcases Hole.cell_cases hm' with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · rw [isWallCell_vertex_iff] at hm'
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨_, Int.toNat_of_nonneg hm'.1⟩
    obtain ⟨c, rfl⟩ : ∃ c : ℕ, (c : ℤ) = y := ⟨_, Int.toNat_of_nonneg hm'.2.2.1⟩
    rw [cell_vertex] at hc
    rcases rows c with h1 | ⟨t, ht1, ht2⟩
    · rcases h1 with h1 | h1
      · exact cover_vertex_off hp hs (Or.inl h1) hc
      · exact cover_vertex_off hp hs (Or.inr h1) hc
    · exact cover_vertex_band hp he' hs ht1 ht2 hc
  · rw [isWallCell_horiz_iff] at hm'
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨_, Int.toNat_of_nonneg hm'.1⟩
    obtain ⟨c, rfl⟩ : ∃ c : ℕ, (c : ℤ) = y := ⟨_, Int.toNat_of_nonneg hm'.2.2.1⟩
    rw [cell_horiz] at hc
    have e : ((2 * (a : ℤ) + 1, 2 * (c : ℤ)) : ℤ × ℤ) = eCell (a, c) (a + 1, c) := by
      simp only [eCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    rcases rows c with h1 | ⟨t, ht1, ht2⟩
    · rcases h1 with h1 | h1
      · exact cover_horiz_off hp hs (Or.inl h1) hc
      · exact cover_horiz_off hp hs (Or.inr h1) hc
    · exact cover_horiz_band hp he' hs ht1 ht2 hc
  · rw [isWallCell_vert_iff] at hm'
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨_, Int.toNat_of_nonneg hm'.1⟩
    obtain ⟨c, rfl⟩ : ∃ c : ℕ, (c : ℤ) = y := ⟨_, Int.toNat_of_nonneg hm'.2.2.1⟩
    rw [cell_vert] at hc
    have e : ((2 * (a : ℤ), 2 * (c : ℤ) + 1) : ℤ × ℤ) = eCell (a, c) (a, c + 1) := by
      simp only [eCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    rcases rows c with h1 | ⟨t, ht1, ht2⟩
    · rcases h1 with h1 | h1
      · exact cover_vert_off hp he' hs (Or.inl h1) hc
      · exact cover_vert_off hp he' hs (Or.inr h1) hc
    · exact cover_vert_band hp he' hs ht1 ht2 hc

end HexHole

/-- **The realization of the hexagonal hole.** -/
def HexHole.realization {h' b : ℕ} {Y0 c0 sL : ℤ} (hp : HexHole.Params h' b Y0 c0 sL)
    (hh' : 1 ≤ h') (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL) :
    (HexHole.shape hp hh' he').Realization :=
  Shape.Realization.ofPaths (HexHole.vmap b Y0 c0 s) (HexHole.pathLen b Y0 c0 s)
    (HexHole.path b Y0 c0 s)
    (fun _ hp' => HexHole.vmap_mem hp hs hp')
    (fun p q hpq hlt => by
      obtain ⟨a, y⟩ := p
      rcases Hole.oriented_cases hpq hlt with rfl | rfl
      · exact (HexHole.horiz_path hp hs hpq).1
      · exact (HexHole.vert_path hp hs hpq).1)
    (fun p q hpq hlt => by
      obtain ⟨a, y⟩ := p
      rcases Hole.oriented_cases hpq hlt with rfl | rfl
      · exact (HexHole.horiz_path hp hs hpq).2.1
      · exact (HexHole.vert_path hp hs hpq).2.1)
    (fun p q hpq hlt => by
      obtain ⟨a, y⟩ := p
      rcases Hole.oriented_cases hpq hlt with rfl | rfl
      · exact (HexHole.horiz_path hp hs hpq).2.2.1
      · exact (HexHole.vert_path hp hs hpq).2.2.1)
    (fun p q hpq hlt i hi => by
      obtain ⟨a, y⟩ := p
      rcases Hole.oriented_cases hpq hlt with rfl | rfl
      · exact ⟨(HexHole.horiz_path hp hs hpq).2.2.2.1 i hi, (HexHole.horiz_ok hp he' hs hpq).1 i hi⟩
      · refine ⟨(HexHole.vert_path hp hs hpq).2.2.2.1 i hi, ?_⟩
        by_cases hY : (y : ℤ) + 1 = Y0
        · rw [HexHole.stair_len hY] at hi
          exact HexHole.stair_step hp he' hs hpq hY hi
        · obtain ⟨h1, h2⟩ := HexHole.vert_simple hp he' hs hpq hY
          simp only at hi
          obtain rfl : i = 0 := by omega
          exact h2)
    (fun p q hpq hlt i j hi hj e => by
      obtain ⟨a, y⟩ := p
      rcases Hole.oriented_cases hpq hlt with rfl | rfl
      · exact (HexHole.horiz_path hp hs hpq).2.2.2.2 i j e
      · exact (HexHole.vert_path hp hs hpq).2.2.2.2 i j hi hj e)
    (fun _ hp' => HexHole.own_vmap hp hs hp')
    (fun p q hpq hlt i hi1 hi => by
      obtain ⟨a, y⟩ := p
      rcases Hole.oriented_cases hpq hlt with rfl | rfl
      · exact (HexHole.horiz_ok hp he' hs hpq).2 i hi1 hi
      · by_cases hY : (y : ℤ) + 1 = Y0
        · rw [HexHole.stair_len hY] at hi
          exact HexHole.stair_inner hp he' hs hpq hY hi1 hi
        · rw [(HexHole.vert_simple hp he' hs hpq hY).1] at hi
          omega)
    (fun _ hm hown => HexHole.covered hp he' hs hm hown)
end GraphMinor.GM13
