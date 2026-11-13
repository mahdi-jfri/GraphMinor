module

public import GraphMinor.GM13.Section7RayShapes
public import GraphMinor.GM13.Section7HexHoleRealize

/-!
# Graph Minors XIII, (7.3): the rays of the hexagonal hole

The realization of the hexagonal hole keeps the rays of the side vertices out of the kept cells
(`HexHole.rayOK`) and keeps the order of the rows (`HexHole.rowMono`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- Cleans the logic constants and casts from the hypotheses and the goal, then calls `omega`. -/
macro "ray_omega" : tactic => `(tactic| (simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul,
  Int.reduceNeg, true_implies, zero_ne_one, false_implies, one_ne_zero, reduceCtorEq, and_true,
  true_and, neg_eq_zero, not_and] at * <;> omega))

/-- Outside the band and left of the hole, the hexagonal hole moves a vertex or an edge back by
`sL` columns, and down by `2b` rows if it is above the band. -/
theorem cell_lo {m1 m2 : ℤ} (hY : m2 / 2 ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ m2 / 2)
    (hm1 : m1 ≤ 2 * (sL + c0 - 1)) (hpar : m2 % 2 = 0 ∨ m1 % 2 = 0) :
    cell b Y0 c0 sL (m1, m2) =
      (m1 - 2 * sL, m2 - if m2 / 2 ≤ Y0 - 1 then 0 else 4 * (b : ℤ)) := by
  unfold cell vertexCell horizCell vertCell
  simp only [hY, ↓reduceIte]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- Outside the band and right of the hole, the hexagonal hole moves a vertex or an edge back by
`sL + 2b` columns, and down by `2b` rows if it is above the band. -/
theorem cell_hi {m1 m2 : ℤ} (hY : m2 / 2 ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ m2 / 2)
    (hm1 : 2 * (sL + 2 * b + c0) ≤ m1) (hpar : m2 % 2 = 0 ∨ m1 % 2 = 0) :
    cell b Y0 c0 sL (m1, m2) =
      (m1 - 2 * sL - 4 * b, m2 - if m2 / 2 ≤ Y0 - 1 then 0 else 4 * (b : ℤ)) := by
  unfold cell vertexCell horizCell vertCell
  simp only [hY, ↓reduceIte]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- **The hexagonal hole keeps the rays.** A kept cell on the ray of a side vertex `p` goes to a
cell on the ray of `p`. The ray of the cell of `vmap p` stays in one row or column outside the
band, and away from the columns of the hole. There the hole moves each cell back by the same
vector as the vertex `p` (`cell_lo`, `cell_hi`). -/
theorem rayOK (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {s : ℕ}
    (hs : (s : ℤ) = sL) : (HexHole.realization hp hh' he' hs).RayOK := by
  have he2 : Even (h' + 2 * b + 2) := even_add_two_mul_add_two he' b
  refine Shape.Realization.rayOK_of_own _ (by omega) he2 hh' he' ?_
  intro p hp' hsd m hm hmW m' hm'
  change own h' b Y0 c0 sL m = some m' at hm'
  change m ∈ rayCells (vCell (vmap b Y0 c0 s p)) _ at hm
  by_cases h0 : m = vCell (vmap b Y0 c0 s p)
  · rw [h0, own_vmap hp hs hp'] at hm'
    rw [← Option.some_injective _ hm']
    exact start_mem_rayCells _ _
  unfold own at hm'
  split_ifs at hm' with hW
  obtain rfl := Option.some_injective _ hm'
  rw [mem_fig1WallCells_iff (by omega) he2] at hmW
  rw [vCell, mem_rayCells_iff (isAxisDir_sideDir _ _)] at hm
  rw [vCell, mem_rayCells_iff (isAxisDir_sideDir _ _)]
  obtain ⟨hp1, hp2, -, -⟩ := hp'
  obtain ⟨hY1, hY2, hc1, hc2, hs1, hs2, hse, hb1⟩ := hp
  subst hs
  obtain ⟨x, y⟩ := p
  obtain ⟨m1, m2⟩ := m
  unfold IsSideVert at hsd
  unfold IsWallCell at hmW
  unfold sideDir at hm ⊢
  unfold vmap at hm h0
  simp only [vCell, Prod.mk.injEq] at hm h0 hsd hp1 hp2 ⊢
  clear hW
  have hY : m2 / 2 ≤ Y0 - 1 ∨ Y0 + 2 * b ≤ m2 / 2 := by split_ifs at hm h0 <;> ray_omega
  have hpar : m2 % 2 = 0 ∨ m1 % 2 = 0 := by split_ifs at hm h0 <;> ray_omega
  by_cases hl : m1 ≤ 2 * ((s : ℤ) + c0 - 1)
  · rw [cell_lo hY hl hpar]
    split_ifs at hm h0 ⊢ <;> ray_omega
  · have hr : 2 * ((s : ℤ) + 2 * b + c0) ≤ m1 := by split_ifs at hm h0 <;> ray_omega
    rw [cell_hi hY hr hpar]
    split_ifs at hm h0 ⊢ <;> ray_omega

/-- **The hexagonal hole keeps the order of the rows**: it keeps the rows below row `Y0` and moves
the others up by `2b`. -/
theorem rowMono (hp : Params h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {s : ℕ}
    (hs : (s : ℤ) = sL) : (HexHole.realization hp hh' he' hs).RowMono := by
  intro p _ q _ hlt
  change (vmap b Y0 c0 s p).2 < (vmap b Y0 c0 s q).2
  unfold vmap
  split_ifs <;> (try simp only) <;> omega

end HexHole

end GraphMinor.GM13
