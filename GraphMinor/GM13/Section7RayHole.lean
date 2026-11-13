module

public import GraphMinor.GM13.Section7RayShapes
public import GraphMinor.GM13.Section7RealizeHole

/-!
# Graph Minors XIII, (7.3): the rays of the hole

The realization of the hole `Hole(Y0, c0)` keeps the rays of the side vertices out of the kept
cells (`Hole.rayOK`) and keeps the order of the rows (`Hole.rowMono`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- Far above the band, the hole moves each cell of a row back by `(4, 4)`. -/
theorem cell_high {Y0 c0 m1 y : ℤ} (hy : Y0 + 2 ≤ y) :
    cell Y0 c0 (m1, 2 * y) = (m1 - 4, 2 * y - 4) := by
  unfold cell vertexCell horizCell
  simp only
  split_ifs <;> hole_omega

/-- **The hole keeps the rays.** A kept cell on the ray of a side vertex `p` goes to a cell on
the ray of `p`. The ray of the cell of `vmap p` meets the old wall only at its start, except for
a side vertex on the left or right from row `Y0` on. There the hole moves cells back by
`(4, 4)` (`cell_high`), which maps the ray onto the ray of `p`. -/
theorem rayOK (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') :
    (realization hp hh' he').RayOK := by
  have hh2 : 2 ≤ h' + 2 := by omega
  have he2 : Even (h' + 2) := he'.add even_two
  refine Shape.Realization.rayOK_of_own _ hh2 he2 hh' he' ?_
  intro p hp' hs m hm hmW m' hm'
  change own h' Y0 c0 m = some m' at hm'
  change m ∈ rayCells (vCell (vmap Y0 c0 p)) _ at hm
  by_cases h0 : m = vCell (vmap Y0 c0 p)
  · rw [h0, own_vmap hp hp'] at hm'
    rw [← Option.some_injective _ hm']
    exact start_mem_rayCells _ _
  unfold own at hm'
  split_ifs at hm' with hW
  obtain rfl := Option.some_injective _ hm'
  rw [mem_fig1WallCells_iff (by omega) he2] at hmW
  rw [vCell, mem_rayCells_iff (isAxisDir_sideDir _ _)] at hm
  rw [vCell, mem_rayCells_iff (isAxisDir_sideDir _ _)]
  obtain ⟨hp1, hp2, -, -⟩ := hp'
  obtain ⟨hY1, hY2, hc1, hc2⟩ := hp
  obtain ⟨a, b⟩ := p
  obtain ⟨m1, m2⟩ := m
  unfold IsSideVert at hs
  unfold IsWallCell at hmW
  unfold sideDir at hm ⊢
  unfold vmap at hm h0
  simp only [vCell, Prod.mk.injEq] at hm h0 hs hp1 hp2 ⊢
  have hb : Y0 ≤ b ∧ b ≠ 0 ∧ b ≠ h' := by
    split_ifs at hm h0 <;> hole_omega
  obtain ⟨y, rfl⟩ : ∃ y : ℤ, m2 = 2 * y := ⟨b + 2, by split_ifs at hm <;> hole_omega⟩
  rw [cell_high (by split_ifs at hm <;> hole_omega)]
  simp only
  split_ifs at hm h0 ⊢ <;> simp only [Nat.cast_add, Nat.cast_ofNat, Int.reduceNeg, true_implies,
    zero_ne_one, false_implies, one_ne_zero, reduceCtorEq, and_true, true_and, neg_eq_zero,
    not_and] at hm h0 hmW ⊢ <;> omega

/-- **The hole keeps the order of the rows**: it keeps the rows below row `Y0` and moves the
others up by two. -/
theorem rowMono (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') :
    (realization hp hh' he').RowMono := by
  intro p _ q _ hlt
  change (vmap Y0 c0 p).2 < (vmap Y0 c0 q).2
  unfold vmap
  split_ifs <;> (try simp only) <;> omega

end Hole

end GraphMinor.GM13
