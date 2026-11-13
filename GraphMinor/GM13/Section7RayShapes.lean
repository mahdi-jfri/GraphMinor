module

public import GraphMinor.GM13.Section7RealizePic

/-!
# Graph Minors XIII, (7.3): the rays of the steps leave the kept cells

`Shape.Realization.exists_homeo` needs two facts about a realization `R` of a shape `τ`: the rays
of the side vertices leave the kept cells (`Realization.RayOK`), and the old vertices keep the
order of the rows (`Realization.RowMono`). This file reduces the first fact to a fact about `τ`
alone (`Realization.rayOK_of_own`): every kept cell `m` on the ray of a side vertex `p` goes to a
cell on the ray of `p` in the new wall of Fig. 1. Since the rays of the wall of Fig. 1 leave the
wall at once (`eq_of_mem_rayCells_of_isWallCell`), that cell is the cell of `p`, so `m` is the
cell of `R.vmap p`.

Both facts are then shown for the turn of a realization (`Realization.rayOK_rotate`,
`Realization.rowMono_rotate`) and for the moved subwalls (`Realization.rayOK_of_trans`,
`Realization.rowMono_of_trans`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function

/-- **The rays of the wall of Fig. 1 leave it at once**: a cell of the wall on the ray of a side
vertex `p` is the cell of `p`. -/
theorem eq_of_mem_rayCells_of_isWallCell {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h)
    (hs : IsSideVert h p) {m : ℤ × ℤ} (hm : m ∈ rayCells (vCell p) (sideDir h p))
    (hmW : IsWallCell h m) : m = vCell p := by
  obtain ⟨hp1, hp2, -, -⟩ := hp
  rw [vCell, mem_rayCells_iff (isAxisDir_sideDir h p)] at hm
  rw [vCell]
  unfold IsSideVert at hs
  unfold sideDir at hm
  unfold IsWallCell at hmW
  obtain ⟨m1, m2⟩ := m
  split_ifs at hm <;> simp only [Int.reduceNeg, true_implies, zero_ne_one, false_implies,
    one_ne_zero, reduceCtorEq, and_true, true_and, neg_eq_zero, Prod.mk.injEq] at hm hmW ⊢ <;>
    omega

namespace Shape.Realization

variable {h h' : ℕ} {τ : Shape h h'} (R : τ.Realization)

/-- **The rays leave the kept cells if the shape keeps them on the rays.** If every kept cell on
the ray of a side vertex `p` goes to a cell on the ray of `p` in the new wall of Fig. 1, then that
cell is the cell of `p` (`eq_of_mem_rayCells_of_isWallCell`), and the only kept cell that goes
to the cell of `p` is the cell of `R.vmap p` (`own_eq_vCell_iff`). -/
theorem rayOK_of_own (hh : 2 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h')
    (hτ : ∀ p ∈ elementaryWallVerts h', IsSideVert h' p →
      ∀ m ∈ rayCells (vCell (R.vmap p)) (sideDir h' p), m ∈ fig1WallCells h →
        ∀ m', τ.own m = some m' → m' ∈ rayCells (vCell p) (sideDir h' p)) :
    R.RayOK := by
  intro p hp hs m hm hmW hown
  obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hown
  have hW := τ.own_mem m hmW m' hm'
  rw [mem_fig1WallCells_iff hh' he'] at hW
  have e := eq_of_mem_rayCells_of_isWallCell hp hs (hτ p hp hs m hm hmW m' hm') hW
  rw [e] at hm'
  exact (R.own_eq_vCell_iff hh he hp m).mp ⟨hmW, hm'⟩

/-! ## The turn of a realization -/

theorem rotC_mem_rayCells_iff (h : ℕ) {c d m : ℤ × ℤ} :
    rotC h m ∈ rayCells (rotC h c) (-d.1, -d.2) ↔ m ∈ rayCells c d := by
  simp only [rayCells, rotC, mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp only [Prod.mk.injEq] at hn
    exact Prod.ext (by simp only; linarith [hn.1]) (by simp only; linarith [hn.2])
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp only [Prod.mk.injEq]; constructor <;> ring⟩

/-- The turn of a side vertex is a side vertex whose ray goes the other way. -/
theorem sideDir_rotV {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') (hh' : 1 ≤ h')
    (hs : IsSideVert h' p) :
    sideDir h' (rotV h' p) = (-(sideDir h' p).1, -(sideDir h' p).2) ∧
      IsSideVert h' (rotV h' p) := by
  obtain ⟨hp1, hp2, -, -⟩ := hp
  unfold IsSideVert at hs ⊢
  unfold sideDir rotV
  simp only
  constructor
  · split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
  · omega

/-- **The rays of the turned realization leave the kept cells**, since the turn maps the rays of
the turned realization onto the rays of `R`. -/
theorem rayOK_rotate (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h') (hR : R.RayOK) :
    (R.rotate hh he hh' he').RayOK := by
  intro p hp hs m hm hmW hown
  have hp' := rotV_mem hp
  obtain ⟨hdir, hs'⟩ := sideDir_rotV hp hh' hs
  have hv := R.vmap_mem _ hp'
  change m ∈ rayCells (vCell (rotV h (R.vmap (rotV h' p)))) (sideDir h' p) at hm
  change (τ.own (rotC h m)).map (rotC h') ≠ none at hown
  have hm' : rotC h m ∈ rayCells (vCell (R.vmap (rotV h' p))) (sideDir h' (rotV h' p)) := by
    rw [hdir, ← rotC_rotC h (vCell (R.vmap (rotV h' p))), ← vCell_rotV hv, rotC_mem_rayCells_iff]
    exact hm
  have e := hR (rotV h' p) hp' hs' (rotC h m) hm' ((mem_fig1WallCells_rotC hh he).mpr hmW)
    (by simpa using hown)
  change m = vCell (rotV h (R.vmap (rotV h' p)))
  rw [vCell_rotV hv, ← e, rotC_rotC]

/-- The turned realization keeps the order of the rows, since the turn reverses it twice. -/
theorem rowMono_rotate (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h')
    (hR : R.RowMono) : (R.rotate hh he hh' he').RowMono := by
  intro p hp q hq hlt
  have h1 := hR (rotV h' q) (rotV_mem hq) (rotV h' p) (rotV_mem hp) (by
    obtain ⟨-, hp2, -, -⟩ := hp
    obtain ⟨-, hq2, -, -⟩ := hq
    simp only [rotV]
    omega)
  obtain ⟨-, h3, -, -⟩ := R.vmap_mem _ (rotV_mem hp)
  obtain ⟨-, h4, -, -⟩ := R.vmap_mem _ (rotV_mem hq)
  change h - (R.vmap (rotV h' p)).2 < h - (R.vmap (rotV h' q)).2
  omega

/-! ## Moved subwalls -/

/-- **The rays of a moved subwall leave the kept cells**: the shape moves each kept cell back by
the same vector as the vertices. -/
theorem rayOK_of_trans (hh : 2 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h') {i j : ℕ}
    (hown : ∀ m, τ.own m = transOwn h' i j m) (hv : ∀ p, R.vmap p = (p.1 + i, p.2 + j)) :
    R.RayOK := by
  refine R.rayOK_of_own hh he hh' he' fun p hp hs m hm _ m' hm' => ?_
  rw [hown] at hm'
  unfold transOwn at hm'
  split_ifs at hm' with hW
  obtain rfl := Option.some_injective _ hm'
  rw [hv] at hm
  obtain ⟨n, hn⟩ := hm
  refine ⟨n, ?_⟩
  rw [hn]
  simp only [vCell, Prod.mk.injEq]
  push_cast
  constructor <;> ring

theorem rowMono_of_trans {i j : ℕ} (hv : ∀ p, R.vmap p = (p.1 + i, p.2 + j)) : R.RowMono := by
  intro p _ q _ hlt
  rw [hv, hv]
  simp only
  omega

end Shape.Realization

end GraphMinor.GM13
