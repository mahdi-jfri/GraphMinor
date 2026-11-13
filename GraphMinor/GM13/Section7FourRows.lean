module

public import GraphMinor.GM13.Section7FourMetric
import GraphMinor.GM13.Section7WallCells

/-!
# Graph Minors XIII, (7.4): a vertex far from a few points reaches a whole row

This file is the planar step of the bound of the tangle metric by the wall distance, in the
coordinates of Fig. 1. Let `X` be a set of at most `M` points and `p₀` a point of the Fig. 1
drawing of the elementary wall of height `h ≥ 2M + 2`, at distance more than `M + 2` from every
point of `X`. Then a connected part of the drawing contains `p₀` and a whole row, and misses `X`
(`exists_free_row_set`).

The part is a stack of bricks: the brick `B₀` containing `p₀`, then bricks going up (or down)
one row at a time, to a row `j` that contains no point of `X`. Such a row exists among the
`M + 1` rows nearest to `p₀`, since the points of `X` lie on at most `M` rows. A brick `i` steps
away is at face distance `i ≤ M` from `B₀`, so its points are at distance at most `M + 2` from
`p₀` (`planeWallDist_le_of_mem_fig1Brick`), and they are not in `X`.
-/

public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor

universe u v

/-! ## Distances between points of two bricks -/

/-- A point of the closed brick with lower left corner `(x, y)` lies at the corner of a square of
that brick. -/
theorem exists_square_of_mem_fig1Brick {h x y : ℕ} (hb : IsFig1Brick h x y) {p : ℝ × ℝ}
    (hp : p ∈ fig1Brick x y) :
    ∃ q ∈ squaresAbove (cellCode p), wallFace h q = ((x : ℤ) + 1, (y : ℤ)) := by
  obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hp
  obtain ⟨⟨m, hm⟩, hbx, hby⟩ := hb
  have hy : cellCode1 p.2 = 2 * (y : ℤ) ∨ cellCode1 p.2 = 2 * (y : ℤ) + 1 ∨
      cellCode1 p.2 = 2 * (y : ℤ) + 2 := cellCode1_mem_iff.mpr ⟨by exact_mod_cast hy1, by
        exact_mod_cast hy2⟩
  rcases le_or_gt p.1 ((x : ℝ) + 1) with hle | hlt
  · have hx : cellCode1 p.1 = 2 * (x : ℤ) ∨ cellCode1 p.1 = 2 * (x : ℤ) + 1 ∨
        cellCode1 p.1 = 2 * (x : ℤ) + 2 := cellCode1_mem_iff.mpr ⟨by exact_mod_cast hx1, by
          exact_mod_cast hle⟩
    refine ⟨(2 * (x : ℤ) + 1, 2 * (y : ℤ) + 1), ?_, ?_⟩
    · rw [mem_squaresAbove_iff]
      simp only [cellCode]
      omega
    · rw [wallFace_square, if_pos (by omega)]
      ext <;> simp only <;> omega
  · have hx : cellCode1 p.1 = 2 * ((x : ℤ) + 1) ∨ cellCode1 p.1 = 2 * ((x : ℤ) + 1) + 1 ∨
        cellCode1 p.1 = 2 * ((x : ℤ) + 1) + 2 := cellCode1_mem_iff.mpr ⟨by push_cast; linarith,
          by push_cast; linarith⟩
    refine ⟨(2 * ((x : ℤ) + 1) + 1, 2 * (y : ℤ) + 1), ?_, ?_⟩
    · rw [mem_squaresAbove_iff]
      simp only [cellCode]
      omega
    · rw [wallFace_square, if_pos (by omega)]
      ext <;> simp only <;> omega

/-- **Points of two bricks.** A point of the brick `B` and a point of the brick `B'` are at distance
at most `2 + hexDist B B'` in the Fig. 1 drawing. -/
theorem planeWallDist_le_of_mem_fig1Brick {h : ℕ} (hh : 1 ≤ h) (he : Even h) {x y x' y' : ℕ}
    (hb : IsFig1Brick h x y) (hb' : IsFig1Brick h x' y') {p z : ℝ × ℝ}
    (hp : p ∈ fig1Brick x y) (hz : z ∈ fig1Brick x' y') :
    (planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h)) (fig1PlaneEquiv p)
      (fig1PlaneEquiv z) : ℤ) ≤ 2 + hexDist ((x : ℤ) + 1, (y : ℤ)) ((x' : ℤ) + 1, (y' : ℤ)) := by
  have N := fig1FaceNaming hh he
  have hnn := hexDist_nonneg ((x : ℤ) + 1, (y : ℤ)) ((x' : ℤ) + 1, (y' : ℤ))
  by_cases hc : cellCode p = cellCode z
  · have := N.planeWallDist_le_two_of_cellCode_eq hc
    omega
  obtain ⟨q, hq, hqF⟩ := exists_square_of_mem_fig1Brick hb hp
  obtain ⟨q', hq', hqF'⟩ := exists_square_of_mem_fig1Brick hb' hz
  have h1 := N.planeWallDist_le hc hq hq'
  have hB : IsBrick h ((x : ℤ) + 1, (y : ℤ)) := by
    obtain ⟨⟨m, hm⟩, h2, h3⟩ := hb
    simp only [IsBrick]; omega
  have hB' : IsBrick h ((x' : ℤ) + 1, (y' : ℤ)) := by
    obtain ⟨⟨m, hm⟩, h2, h3⟩ := hb'
    simp only [IsBrick]; omega
  have hne : ∀ {K : ℤ × ℤ}, IsBrick h K → K ≠ outFace :=
    fun hK hK' => not_isBrick_outFace h (hK' ▸ hK)
  rw [hqF, hqF', faceDist_of_ne (hne hB) (hne hB')] at h1
  have h2 := cellInd_le_one (fig1WallCells h) (cellCode p)
  have h3 := cellInd_le_one (fig1WallCells h) (cellCode z)
  have h4 := min_le_left (hexDist ((x : ℤ) + 1, (y : ℤ)) ((x' : ℤ) + 1, (y' : ℤ)))
    (outDepth h ((x : ℤ) + 1, (y : ℤ)) + outDepth h ((x' : ℤ) + 1, (y' : ℤ)))
  omega

/-- **Every point of the drawing is on a brick.** A point of the Fig. 1 drawing of the elementary
wall of height `h` lies in a closed brick of that wall. -/
theorem exists_fig1Brick_of_mem_fig1Set {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℝ × ℝ}
    (hp : p ∈ fig1Set h) : ∃ x y : ℕ, IsFig1Brick h x y ∧ p ∈ fig1Brick x y := by
  have hc : cellCode p ∈ fig1WallCells h := by
    rw [fig1Set_eq_cellSet] at hp; exact hp
  rw [mem_fig1WallCells_iff (by omega) he] at hc
  simp only [IsWallCell] at hc
  obtain ⟨k, hk⟩ := he
  set a := (cellCode p).1 with ha
  set b := (cellCode p).2 with hb
  let cond : ℤ → ℤ → Prop := fun xx yy =>
    0 ≤ yy ∧ yy < h ∧ 1 ≤ xx + (xx + yy) % 2 ∧ xx + (xx + yy) % 2 ≤ 2 * h
  have hex : ∃ xx yy : ℤ, (xx = (a - 1) / 2 ∨ xx = a / 2) ∧ (yy = (b - 1) / 2 ∨ yy = b / 2) ∧
      cond xx yy := by
    by_cases h11 : cond ((a - 1) / 2) ((b - 1) / 2)
    · exact ⟨_, _, Or.inl rfl, Or.inl rfl, h11⟩
    by_cases h12 : cond ((a - 1) / 2) (b / 2)
    · exact ⟨_, _, Or.inl rfl, Or.inr rfl, h12⟩
    by_cases h21 : cond (a / 2) ((b - 1) / 2)
    · exact ⟨_, _, Or.inr rfl, Or.inl rfl, h21⟩
    by_cases h22 : cond (a / 2) (b / 2)
    · exact ⟨_, _, Or.inr rfl, Or.inr rfl, h22⟩
    exfalso
    simp only [cond] at h11 h12 h21 h22
    omega
  obtain ⟨xx, yy, hxx, hyy, hcond⟩ := hex
  simp only [cond] at hcond
  have hpx : (xx : ℝ) ≤ p.1 ∧ p.1 ≤ xx + 1 := cellCode1_mem_iff.mp (by
    change cellCode1 p.1 = _ ∨ _
    have : cellCode1 p.1 = a := rfl
    omega)
  have hpy : (yy : ℝ) ≤ p.2 ∧ p.2 ≤ yy + 1 := cellCode1_mem_iff.mp (by
    have : cellCode1 p.2 = b := rfl
    omega)
  set X := xx + (xx + yy) % 2 with hX
  refine ⟨(X - 1).toNat, yy.toNat, ⟨?_, by omega, by omega⟩, ?_, ?_⟩
  · rw [Nat.odd_iff]; omega
  · have h1 : (((X - 1).toNat : ℕ) : ℝ) = (X : ℝ) - 1 := by
      have : (((X - 1).toNat : ℕ) : ℤ) = X - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have h2 : (X : ℝ) = xx ∨ (X : ℝ) = xx + 1 := by
      rcases Int.emod_two_eq_zero_or_one (xx + yy) with h | h
      · left; rw [hX, h]; simp
      · right; rw [hX, h]; push_cast; ring
    rw [h1]
    constructor <;> rcases h2 with h2 | h2 <;> rw [h2] <;> linarith [hpx.1, hpx.2]
  · have h1 : ((yy.toNat : ℕ) : ℝ) = (yy : ℝ) := by
      have : ((yy.toNat : ℕ) : ℤ) = yy := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [h1]
    exact hpy

/-! ## Connected pieces -/

/-- The frontier of a closed rectangle is connected. -/
theorem isPreconnected_frontier_rect {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IsPreconnected (frontier (Icc a b ×ˢ Icc c d)) := by
  have e : frontier (Icc a b ×ˢ Icc c d) =
      ((Icc a b ×ˢ {c}) ∪ ({a} ×ˢ Icc c d)) ∪ ((Icc a b ×ˢ {d}) ∪ ({b} ×ˢ Icc c d)) := by
    rw [frontier_prod_eq, closure_Icc, closure_Icc, frontier_Icc hab, frontier_Icc hcd]
    ext ⟨x, y⟩
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  rw [e]
  have hB := (isPreconnected_Icc (a := a) (b := b)).prod (isPreconnected_singleton (x := c))
  have hL := (isPreconnected_singleton (x := a)).prod (isPreconnected_Icc (a := c) (b := d))
  have hT := (isPreconnected_Icc (a := a) (b := b)).prod (isPreconnected_singleton (x := d))
  have hR := (isPreconnected_singleton (x := b)).prod (isPreconnected_Icc (a := c) (b := d))
  refine IsPreconnected.union (b, c) (Or.inl ⟨right_mem_Icc.mpr hab, rfl⟩)
    (Or.inr ⟨rfl, left_mem_Icc.mpr hcd⟩) ?_ ?_
  · exact IsPreconnected.union (a, c) ⟨left_mem_Icc.mpr hab, rfl⟩ ⟨rfl, left_mem_Icc.mpr hcd⟩ hB hL
  · exact IsPreconnected.union (b, d) ⟨right_mem_Icc.mpr hab, rfl⟩ ⟨rfl, right_mem_Icc.mpr hcd⟩
      hT hR

theorem mem_frontier_rect_of_snd_eq {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {z : ℝ × ℝ}
    (hz1 : z.1 ∈ Icc a b) (hz2 : z.2 = c ∨ z.2 = d) : z ∈ frontier (Icc a b ×ˢ Icc c d) := by
  rw [frontier_prod_eq, closure_Icc, closure_Icc, frontier_Icc hab, frontier_Icc hcd]
  exact Or.inl ⟨hz1, hz2⟩

theorem isPreconnected_frontier_fig1Brick (x y : ℕ) :
    IsPreconnected (frontier (fig1Brick x y)) :=
  isPreconnected_frontier_rect (by linarith) (by linarith)

/-- Two bricks on consecutive rows whose abscissas differ by one share a point of their
frontiers. -/
theorem frontier_fig1Brick_inter_nonempty {x y x' : ℕ} (hx : x' ≤ x + 1 ∧ x ≤ x' + 1) :
    (frontier (fig1Brick x y) ∩ frontier (fig1Brick x' (y + 1))).Nonempty := by
  refine ⟨((x : ℝ) + 1, (y : ℝ) + 1), ?_, ?_⟩
  · exact mem_frontier_rect_of_snd_eq (by linarith) (by linarith)
      ⟨by linarith, by linarith⟩ (Or.inr rfl)
  · have h1 : (x' : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast hx.1
    have h2 : (x : ℝ) ≤ (x' : ℝ) + 1 := by exact_mod_cast hx.2
    exact mem_frontier_rect_of_snd_eq (by linarith) (by linarith) ⟨h1, by linarith⟩
      (Or.inl (by push_cast; ring))

/-- A row segment of the Fig. 1 drawing: the row `j` from abscissa `1` to `2h + 1`. -/
@[expose] def fig1RowSeg (h j : ℕ) : Set (ℝ × ℝ) := Icc (1 : ℝ) (2 * (h : ℝ) + 1) ×ˢ {(j : ℝ)}

theorem fig1RowSeg_subset_fig1Set {h j : ℕ} (hj : j < h) : fig1RowSeg h j ⊆ fig1Set h := by
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy⟩
  simp only [mem_singleton_iff] at hy
  subst hy
  set i := ⌊x⌋₊ with hi
  have hi1 : (i : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hi2 : x < (i : ℝ) + 1 := Nat.lt_floor_add_one x
  have hi3 : 1 ≤ i := Nat.le_floor (by simpa using hx1)
  by_cases hlast : i ≤ 2 * h
  · refine horizontalLatticeLine_subset_fig1Set (i := i) (j := j) ?_ ?_ ⟨⟨hi1, hi2.le⟩, rfl⟩
    · refine ⟨by omega, by omega, by simp <;> omega, by simp <;> omega⟩
    · refine ⟨by omega, by omega, by simp <;> omega, by simp <;> omega⟩
  · have hx : x = 2 * (h : ℝ) + 1 := by
      have : (2 * h + 1 : ℕ) ≤ i := by omega
      have : (2 * (h : ℝ) + 1) ≤ i := by exact_mod_cast this
      linarith
    refine horizontalLatticeLine_subset_fig1Set (i := 2 * h) (j := j) ?_ ?_ ⟨⟨?_, ?_⟩, rfl⟩
    · refine ⟨by omega, by omega, by simp, by simp <;> omega⟩
    · refine ⟨by omega, by omega, by simp <;> omega, by simp <;> omega⟩
    · push_cast; linarith
    · push_cast; linarith

theorem isPreconnected_fig1RowSeg (h j : ℕ) : IsPreconnected (fig1RowSeg h j) :=
  isPreconnected_Icc.prod isPreconnected_singleton

/-! ## The free row -/

/-- **Pigeonhole for rows.** If `X` has at most `M` points, then among the `M + 1` rows
`lo, …, lo + M` there is one that contains no point of `X`. -/
theorem exists_free_row {X : Set (ℝ × ℝ)} (hX : X.Finite) {M : ℕ} (hXM : X.ncard ≤ M) (lo : ℕ) :
    ∃ t ≤ M, ∀ z ∈ X, z.2 ≠ ((lo + t : ℕ) : ℝ) := by
  by_contra hno
  push Not at hno
  have hsub : ∀ t ∈ (Iic M : Set ℕ), ((lo + t : ℕ) : ℝ) ∈ Prod.snd '' X := by
    intro t ht
    obtain ⟨z, hz, hzt⟩ := hno t ht
    exact ⟨z, hz, hzt⟩
  have hinj : InjOn (fun t : ℕ => ((lo + t : ℕ) : ℝ)) (Iic M) := by
    intro a _ b _ hab
    have : ((lo + a : ℕ) : ℝ) = ((lo + b : ℕ) : ℝ) := hab
    have := Nat.cast_injective this
    omega
  have h1 := ncard_le_ncard_of_injOn _ hsub hinj (hX.image _)
  have h2 : (Iic M : Set ℕ).ncard = M + 1 := by
    rw [← Finset.coe_Iic, ncard_coe_finset, Nat.card_Iic]
  have h3 := ncard_image_le (f := Prod.snd) hX
  omega

/-- **The planar step.** Let `X` be a finite set of at most `M` points, `h ≥ 2M + 2` even, and
`p₀` a point of the Fig. 1 drawing of the elementary wall of height `h` at distance more than
`M + 2` from every point of `X`. Then some connected part of the drawing contains `p₀` and the row
segment `fig1RowSeg h j` of a row `j < h`, and misses `X`. -/
theorem exists_free_row_set {h M : ℕ} (he : Even h) (hh : 2 * M + 2 ≤ h) {X : Set (ℝ × ℝ)}
    (hX : X.Finite) (hXM : X.ncard ≤ M) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ fig1Set h)
    (hfar : ∀ z ∈ X, M + 2 < planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h))
      (fig1PlaneEquiv p₀) (fig1PlaneEquiv z)) :
    ∃ (j : ℕ) (Y : Set (ℝ × ℝ)), j < h ∧ IsPreconnected Y ∧ p₀ ∈ Y ∧ Y ⊆ fig1Set h ∧
      Disjoint Y X ∧ fig1RowSeg h j ⊆ Y := by
  classical
  obtain ⟨x₀, y₀, hb₀, hp₀B⟩ := exists_fig1Brick_of_mem_fig1Set (by omega) he hp₀
  have hb₀' := hb₀
  obtain ⟨⟨m₀, hm₀⟩, hx₀, hy₀⟩ := hb₀'
  -- the direction and the rows
  let up : Prop := y₀ + M + 1 ≤ h
  let lo : ℕ := if up then y₀ else y₀ - M
  obtain ⟨t, htM, hfree⟩ := exists_free_row hX hXM lo
  let j := lo + t
  let k : ℕ := if up then t else M - t
  let by' : ℕ → ℕ := fun i => if up then y₀ + i else y₀ - i
  let bx : ℕ → ℕ := fun i => if i % 2 = 0 then x₀ else
    (if x₀ + 3 ≤ 2 * h + 1 then x₀ + 1 else x₀ - 1)
  have hbyk : by' k = j := by
    simp only [by', k, j, lo]
    split_ifs with hu <;> omega
  have hk : k ≤ M := by simp only [k]; split_ifs <;> omega
  have hbrick : ∀ i ≤ M, IsFig1Brick h (bx i) (by' i) := by
    intro i hi
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.odd_iff]
      simp only [bx, by', up]
      split_ifs <;> omega
    · simp only [bx]; split_ifs <;> omega
    · simp only [by', up]; split_ifs <;> omega
  have hjh : j < h := by
    have := (hbrick k hk).2.2
    rw [hbyk] at this
    omega
  -- the set
  let Y : Set (ℝ × ℝ) := (⋃ i ∈ Iic k, frontier (fig1Brick (bx i) (by' i))) ∪ fig1RowSeg h j
  refine ⟨j, Y, hjh, ?_, ?_, ?_, ?_, subset_union_right⟩
  · -- connected
    have hchain : IsPreconnected (⋃ i ∈ Iic k, frontier (fig1Brick (bx i) (by' i))) := by
      refine IsPreconnected.biUnion_of_chain ordConnected_Iic
        (fun i _ => isPreconnected_frontier_fig1Brick _ _) ?_
      intro i hi hi1
      rw [Order.succ_eq_add_one] at hi1 ⊢
      have hi1' : i + 1 ≤ M := (mem_Iic.mp hi1).trans hk
      have hdx : bx (i + 1) ≤ bx i + 1 ∧ bx i ≤ bx (i + 1) + 1 := by
        simp only [bx]; split_ifs <;> omega
      by_cases hu : up
      · have e1 : by' (i + 1) = by' i + 1 := by simp only [by', if_pos hu]; omega
        rw [e1]
        exact frontier_fig1Brick_inter_nonempty hdx
      · have e1 : by' i = by' (i + 1) + 1 := by
          simp only [by', if_neg hu]
          simp only [up] at hu
          omega
        rw [e1, inter_comm]
        exact frontier_fig1Brick_inter_nonempty ⟨hdx.2, hdx.1⟩
    refine IsPreconnected.union (((bx k : ℝ) + 1), (j : ℝ)) ?_ ?_ hchain
      (isPreconnected_fig1RowSeg h j)
    · refine mem_biUnion (x := k) (mem_Iic.mpr le_rfl) ?_
      rw [hbyk]
      exact mem_frontier_rect_of_snd_eq (by linarith) (by linarith)
        ⟨by linarith, by linarith⟩ (Or.inl rfl)
    · have hbk := (hbrick k hk).2.1
      refine ⟨⟨by linarith [(Nat.cast_nonneg (bx k) : (0 : ℝ) ≤ bx k)], ?_⟩, rfl⟩
      have : ((bx k : ℕ) : ℝ) + 1 ≤ 2 * (h : ℝ) + 1 := by
        have : bx k + 1 ≤ 2 * h + 1 := by omega
        exact_mod_cast this
      exact this
  · -- p₀ ∈ Y
    refine Or.inl (mem_biUnion (x := 0) (mem_Iic.mpr (Nat.zero_le _)) ?_)
    have e0 : bx 0 = x₀ := by simp [bx]
    have e1 : by' 0 = y₀ := by simp [by']
    rw [e0, e1]
    refine ⟨subset_closure hp₀B, fun hint => ?_⟩
    have hint' : p₀ ∈ Ioo (x₀ : ℝ) ((x₀ : ℝ) + 2) ×ˢ Ioo (y₀ : ℝ) ((y₀ : ℝ) + 1) := by
      rw [← interior_Icc, ← interior_Icc, ← interior_prod_eq]
      exact hint
    exact Set.disjoint_left.mp (disjoint_open_brick_fig1Set (h := h) ⟨m₀, hm₀⟩) hint' hp₀
  · -- Y ⊆ fig1Set
    refine union_subset (iUnion₂_subset fun i hi => ?_) (fig1RowSeg_subset_fig1Set hjh)
    obtain ⟨hodd, h1, h2⟩ := hbrick i ((mem_Iic.mp hi).trans hk)
    exact frontier_brick_subset_fig1Set he h1 h2 hodd
  · -- Y misses X
    rw [Set.disjoint_left]
    rintro z (hz | hz) hzX
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
      have hik : i ≤ M := (mem_Iic.mp hi).trans hk
      have hzB : z ∈ fig1Brick (bx i) (by' i) :=
        (isClosed_Icc.prod isClosed_Icc).frontier_subset hzi
      have hd := planeWallDist_le_of_mem_fig1Brick (by omega) he hb₀ (hbrick i hik) hp₀B hzB
      have hhex : hexDist ((x₀ : ℤ) + 1, (y₀ : ℤ)) (((bx i : ℕ) : ℤ) + 1, ((by' i : ℕ) : ℤ)) ≤
          (i : ℤ) := by
        have hdx : bx i ≤ x₀ + 1 ∧ x₀ ≤ bx i + 1 ∧ (i % 2 = 0 → bx i = x₀) := by
          simp only [bx]; split_ifs <;> omega
        have hdy : (by' i = y₀ + i ∨ by' i + i = y₀) := by
          simp only [by']; split_ifs <;> omega
        simp only [hexDist]
        omega
      have := hfar z hzX
      omega
    · obtain ⟨-, hz2⟩ := hz
      exact hfree z hzX hz2

end GraphMinor.GM13
