module

public import GraphMinor.GM13.Section7WallCells

/-!
# Graph Minors XIII, Section 7: cell walks in the wall of Fig. 1

This file proves the upper bound that matches `le_planeWallDist_fig1`. For points `s, t` in
different cells, and any faces `F` at `s` and `G` at `t`, `d(s, t) ≤ [s] + [t] + D(F, G)`,
where `D` is `faceDist` (`planeWallDist_fig1_le`).

The proof builds cell walks. `cellDist 𝒰 c d` is the least cost of a cell walk from `c` to `d`,
not counting the first cell. It obeys the triangle inequality, and one step to a cell `d` costs
`[d]`. Then:

* two squares of the same face are at `cellDist` zero (`cellDist_eq_zero_of_wallFace_eq`). A brick
  has two squares with a free cell between them, and every square of the outer face is joined to
  the square `(-1, -1)` around the outside of the wall;
* squares of touching faces are at `cellDist` at most one (`cellDist_le_one_of_faceAdj`), by a
  walk across one cell of the wall;
* a brick has a touching brick one step nearer to any other brick, and, unless it touches the
  outer face, a touching brick one step nearer to the outer face. So `cellDist` between squares is
  at most the face distance (`cellDist_le_faceDist`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## The least cost of a cell walk -/

namespace CellWalk

/-- The walk run backwards. -/
def reverse : {c d : ℤ × ℤ} → CellWalk c d → CellWalk d c
  | _, _, nil c => nil c
  | _, _, cons h w => w.reverse.append (cons h.symm (nil _))

theorem costTail_append (𝒰 : Set (ℤ × ℤ)) :
    ∀ {c d e : ℤ × ℤ} (w : CellWalk c d) (w' : CellWalk d e),
      (w.append w').costTail 𝒰 = w.costTail 𝒰 + w'.costTail 𝒰
  | _, _, _, nil _, w' => by simp [append, costTail]
  | _, _, _, cons _ w, w' => by
    show (w.append w').cost 𝒰 = w.cost 𝒰 + w'.costTail 𝒰
    rw [cost_append, cost_eq_ind_add_costTail 𝒰 w', cost_eq_costInit_add_ind 𝒰 w]
    ring

theorem costTail_reverse (𝒰 : Set (ℤ × ℤ)) :
    ∀ {c d : ℤ × ℤ} (w : CellWalk c d),
      w.reverse.costTail 𝒰 + cellInd 𝒰 d = w.costTail 𝒰 + cellInd 𝒰 c
  | _, _, nil _ => by simp [reverse, costTail]
  | c, _, cons h w => by
    have := costTail_reverse 𝒰 w
    have e : (cons h.symm (nil c)).costTail 𝒰 = cellInd 𝒰 c := rfl
    show (w.reverse.append (cons h.symm (nil c))).costTail 𝒰 + _ = w.cost 𝒰 + _
    rw [costTail_append, e, cost_eq_ind_add_costTail 𝒰 w]
    omega

end CellWalk

/-- The least cost of a cell walk from `c` to `d`, not counting the first cell. -/
noncomputable def cellDist (𝒰 : Set (ℤ × ℤ)) (c d : ℤ × ℤ) : ℕ :=
  sInf (range fun w : CellWalk c d => w.costTail 𝒰)

theorem exists_cellDist_eq (𝒰 : Set (ℤ × ℤ)) (c d : ℤ × ℤ) :
    ∃ w : CellWalk c d, w.costTail 𝒰 = cellDist 𝒰 c d := by
  obtain ⟨w⟩ := nonempty_cellWalk c d
  have hne : (range fun w : CellWalk c d => w.costTail 𝒰).Nonempty := ⟨_, w, rfl⟩
  obtain ⟨w', hw'⟩ := Nat.sInf_mem hne
  exact ⟨w', hw'⟩

theorem cellDist_le (𝒰 : Set (ℤ × ℤ)) {c d : ℤ × ℤ} (w : CellWalk c d) :
    cellDist 𝒰 c d ≤ w.costTail 𝒰 :=
  Nat.sInf_le ⟨w, rfl⟩

theorem cellDist_self (𝒰 : Set (ℤ × ℤ)) (c : ℤ × ℤ) : cellDist 𝒰 c c = 0 := by
  have := cellDist_le 𝒰 (CellWalk.nil c)
  simp only [CellWalk.costTail] at this
  omega

theorem cellDist_triangle (𝒰 : Set (ℤ × ℤ)) (c d e : ℤ × ℤ) :
    cellDist 𝒰 c e ≤ cellDist 𝒰 c d + cellDist 𝒰 d e := by
  obtain ⟨w, hw⟩ := exists_cellDist_eq 𝒰 c d
  obtain ⟨w', hw'⟩ := exists_cellDist_eq 𝒰 d e
  have := cellDist_le 𝒰 (w.append w')
  rw [CellWalk.costTail_append, hw, hw'] at this
  exact this

/-- One step costs `[d]`. -/
theorem cellDist_le_of_cellRel (𝒰 : Set (ℤ × ℤ)) {c d : ℤ × ℤ} (h : CellRel c d) :
    cellDist 𝒰 c d ≤ cellInd 𝒰 d := by
  have := cellDist_le 𝒰 (CellWalk.cons h (CellWalk.nil d))
  simpa [CellWalk.costTail, CellWalk.cost] using this

/-- Running a walk backwards changes its cost by the difference of the indicators of its ends. -/
theorem cellDist_symm_le (𝒰 : Set (ℤ × ℤ)) (c d : ℤ × ℤ) :
    cellDist 𝒰 d c + cellInd 𝒰 d ≤ cellDist 𝒰 c d + cellInd 𝒰 c := by
  obtain ⟨w, hw⟩ := exists_cellDist_eq 𝒰 c d
  have h1 := cellDist_le 𝒰 w.reverse
  have h2 := CellWalk.costTail_reverse 𝒰 w
  omega

/-- **Upper bound by a cell distance.** For points in different cells, `d(s, t)` is at most
`[s]` plus the cell distance between their cells. -/
theorem planeWallDist_cellSet_le_cellDist {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c)
    {s t : ℝ × ℝ} (hst : cellCode s ≠ cellCode t) :
    planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) ≤
      cellInd 𝒰 (cellCode s) + cellDist 𝒰 (cellCode s) (cellCode t) := by
  obtain ⟨w, hw⟩ := exists_cellDist_eq 𝒰 (cellCode s) (cellCode t)
  have hne : s ≠ t := fun h => hst (by rw [h])
  have h1 := planeWallDist_cellSet_le h𝒰 hne w
    (fun hn => absurd (CellWalk.eq_of_isNil w hn) hst)
  rw [CellWalk.cost_eq_ind_add_costTail, hw] at h1
  exact h1

/-- A walk along a row of free cells costs nothing. -/
theorem cellDist_row_eq_zero (𝒰 : Set (ℤ × ℤ)) (b : ℤ) :
    ∀ (k : ℕ) (a : ℤ), (∀ x, a < x → x ≤ a + k → (x, b) ∉ 𝒰) →
      cellDist 𝒰 (a, b) (a + k, b) = 0
  | 0, a, _ => by simpa using cellDist_self 𝒰 (a, b)
  | k + 1, a, hfree => by
    have h1 := cellDist_row_eq_zero 𝒰 b k a (fun x h1 h2 => hfree x h1 (by push_cast; omega))
    have h2 := cellDist_le_of_cellRel 𝒰 (cellRel_succ_fst (a + k) b)
    rw [cellInd_of_not_mem (hfree _ (by omega) (by push_cast; omega))] at h2
    have h3 := cellDist_triangle 𝒰 (a, b) (a + k, b) (a + k + 1, b)
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [e]
    omega

/-- A walk along a column of free cells costs nothing. -/
theorem cellDist_col_eq_zero (𝒰 : Set (ℤ × ℤ)) (a : ℤ) :
    ∀ (k : ℕ) (b : ℤ), (∀ y, b < y → y ≤ b + k → (a, y) ∉ 𝒰) →
      cellDist 𝒰 (a, b) (a, b + k) = 0
  | 0, b, _ => by simpa using cellDist_self 𝒰 (a, b)
  | k + 1, b, hfree => by
    have h1 := cellDist_col_eq_zero 𝒰 a k b (fun y h1 h2 => hfree y h1 (by push_cast; omega))
    have h2 := cellDist_le_of_cellRel 𝒰 (cellRel_succ_snd a (b + k))
    rw [cellInd_of_not_mem (hfree _ (by omega) (by push_cast; omega))] at h2
    have h3 := cellDist_triangle 𝒰 (a, b) (a, b + k) (a, b + k + 1)
    have e : b + ((k + 1 : ℕ) : ℤ) = b + k + 1 := by push_cast; ring
    rw [e]
    omega

/-- Between two cells of a row, if all cells strictly between them and the two ends are free,
the cell distance is zero in both directions. -/
theorem cellDist_row_eq_zero' (𝒰 : Set (ℤ × ℤ)) {a a' b : ℤ}
    (hfree : ∀ x, min a a' ≤ x → x ≤ max a a' → (x, b) ∉ 𝒰) :
    cellDist 𝒰 (a, b) (a', b) = 0 := by
  rcases le_total a a' with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have := cellDist_row_eq_zero 𝒰 b k a (fun x h1 h2 => hfree x (by omega) (by omega))
    rwa [← hk, add_sub_cancel] at this
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have := cellDist_row_eq_zero 𝒰 b k a' (fun x h1 h2 => hfree x (by omega) (by omega))
    rw [← hk, add_sub_cancel] at this
    have h2 := cellDist_symm_le 𝒰 (a', b) (a, b)
    rw [cellInd_of_not_mem (hfree a (by omega) (by omega)),
      cellInd_of_not_mem (hfree a' (by omega) (by omega))] at h2
    omega

theorem cellDist_col_eq_zero' (𝒰 : Set (ℤ × ℤ)) {a b b' : ℤ}
    (hfree : ∀ y, min b b' ≤ y → y ≤ max b b' → (a, y) ∉ 𝒰) :
    cellDist 𝒰 (a, b) (a, b') = 0 := by
  rcases le_total b b' with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have := cellDist_col_eq_zero 𝒰 a k b (fun y h1 h2 => hfree y (by omega) (by omega))
    rwa [← hk, add_sub_cancel] at this
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have := cellDist_col_eq_zero 𝒰 a k b' (fun y h1 h2 => hfree y (by omega) (by omega))
    rw [← hk, add_sub_cancel] at this
    have h2 := cellDist_symm_le 𝒰 (a, b') (a, b)
    rw [cellInd_of_not_mem (hfree b (by omega) (by omega)),
      cellInd_of_not_mem (hfree b' (by omega) (by omega))] at h2
    omega


/-! ## Walks inside one face of the wall -/

section Wall

variable {h : ℕ} (hh : 1 ≤ h) (he : Even h)
include hh he

/-- The cells off the wall of height `h`, by arithmetic. -/
theorem not_mem_fig1WallCells {c : ℤ × ℤ} (hc : ¬ IsWallCell h c) : c ∉ fig1WallCells h := by
  rwa [mem_fig1WallCells_iff hh he]

omit hh he in
theorem square_not_mem_fig1WallCells (x y : ℤ) : (2 * x + 1, 2 * y + 1) ∉ fig1WallCells h :=
  fun hc => fig1WallCells_not_square h _ hc
    ⟨show (2 * x + 1) % 2 = 1 by omega, show (2 * y + 1) % 2 = 1 by omega⟩

/-- The square of the outer face used as a base point. -/
def outBase : ℤ × ℤ := (-1, -1)

/-- The square in the middle of the brick `F`. -/
def brickSq (F : ℤ × ℤ) : ℤ × ℤ := (2 * F.1 + 1, 2 * F.2 + 1)

omit hh he in
theorem wallFace_brickSq {F : ℤ × ℤ} (hF : IsBrick h F) : wallFace h (brickSq F) = F := by
  unfold brickSq
  rw [wallFace_square]
  unfold IsBrick at hF
  have hp : (F.1 + F.2) % 2 = 0 := by omega
  rw [hp, add_zero]
  split_ifs with hc
  · rfl
  · exact absurd (by omega) hc

/-- Squares of the outer face are joined to `outBase` around the outside of the wall. -/
theorem cellDist_out_base {x y : ℤ} (hq : wallFace h (2 * x + 1, 2 * y + 1) = outFace) :
    cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) outBase = 0 := by
  rw [wallFace_square] at hq
  have hb : ¬ (0 ≤ y ∧ y < h ∧ 1 ≤ x + (x + y) % 2 ∧ x + (x + y) % 2 ≤ 2 * h) := by
    intro hb
    split_ifs at hq
    simp [outFace, Prod.ext_iff] at hq
    omega
  obtain ⟨k, hk⟩ := he
  set 𝒰 := fig1WallCells h
  have free : ∀ c : ℤ × ℤ, ¬ IsWallCell h c → c ∉ 𝒰 := fun c hc => not_mem_fig1WallCells hh ⟨k, hk⟩ hc
  -- a walk along row `b` to `(a', b)`, then along column `a'` to `(a', -1)`, then along row `-1`
  have route : ∀ a a' b : ℤ, (∀ t, min a a' ≤ t → t ≤ max a a' → ¬ IsWallCell h (t, b)) →
      (∀ t, min b (-1) ≤ t → t ≤ max b (-1) → ¬ IsWallCell h (a', t)) →
      (∀ t, min a' (-1) ≤ t → t ≤ max a' (-1) → ¬ IsWallCell h (t, -1)) →
      cellDist 𝒰 (a, b) outBase = 0 := by
    intro a a' b h1 h2 h3
    have e1 := cellDist_row_eq_zero' 𝒰 (b := b) (fun t ht1 ht2 => free _ (h1 t ht1 ht2))
    have e2 := cellDist_col_eq_zero' 𝒰 (a := a') (b := b) (b' := -1)
      (fun t ht1 ht2 => free _ (h2 t ht1 ht2))
    have e3 := cellDist_row_eq_zero' 𝒰 (a := a') (a' := -1) (b := -1)
      (fun t ht1 ht2 => free _ (h3 t ht1 ht2))
    have t1 := cellDist_triangle 𝒰 (a, b) (a', b) (a', -1)
    have t2 := cellDist_triangle 𝒰 (a, b) (a', -1) outBase
    unfold outBase at *
    omega
  by_cases hy : y < 0 ∨ h ≤ y
  · -- below or above the rows: along the row to `x = -1`, then down
    apply route _ (-1) _ <;> intro t ht1 ht2 <;> unfold IsWallCell <;> simp only <;> omega
  · by_cases hx : x < 0 ∨ 2 * h < x
    · -- left or right of the wall: along the column down to `-1`, then along row `-1`
      apply route _ (2 * x + 1) _ <;> intro t ht1 ht2 <;> unfold IsWallCell <;> simp only <;>
        omega
    · by_cases hx0 : x = 0
      · subst hx0
        apply route _ (-1) _ <;> intro t ht1 ht2 <;> unfold IsWallCell <;> simp only <;> omega
      · have hx2 : x = 2 * h := by omega
        subst hx2
        apply route _ (4 * h + 3) _ <;> intro t ht1 ht2 <;> unfold IsWallCell <;> simp only <;>
          omega

/-- A square of a brick is joined for free to the middle square of the brick: the two squares
of a brick are separated by a cell where the wall has no vertical edge. -/
theorem cellDist_brickSq {x y : ℤ} {F : ℤ × ℤ} (hq : wallFace h (2 * x + 1, 2 * y + 1) = F)
    (hF : IsBrick h F) : cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) (brickSq F) = 0 := by
  rw [wallFace_square] at hq
  split_ifs at hq with hb
  · subst hq
    unfold brickSq
    simp only
    obtain ⟨k, hk⟩ := he
    apply cellDist_row_eq_zero'
    intro t ht1 ht2
    apply not_mem_fig1WallCells hh ⟨k, hk⟩
    unfold IsWallCell
    simp only
    omega
  · exact absurd (hq ▸ hF) (not_isBrick_outFace h)


omit hh he in
theorem cellInd_le_one (𝒰 : Set (ℤ × ℤ)) (c : ℤ × ℤ) : cellInd 𝒰 c ≤ 1 := by
  unfold cellInd
  split_ifs <;> omega

omit hh he in
/-- Between two squares the cell distance is symmetric. -/
theorem cellDist_square_comm (x y x' y' : ℤ) :
    cellDist (fig1WallCells h) (2 * x' + 1, 2 * y' + 1) (2 * x + 1, 2 * y + 1) =
      cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x' + 1, 2 * y' + 1) := by
  have h1 := cellDist_symm_le (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x' + 1, 2 * y' + 1)
  have h2 := cellDist_symm_le (fig1WallCells h) (2 * x' + 1, 2 * y' + 1) (2 * x + 1, 2 * y + 1)
  rw [cellInd_of_not_mem (square_not_mem_fig1WallCells x y),
    cellInd_of_not_mem (square_not_mem_fig1WallCells x' y')] at h1 h2
  omega

omit hh he in
theorem outBase_eq : (outBase : ℤ × ℤ) = (2 * (-1) + 1, 2 * (-1) + 1) := rfl

omit hh he in
theorem brickSq_eq (F : ℤ × ℤ) : brickSq F = (2 * F.1 + 1, 2 * F.2 + 1) := rfl

/-- Two squares of the same face are at cell distance zero. -/
theorem cellDist_eq_zero_of_wallFace_eq {x y x' y' : ℤ}
    (heq : wallFace h (2 * x + 1, 2 * y + 1) = wallFace h (2 * x' + 1, 2 * y' + 1)) :
    cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x' + 1, 2 * y' + 1) = 0 := by
  rcases isBrick_or_eq_outFace_wallFace h (2 * x + 1, 2 * y + 1) with hb | ho
  · have h1 := cellDist_brickSq hh he rfl hb
    have h2 := cellDist_brickSq hh he heq.symm (heq ▸ hb)
    rw [brickSq_eq] at h1 h2
    rw [cellDist_square_comm] at h2
    have := cellDist_triangle (fig1WallCells h) (2 * x + 1, 2 * y + 1)
      (2 * (wallFace h (2 * x + 1, 2 * y + 1)).1 + 1, 2 * (wallFace h (2 * x + 1, 2 * y + 1)).2 + 1)
      (2 * x' + 1, 2 * y' + 1)
    omega
  · have h1 := cellDist_out_base hh he ho
    have h2 := cellDist_out_base hh he (heq ▸ ho)
    rw [outBase_eq] at h1 h2
    rw [cellDist_square_comm] at h2
    have := cellDist_triangle (fig1WallCells h) (2 * x + 1, 2 * y + 1)
      (2 * (-1) + 1, 2 * (-1) + 1) (2 * x' + 1, 2 * y' + 1)
    omega

omit hh he in
/-- Two squares above a common cell `m`, the second off the drawing, are at cell distance at most
one: the walk crosses `m`. -/
theorem cellDist_le_one_of_common {𝒰 : Set (ℤ × ℤ)} {q m q' : ℤ × ℤ} (hq : q ∈ squaresAbove m)
    (hq' : q' ∈ squaresAbove m) (hq'U : q' ∉ 𝒰) : cellDist 𝒰 q q' ≤ 1 := by
  have h1 := cellDist_le_of_cellRel 𝒰 (Or.inr hq.2 : CellRel q m)
  have h2 := cellDist_le_of_cellRel 𝒰 (Or.inl hq'.2 : CellRel m q')
  rw [cellInd_of_not_mem hq'U] at h2
  have h3 := cellInd_le_one 𝒰 m
  have := cellDist_triangle 𝒰 q m q'
  omega

omit hh he in
/-- Touching faces have squares above a common cell. -/
theorem exists_common_of_faceAdj {F G : ℤ × ℤ} (hFG : FaceAdj h F G) :
    ∃ x0 y0 x1 y1 : ℤ, ∃ m : ℤ × ℤ, wallFace h (2 * x0 + 1, 2 * y0 + 1) = F ∧
      wallFace h (2 * x1 + 1, 2 * y1 + 1) = G ∧ (2 * x0 + 1, 2 * y0 + 1) ∈ squaresAbove m ∧
      (2 * x1 + 1, 2 * y1 + 1) ∈ squaresAbove m := by
  -- the case of a brick `F` touching the outer face
  have hout : ∀ {F : ℤ × ℤ}, IsBrick h F → outDepth h F = 1 →
      ∃ x0 y0 x1 y1 : ℤ, ∃ m : ℤ × ℤ, wallFace h (2 * x0 + 1, 2 * y0 + 1) = F ∧
        wallFace h (2 * x1 + 1, 2 * y1 + 1) = outFace ∧
        (2 * x0 + 1, 2 * y0 + 1) ∈ squaresAbove m ∧ (2 * x1 + 1, 2 * y1 + 1) ∈ squaresAbove m := by
    intro F hF hd
    obtain ⟨X, y⟩ := F
    unfold IsBrick at hF
    unfold outDepth at hd
    simp only at hF hd
    have hc : y = 0 ∨ y = h - 1 ∨ X ≤ 2 ∨ 2 * h - 1 ≤ X := by omega
    rcases hc with hc | hc | hc | hc
    · refine ⟨X, y, X, y - 1, (2 * X + 1, 2 * y), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X, y, X, y + 1, (2 * X + 1, 2 * y + 2), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X - 1, y, X - 2, y, (2 * X - 2, 2 * y + 1), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X, y, X + 1, y, (2 * X + 2, 2 * y + 1), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
  rcases hFG with ⟨hF, hG, hd⟩ | ⟨rfl, hG, hd⟩ | ⟨rfl, hF, hd⟩
  · obtain ⟨X, y⟩ := F
    obtain ⟨X', y'⟩ := G
    unfold IsBrick at hF hG
    unfold hexDist at hd
    simp only at hF hG hd
    have hc : (X' = X + 2 ∧ y' = y) ∨ (X' = X - 2 ∧ y' = y) ∨ (X' = X + 1 ∧ y' = y + 1) ∨
        (X' = X - 1 ∧ y' = y + 1) ∨ (X' = X + 1 ∧ y' = y - 1) ∨ (X' = X - 1 ∧ y' = y - 1) := by
      omega
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      subst X' y'
    · refine ⟨X, y, X + 1, y, (2 * X + 2, 2 * y + 1), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X - 1, y, X - 2, y, (2 * X - 2, 2 * y + 1), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X, y, X, y + 1, (2 * X + 1, 2 * y + 2), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X - 1, y, X - 1, y + 1, (2 * X - 1, 2 * y + 2), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X, y, X, y - 1, (2 * X + 1, 2 * y), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
    · refine ⟨X - 1, y, X - 1, y - 1, (2 * X - 1, 2 * y), ?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [wallFace_square]; split_ifs <;> simp only [outFace, Prod.mk.injEq, and_true] <;> omega)
        | (rw [mem_squaresAbove_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega)
  · obtain ⟨x0, y0, x1, y1, m, h1, h2, h3, h4⟩ := hout hG hd
    exact ⟨x1, y1, x0, y0, m, h2, h1, h4, h3⟩
  · exact hout hF hd

/-- Squares of touching faces are at cell distance at most one. -/
theorem cellDist_le_one_of_faceAdj {x y x' y' : ℤ}
    (hFG : FaceAdj h (wallFace h (2 * x + 1, 2 * y + 1)) (wallFace h (2 * x' + 1, 2 * y' + 1))) :
    cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x' + 1, 2 * y' + 1) ≤ 1 := by
  obtain ⟨x0, y0, x1, y1, m, h1, h2, h3, h4⟩ := exists_common_of_faceAdj hFG
  have e1 := cellDist_eq_zero_of_wallFace_eq hh he h1.symm
  have e2 := cellDist_eq_zero_of_wallFace_eq hh he h2
  have e3 := cellDist_le_one_of_common h3 h4 (square_not_mem_fig1WallCells (h := h) x1 y1)
  have t1 := cellDist_triangle (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x0 + 1, 2 * y0 + 1)
    (2 * x1 + 1, 2 * y1 + 1)
  have t2 := cellDist_triangle (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x1 + 1, 2 * y1 + 1)
    (2 * x' + 1, 2 * y' + 1)
  omega


/-! ## Walks along the bricks -/

omit hh he in
/-- A brick has a touching brick one step nearer to any other brick. -/
theorem exists_hex_step {F G : ℤ × ℤ} (hF : IsBrick h F) (hG : IsBrick h G) (hne : F ≠ G) :
    ∃ F', IsBrick h F' ∧ hexDist F F' = 1 ∧ hexDist F' G + 1 ≤ hexDist F G := by
  obtain ⟨X, y⟩ := F
  obtain ⟨X', y'⟩ := G
  unfold IsBrick at hF hG
  simp only [ne_eq, Prod.mk.injEq] at hF hG hne
  have hc : y < y' ∨ y' < y ∨ y = y' := by omega
  rcases hc with hc | hc | hc
  · by_cases h1 : X < X'
    · exact ⟨(X + 1, y + 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    by_cases h2 : X' < X
    · exact ⟨(X - 1, y + 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    by_cases h3 : X < 2 * h
    · exact ⟨(X + 1, y + 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    · exact ⟨(X - 1, y + 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
  · by_cases h1 : X < X'
    · exact ⟨(X + 1, y - 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    by_cases h2 : X' < X
    · exact ⟨(X - 1, y - 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    by_cases h3 : X < 2 * h
    · exact ⟨(X + 1, y - 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    · exact ⟨(X - 1, y - 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
  · by_cases h1 : X < X'
    · exact ⟨(X + 2, y), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩
    · exact ⟨(X - 2, y), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by unfold hexDist; simp only; omega⟩

omit hh he in
/-- A brick that does not touch the outer face has a touching brick one step nearer to it. -/
theorem exists_out_step {F : ℤ × ℤ} (hF : IsBrick h F) (h2 : 2 ≤ outDepth h F) :
    ∃ F', IsBrick h F' ∧ hexDist F F' = 1 ∧ outDepth h F' + 1 ≤ outDepth h F := by
  obtain ⟨X, y⟩ := F
  unfold IsBrick at hF
  unfold outDepth at h2 ⊢
  simp only at hF h2 ⊢
  have hc : 2 ≤ y + 1 ∧ min (min (y + 1) (h - y)) (min ((X + 1) / 2) ((2 * h + 2 - X) / 2)) = y + 1 ∨
      min (min (y + 1) (h - y)) (min ((X + 1) / 2) ((2 * h + 2 - X) / 2)) = h - y ∨
      min (min (y + 1) (h - y)) (min ((X + 1) / 2) ((2 * h + 2 - X) / 2)) = (X + 1) / 2 ∨
      min (min (y + 1) (h - y)) (min ((X + 1) / 2) ((2 * h + 2 - X) / 2)) =
        (2 * h + 2 - X) / 2 := by omega
  rcases hc with ⟨-, hc⟩ | hc | hc | hc <;> rw [hc] at h2 ⊢
  · by_cases h3 : X < 2 * h
    · exact ⟨(X + 1, y - 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by simp only; omega⟩
    · exact ⟨(X - 1, y - 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by simp only; omega⟩
  · by_cases h3 : X < 2 * h
    · exact ⟨(X + 1, y + 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by simp only; omega⟩
    · exact ⟨(X - 1, y + 1), by unfold IsBrick; simp only; omega,
        by unfold hexDist; simp only; omega, by simp only; omega⟩
  · exact ⟨(X - 2, y), by unfold IsBrick; simp only; omega,
      by unfold hexDist; simp only; omega, by simp only; omega⟩
  · exact ⟨(X + 2, y), by unfold IsBrick; simp only; omega,
      by unfold hexDist; simp only; omega, by simp only; omega⟩

/-- Two touching bricks have their middle squares at cell distance at most one. -/
theorem cellDist_brickSq_le_one {F F' : ℤ × ℤ} (hF : IsBrick h F) (hF' : IsBrick h F')
    (hd : hexDist F F' = 1) : cellDist (fig1WallCells h) (brickSq F) (brickSq F') ≤ 1 := by
  have hadj : FaceAdj h F F' := Or.inl ⟨hF, hF', hd⟩
  rw [← wallFace_brickSq hF, ← wallFace_brickSq hF'] at hadj
  exact cellDist_le_one_of_faceAdj hh he hadj

/-- Along the bricks, the cell distance between middle squares is at most the step count. -/
theorem cellDist_brickSq_le_hexDist :
    ∀ n : ℕ, ∀ F G : ℤ × ℤ, IsBrick h F → IsBrick h G → hexDist F G ≤ n →
      cellDist (fig1WallCells h) (brickSq F) (brickSq G) ≤ n
  | 0, F, G, hF, hG, hd => by
    have hFG : F = G := by
      unfold IsBrick at hF hG
      unfold hexDist at hd
      exact Prod.ext (by omega) (by omega)
    subst hFG
    simp [cellDist_self]
  | n + 1, F, G, hF, hG, hd => by
    by_cases hFG : F = G
    · subst hFG
      simp [cellDist_self]
    obtain ⟨F', hF', h1, h2⟩ := exists_hex_step hF hG hFG
    have e1 := cellDist_brickSq_le_one hh he hF hF' h1
    have e2 := cellDist_brickSq_le_hexDist n F' G hF' hG (by push_cast at hd; omega)
    have := cellDist_triangle (fig1WallCells h) (brickSq F) (brickSq F') (brickSq G)
    omega

omit hh he in
theorem wallFace_outBase : wallFace h outBase = outFace := by
  rw [outBase_eq, wallFace_square]
  split_ifs with hc
  · omega
  · rfl

/-- The cell distance from the middle square of a brick to `outBase` is at most the step count
to the outer face. -/
theorem cellDist_brickSq_out_le :
    ∀ n : ℕ, ∀ F : ℤ × ℤ, IsBrick h F → outDepth h F ≤ n →
      cellDist (fig1WallCells h) (brickSq F) outBase ≤ n
  | 0, F, hF, hd => by
    have := one_le_outDepth hF
    omega
  | n + 1, F, hF, hd => by
    by_cases h1 : outDepth h F = 1
    · have hadj : FaceAdj h F outFace := Or.inr (Or.inr ⟨rfl, hF, h1⟩)
      rw [← wallFace_brickSq hF, ← wallFace_outBase (h := h)] at hadj
      rw [brickSq_eq, outBase_eq] at hadj ⊢
      have := cellDist_le_one_of_faceAdj hh he hadj
      omega
    · have h2 := one_le_outDepth hF
      obtain ⟨F', hF', e1, e2⟩ := exists_out_step hF (by omega)
      have e3 := cellDist_brickSq_le_one hh he hF hF' e1
      have e4 := cellDist_brickSq_out_le n F' hF' (by push_cast at hd; omega)
      have := cellDist_triangle (fig1WallCells h) (brickSq F) (brickSq F') outBase
      omega

/-- **Cell distance against face distance.** Two squares are at cell distance at most the face
distance between their faces. -/
theorem cellDist_le_faceDist (x y x' y' : ℤ) :
    (cellDist (fig1WallCells h) (2 * x + 1, 2 * y + 1) (2 * x' + 1, 2 * y' + 1) : ℤ) ≤
      faceDist h (wallFace h (2 * x + 1, 2 * y + 1)) (wallFace h (2 * x' + 1, 2 * y' + 1)) := by
  have hne : ∀ {K : ℤ × ℤ}, IsBrick h K → K ≠ outFace :=
    fun hb hk => not_isBrick_outFace h (hk ▸ hb)
  -- distances from a square to the middle square of its face, and to `outBase`
  have toSq : ∀ {a b : ℤ}, IsBrick h (wallFace h (2 * a + 1, 2 * b + 1)) →
      cellDist (fig1WallCells h) (2 * a + 1, 2 * b + 1) (brickSq (wallFace h (2 * a + 1, 2 * b + 1))) = 0 ∧
      cellDist (fig1WallCells h) (brickSq (wallFace h (2 * a + 1, 2 * b + 1))) (2 * a + 1, 2 * b + 1) = 0 := by
    intro a b hb
    have h1 := cellDist_brickSq hh he rfl hb
    refine ⟨h1, ?_⟩
    rw [brickSq_eq] at h1 ⊢
    rw [cellDist_square_comm] at h1 ⊢
    rw [cellDist_square_comm]
    exact h1
  have toBase : ∀ {a b : ℤ}, wallFace h (2 * a + 1, 2 * b + 1) = outFace →
      cellDist (fig1WallCells h) (2 * a + 1, 2 * b + 1) outBase = 0 ∧
      cellDist (fig1WallCells h) outBase (2 * a + 1, 2 * b + 1) = 0 := by
    intro a b hb
    have h1 := cellDist_out_base hh he hb
    refine ⟨h1, ?_⟩
    rw [outBase_eq] at h1 ⊢
    rw [cellDist_square_comm]
    exact h1
  have sqBase : ∀ {F : ℤ × ℤ}, IsBrick h F →
      (cellDist (fig1WallCells h) (brickSq F) outBase : ℤ) ≤ outDepth h F ∧
      (cellDist (fig1WallCells h) outBase (brickSq F) : ℤ) ≤ outDepth h F := by
    intro F hF
    have h0 := one_le_outDepth hF
    have h1 := cellDist_brickSq_out_le hh he (outDepth h F).toNat F hF (by omega)
    have h2 : cellDist (fig1WallCells h) outBase (brickSq F) = cellDist (fig1WallCells h) (brickSq F) outBase := by
      rw [outBase_eq, brickSq_eq, cellDist_square_comm]
    rw [h2]
    constructor <;> omega
  have t := fun a b c => cellDist_triangle (fig1WallCells h) a b c
  rcases isBrick_or_eq_outFace_wallFace h (2 * x + 1, 2 * y + 1) with hb | ho <;>
    rcases isBrick_or_eq_outFace_wallFace h (2 * x' + 1, 2 * y' + 1) with hb' | ho'
  · rw [faceDist_of_ne (hne hb) (hne hb')]
    have a1 := (toSq hb).1
    have a2 := (toSq hb').2
    have a3 := cellDist_brickSq_le_hexDist hh he (hexDist (wallFace h (2 * x + 1, 2 * y + 1)) (wallFace h (2 * x' + 1, 2 * y' + 1))).toNat
      _ _ hb hb' (by omega)
    have a4 := (sqBase hb).1
    have a5 := (sqBase hb').2
    have b1 := t (2 * x + 1, 2 * y + 1) (brickSq (wallFace h (2 * x + 1, 2 * y + 1))) (2 * x' + 1, 2 * y' + 1)
    have b2 := t (brickSq (wallFace h (2 * x + 1, 2 * y + 1))) (brickSq (wallFace h (2 * x' + 1, 2 * y' + 1))) (2 * x' + 1, 2 * y' + 1)
    have b3 := t (brickSq (wallFace h (2 * x + 1, 2 * y + 1))) outBase (2 * x' + 1, 2 * y' + 1)
    have b4 := t outBase (brickSq (wallFace h (2 * x' + 1, 2 * y' + 1))) (2 * x' + 1, 2 * y' + 1)
    have := hexDist_nonneg (wallFace h (2 * x + 1, 2 * y + 1)) (wallFace h (2 * x' + 1, 2 * y' + 1))
    rw [le_min_iff]
    constructor <;> omega
  · rw [ho', faceDist_out_right (hne hb)]
    have a1 := (toSq hb).1
    have a4 := (sqBase hb).1
    have a5 := (toBase ho').2
    have b1 := t (2 * x + 1, 2 * y + 1) (brickSq (wallFace h (2 * x + 1, 2 * y + 1))) (2 * x' + 1, 2 * y' + 1)
    have b3 := t (brickSq (wallFace h (2 * x + 1, 2 * y + 1))) outBase (2 * x' + 1, 2 * y' + 1)
    omega
  · rw [ho, faceDist_out_left (hne hb')]
    have a1 := (toBase ho).1
    have a4 := (sqBase hb').2
    have a5 := (toSq hb').2
    have b1 := t (2 * x + 1, 2 * y + 1) outBase (2 * x' + 1, 2 * y' + 1)
    have b3 := t outBase (brickSq (wallFace h (2 * x' + 1, 2 * y' + 1))) (2 * x' + 1, 2 * y' + 1)
    omega
  · rw [ho, ho', faceDist_out_out]
    have := cellDist_eq_zero_of_wallFace_eq hh he (ho.trans ho'.symm)
    omega

/-- **Upper bound for the wall of Fig. 1.** For points `s, t` in different cells, and any faces
`F` at `s` and `G` at `t`, `d(s, t) ≤ [s] + [t] + D(F, G)`. -/
theorem planeWallDist_fig1_le {s t : ℝ × ℝ} (hst : cellCode s ≠ cellCode t) {q q' : ℤ × ℤ}
    (hq : q ∈ squaresAbove (cellCode s)) (hq' : q' ∈ squaresAbove (cellCode t)) :
    (planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h)) (fig1PlaneEquiv s)
        (fig1PlaneEquiv t) : ℤ) ≤
      cellInd (fig1WallCells h) (cellCode s) + cellInd (fig1WallCells h) (cellCode t) +
        faceDist h (wallFace h q) (wallFace h q') := by
  have h1 := planeWallDist_cellSet_le_cellDist (fig1WallCells_not_square h) hst
  obtain ⟨x, y, rfl, -⟩ := exists_of_mem_squaresAbove hq
  obtain ⟨x', y', rfl, -⟩ := exists_of_mem_squaresAbove hq'
  have h2 := cellDist_le_of_cellRel (fig1WallCells h) (Or.inl hq.2 : CellRel (cellCode s) (2 * x + 1, 2 * y + 1))
  have h3 := cellDist_le_of_cellRel (fig1WallCells h)
    (Or.inr hq'.2 : CellRel (2 * x' + 1, 2 * y' + 1) (cellCode t))
  rw [cellInd_of_not_mem (square_not_mem_fig1WallCells x y)] at h2
  have h4 := cellDist_le_faceDist hh he x y x' y'
  have t1 := cellDist_triangle (fig1WallCells h) (cellCode s) (2 * x + 1, 2 * y + 1) (2 * x' + 1, 2 * y' + 1)
  have t2 := cellDist_triangle (fig1WallCells h) (cellCode s) (2 * x' + 1, 2 * y' + 1) (cellCode t)
  omega

end Wall

end GraphMinor.GM13
