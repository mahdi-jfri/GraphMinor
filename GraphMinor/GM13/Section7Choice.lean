module

public import GraphMinor.GM13.Section7HoleDepthTest
public import GraphMinor.GM13.Section7Rotate
public import GraphMinor.GM13.Section7RayHole

/-!
# Graph Minors XIII, (7.3): a shape for each element

For (7.3) with `r = 0` we must remove a given vertex `v` of the wall. This file shows that every
element of the wall of Fig. 1 of height `h' + 2` (with `h'` even and positive) is deleted by some
shape that passes the depth test (`exists_deleting_shape`). So the new wall has `d' ≥ d - 4` and
does not contain `v`.

The shapes are the moved subwalls `T(1, 1)` and `T(3, 1)`, which delete the elements near the
sides of the wall, the hole `Hole(Y0, c0)`, and the hole turned by 180 degrees. An element away
from the sides is deleted by a hole whose band or cut passes through it. The hole must have good
parameters (`Hole.Good`): its cut must lie near the left side when `Y0` is even and far from it
when `Y0` is odd. An element in the lower part of the wall can always be reached by such a hole;
an element in the upper part is reached by the turned hole, which works from the top. For each
kind of element (vertex, horizontal edge, vertical edge) and each parity class we try two or three
holes in a fixed order; one of them has good parameters, and it deletes the element. This rule
was found and tested by computer for all heights up to 30.
-/

public section

namespace GraphMinor.GM13

open Set

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

theorem good_iff : Good h' Y0 c0 ↔ 1 ≤ Y0 ∧ Y0 ≤ h' ∧ 1 ≤ c0 ∧ c0 ≤ 2 * h' + 1 ∧
    (Y0 % 2 = 0 → c0 ≤ 2 * h' + 2 - 2 * Y0) ∧ (Y0 % 2 = 1 → 2 * Y0 ≤ c0) := by
  constructor
  · rintro ⟨⟨Y1, Y2, c1, c2⟩, ge, go⟩
    exact ⟨Y1, Y2, c1, c2, ge, go⟩
  · rintro ⟨Y1, Y2, c1, c2, ge, go⟩
    exact ⟨⟨Y1, Y2, c1, c2⟩, ge, go⟩

/-- A hole with good parameters that deletes `m`. -/
theorem choice_hole (hh' : 1 ≤ h') (he' : Even h') {m : ℤ × ℤ} (hg : Good h' Y0 c0)
    (hd : ¬ IsWallCell h' (cell Y0 c0 m)) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own m = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono :=
  ⟨shape hg.toParams hh' he', depthTest hg hh' he', by rw [shape_own]; exact own_none hd,
    ⟨realization hg.toParams hh' he', rayOK hg.toParams hh' he', rowMono hg.toParams hh' he'⟩⟩

/-- A turned hole with good parameters that deletes `m`. -/
theorem choice_rot (hh' : 1 ≤ h') (he' : Even h') {m : ℤ × ℤ} (hg : Good h' Y0 c0)
    (hd : ¬ IsWallCell h' (cell Y0 c0 (rotC (h' + 2) m))) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own m = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  refine ⟨(shape hg.toParams hh' he').rotate (by omega) (even_succ_succ he') hh' he',
    (depthTest hg hh' he').rotate (by omega) (even_succ_succ he') hh' he', ?_,
    ⟨(realization hg.toParams hh' he').rotate (by omega) (even_succ_succ he') hh' he',
      Shape.Realization.rayOK_rotate _ _ _ _ _ (rayOK hg.toParams hh' he'),
      Shape.Realization.rowMono_rotate _ _ _ _ _ (rowMono hg.toParams hh' he')⟩⟩
  change ((shape hg.toParams hh' he').own (rotC (h' + 2) m)).map (rotC h') = none
  rw [shape_own, own_none hd, Option.map_none]

end Hole

/-- A moved subwall `T(i, 1)` that deletes `m`. -/
theorem choice_trans {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {i : ℕ} (hi : i = 1 ∨ i = 3)
    {m c : ℤ × ℤ} (hc : c = (m.1 - 2 * (i : ℤ), m.2 - 2 * 1)) (hd : ¬ IsWallCell h' c) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own m = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  refine ⟨transShape1 h' hh' he' (i := (i : ℤ)) (by omega),
    transShape1_depthTest h' hh' he' (i := (i : ℤ)) (by omega), ?_,
    ⟨transRealization h' hh' he' hi,
      Shape.Realization.rayOK_of_trans _ (by omega) (Hole.even_succ_succ he') hh' he' (j := 1)
        (fun _ => rfl) (fun _ => rfl),
      Shape.Realization.rowMono_of_trans _ (j := 1) (fun _ => rfl)⟩⟩
  change transOwn h' i 1 m = none
  unfold transOwn
  rw [ite_eq_right (hc ▸ hd)]

theorem rotC_vertex (h : ℕ) (x y : ℤ) :
    rotC h (2 * x, 2 * y) = (2 * (2 * h + 1 - x), 2 * (h - y)) := by
  unfold rotC; ext <;> simp only <;> ring

theorem rotC_horiz (h : ℕ) (x y : ℤ) :
    rotC h (2 * x + 1, 2 * y) = (2 * (2 * h - x) + 1, 2 * (h - y)) := by
  unfold rotC; ext <;> simp only <;> ring

theorem rotC_vert (h : ℕ) (x y : ℤ) :
    rotC h (2 * x, 2 * y + 1) = (2 * (2 * h + 1 - x), 2 * (h - 1 - y) + 1) := by
  unfold rotC; ext <;> simp only <;> ring

/-- Shows that the hole with the given parameters deletes the element, by the cases of the cell
formula. -/
macro "cdel_tac" : tactic => `(tactic| (
  simp only [rotC_vertex, rotC_horiz, rotC_vert, Hole.cell_vertex, Hole.cell_horiz,
    Hole.cell_vert, Hole.vertexCell, Hole.horizCell, Hole.vertCell]
  split_ifs <;> simp only [isWallCell_vertex_iff, isWallCell_horiz_iff, isWallCell_vert_iff,
    Hole.not_isWallCell_odd_odd, not_false_eq_true, not_and, not_or] <;> omega))

set_option hygiene false in
/-- Uses the hole `Hole(Y0, c0)` if its parameters are good. -/
macro "try_hole " Y0:term:max c0:term:max : tactic => `(tactic| (
  by_cases g : Hole.Good h' $Y0 $c0
  · exact Hole.choice_hole hh' he' g (by rw [Hole.good_iff] at g; cdel_tac)
  rw [Hole.good_iff] at g))

set_option hygiene false in
/-- Uses the turned hole `Hole(Y0, c0)` if its parameters are good. -/
macro "try_rot " Y0:term:max c0:term:max : tactic => `(tactic| (
  by_cases g : Hole.Good h' $Y0 $c0
  · exact Hole.choice_rot hh' he' g (by rw [Hole.good_iff] at g; cdel_tac)
  rw [Hole.good_iff] at g))

set_option hygiene false in
/-- Uses the hole `Hole(Y0, c0)`, whose parameters are good by the failed tries. -/
macro "last_hole " Y0:term:max c0:term:max : tactic => `(tactic| (
  have g : Hole.Good h' $Y0 $c0 := Hole.good_iff.mpr (by omega)
  exact Hole.choice_hole hh' he' g (by rw [Hole.good_iff] at g; cdel_tac)))

set_option hygiene false in
/-- Uses the turned hole `Hole(Y0, c0)`, whose parameters are good by the failed tries. -/
macro "last_rot " Y0:term:max c0:term:max : tactic => `(tactic| (
  have g : Hole.Good h' $Y0 $c0 := Hole.good_iff.mpr (by omega)
  exact Hole.choice_rot hh' he' g (by rw [Hole.good_iff] at g; cdel_tac)))

variable {h' : ℕ}

theorem choice_vertex (hh' : 1 ≤ h') (he' : Even h') {x y : ℤ}
    (t1 : IsWallCell h' (2 * (x - 1), 2 * (y - 1)))
    (t3 : IsWallCell h' (2 * (x - 3), 2 * (y - 1))) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own (2 * x, 2 * y) = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  rw [isWallCell_vertex_iff] at t1 t3
  obtain ⟨k, hk⟩ := he'
  have he' : Even h' := ⟨k, hk⟩
  rcases Int.emod_two_eq_zero_or_one (x + y) with p | p <;>
  rcases Int.emod_two_eq_zero_or_one y with q | q
  · try_hole (y - 1) (x - 1)
    try_hole y (x - 2)
    last_rot (h' + 2 - y) (2 * h' + 5 - x - 1)
  · try_rot (h' + 2 - y) (2 * h' + 5 - x - 1)
    last_hole y x
  · try_rot (h' + 2 - y - 1) (2 * h' + 5 - x - 1)
    try_hole y (x - 1)
    last_rot (h' + 2 - y) (2 * h' + 5 - x - 2)
  · try_hole y (x - 1)
    last_rot (h' + 2 - y) (2 * h' + 5 - x)

theorem choice_horiz (hh' : 1 ≤ h') (he' : Even h') {x y : ℤ}
    (t1 : IsWallCell h' (2 * (x - 1) + 1, 2 * (y - 1)))
    (t3 : IsWallCell h' (2 * (x - 3) + 1, 2 * (y - 1))) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own (2 * x + 1, 2 * y) = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  rw [isWallCell_horiz_iff] at t1 t3
  obtain ⟨k, hk⟩ := he'
  have he' : Even h' := ⟨k, hk⟩
  rcases Int.emod_two_eq_zero_or_one (x + y) with p | p <;>
  rcases Int.emod_two_eq_zero_or_one y with q | q
  · try_hole (y - 1) (x - 1)
    last_rot (h' + 2 - y - 1) (2 * h' + 4 - x - 1)
  · try_hole y x
    last_rot (h' + 2 - y) (2 * h' + 4 - x)
  · try_hole (y - 1) x
    last_rot (h' + 2 - y - 1) (2 * h' + 4 - x)
  · try_hole y (x + 1)
    last_rot (h' + 2 - y) (2 * h' + 4 - x + 1)

theorem choice_vert (hh' : 1 ≤ h') (he' : Even h') {x y : ℤ}
    (hm : IsWallCell (h' + 2) (2 * x, 2 * y + 1)) (t1 : IsWallCell h' (2 * (x - 1), 2 * (y - 1) + 1))
    (t3 : IsWallCell h' (2 * (x - 3), 2 * (y - 1) + 1)) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own (2 * x, 2 * y + 1) = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  rw [isWallCell_vert_iff] at hm t1 t3
  obtain ⟨k, hk⟩ := he'
  have he' : Even h' := ⟨k, hk⟩
  rcases Int.emod_two_eq_zero_or_one y with q | q
  · try_rot (h' + 1 - y) (2 * h' + 5 - x - 1)
    last_hole (y + 1) x
  · try_hole y (x - 1)
    last_rot (h' + 1 - y + 1) (2 * h' + 5 - x)

/-- **Every element is deleted by a shape that passes the depth test.** -/
theorem exists_deleting_shape (hh' : 1 ≤ h') (he' : Even h') {m : ℤ × ℤ}
    (hm : m ∈ fig1WallCells (h' + 2)) :
    ∃ τ : Shape (h' + 2) h', τ.DepthTest ∧ τ.own m = none ∧
      ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  rw [mem_fig1WallCells_iff (by omega) (Hole.even_succ_succ he')] at hm
  rcases Hole.cell_cases hm with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · by_cases t1 : IsWallCell h' (2 * (x - 1), 2 * (y - 1))
    · by_cases t3 : IsWallCell h' (2 * (x - 3), 2 * (y - 1))
      · exact choice_vertex hh' he' t1 t3
      · exact choice_trans hh' he' (i := 3) (Or.inr rfl) (by ext <;> simp only <;> push_cast <;> ring) t3
    · exact choice_trans hh' he' (i := 1) (Or.inl rfl) (by ext <;> simp only <;> push_cast <;> ring) t1
  · by_cases t1 : IsWallCell h' (2 * (x - 1) + 1, 2 * (y - 1))
    · by_cases t3 : IsWallCell h' (2 * (x - 3) + 1, 2 * (y - 1))
      · exact choice_horiz hh' he' t1 t3
      · exact choice_trans hh' he' (i := 3) (Or.inr rfl) (by ext <;> simp only <;> push_cast <;> ring) t3
    · exact choice_trans hh' he' (i := 1) (Or.inl rfl) (by ext <;> simp only <;> push_cast <;> ring) t1
  · by_cases t1 : IsWallCell h' (2 * (x - 1), 2 * (y - 1) + 1)
    · by_cases t3 : IsWallCell h' (2 * (x - 3), 2 * (y - 1) + 1)
      · exact choice_vert hh' he' hm t1 t3
      · exact choice_trans hh' he' (i := 3) (Or.inr rfl) (by ext <;> simp only <;> push_cast <;> ring) t3
    · exact choice_trans hh' he' (i := 1) (Or.inl rfl) (by ext <;> simp only <;> push_cast <;> ring) t1

end GraphMinor.GM13
