module

public import GraphMinor.GM13.Section7HexHoleDepth
public import GraphMinor.GM13.Section7RealizePaths

/-!
# Graph Minors XIII, (7.3): the paths of the hexagonal hole

This file gives the old path of each new edge for the hexagonal hole, as a function with a
length (`HexHole.path`, `HexHole.pathLen`), and checks each step and each inner vertex against
`HexHole.own`. The covering of all kept elements and the realization itself are in
`Section7HexHoleRealize.lean`.

The old vertex of the new vertex `(x, y)` is `(x + sL, y)` left of the cut and `(x + sL + 2b, y)`
right of it, moved up by `2b` from row `Y0` on (`HexHole.vmap`). A horizontal edge runs along its
row; across the cut it has `2b + 1` old edges. A vertical edge is one old edge, except from row
`Y0 - 1` to row `Y0`: there it is a staircase of `4b + 1` old edges. After `2t` of them it is
`min t (2b - t)` columns away from its start, to the left of the cut it moves left and to the
right it moves right (`HexHole.stair_path`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- The old vertex of the new vertex `p`, with `s = sL` as a natural number. -/
def vmap (b : ℕ) (Y0 c0 : ℤ) (s : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (if (p.1 : ℤ) < c0 then p.1 + s else p.1 + s + 2 * b,
    if (p.2 : ℤ) < Y0 then p.2 else p.2 + 2 * b)

/-- The number of old edges on the path of the new edge `pq` (going right or up). -/
def pathLen (b : ℕ) (Y0 c0 : ℤ) (s : ℕ) (p q : ℕ × ℕ) : ℕ :=
  if p.2 = q.2 then (vmap b Y0 c0 s q).1 - (vmap b Y0 c0 s p).1
  else 2 * ((vmap b Y0 c0 s q).2 - (vmap b Y0 c0 s p).2) - 1

/-- The `j`-th vertex of the old path of the new edge `pq` (going right or up). A horizontal edge
runs along its row. A vertical edge goes up, and from row `Y0 - 1` it is a staircase: after `2t`
steps it is `min t (2b - t)` columns away from its start, to the left of the cut it moves left. -/
def path (b : ℕ) (Y0 c0 : ℤ) (s : ℕ) (p q : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  if p.2 = q.2 then ((vmap b Y0 c0 s p).1 + j, (vmap b Y0 c0 s p).2)
  else
    (if (p.1 : ℤ) < c0 then
        (vmap b Y0 c0 s p).1 -
          min (j / 2) (((vmap b Y0 c0 s q).2 - (vmap b Y0 c0 s p).2 - 1) - j / 2)
      else (vmap b Y0 c0 s p).1 +
          min (j / 2) (((vmap b Y0 c0 s q).2 - (vmap b Y0 c0 s p).2 - 1) - j / 2),
      (vmap b Y0 c0 s p).2 + (j + 1) / 2)

theorem vmap_mem (hp : Params h' b Y0 c0 sL) {s : ℕ} (hs : (s : ℤ) = sL) {p : ℕ × ℕ}
    (hp' : p ∈ elementaryWallVerts h') : vmap b Y0 c0 s p ∈ elementaryWallVerts (h' + 2 * b + 2) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have h3' : ¬ (x = 0 ∧ y = 0) := fun e => h3 (Prod.ext e.1 e.2)
  have h4' : ¬ (x = 2 * h' + 1 ∧ y = h') := fun e => h4 (Prod.ext e.1 e.2)
  dsimp only at h1 h2
  simp only [vmap]
  split_ifs <;> refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    intro e <;> (try simp only [Prod.mk.injEq] at e) <;> omega

theorem own_eq_eCell (he' : Even h') {m : ℤ × ℤ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hc : cell b Y0 c0 sL m = eCell p q) : own h' b Y0 c0 sL m = some (eCell p q) := by
  unfold own
  rw [hc]
  simp only [isWallCell_eCell he' hpq, ↓reduceIte]

theorem own_eq_vCell {m : ℤ × ℤ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h')
    (hc : cell b Y0 c0 sL m = vCell p) : own h' b Y0 c0 sL m = some (vCell p) := by
  unfold own
  rw [hc]
  simp only [isWallCell_vCell hp, ↓reduceIte]

theorem cell_vCell (u : ℕ × ℕ) : cell b Y0 c0 sL (vCell u) = vertexCell b Y0 c0 sL u.1 u.2 :=
  cell_vertex _ _ _ _ _ _

theorem cell_eCell_h {u w : ℕ × ℕ} (h1 : w.1 = u.1 + 1) (h2 : w.2 = u.2) :
    cell b Y0 c0 sL (eCell u w) = horizCell b Y0 c0 sL u.1 u.2 := by
  rw [← cell_horiz]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

theorem cell_eCell_v {u w : ℕ × ℕ} (h1 : w.1 = u.1) (h2 : w.2 = u.2 + 1) :
    cell b Y0 c0 sL (eCell u w) = vertCell b Y0 c0 sL u.1 u.2 := by
  rw [← cell_vert]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

theorem cell_eCell_h' {u w : ℕ × ℕ} (h1 : u.1 = w.1 + 1) (h2 : w.2 = u.2) :
    cell b Y0 c0 sL (eCell u w) = horizCell b Y0 c0 sL w.1 u.2 := by
  rw [← cell_horiz]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

theorem own_vmap (hp : Params h' b Y0 c0 sL) {s : ℕ} (hs : (s : ℤ) = sL) {p : ℕ × ℕ}
    (hp' : p ∈ elementaryWallVerts h') :
    own h' b Y0 c0 sL (vCell (vmap b Y0 c0 s p)) = some (vCell p) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  apply own_eq_vCell hp'
  rw [cell_vCell]
  obtain ⟨x, y⟩ := p
  simp only [vmap, vertexCell, vCell]
  split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> push_cast at * <;> omega

/-- The path of a horizontal edge: its edges and inner vertices go to the edge. -/
theorem horiz_ok (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL)
    {a y : ℕ} (hpq : elementaryWallAdj h' (a, y) (a + 1, y)) :
    (∀ j < pathLen b Y0 c0 s (a, y) (a + 1, y),
      own h' b Y0 c0 sL (eCell (path b Y0 c0 s (a, y) (a + 1, y) j)
        (path b Y0 c0 s (a, y) (a + 1, y) (j + 1))) = some (eCell (a, y) (a + 1, y))) ∧
    (∀ j, 1 ≤ j → j < pathLen b Y0 c0 s (a, y) (a + 1, y) →
      own h' b Y0 c0 sL (vCell (path b Y0 c0 s (a, y) (a + 1, y) j)) =
        some (eCell (a, y) (a + 1, y))) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  simp only [pathLen, path, if_true]
  constructor
  · intro j hj
    apply own_eq_eCell he' hpq
    rw [cell_eCell_h (by simp only; omega) (by simp only)]
    simp only [vmap, horizCell, eCell] at hj ⊢
    split_ifs at hj ⊢ <;> simp only [Prod.mk.injEq, and_true, true_and] <;> push_cast at * <;> omega
  · intro j hj1 hj
    apply own_eq_eCell he' hpq
    have ha : (a : ℤ) < c0 ∧ ¬ ((a + 1 : ℕ) : ℤ) < c0 := by
      simp only [vmap] at hj; split_ifs at hj <;> push_cast at * <;> omega
    have hj' : j < 2 * b + 1 := by
      simp only [vmap, if_pos ha.1, if_neg ha.2] at hj; omega
    clear hj
    rw [cell_vCell]
    simp only [vmap, if_pos ha.1]
    unfold vertexCell
    by_cases hy : (y : ℤ) < Y0
    · simp only [if_pos hy]
      push_cast
      simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, eCell, Prod.mk.injEq]
      omega
    · simp only [if_neg hy]
      push_cast
      simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, eCell, Prod.mk.injEq]
      omega

/-- The path of a vertical edge that does not start on row `Y0 - 1` is one old edge. -/
theorem vert_simple (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL)
    {a y : ℕ} (hpq : elementaryWallAdj h' (a, y) (a, y + 1)) (hY : (y : ℤ) + 1 ≠ Y0) :
    pathLen b Y0 c0 s (a, y) (a, y + 1) = 1 ∧
    own h' b Y0 c0 sL (eCell (path b Y0 c0 s (a, y) (a, y + 1) 0)
        (path b Y0 c0 s (a, y) (a, y + 1) 1)) = some (eCell (a, y) (a, y + 1)) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  have hne : y ≠ y + 1 := by omega
  constructor
  · simp only [pathLen, if_neg hne, vmap]
    split_ifs <;> push_cast at * <;> omega
  · apply own_eq_eCell he' hpq
    have e1 : path b Y0 c0 s (a, y) (a, y + 1) 0 = vmap b Y0 c0 s (a, y) := by
      simp only [path, if_neg hne]; split_ifs <;> simp
    have e2 : path b Y0 c0 s (a, y) (a, y + 1) 1 =
        ((vmap b Y0 c0 s (a, y)).1, (vmap b Y0 c0 s (a, y)).2 + 1) := by
      simp only [path, if_neg hne, vmap]; split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
    rw [e1, e2, cell_eCell_v (by simp only) (by simp only)]
    simp only [vmap, vertCell, eCell]
    split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> push_cast at * <;> omega

theorem cell_eCell_hx {u w : ℕ × ℕ} {x : ℤ} (h1 : w.1 = u.1 + 1 ∨ u.1 = w.1 + 1)
    (h2 : w.2 = u.2) (hx : x = min (u.1 : ℤ) (w.1 : ℤ)) :
    cell b Y0 c0 sL (eCell u w) = horizCell b Y0 c0 sL x u.2 := by
  rw [← cell_horiz]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

/-- The staircase of the new vertical edge from `(a, Y0 - 1)` to `(a, Y0)`. -/
theorem stair_path {s : ℕ} {a y : ℕ} (hY : (y : ℤ) + 1 = Y0) (j : ℕ) :
    path b Y0 c0 s (a, y) (a, y + 1) j =
      (if (a : ℤ) < c0 then a + s - min (j / 2) (2 * b - j / 2)
        else a + s + 2 * b + min (j / 2) (2 * b - j / 2), y + (j + 1) / 2) := by
  have hne : y ≠ y + 1 := by omega
  have r1 : (y : ℤ) < Y0 := by omega
  have r2 : ¬ ((y + 1 : ℕ) : ℤ) < Y0 := by push_cast; omega
  simp only [path, if_neg hne, vmap, if_pos r1, if_neg r2]
  have e : y + 1 + 2 * b - y - 1 = 2 * b := by omega
  rw [e]
  split_ifs <;> rfl

theorem stair_len {s : ℕ} {a y : ℕ} (hY : (y : ℤ) + 1 = Y0) :
    pathLen b Y0 c0 s (a, y) (a, y + 1) = 4 * b + 1 := by
  have hne : y ≠ y + 1 := by omega
  have r1 : (y : ℤ) < Y0 := by omega
  have r2 : ¬ ((y + 1 : ℕ) : ℤ) < Y0 := by push_cast; omega
  simp only [pathLen, if_neg hne, vmap, if_pos r1, if_neg r2]
  omega

/-- Each step of a staircase goes to the new vertical edge. -/
theorem stair_step (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL)
    {a y : ℕ} (hpq : elementaryWallAdj h' (a, y) (a, y + 1)) (hY : (y : ℤ) + 1 = Y0) {j : ℕ}
    (hj : j < 4 * b + 1) :
    own h' b Y0 c0 sL (eCell (path b Y0 c0 s (a, y) (a, y + 1) j)
        (path b Y0 c0 s (a, y) (a, y + 1) (j + 1))) = some (eCell (a, y) (a, y + 1)) := by
  have hodd : (a + y) % 2 = 1 := by
    obtain ⟨-, -, h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩⟩ := hpq
    · omega
    · exact Nat.odd_iff.mp h
    · omega
  have ha : (a : ℤ) ≤ 2 * h' + 1 := by
    obtain ⟨⟨h1, -⟩, -⟩ := hpq; push_cast; omega
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  apply own_eq_eCell he' hpq
  rw [stair_path hY, stair_path hY]
  obtain ⟨t, rfl | rfl⟩ : ∃ t, j = 2 * t ∨ j = 2 * t + 1 := ⟨j / 2, by omega⟩
  · rw [cell_eCell_v (by simp only; split_ifs <;> omega) (by simp only; omega)]
    simp only [show 2 * t / 2 = t by omega, show (2 * t + 1) / 2 = t by omega]
    unfold vertCell off
    simp only [eCell]
    split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> push_cast at * <;> omega
  · simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega,
      show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega]
    have hrow : ((y + (t + 1) : ℕ) : ℤ) = Y0 + t := by push_cast; omega
    by_cases hL : (a : ℤ) < c0 <;> by_cases ht : t + 1 ≤ b <;>
      simp only [hL, ↓reduceIte] <;>
      [rw [cell_eCell_hx (x := a + sL - t - 1) (by simp only; omega) (by rfl)
        (by simp only; push_cast; omega)];
       rw [cell_eCell_hx (x := a + sL - 2 * b + t) (by simp only; omega) (by rfl)
        (by simp only; push_cast; omega)];
       rw [cell_eCell_hx (x := a + sL + 2 * b + t) (by simp only; omega) (by rfl)
        (by simp only; push_cast; omega)];
       rw [cell_eCell_hx (x := a + sL + 4 * b - t - 1) (by simp only; omega) (by rfl)
        (by simp only; push_cast; omega)]] <;>
      simp only [hrow] <;> unfold horizCell <;>
      simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, eCell, Prod.mk.injEq, true_and,
        and_true, add_sub_cancel_left] <;>
      push_cast <;> omega

/-- Each inner vertex of a staircase goes to the new vertical edge. -/
theorem stair_inner (hp : Params h' b Y0 c0 sL) (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL)
    {a y : ℕ} (hpq : elementaryWallAdj h' (a, y) (a, y + 1)) (hY : (y : ℤ) + 1 = Y0) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j < 4 * b + 1) :
    own h' b Y0 c0 sL (vCell (path b Y0 c0 s (a, y) (a, y + 1) j)) =
      some (eCell (a, y) (a, y + 1)) := by
  have hodd : (a + y) % 2 = 1 := by
    obtain ⟨-, -, h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩⟩ := hpq
    · omega
    · exact Nat.odd_iff.mp h
    · omega
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  apply own_eq_eCell he' hpq
  rw [stair_path hY, cell_vCell]
  obtain ⟨t, rfl | rfl⟩ : ∃ t, j = 2 * t + 1 ∨ j = 2 * t + 2 := ⟨(j - 1) / 2, by omega⟩
  · simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega]
    have hrow : ((y + (t + 1) : ℕ) : ℤ) = Y0 + t := by push_cast; omega
    by_cases hL : (a : ℤ) < c0 <;> by_cases ht : t + 1 ≤ b <;>
      simp only [hL, ↓reduceIte, hrow] <;> unfold vertexCell <;>
      simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, eCell, Prod.mk.injEq, true_and,
        and_true, add_sub_cancel_left] <;>
      omega
  · simp only [show (2 * t + 2) / 2 = t + 1 by omega, show (2 * t + 2 + 1) / 2 = t + 1 by omega]
    have hrow : ((y + (t + 1) : ℕ) : ℤ) = Y0 + t := by push_cast; omega
    by_cases hL : (a : ℤ) < c0 <;> by_cases ht : t + 1 ≤ b <;>
      simp only [hL, ↓reduceIte, hrow] <;> unfold vertexCell <;>
      simp (disch := omega) only [if_pos, if_neg, ↓reduceIte, eCell, Prod.mk.injEq, true_and,
        and_true, add_sub_cancel_left] <;>
      omega

/-- Proves adjacency in an elementary wall from coordinates. -/
macro "hadj_tac" : tactic => `(tactic| (simp only [elementaryWallAdj, elementaryWallVerts,
  Set.mem_setOf_eq, ne_eq, Prod.mk.injEq, Nat.odd_iff, true_and, and_true, true_or, or_true,
  not_and] at * <;> omega))

/-- The ends and the steps of the path of a horizontal edge. -/
theorem horiz_path (hp : Params h' b Y0 c0 sL) {s : ℕ} (hs : (s : ℤ) = sL) {a y : ℕ}
    (hpq : elementaryWallAdj h' (a, y) (a + 1, y)) :
    1 ≤ pathLen b Y0 c0 s (a, y) (a + 1, y) ∧
    path b Y0 c0 s (a, y) (a + 1, y) 0 = vmap b Y0 c0 s (a, y) ∧
    path b Y0 c0 s (a, y) (a + 1, y) (pathLen b Y0 c0 s (a, y) (a + 1, y)) =
      vmap b Y0 c0 s (a + 1, y) ∧
    (∀ j < pathLen b Y0 c0 s (a, y) (a + 1, y), elementaryWallAdj (h' + 2 * b + 2)
      (path b Y0 c0 s (a, y) (a + 1, y) j) (path b Y0 c0 s (a, y) (a + 1, y) (j + 1))) ∧
    (∀ i j, path b Y0 c0 s (a, y) (a + 1, y) i = path b Y0 c0 s (a, y) (a + 1, y) j → i = j) := by
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  simp only [pathLen, path, if_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [vmap]; split_ifs <;> push_cast at * <;> omega
  · simp
  · simp only [vmap]; split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> push_cast at * <;> omega
  · intro j hj
    simp only [vmap] at hj ⊢
    split_ifs at hj ⊢ <;> hadj_tac
  · intro i j e
    simp only [Prod.mk.injEq] at e
    omega

/-- The ends and the steps of the path of a vertical edge. -/
theorem vert_path (hp : Params h' b Y0 c0 sL) {s : ℕ} (hs : (s : ℤ) = sL) {a y : ℕ}
    (hpq : elementaryWallAdj h' (a, y) (a, y + 1)) :
    1 ≤ pathLen b Y0 c0 s (a, y) (a, y + 1) ∧
    path b Y0 c0 s (a, y) (a, y + 1) 0 = vmap b Y0 c0 s (a, y) ∧
    path b Y0 c0 s (a, y) (a, y + 1) (pathLen b Y0 c0 s (a, y) (a, y + 1)) =
      vmap b Y0 c0 s (a, y + 1) ∧
    (∀ j < pathLen b Y0 c0 s (a, y) (a, y + 1), elementaryWallAdj (h' + 2 * b + 2)
      (path b Y0 c0 s (a, y) (a, y + 1) j) (path b Y0 c0 s (a, y) (a, y + 1) (j + 1))) ∧
    (∀ i j, i ≤ pathLen b Y0 c0 s (a, y) (a, y + 1) → j ≤ pathLen b Y0 c0 s (a, y) (a, y + 1) →
      path b Y0 c0 s (a, y) (a, y + 1) i = path b Y0 c0 s (a, y) (a, y + 1) j → i = j) := by
  have hodd : (a + y) % 2 = 1 := by
    obtain ⟨-, -, h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩⟩ := hpq
    · omega
    · exact Nat.odd_iff.mp h
    · omega
  have hpq' := hpq
  obtain ⟨⟨ha1, hy1, -, -⟩, ⟨-, hy2, -, -⟩, -⟩ := hpq'
  simp only at ha1 hy1 hy2
  obtain ⟨Y1, Y2, c1, c2, s1, s2, se, b1⟩ := hp
  have hne : y ≠ y + 1 := by omega
  by_cases hY : (y : ℤ) + 1 = Y0
  · rw [stair_len hY]
    simp only [stair_path hY]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp only [vmap, Nat.zero_div, Nat.reduceDiv, min_eq_left (Nat.zero_le _)]
      split_ifs <;> simp only [Prod.mk.injEq] <;> push_cast at * <;> omega
    · simp only [vmap]
      have r2 : ¬ ((y + 1 : ℕ) : ℤ) < Y0 := by push_cast; omega
      simp only [r2, ↓reduceIte]
      split_ifs <;> simp only [Prod.mk.injEq] <;> omega
    · intro j hj
      obtain ⟨t, rfl | rfl⟩ : ∃ t, j = 2 * t ∨ j = 2 * t + 1 := ⟨j / 2, by omega⟩
      · simp only [show 2 * t / 2 = t by omega, show (2 * t + 1) / 2 = t by omega,
          show (2 * t + 1 + 1) / 2 = t + 1 by omega]
        split_ifs <;> hadj_tac
      · simp only [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega,
          show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega]
        split_ifs <;> hadj_tac
    · intro i j hi hj e
      split_ifs at e <;> simp only [Prod.mk.injEq] at e <;> omega
  · simp only [pathLen, path, if_neg hne, vmap] at *
    have hrow : ((y : ℤ) < Y0 ∧ ((y + 1 : ℕ) : ℤ) < Y0) ∨
        (¬ (y : ℤ) < Y0 ∧ ¬ ((y + 1 : ℕ) : ℤ) < Y0) := by push_cast; omega
    rcases hrow with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> simp only [r1, r2, ↓reduceIte] <;>
    · refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · split_ifs <;> simp
      · split_ifs <;> simp only [Prod.mk.injEq] <;> omega
      · intro j hj
        obtain rfl : j = 0 := by omega
        split_ifs <;> hadj_tac
      · intro i j hi hj e
        split_ifs at e <;> simp only [Prod.mk.injEq] at e <;> omega

end HexHole
end GraphMinor.GM13
