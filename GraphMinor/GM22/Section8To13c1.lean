module

public import GraphMinor.GM22.Section8To13c
public import GraphMinor.GM14.Suppress

/-!
# Graph Minors XXII: Elementary Walls and Walls are Subdivisions of Simple 3-Connected Graphs

This file proves that for every even `h ≥ 2`, `elementaryWall h` satisfies `GM14.Whitney.Good`,
and hence by `GM14.Whitney.good_sub` is a subdivision of a simple 3-connected graph
(`isSubdivisionOfSimpleThreeConnected_elementaryWall`). Combining this with
`isSubdivision_wall_of_elementaryWall` from `Section8To13c.lean`, we conclude that every wall
`W : GM13.Wall α β` is a subdivision of a simple 3-connected graph
(`isSubdivisionOfSimpleThreeConnected_wall`), establishing Hypothesis (i) of Theorem 8.3.
-/

@[expose] public section

set_option autoImplicit false

namespace GraphMinor.GM22

open Classical
open Set Function Graph
open GraphMinor GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM13 GraphMinor.GM14.Whitney

universe u v

/-! ## 1. Finiteness, Looplessness, and Degree Formula for `elementaryWall h` -/

lemma finite_elementaryWallVerts (h : ℕ) : (elementaryWallVerts h).Finite := by
  refine ((finite_Iic (2 * h + 1)).prod (finite_Iic h)).subset ?_
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

lemma not_elementaryWallAdj_self (h : ℕ) (p : ℕ × ℕ) : ¬ elementaryWallAdj h p p := by
  rintro ⟨-, -, ⟨-, h1 | h1⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩⟩ <;> omega

lemma no_loop_elementaryWall (h : ℕ) (e : Sym2 (ℕ × ℕ)) (p : ℕ × ℕ) :
    ¬ (elementaryWall h).IsLink e p p := by
  rintro ⟨hadj, -⟩
  exact not_elementaryWallAdj_self h p hadj

lemma finite_elementaryWall_edges (h : ℕ) : E(elementaryWall h).Finite := by
  have hV := finite_elementaryWallVerts h
  refine ((hV.prod hV).image (fun pq : (ℕ × ℕ) × (ℕ × ℕ) => s(pq.1, pq.2))).subset ?_
  rintro e ⟨p, q, hadj, rfl⟩
  exact ⟨(p, q), ⟨hadj.1, hadj.2.1⟩, rfl⟩

lemma inc_elementaryWall_eq_image (h : ℕ) (p : ℕ × ℕ) :
    {e | (elementaryWall h).Inc e p} = (fun q => s(p, q)) '' {q | elementaryWallAdj h p q} := by
  ext e
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨q, hadj, rfl⟩
    exact ⟨q, hadj, rfl⟩
  · rintro ⟨q, hadj, rfl⟩
    exact ⟨q, hadj, rfl⟩

lemma deg_elementaryWall_eq_ncard_adj (h : ℕ) (p : ℕ × ℕ) :
    deg (elementaryWall h) p = {q | elementaryWallAdj h p q}.ncard := by
  unfold deg
  rw [inc_elementaryWall_eq_image]
  refine Set.InjOn.ncard_image ?_
  intro q₁ hq₁ q₂ _ heq
  rcases Sym2.eq_iff.mp heq with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (not_elementaryWallAdj_self h q₁ hq₁).elim

/-! ## 2. Degree-2 and Degree-3 Vertices of `elementaryWall h` -/

/-- The vertices of `elementaryWall h` that have degree 2. -/
def isElemWallDeg2 (h : ℕ) (p : ℕ × ℕ) : Prop :=
  p ∈ elementaryWallVerts h ∧
    (p.1 = 0 ∨ p.1 = 2 * h + 1 ∨ p = (1, 0) ∨ p = (2 * h, h) ∨
      (p.2 = 0 ∧ Even p.1) ∨ (p.2 = h ∧ Odd p.1))

/-- Counter-clockwise perimeter neighbour of a degree-2 vertex of `elementaryWall h`. -/
def elemWallN1 (h : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 = 0 then
    if p.2 = h then (0, h - 1)
    else if Odd p.2 then (1, p.2)
    else (0, p.2 - 1)
  else if p.2 = h then
    (p.1 - 1, h)
  else if p.1 = 2 * h + 1 then
    if p.2 = 0 then (2 * h + 1, 1)
    else if Odd p.2 then (2 * h, p.2)
    else (2 * h + 1, p.2 + 1)
  else
    (p.1 + 1, 0)

/-- Clockwise perimeter neighbour of a degree-2 vertex of `elementaryWall h`. -/
def elemWallN2 (h : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 = 0 then
    if p.2 = h then (1, h)
    else if Odd p.2 then (0, p.2 + 1)
    else (1, p.2)
  else if p.2 = h then
    if p.1 = 2 * h then (2 * h, h - 1)
    else (p.1 + 1, h)
  else if p.1 = 2 * h + 1 then
    if p.2 = 0 then (2 * h, 0)
    else if Odd p.2 then (2 * h + 1, p.2 - 1)
    else (2 * h, p.2)
  else
    if p.1 = 1 then (1, 1)
    else (p.1 - 1, 0)

set_option maxHeartbeats 800000 in
lemma elementaryWallAdj_iff_of_deg2 {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) (q : ℕ × ℕ) :
    elementaryWallAdj h p q ↔ q = elemWallN1 h p ∨ q = elemWallN2 h p := by
  rcases hp with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdeg⟩
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold elemWallN1 elemWallN2
  dsimp only at *
  simp only [elementaryWallAdj, elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq,
    not_and, Nat.odd_iff, Nat.even_iff] at *
  have h_y0 : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → y = 0 := by
    intro hx0 hyh hx2h1
    rcases hdeg with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have h_x0 : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → x ≠ 1 → x % 2 = 0 := by
    intro hx0 hyh hx2h1 hx1
    rcases hdeg with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have h_yh : x ≠ 0 → y = h → x ≠ 2 * h → x % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdeg with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have h_xy_mod := Nat.add_mod x y
  have h_qxy_mod := Nat.add_mod qx qy
  split_ifs <;>
  · simp only [Prod.mk.injEq] at *
    constructor
    · rintro ⟨_, ⟨hq1, hq2, hq00, hq2h⟩, ⟨hy, hx1 | hx1⟩ | ⟨hx, ⟨hy1, hodd⟩ | ⟨hy1, hodd⟩⟩⟩ <;>
      · first
        | (left; exact ⟨by omega, by omega⟩)
        | (right; exact ⟨by omega, by omega⟩)
    · rintro (⟨hqx, hqy⟩ | ⟨hqx, hqy⟩) <;>
      · refine ⟨⟨hp1, hp2, hp00, hp2h⟩, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
        first
        | (left; exact ⟨by omega, by omega⟩)
        | (right; refine ⟨by omega, ?_⟩;
           first
           | (left; exact ⟨by omega, by omega⟩)
           | (right; exact ⟨by omega, by omega⟩))

lemma elemWallN1_ne_elemWallN2 {h : ℕ} (hh : 2 ≤ h) {p : ℕ × ℕ} (hp : isElemWallDeg2 h p) :
    elemWallN1 h p ≠ elemWallN2 h p := by
  rcases hp with ⟨⟨hp1, hp2, hp00, hp2h⟩, _⟩
  rcases p with ⟨x, y⟩
  unfold elemWallN1 elemWallN2
  dsimp only at *
  split_ifs <;> simp only [ne_eq, Prod.mk.injEq, not_and] at * <;> omega

lemma deg_eq_two_of_isElemWallDeg2 {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) : deg (elementaryWall h) p = 2 := by
  rw [deg_elementaryWall_eq_ncard_adj]
  have hset : {q | elementaryWallAdj h p q} = {elemWallN1 h p, elemWallN2 h p} := by
    ext q
    rw [mem_ofPred_eq, elementaryWallAdj_iff_of_deg2 hh he hp, mem_insert_iff, mem_singleton_iff]
  rw [hset, ncard_pair (elemWallN1_ne_elemWallN2 hh hp)]

/-- The vertical neighbour of a degree-3 vertex of `elementaryWall h`. -/
def elemWallVertNbr (p : ℕ × ℕ) : ℕ × ℕ :=
  if Odd (p.1 + p.2) then (p.1, p.2 + 1) else (p.1, p.2 - 1)

set_option maxHeartbeats 800000 in
lemma elementaryWallAdj_iff_of_not_deg2 {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ}
    (hpV : p ∈ elementaryWallVerts h) (hp : ¬ isElemWallDeg2 h p) (q : ℕ × ℕ) :
    elementaryWallAdj h p q ↔
      q = (p.1 - 1, p.2) ∨ q = (p.1 + 1, p.2) ∨ q = elemWallVertNbr p := by
  have hdeg : ¬ (p.1 = 0 ∨ p.1 = 2 * h + 1 ∨ p = (1, 0) ∨ p = (2 * h, h) ∨
      (p.2 = 0 ∧ Even p.1) ∨ (p.2 = h ∧ Odd p.1)) := fun h1 => hp ⟨hpV, h1⟩
  rcases hpV with ⟨hp1, hp2, hp00, hp2h⟩
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold elemWallVertNbr
  dsimp only at *
  split_ifs with hodd <;>
  · simp only [elementaryWallAdj, elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq,
      Nat.odd_iff, Nat.even_iff, not_or, not_and] at *
    obtain ⟨hx0, hx2h1, hp10, hp2hh, hy0e, hyho⟩ := hdeg
    have h_xy_mod := Nat.add_mod x y
    have h_qxy_mod := Nat.add_mod qx qy
    have hy_lt : (x + y) % 2 = 1 → y < h := by
      intro ho
      by_contra hge
      have hy_eq : y = h := by omega
      exact hyho hy_eq (by omega)
    have hy_pos : ¬ (x + y) % 2 = 1 → 0 < y := by
      intro hev
      by_contra hle
      have hy_eq : y = 0 := by omega
      exact hy0e hy_eq (by omega)
    constructor
    · rintro ⟨_, ⟨hq1, hq2, hq00, hq2h⟩, ⟨hy, hx1 | hx1⟩ | ⟨hx, ⟨hy1, ho⟩ | ⟨hy1, ho⟩⟩⟩
      · right; left; exact ⟨by omega, by omega⟩
      · left; exact ⟨by omega, by omega⟩
      · right; right; exact ⟨by omega, by omega⟩
      · right; right; exact ⟨by omega, by omega⟩
    · rintro (⟨hqx, hqy⟩ | ⟨hqx, hqy⟩ | ⟨hqx, hqy⟩)
      · refine ⟨⟨hp1, hp2, hp00, hp2h⟩, ⟨by omega, by omega, by omega, by omega⟩,
          Or.inl ⟨by omega, Or.inr (by omega)⟩⟩
      · refine ⟨⟨hp1, hp2, hp00, hp2h⟩, ⟨by omega, by omega, by omega, by omega⟩,
          Or.inl ⟨by omega, Or.inl (by omega)⟩⟩
      · refine ⟨⟨hp1, hp2, hp00, hp2h⟩, ⟨by omega, by omega, by omega, by omega⟩, Or.inr ⟨by omega, ?_⟩⟩
        first
        | (left; exact ⟨by omega, by omega⟩)
        | (right; exact ⟨by omega, by omega⟩)

lemma deg_eq_three_of_not_isElemWallDeg2 {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ}
    (hpV : p ∈ elementaryWallVerts h) (hp : ¬ isElemWallDeg2 h p) :
    deg (elementaryWall h) p = 3 := by
  rw [deg_elementaryWall_eq_ncard_adj]
  have hset : {q | elementaryWallAdj h p q} =
      {(p.1 - 1, p.2), (p.1 + 1, p.2), elemWallVertNbr p} := by
    ext q
    rw [mem_ofPred_eq, elementaryWallAdj_iff_of_not_deg2 hh he hpV hp]
    simp only [mem_insert_iff, mem_singleton_iff]
  have h1 : p.1 ≠ 0 := fun h0 => hp ⟨hpV, Or.inl h0⟩
  have h2 : elemWallVertNbr p ≠ (p.1 - 1, p.2) ∧ elemWallVertNbr p ≠ (p.1 + 1, p.2) := by
    unfold elemWallVertNbr
    split_ifs <;> simp only [ne_eq, Prod.ext_iff] <;> omega
  have h3 : (p.1 - 1, p.2) ≠ (p.1 + 1, p.2) := by
    simp only [ne_eq, Prod.ext_iff]; omega
  rw [hset, ncard_insert_of_notMem, ncard_pair h2.2.symm]
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨h3, h2.1.symm⟩

lemma four_deg_ne_two_elementaryWall {h : ℕ} (hh : 2 ≤ h) (he : Even h) :
    4 ≤ {v | v ∈ V(elementaryWall h) ∧ deg (elementaryWall h) v ≠ 2}.ncard := by
  let S : Set (ℕ × ℕ) := {(1, 1), (2, 1), (3, 1), (4, 1)}
  have hsub : S ⊆ {v | v ∈ V(elementaryWall h) ∧ deg (elementaryWall h) v ≠ 2} := by
    intro p hp
    have hpV : p ∈ elementaryWallVerts h := by
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by omega, by decide, by simp only [ne_eq, Prod.ext_iff]; omega⟩
    have hpnot : ¬ isElemWallDeg2 h p := by
      rintro ⟨-, h0 | h1 | h2 | h3 | ⟨h4, -⟩ | ⟨h5, -⟩⟩ <;>
        (rcases hp with rfl | rfl | rfl | rfl <;> simp only [Prod.ext_iff] at * <;> omega)
    exact ⟨hpV, by rw [deg_eq_three_of_not_isElemWallDeg2 hh he hpV hpnot]; decide⟩
  have hfin : {v | v ∈ V(elementaryWall h) ∧ deg (elementaryWall h) v ≠ 2}.Finite :=
    (finite_elementaryWallVerts h).subset fun _ hv => hv.1
  have hcard : S.ncard = 4 := by
    simp only [S]
    rw [ncard_insert_of_notMem (by decide) (toFinite _),
      ncard_insert_of_notMem (by decide) (toFinite _),
      ncard_pair (by decide)]
  exact hcard ▸ ncard_le_ncard hsub hfin

/-! ## 3. Perimeter Chain Properties of Degree-2 Vertices -/

set_option maxHeartbeats 800000 in
lemma elemWallN2_of_eq_elemWallN1 {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p q : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) (hq : isElemWallDeg2 h q) (hqp : q = elemWallN1 h p) :
    elemWallN2 h q = p := by
  rcases hp with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdegp⟩
  rcases hq with ⟨⟨hq1, hq2, hq00, hq2h⟩, hdegq⟩
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold elemWallN1 at hqp
  unfold elemWallN2
  dsimp only at *
  have h_y0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → y = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_x0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → x ≠ 1 → x % 2 = 0 := by
    intro hx0 hyh hx2h1 hx1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_yhp : x ≠ 0 → y = h → x ≠ 2 * h → x % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_y0q : qx ≠ 0 → qy ≠ h → qx ≠ 2 * h + 1 → qy = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_x0q : qx ≠ 0 → qy ≠ h → qx ≠ 2 * h + 1 → qx ≠ 1 → qx % 2 = 0 := by
    intro hx0 hyh hx2h1 hx1
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_yhq : qx ≠ 0 → qy = h → qx ≠ 2 * h → qx % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  split_ifs at hqp ⊢ <;>
    simp only [Prod.mk.injEq, ne_eq, not_and, Nat.odd_iff, Nat.even_iff] at * <;> omega

set_option maxHeartbeats 800000 in
lemma elemWallN1_of_eq_elemWallN2 {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p q : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) (hq : isElemWallDeg2 h q) (hqp : q = elemWallN2 h p) :
    elemWallN1 h q = p := by
  rcases hp with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdegp⟩
  rcases hq with ⟨⟨hq1, hq2, hq00, hq2h⟩, hdegq⟩
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold elemWallN2 at hqp
  unfold elemWallN1
  dsimp only at *
  have h_y0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → y = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_x0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → x ≠ 1 → x % 2 = 0 := by
    intro hx0 hyh hx2h1 hx1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_yhp : x ≠ 0 → y = h → x ≠ 2 * h → x % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_y0q : qx ≠ 0 → qy ≠ h → qx ≠ 2 * h + 1 → qy = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_x0q : qx ≠ 0 → qy ≠ h → qx ≠ 2 * h + 1 → qx ≠ 1 → qx % 2 = 0 := by
    intro hx0 hyh hx2h1 hx1
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_yhq : qx ≠ 0 → qy = h → qx ≠ 2 * h → qx % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  split_ifs at hqp ⊢ <;>
    simp only [Prod.mk.injEq, ne_eq, not_and, Nat.odd_iff, Nat.even_iff] at * <;> omega

set_option maxHeartbeats 800000 in
lemma elemWallN1_injOn {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p q : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) (hq : isElemWallDeg2 h q) (heq : elemWallN1 h p = elemWallN1 h q) :
    p = q := by
  rcases hp with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdegp⟩
  rcases hq with ⟨⟨hq1, hq2, hq00, hq2h⟩, hdegq⟩
  rcases p with ⟨x, y⟩
  rcases q with ⟨qx, qy⟩
  unfold elemWallN1 at heq
  dsimp only at *
  have h_y0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → y = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_y0q : qx ≠ 0 → qy ≠ h → qx ≠ 2 * h + 1 → qy = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_yhp : x ≠ 0 → y = h → x ≠ 2 * h → x % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_yhq : qx ≠ 0 → qy = h → qx ≠ 2 * h → qx % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegq with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  split_ifs at heq <;>
    simp only [Prod.mk.injEq, ne_eq, not_and, Nat.odd_iff, Nat.even_iff] at * <;> omega

set_option maxHeartbeats 800000 in
lemma isElemWallDeg2_elemWallN2_iff {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) :
    isElemWallDeg2 h (elemWallN2 h p) ↔
      p = (0, h) ∨ (p.1 = 0 ∧ p.2 < h ∧ Odd p.2) ∨ p = (2 * h - 1, h) ∨
      (p.1 = 2 * h + 1 ∧ 0 < p.2 ∧ p.2 < h ∧ Odd p.2) ∨ p = (2 * h + 1, 0) ∨ p = (2, 0) := by
  have hadj : elementaryWallAdj h p (elemWallN2 h p) :=
    (elementaryWallAdj_iff_of_deg2 hh he hp (elemWallN2 h p)).mpr (Or.inr rfl)
  have hqV : elemWallN2 h p ∈ elementaryWallVerts h := hadj.2.1
  rcases hp with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdegp⟩
  rcases p with ⟨x, y⟩
  generalize hq_eq : elemWallN2 h (x, y) = q
  rcases q with ⟨qx, qy⟩
  rw [hq_eq] at hqV
  have h_y0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → y = 0 := by
    intro hx0 hyh hx2h1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h_x0p : x ≠ 0 → y ≠ h → x ≠ 2 * h + 1 → x ≠ 1 → x % 2 = 0 := by
    intro hx0 hyh hx2h1 hx1
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  have h_yhp : x ≠ 0 → y = h → x ≠ 2 * h → x % 2 = 1 := by
    intro hx0 hyh hx2h
    rcases hdegp with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega
  unfold elemWallN2 at hq_eq
  dsimp only at *
  split_ifs at hq_eq <;>
  · simp only [isElemWallDeg2, Prod.mk.injEq, ne_eq, not_and, Nat.odd_iff, Nat.even_iff] at *
    constructor
    · rintro ⟨_, h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;>
      · first
        | (left; exact ⟨by omega, by omega⟩)
        | (right; left; exact ⟨by omega, by omega, by omega⟩)
        | (right; right; left; exact ⟨by omega, by omega⟩)
        | (right; right; right; left; exact ⟨by omega, by omega, by omega, by omega⟩)
        | (right; right; right; right; left; exact ⟨by omega, by omega⟩)
        | (right; right; right; right; right; exact ⟨by omega, by omega⟩)
    · intro hcases
      refine ⟨hqV, ?_⟩
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      · first
        | (left; omega)
        | (right; left; omega)
        | (right; right; left; exact ⟨by omega, by omega⟩)
        | (right; right; right; left; exact ⟨by omega, by omega⟩)
        | (right; right; right; right; left; exact ⟨by omega, by omega⟩)
        | (right; right; right; right; right; exact ⟨by omega, by omega⟩)

set_option maxHeartbeats 800000 in
lemma isElemWallDeg2_elemWallN2_twice_iff {h : ℕ} (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ}
    (hp : isElemWallDeg2 h p) (hp1 : isElemWallDeg2 h (elemWallN2 h p)) :
    isElemWallDeg2 h (elemWallN2 h (elemWallN2 h p)) ↔
      p = (0, h - 1) ∨ p = (2 * h + 1, 1) := by
  have h1 := (isElemWallDeg2_elemWallN2_iff hh he hp).mp hp1
  rw [isElemWallDeg2_elemWallN2_iff hh he hp1]
  rcases p with ⟨x, y⟩
  generalize hq_eq : elemWallN2 h (x, y) = q
  rcases q with ⟨qx, qy⟩
  unfold elemWallN2 at hq_eq
  dsimp only at *
  split_ifs at hq_eq <;>
  · simp only [Prod.mk.injEq, Nat.odd_iff, Nat.even_iff] at *
    constructor
    · rintro (⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b, c, d⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;>
      (rcases h1 with ⟨c1, c2⟩ | ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
        first | (left; exact ⟨by omega, by omega⟩) | (right; exact ⟨by omega, by omega⟩))
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;>
      first
      | (left; exact ⟨by omega, by omega⟩)
      | (right; right; right; right; left; exact ⟨by omega, by omega⟩)

lemma not_isElemWallDeg2_elemWallN2_thrice {h : ℕ} (hh : 2 ≤ h) (he : Even h) (p : ℕ × ℕ) :
    ¬ (isElemWallDeg2 h p ∧ isElemWallDeg2 h (elemWallN2 h p) ∧
       isElemWallDeg2 h (elemWallN2 h (elemWallN2 h p)) ∧
       isElemWallDeg2 h (elemWallN2 h (elemWallN2 h (elemWallN2 h p)))) := by
  rintro ⟨hp, hp1, hp2, hp3⟩
  have h2 := (isElemWallDeg2_elemWallN2_twice_iff hh he hp hp1).mp hp2
  have h3 := (isElemWallDeg2_elemWallN2_twice_iff hh he hp1 hp2).mp hp3
  rcases h2 with rfl | rfl <;>
  · unfold elemWallN2 at h3
    dsimp only at h3
    split_ifs at h3 <;> simp only [Prod.mk.injEq, Nat.odd_iff, Nat.even_iff] at * <;> omega

lemma not_isElemWallDeg2_elemWallN1_thrice {h : ℕ} (hh : 2 ≤ h) (he : Even h) (p : ℕ × ℕ) :
    ¬ (isElemWallDeg2 h p ∧ isElemWallDeg2 h (elemWallN1 h p) ∧
       isElemWallDeg2 h (elemWallN1 h (elemWallN1 h p)) ∧
       isElemWallDeg2 h (elemWallN1 h (elemWallN1 h (elemWallN1 h p)))) := by
  rintro ⟨hp, hp1, hp2, hp3⟩
  set q := elemWallN1 h (elemWallN1 h (elemWallN1 h p))
  have hq1 : elemWallN2 h q = elemWallN1 h (elemWallN1 h p) :=
    elemWallN2_of_eq_elemWallN1 hh he hp2 hp3 rfl
  have hq2 : elemWallN2 h (elemWallN2 h q) = elemWallN1 h p := by
    rw [hq1]
    exact elemWallN2_of_eq_elemWallN1 hh he hp1 hp2 rfl
  have hq3 : elemWallN2 h (elemWallN2 h (elemWallN2 h q)) = p := by
    rw [hq2]
    exact elemWallN2_of_eq_elemWallN1 hh he hp hp1 rfl
  exact not_isElemWallDeg2_elemWallN2_thrice hh he q
    ⟨hp3, hq1.symm ▸ hp2, hq2.symm ▸ hp1, hq3.symm ▸ hp⟩

/-- `p₁` and `p₂` are the ends of a chain of 1, 2, or 3 degree-2 vertices of `elementaryWall h`
oriented clockwise along `elemWallN2`. -/
def InElemWallDeg2Chain (h : ℕ) (p₁ p₂ : ℕ × ℕ) : Prop :=
  isElemWallDeg2 h p₁ ∧
    (p₂ = p₁ ∨
     (isElemWallDeg2 h p₂ ∧ p₂ = elemWallN2 h p₁) ∨
     (isElemWallDeg2 h (elemWallN2 h p₁) ∧ isElemWallDeg2 h p₂ ∧
       p₂ = elemWallN2 h (elemWallN2 h p₁)))

/-- Clockwise orientation predicate for the endpoints `(a, b) = (elemWallN1 h p₁, elemWallN2 h p₂)`
of a degree-2 chain in `elementaryWall h`. -/
def ElemWallChainOriented (h : ℕ) (a b : ℕ × ℕ) : Prop :=
  (a.2 < b.2 ∧ a.1 ≤ 1 ∧ b.1 ≤ 2) ∨
  (a.1 = 1 ∧ b.1 = 0 ∧ a.2 = b.2 ∧ a.2 < h ∧ Odd a.2) ∨
  (a.1 = 0 ∧ b.1 = 1 ∧ a.2 = b.2 ∧ 0 < a.2 ∧ a.2 < h ∧ Even a.2) ∨
  (a.1 = 0 ∧ a.2 = h - 1 ∧ b.1 = 1 ∧ b.2 = h) ∨
  (a.1 < b.1 ∧ a.1 ≤ 2 * h - 1 ∧ a.2 = h ∧ (b.2 = h ∨ (b.1 = 2 * h ∧ b.2 = h - 1))) ∨
  (a.1 = 2 * h - 1 ∧ a.2 = h ∧ b.1 = 2 * h ∧ b.2 = h - 1) ∨
  (b.2 < a.2 ∧ 2 * h - 1 ≤ b.1 ∧ 2 * h ≤ a.1) ∨
  (a.1 = 2 * h ∧ b.1 = 2 * h + 1 ∧ a.2 = b.2 ∧ 1 ≤ a.2 ∧ Odd a.2) ∨
  (a.1 = 2 * h + 1 ∧ b.1 = 2 * h ∧ a.2 = b.2 ∧ 0 < a.2 ∧ a.2 < h ∧ Even a.2) ∨
  (a.1 = 2 * h + 1 ∧ a.2 = 1 ∧ b.1 = 2 * h ∧ b.2 = 0) ∨
  (b.1 < a.1 ∧ 2 ≤ a.1 ∧ a.2 = 0 ∧ (b.2 = 0 ∨ (b.1 = 1 ∧ b.2 = 1))) ∨
  (a.1 = 2 ∧ a.2 = 0 ∧ b.1 = 1 ∧ b.2 = 1)

lemma not_elemWallChainOriented_symm {h : ℕ} (hh : 2 ≤ h) {a b : ℕ × ℕ}
    (hab : ElemWallChainOriented h a b) (hba : ElemWallChainOriented h b a) : False := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by_⟩
  dsimp only [ElemWallChainOriented] at hab hba
  simp only [Nat.odd_iff, Nat.even_iff] at hab hba
  rcases hab with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4 | ⟨h4, h5⟩⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4 | ⟨h4, h5⟩⟩ | ⟨h1, h2, h3, h4⟩ <;>
    (rcases hba with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3, g4, g5⟩ | ⟨g1, g2, g3, g4, g5, g6⟩ | ⟨g1, g2, g3, g4⟩ |
        ⟨g1, g2, g3, g4 | ⟨g4, g5⟩⟩ | ⟨g1, g2, g3, g4⟩ |
        ⟨g1, g2, g3⟩ | ⟨g1, g2, g3, g4, g5⟩ | ⟨g1, g2, g3, g4, g5, g6⟩ | ⟨g1, g2, g3, g4⟩ |
        ⟨g1, g2, g3, g4 | ⟨g4, g5⟩⟩ | ⟨g1, g2, g3, g4⟩ <;> omega)

set_option maxHeartbeats 1600000 in
lemma elemWallChain_endpoints_props {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {p₁ p₂ : ℕ × ℕ} (hc : InElemWallDeg2Chain h p₁ p₂) :
    elemWallN1 h p₁ ≠ elemWallN2 h p₂ ∧
    ElemWallChainOriented h (elemWallN1 h p₁) (elemWallN2 h p₂) := by
  have hh_even : h % 2 = 0 := Nat.even_iff.mp he
  rcases hc with ⟨hp1_deg, hp2_eq | ⟨hp2_deg, hp2_eq⟩ | ⟨hp_mid, hp2_deg, hp2_eq⟩⟩
  · -- Case 1: `p₂ = p₁`
    subst p₂
    refine ⟨elemWallN1_ne_elemWallN2 hh hp1_deg, ?_⟩
    rcases hp1_deg with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdegp⟩
    rcases p₁ with ⟨x, y⟩
    dsimp only at hp1 hp2
    simp only [ne_eq, Prod.mk.injEq, not_and] at hp00 hp2h hdegp
    rcases hdegp with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, hyh_eq⟩ | ⟨rfl, c2⟩ | ⟨hyh_eq, c2⟩
    · -- `x = 0`
      have h0 : ¬ (y = 0) := hp00 rfl
      by_cases hyh : y = h
      · subst hyh
        unfold elemWallN1 elemWallN2; simp only [ite_true]
        right; right; right; left; exact ⟨rfl, rfl, rfl, rfl⟩
      · by_cases hyo : Odd y
        · unfold elemWallN1 elemWallN2; simp only [ite_true, hyh, hyo, ite_false]
          left; exact ⟨by omega, by omega, by omega⟩
        · unfold elemWallN1 elemWallN2; simp only [ite_true, hyh, hyo, ite_false]
          left; exact ⟨by omega, by omega, by omega⟩
    · -- `x = 2 * h + 1`
      have hyh : y ≠ h := hp2h rfl
      have hx0 : 2 * h + 1 ≠ 0 := by omega
      by_cases hy0 : y = 0
      · subst hy0
        unfold elemWallN1 elemWallN2; simp only [hx0, hyh, ite_true, ite_false]
        right; right; right; right; right; right; right; right; right; left
        exact ⟨rfl, rfl, rfl, rfl⟩
      · by_cases hyo : Odd y
        · unfold elemWallN1 elemWallN2; simp only [hx0, hyh, hy0, hyo, ite_true, ite_false]
          right; right; right; right; right; right; left
          exact ⟨by omega, by omega, by omega⟩
        · unfold elemWallN1 elemWallN2; simp only [hx0, hyh, hy0, hyo, ite_true, ite_false]
          right; right; right; right; right; right; left
          exact ⟨by omega, by omega, by omega⟩
    · -- `x = 1 ∧ y = 0`
      have hx0 : (1 : ℕ) ≠ 0 := by decide
      have hyh : (0 : ℕ) ≠ h := by omega
      have hx2h1 : (1 : ℕ) ≠ 2 * h + 1 := by omega
      unfold elemWallN1 elemWallN2; simp only [hx0, hyh, hx2h1, ite_true, ite_false]
      right; right; right; right; right; right; right; right; right; right; right
      exact ⟨rfl, rfl, rfl, rfl⟩
    · -- `x = 2 * h ∧ y = h`
      rw [hyh_eq]
      have hx0 : 2 * h ≠ 0 := by omega
      unfold elemWallN1 elemWallN2; simp only [hx0, ite_true]
      right; right; right; right; right; left
      exact ⟨rfl, rfl, rfl, rfl⟩
    · -- `y = 0 ∧ Even x`
      have hx_even : x % 2 = 0 := Nat.even_iff.mp c2
      have hx0 : x ≠ 0 := fun h0 => hp00 h0 rfl
      have hyh : (0 : ℕ) ≠ h := by omega
      have hx2h1 : x ≠ 2 * h + 1 := by omega
      have hx1 : x ≠ 1 := by omega
      unfold elemWallN1 elemWallN2; simp only [hx0, hyh, hx2h1, hx1, ite_true, ite_false]
      right; right; right; right; right; right; right; right; right; right; left
      exact ⟨by omega, by omega, rfl, Or.inl rfl⟩
    · -- `y = h ∧ Odd x`
      rw [hyh_eq]
      have hx_odd : x % 2 = 1 := Nat.odd_iff.mp c2
      have hx0 : x ≠ 0 := by omega
      have hx2h : x ≠ 2 * h := by omega
      unfold elemWallN1 elemWallN2; simp only [hx0, hx2h, ite_true, ite_false]
      right; right; right; right; left
      exact ⟨by omega, by omega, rfl, Or.inl rfl⟩
  · -- Case 2: `p₂ = elemWallN2 h p₁`
    have h1 := (isElemWallDeg2_elemWallN2_iff hh he hp1_deg).mp (hp2_eq ▸ hp2_deg)
    rcases p₁ with ⟨x, y⟩
    dsimp only at h1
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, hyh, hyo⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hy0, hyh, hyo⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `p₁ = (0, h)`
      subst p₂
      have h10 : (1 : ℕ) ≠ 0 := by decide
      have h12h : (1 : ℕ) ≠ 2 * h := by omega
      have ha : elemWallN1 h (0, h) = (0, h - 1) := by
        unfold elemWallN1; simp only [ite_true]
      have hb1 : elemWallN2 h (0, h) = (1, h) := by
        unfold elemWallN2; simp only [ite_true]
      have hb2 : elemWallN2 h (1, h) = (2, h) := by
        unfold elemWallN2; simp only [h10, h12h, ite_true, ite_false]
      rw [ha, hb1, hb2]
      refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
      left; exact ⟨by omega, by omega, by omega⟩
    · -- `x = 0 ∧ y < h ∧ Odd y`
      subst p₂
      have hy_ne_h : y ≠ h := by omega
      have hy1_even : ¬ Odd (y + 1) := by
        rw [Nat.odd_iff] at hyo ⊢; omega
      have ha : elemWallN1 h (0, y) = (1, y) := by
        unfold elemWallN1; simp only [hy_ne_h, hyo, ite_true, ite_false]
      have hb1 : elemWallN2 h (0, y) = (0, y + 1) := by
        unfold elemWallN2; simp only [hy_ne_h, hyo, ite_true, ite_false]
      rw [ha, hb1]
      by_cases hy1h : y + 1 = h
      · have hb2 : elemWallN2 h (0, y + 1) = (1, h) := by
          rw [hy1h]; unfold elemWallN2; simp only [ite_true]
        rw [hb2]
        refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
        left; exact ⟨by omega, by omega, by omega⟩
      · have hb2 : elemWallN2 h (0, y + 1) = (1, y + 1) := by
          unfold elemWallN2; simp only [hy1h, hy1_even, ite_true, ite_false]
        rw [hb2]
        refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
        left; exact ⟨by omega, by omega, by omega⟩
    · -- `p₁ = (2 * h - 1, h)`
      subst p₂
      have hx0 : 2 * h - 1 ≠ 0 := by omega
      have hx2h : 2 * h - 1 ≠ 2 * h := by omega
      have hx2h0 : 2 * h ≠ 0 := by omega
      have ha : elemWallN1 h (2 * h - 1, h) = (2 * h - 2, h) := by
        unfold elemWallN1; simp only [hx0, ite_true, ite_false]
        ext <;> dsimp only
        omega
      have hb1 : elemWallN2 h (2 * h - 1, h) = (2 * h, h) := by
        unfold elemWallN2; simp only [hx0, hx2h, ite_true, ite_false]
        ext <;> dsimp only
        omega
      have hb2 : elemWallN2 h (2 * h, h) = (2 * h, h - 1) := by
        unfold elemWallN2; simp only [hx2h0, ite_true, ite_false]
      rw [ha, hb1, hb2]
      refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
      right; right; right; right; left
      exact ⟨by omega, by omega, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · -- `x = 2 * h + 1 ∧ 0 < y ∧ y < h ∧ Odd y`
      subst p₂
      have hx0 : 2 * h + 1 ≠ 0 := by omega
      have hy_ne_h : y ≠ h := by omega
      have hy_ne_0 : y ≠ 0 := by omega
      have hy1_ne_h : y - 1 ≠ h := by omega
      have hy1_even : ¬ Odd (y - 1) := by
        rw [Nat.odd_iff] at hyo ⊢; omega
      have ha : elemWallN1 h (2 * h + 1, y) = (2 * h, y) := by
        unfold elemWallN1; simp only [hx0, hy_ne_h, hy_ne_0, hyo, ite_true, ite_false]
      have hb1 : elemWallN2 h (2 * h + 1, y) = (2 * h + 1, y - 1) := by
        unfold elemWallN2; simp only [hx0, hy_ne_h, hy_ne_0, hyo, ite_true, ite_false]
      rw [ha, hb1]
      by_cases hy10 : y - 1 = 0
      · have h0h : (0 : ℕ) ≠ h := by omega
        have hb2 : elemWallN2 h (2 * h + 1, y - 1) = (2 * h, 0) := by
          rw [hy10]; unfold elemWallN2; simp only [hx0, h0h, ite_true, ite_false]
        rw [hb2]
        refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
        right; right; right; right; right; right; left
        exact ⟨by omega, by omega, by omega⟩
      · have hb2 : elemWallN2 h (2 * h + 1, y - 1) = (2 * h, y - 1) := by
          unfold elemWallN2; simp only [hx0, hy1_ne_h, hy10, hy1_even, ite_true, ite_false]
        rw [hb2]
        refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
        right; right; right; right; right; right; left
        exact ⟨by omega, by omega, by omega⟩
    · -- `p₁ = (2 * h + 1, 0)`
      subst p₂
      have hx0 : 2 * h + 1 ≠ 0 := by omega
      have h0h : (0 : ℕ) ≠ h := by omega
      have hx2h0 : 2 * h ≠ 0 := by omega
      have hx2h2h1 : 2 * h ≠ 2 * h + 1 := by omega
      have hx2h1 : 2 * h ≠ 1 := by omega
      have ha : elemWallN1 h (2 * h + 1, 0) = (2 * h + 1, 1) := by
        unfold elemWallN1; simp only [hx0, h0h, ite_true, ite_false]
      have hb1 : elemWallN2 h (2 * h + 1, 0) = (2 * h, 0) := by
        unfold elemWallN2; simp only [hx0, h0h, ite_true, ite_false]
      have hb2 : elemWallN2 h (2 * h, 0) = (2 * h - 1, 0) := by
        unfold elemWallN2; simp only [hx2h0, h0h, hx2h2h1, hx2h1, ite_false]
      rw [ha, hb1, hb2]
      refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
      right; right; right; right; right; right; left
      exact ⟨by omega, by omega, by omega⟩
    · -- `p₁ = (2, 0)`
      subst p₂
      have h20 : (2 : ℕ) ≠ 0 := by decide
      have h0h : (0 : ℕ) ≠ h := by omega
      have h22h1 : (2 : ℕ) ≠ 2 * h + 1 := by omega
      have h21 : (2 : ℕ) ≠ 1 := by decide
      have h10 : (1 : ℕ) ≠ 0 := by decide
      have h12h1 : (1 : ℕ) ≠ 2 * h + 1 := by omega
      have ha : elemWallN1 h (2, 0) = (3, 0) := by
        unfold elemWallN1; simp only [h20, h0h, h22h1, ite_false]
      have hb1 : elemWallN2 h (2, 0) = (1, 0) := by
        unfold elemWallN2; simp only [h20, h0h, h22h1, h21, ite_false]
      have hb2 : elemWallN2 h (1, 0) = (1, 1) := by
        unfold elemWallN2; simp only [h10, h0h, h12h1, ite_true, ite_false]
      rw [ha, hb1, hb2]
      refine ⟨by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
      right; right; right; right; right; right; right; right; right; right; left
      exact ⟨by omega, by omega, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · -- Case 3: `p₂ = elemWallN2 h (elemWallN2 h p₁)`
    have h2 := (isElemWallDeg2_elemWallN2_twice_iff hh he hp1_deg hp_mid).mp (hp2_eq ▸ hp2_deg)
    have hh1_odd : Odd (h - 1) := by rw [Nat.odd_iff]; omega
    have h1_odd : Odd 1 := by decide
    have h1_ne_0 : (1 : ℕ) ≠ 0 := by decide
    have h1_ne_h : (1 : ℕ) ≠ h := by omega
    have h1_ne_2h1 : (1 : ℕ) ≠ 2 * h + 1 := by omega
    have h1_ne_2h : (1 : ℕ) ≠ 2 * h := by omega
    have h2h1_ne_0 : 2 * h + 1 ≠ 0 := by omega
    have h0_ne_h : (0 : ℕ) ≠ h := by omega
    have h2h_ne_0 : 2 * h ≠ 0 := by omega
    have h2h_ne_2h1 : 2 * h ≠ 2 * h + 1 := by omega
    have h2h_ne_1 : 2 * h ≠ 1 := by omega
    rcases h2 with rfl | rfl
    · subst p₂
      have ha : elemWallN1 h (0, h - 1) = (1, h - 1) := by
        unfold elemWallN1; dsimp only; split_ifs <;> try rfl
        all_goals omega
      have hb1 : elemWallN2 h (0, h - 1) = (0, h) := by
        unfold elemWallN2; dsimp only; split_ifs <;> try omega
        ext <;> dsimp only
        omega
      have hb2 : elemWallN2 h (0, h) = (1, h) := by
        unfold elemWallN2; dsimp only; split_ifs <;> try rfl
        all_goals omega
      have hb3 : elemWallN2 h (1, h) = (2, h) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h1_ne_0, ite_eq_left rfl, ite_eq_right h1_ne_2h]
      rw [ha, hb1, hb2, hb3]
      simp only [ElemWallChainOriented, Prod.mk.injEq, ne_eq, not_and]
      refine ⟨by omega, ?_⟩
      left; exact ⟨by omega, by omega, by omega⟩
    · subst p₂
      have ha : elemWallN1 h (2 * h + 1, 1) = (2 * h, 1) := by
        unfold elemWallN1; dsimp only
        rw [ite_eq_right h2h1_ne_0, ite_eq_right h1_ne_h, ite_eq_left rfl,
          ite_eq_right h1_ne_0, ite_eq_left h1_odd]
      have hb1 : elemWallN2 h (2 * h + 1, 1) = (2 * h + 1, 0) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h2h1_ne_0, ite_eq_right h1_ne_h, ite_eq_left rfl,
          ite_eq_right h1_ne_0, ite_eq_left h1_odd]
      have hb2 : elemWallN2 h (2 * h + 1, 0) = (2 * h, 0) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h2h1_ne_0, ite_eq_right h0_ne_h, ite_eq_left rfl, ite_eq_left rfl]
      have hb3 : elemWallN2 h (2 * h, 0) = (2 * h - 1, 0) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h2h_ne_0, ite_eq_right h0_ne_h, ite_eq_right h2h_ne_2h1, ite_eq_right h2h_ne_1]
      rw [ha, hb1, hb2, hb3]
      simp only [ElemWallChainOriented, Prod.mk.injEq, ne_eq, not_and]
      refine ⟨by omega, ?_⟩
      right; right; right; right; right; right; left; exact ⟨by omega, by omega, by omega⟩

lemma exists_elemWallN1_exit {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {U : Set (ℕ × ℕ)} (hU_deg2 : ∀ p ∈ U, isElemWallDeg2 h p)
    {p₀ : ℕ × ℕ} (hp₀ : p₀ ∈ U) :
    ∃ p₁ ∈ U, elemWallN1 h p₁ ∉ U := by
  by_cases h1 : elemWallN1 h p₀ ∉ U
  · exact ⟨p₀, hp₀, h1⟩
  · push Not at h1
    by_cases h2 : elemWallN1 h (elemWallN1 h p₀) ∉ U
    · exact ⟨elemWallN1 h p₀, h1, h2⟩
    · push Not at h2
      by_cases h3 : elemWallN1 h (elemWallN1 h (elemWallN1 h p₀)) ∉ U
      · exact ⟨elemWallN1 h (elemWallN1 h p₀), h2, h3⟩
      · push Not at h3
        exact (not_isElemWallDeg2_elemWallN1_thrice hh he p₀
          ⟨hU_deg2 p₀ hp₀, hU_deg2 _ h1, hU_deg2 _ h2, hU_deg2 _ h3⟩).elim

lemma exists_elemWallN2_chain {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {U : Set (ℕ × ℕ)} (hU_deg2 : ∀ p ∈ U, isElemWallDeg2 h p)
    {p₁ : ℕ × ℕ} (hp₁ : p₁ ∈ U) :
    ∃ p₂ ∈ U, InElemWallDeg2Chain h p₁ p₂ ∧ elemWallN2 h p₂ ∉ U := by
  by_cases h1 : elemWallN2 h p₁ ∉ U
  · exact ⟨p₁, hp₁, ⟨hU_deg2 p₁ hp₁, Or.inl rfl⟩, h1⟩
  · push Not at h1
    by_cases h2 : elemWallN2 h (elemWallN2 h p₁) ∉ U
    · exact ⟨elemWallN2 h p₁, h1,
        ⟨hU_deg2 p₁ hp₁, Or.inr (Or.inl ⟨hU_deg2 _ h1, rfl⟩)⟩, h2⟩
    · push Not at h2
      by_cases h3 : elemWallN2 h (elemWallN2 h (elemWallN2 h p₁)) ∉ U
      · exact ⟨elemWallN2 h (elemWallN2 h p₁), h2,
          ⟨hU_deg2 p₁ hp₁, Or.inr (Or.inr ⟨hU_deg2 _ h1, hU_deg2 _ h2, rfl⟩)⟩, h3⟩
      · push Not at h3
        exact (not_isElemWallDeg2_elemWallN2_thrice hh he p₁
          ⟨hU_deg2 p₁ hp₁, hU_deg2 _ h1, hU_deg2 _ h2, hU_deg2 _ h3⟩).elim

lemma mem_separation_inter_of_adj {α : Type u} {β : Type v} {G G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) {e : β} {u v : α}
    (hl : G.IsLink e u v) (hu : u ∈ V(G₁) \ V(G₂)) (hv : v ∉ V(G₁) \ V(G₂)) :
    v ∈ V(G₁) ∩ V(G₂) := by
  have he : e ∈ E(G) := hl.edge_mem
  rw [← hsep.2.2.2.1] at he
  rcases he with he1 | he2
  · obtain ⟨x, y, hl1⟩ := (G₁.edge_mem_iff_exists_isLink e).mp he1
    have hlG : G.IsLink e x y := hl1.mono hsep.1
    have hv1 : v ∈ V(G₁) := by
      rcases G.eq_or_eq_of_isLink_of_isLink hl.symm hlG with rfl | rfl
      · exact hl1.left_mem
      · exact hl1.right_mem
    have hv2 : v ∈ V(G₂) := by
      by_contra hnv2
      exact hv ⟨hv1, hnv2⟩
    exact ⟨hv1, hv2⟩
  · obtain ⟨x, y, hl2⟩ := (G₂.edge_mem_iff_exists_isLink e).mp he2
    have hlG : G.IsLink e x y := hl2.mono hsep.2.1
    have hu2 : u ∈ V(G₂) := by
      rcases G.eq_or_eq_of_isLink_of_isLink hl hlG with rfl | rfl
      · exact hl2.left_mem
      · exact hl2.right_mem
    exact (hu.2 hu2).elim

set_option maxHeartbeats 1600000 in
lemma elemWallChain_not_adj {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {p₁ p₂ : ℕ × ℕ} (hc : InElemWallDeg2Chain h p₁ p₂) :
    ¬ elementaryWallAdj h (elemWallN1 h p₁) (elemWallN2 h p₂) := by
  rcases hc with ⟨hp1_deg, hp2_eq | ⟨hp2_deg, hp2_eq⟩ | ⟨hp_mid, hp2_deg, hp2_eq⟩⟩
  · subst p₂
    rcases hp1_deg with ⟨⟨hp1, hp2, hp00, hp2h⟩, hdegp⟩
    rcases p₁ with ⟨x, y⟩
    generalize ha_eq : elemWallN1 h (x, y) = a
    generalize hb_eq : elemWallN2 h (x, y) = b
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, by_⟩
    unfold elemWallN1 at ha_eq
    unfold elemWallN2 at hb_eq
    dsimp only at *
    have h_ab_mod1 := Nat.add_mod ax ay
    have h_ab_mod2 := Nat.add_mod bx by_
    split_ifs at ha_eq hb_eq <;>
    · simp only [Prod.mk.injEq, ne_eq, not_and, Nat.odd_iff, Nat.even_iff] at *
      rcases hdegp with c1 | c1 | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
      · rintro ⟨_, _, ⟨_, _ | _⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩⟩ <;>
          simp only [Nat.odd_iff] at * <;> omega
  · have h1 := (isElemWallDeg2_elemWallN2_iff hh he hp1_deg).mp (hp2_eq ▸ hp2_deg)
    rcases hp1_deg with ⟨⟨hp1, hp2, hp00, hp2h⟩, _⟩
    rcases p₁ with ⟨x, y⟩
    rcases p₂ with ⟨qx, qy⟩
    generalize ha_eq : elemWallN1 h (x, y) = a
    generalize hb_eq : elemWallN2 h (qx, qy) = b
    rcases a with ⟨ax, ay⟩
    rcases b with ⟨bx, by_⟩
    have h_ab_mod1 := Nat.add_mod ax ay
    have h_ab_mod2 := Nat.add_mod bx by_
    unfold elemWallN1 at ha_eq
    unfold elemWallN2 at hp2_eq hb_eq
    dsimp only at *
    split_ifs at ha_eq hp2_eq hb_eq <;>
    · simp only [Prod.mk.injEq, ne_eq, not_and, Nat.odd_iff, Nat.even_iff] at *
      rcases h1 with ⟨c1, c2⟩ | ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
      · rintro ⟨_, _, ⟨_, _ | _⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩⟩ <;>
          simp only [Nat.odd_iff] at * <;> omega
  · have h2 := (isElemWallDeg2_elemWallN2_twice_iff hh he hp1_deg hp_mid).mp (hp2_eq ▸ hp2_deg)
    have hh_even : h % 2 = 0 := Nat.even_iff.mp he
    have hh1_odd : Odd (h - 1) := by rw [Nat.odd_iff]; omega
    have h1_odd : Odd 1 := by decide
    have h1_ne_0 : (1 : ℕ) ≠ 0 := by decide
    have h1_ne_h : (1 : ℕ) ≠ h := by omega
    have h1_ne_2h : (1 : ℕ) ≠ 2 * h := by omega
    have h2h1_ne_0 : 2 * h + 1 ≠ 0 := by omega
    have h0_ne_h : (0 : ℕ) ≠ h := by omega
    have h2h_ne_0 : 2 * h ≠ 0 := by omega
    have h2h_ne_2h1 : 2 * h ≠ 2 * h + 1 := by omega
    have h2h_ne_1 : 2 * h ≠ 1 := by omega
    rcases h2 with rfl | rfl
    · subst p₂
      have ha : elemWallN1 h (0, h - 1) = (1, h - 1) := by
        unfold elemWallN1; dsimp only; split_ifs <;> try rfl
        all_goals omega
      have hb1 : elemWallN2 h (0, h - 1) = (0, h) := by
        unfold elemWallN2; dsimp only; split_ifs <;> try omega
        ext <;> dsimp only
        omega
      have hb2 : elemWallN2 h (0, h) = (1, h) := by
        unfold elemWallN2; dsimp only; split_ifs <;> try rfl
        all_goals omega
      have hb3 : elemWallN2 h (1, h) = (2, h) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h1_ne_0, ite_eq_left rfl, ite_eq_right h1_ne_2h]
      rw [ha, hb1, hb2, hb3]
      rintro ⟨_, _, ⟨_, _ | _⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩⟩ <;> omega
    · subst p₂
      have ha : elemWallN1 h (2 * h + 1, 1) = (2 * h, 1) := by
        unfold elemWallN1; dsimp only
        rw [ite_eq_right h2h1_ne_0, ite_eq_right h1_ne_h, ite_eq_left rfl,
          ite_eq_right h1_ne_0, ite_eq_left h1_odd]
      have hb1 : elemWallN2 h (2 * h + 1, 1) = (2 * h + 1, 0) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h2h1_ne_0, ite_eq_right h1_ne_h, ite_eq_left rfl,
          ite_eq_right h1_ne_0, ite_eq_left h1_odd]
      have hb2 : elemWallN2 h (2 * h + 1, 0) = (2 * h, 0) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h2h1_ne_0, ite_eq_right h0_ne_h, ite_eq_left rfl, ite_eq_left rfl]
      have hb3 : elemWallN2 h (2 * h, 0) = (2 * h - 1, 0) := by
        unfold elemWallN2; dsimp only
        rw [ite_eq_right h2h_ne_0, ite_eq_right h0_ne_h, ite_eq_right h2h_ne_2h1, ite_eq_right h2h_ne_1]
      rw [ha, hb1, hb2, hb3]
      rintro ⟨_, _, ⟨_, _ | _⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩⟩ <;> omega

lemma thin_of_diff_subset_isElemWallDeg2 {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {G₁ G₂ : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))}
    (hsep : IsGraphSeparation (elementaryWall h) G₁ G₂)
    (hcard : (V(G₁) ∩ V(G₂)).ncard ≤ 2)
    (hdeg2 : ∀ p ∈ V(G₁) \ V(G₂), isElemWallDeg2 h p) :
    Thin (elementaryWall h) G₁ G₂ := by
  set X := V(G₁) ∩ V(G₂)
  set U := V(G₁) \ V(G₂)
  have hX_fin : X.Finite :=
    (finite_elementaryWallVerts h).subset fun p hp => hsep.1.vertexSet_mono hp.1
  have hU_fin : U.Finite :=
    (finite_elementaryWallVerts h).subset fun p hp => hsep.1.vertexSet_mono hp.1
  by_cases hU : U.Nonempty
  · right
    obtain ⟨p₀, hp₀⟩ := hU
    obtain ⟨p₁, hp₁U, hp₁_exit⟩ := exists_elemWallN1_exit hh he hdeg2 hp₀
    obtain ⟨p₂, hp₂U, hc12, hp₂_exit⟩ := exists_elemWallN2_chain hh he hdeg2 hp₁U
    set x₁ := elemWallN1 h p₁
    set x₂ := elemWallN2 h p₂
    have hp₁_deg : isElemWallDeg2 h p₁ := hdeg2 p₁ hp₁U
    have hp₂_deg : isElemWallDeg2 h p₂ := hdeg2 p₂ hp₂U
    have hl₁ : (elementaryWall h).IsLink s(p₁, x₁) p₁ x₁ :=
      ⟨(elementaryWallAdj_iff_of_deg2 hh he hp₁_deg x₁).mpr (Or.inl rfl), rfl⟩
    have hl₂ : (elementaryWall h).IsLink s(p₂, x₂) p₂ x₂ :=
      ⟨(elementaryWallAdj_iff_of_deg2 hh he hp₂_deg x₂).mpr (Or.inr rfl), rfl⟩
    have hx₁X : x₁ ∈ X := mem_separation_inter_of_adj hsep hl₁ hp₁U hp₁_exit
    have hx₂X : x₂ ∈ X := mem_separation_inter_of_adj hsep hl₂ hp₂U hp₂_exit
    obtain ⟨hx_ne, h_oriented⟩ := elemWallChain_endpoints_props hh he hc12
    have hnot_adj : ¬ elementaryWallAdj h x₁ x₂ := elemWallChain_not_adj hh he hc12
    have hsubX : ({x₁, x₂} : Set (ℕ × ℕ)) ⊆ X := by
      rintro z (rfl | rfl)
      · exact hx₁X
      · exact hx₂X
    have hcard_pair : ({x₁, x₂} : Set (ℕ × ℕ)).ncard = 2 := ncard_pair hx_ne
    have hX_card : X.ncard = 2 := le_antisymm hcard (hcard_pair ▸ ncard_le_ncard hsubX hX_fin)
    have hX_eq : X = {x₁, x₂} :=
      (eq_of_subset_of_ncard_le hsubX (by rw [hX_card, hcard_pair]) hX_fin).symm
    refine ⟨hX_card, fun v hv => deg_eq_two_of_isElemWallDeg2 hh he (hdeg2 v hv), ?_⟩
    have hunique_exit : ∀ q ∈ U, elemWallN1 h q ∉ U → q = p₁ := by
      intro q hqU hq_exit
      obtain ⟨q₂, hq₂U, hcq, hq₂_exit⟩ := exists_elemWallN2_chain hh he hdeg2 hqU
      have hq_deg : isElemWallDeg2 h q := hdeg2 q hqU
      have hq₂_deg : isElemWallDeg2 h q₂ := hdeg2 q₂ hq₂U
      have hlq₁ : (elementaryWall h).IsLink s(q, elemWallN1 h q) q (elemWallN1 h q) :=
        ⟨(elementaryWallAdj_iff_of_deg2 hh he hq_deg _).mpr (Or.inl rfl), rfl⟩
      have hlq₂ : (elementaryWall h).IsLink s(q₂, elemWallN2 h q₂) q₂ (elemWallN2 h q₂) :=
        ⟨(elementaryWallAdj_iff_of_deg2 hh he hq₂_deg _).mpr (Or.inr rfl), rfl⟩
      have hqx₁ : elemWallN1 h q ∈ X := mem_separation_inter_of_adj hsep hlq₁ hqU hq_exit
      have hqx₂ : elemWallN2 h q₂ ∈ X := mem_separation_inter_of_adj hsep hlq₂ hq₂U hq₂_exit
      rw [hX_eq] at hqx₁ hqx₂
      obtain ⟨hq_ne, hq_oriented⟩ := elemWallChain_endpoints_props hh he hcq
      rcases hqx₁ with hqx₁_eq | hqx₁_eq
      · exact elemWallN1_injOn hh he hq_deg hp₁_deg hqx₁_eq
      · rcases hqx₂ with hqx₂_eq | hqx₂_eq
        · rw [hqx₁_eq, hqx₂_eq] at hq_oriented
          exact (not_elemWallChainOriented_symm hh h_oriented hq_oriented).elim
        · exact (hq_ne (hqx₁_eq.trans hqx₂_eq.symm)).elim
    have hE_sub : E(G₁) ⊆ insert s(p₁, x₁) ((fun p => s(p, elemWallN2 h p)) '' U) := by
      intro e he1
      obtain ⟨u, v, hl1⟩ := (G₁.edge_mem_iff_exists_isLink e).mp he1
      have hlG : (elementaryWall h).IsLink e u v := hl1.mono hsep.1
      have hu1 : u ∈ V(G₁) := hl1.left_mem
      have hv1 : v ∈ V(G₁) := hl1.right_mem
      by_cases huU : u ∈ U
      · have hu_deg : isElemWallDeg2 h u := hdeg2 u huU
        have hadj := (elementaryWallAdj_iff_of_deg2 hh he hu_deg v).mp hlG.1
        rcases hadj with rfl | rfl
        · by_cases hvU : elemWallN1 h u ∈ U
          · have hv_deg : isElemWallDeg2 h (elemWallN1 h u) := hdeg2 _ hvU
            have hN2 := elemWallN2_of_eq_elemWallN1 hh he hu_deg hv_deg rfl
            right
            refine ⟨elemWallN1 h u, hvU, ?_⟩
            dsimp only
            rw [hN2, Sym2.eq_swap, ← hlG.2]
          · have hu_eq : u = p₁ := hunique_exit u huU hvU
            subst hu_eq
            exact Or.inl hlG.2
        · right
          exact ⟨u, huU, hlG.2.symm⟩
      · have hu2 : u ∈ V(G₂) := by
          by_contra hnu2; exact huU ⟨hu1, hnu2⟩
        have huX : u ∈ X := ⟨hu1, hu2⟩
        by_cases hvU : v ∈ U
        · have hv_deg : isElemWallDeg2 h v := hdeg2 v hvU
          have hadj := (elementaryWallAdj_iff_of_deg2 hh he hv_deg u).mp hlG.symm.1
          rcases hadj with rfl | rfl
          · have hv_eq : v = p₁ := hunique_exit v hvU huU
            subst hv_eq
            left
            rw [hlG.2, Sym2.eq_swap]
          · right
            refine ⟨v, hvU, ?_⟩
            dsimp only
            rw [hlG.2, Sym2.eq_swap]
        · have hv2 : v ∈ V(G₂) := by
            by_contra hnv2; exact hvU ⟨hv1, hnv2⟩
          have hvX : v ∈ X := ⟨hv1, hv2⟩
          rw [hX_eq] at huX hvX
          exfalso
          rcases huX with rfl | rfl <;> rcases hvX with rfl | rfl
          · exact not_elementaryWallAdj_self h x₁ hlG.1
          · exact hnot_adj hlG.1
          · exact hnot_adj hlG.symm.1
          · exact not_elementaryWallAdj_self h x₂ hlG.1
    have hfin_img : ((fun p => s(p, elemWallN2 h p)) '' U).Finite := hU_fin.image _
    have hfin_ins : (insert s(p₁, x₁) ((fun p => s(p, elemWallN2 h p)) '' U)).Finite :=
      hfin_img.insert _
    calc E(G₁).ncard
      _ ≤ (insert s(p₁, x₁) ((fun p => s(p, elemWallN2 h p)) '' U)).ncard :=
          ncard_le_ncard hE_sub hfin_ins
      _ ≤ ((fun p => s(p, elemWallN2 h p)) '' U).ncard + 1 := ncard_insert_le _ _
      _ ≤ U.ncard + 1 := Nat.add_le_add_right (ncard_image_le hU_fin) 1
  · have hsubV : V(G₁) ⊆ V(G₂) := by
      intro v hv1
      by_contra hv2
      exact hU ⟨v, hv1, hv2⟩
    have hU_empty : U = ∅ := not_nonempty_iff_eq_empty.mp hU
    by_cases hE1 : E(G₁) = ∅
    · exact Or.inl ⟨hsubV, hE1⟩
    · right
      obtain ⟨e₀, he₀⟩ := nonempty_iff_ne_empty.mpr hE1
      obtain ⟨u₀, v₀, hl₀⟩ := (G₁.edge_mem_iff_exists_isLink e₀).mp he₀
      have hl₀G : (elementaryWall h).IsLink e₀ u₀ v₀ := hl₀.mono hsep.1
      have hu₀_ne_v₀ : u₀ ≠ v₀ := fun heq => not_elementaryWallAdj_self h u₀ (heq ▸ hl₀G.1)
      have hsubX : ({u₀, v₀} : Set (ℕ × ℕ)) ⊆ X := by
        rintro z (rfl | rfl)
        · exact ⟨hl₀.left_mem, hsubV hl₀.left_mem⟩
        · exact ⟨hl₀.right_mem, hsubV hl₀.right_mem⟩
      have hcard_pair : ({u₀, v₀} : Set (ℕ × ℕ)).ncard = 2 := ncard_pair hu₀_ne_v₀
      have hX_card : X.ncard = 2 := le_antisymm hcard (hcard_pair ▸ ncard_le_ncard hsubX hX_fin)
      have hX_eq : X = {u₀, v₀} :=
        (eq_of_subset_of_ncard_le hsubX (by rw [hX_card, hcard_pair]) hX_fin).symm
      refine ⟨hX_card, fun v hv => (notMem_empty v (hU_empty ▸ hv)).elim, ?_⟩
      have hE_sub : E(G₁) ⊆ {s(u₀, v₀)} := by
        intro e he1
        obtain ⟨u, v, hl1⟩ := (G₁.edge_mem_iff_exists_isLink e).mp he1
        have hlG : (elementaryWall h).IsLink e u v := hl1.mono hsep.1
        have huX : u ∈ X := ⟨hl1.left_mem, hsubV hl1.left_mem⟩
        have hvX : v ∈ X := ⟨hl1.right_mem, hsubV hl1.right_mem⟩
        rw [hX_eq] at huX hvX
        rw [mem_singleton_iff]
        rcases huX with rfl | rfl <;> rcases hvX with rfl | rfl
        · exact (not_elementaryWallAdj_self h _ hlG.1).elim
        · exact hlG.2
        · rw [hlG.2, Sym2.eq_swap]
        · exact (not_elementaryWallAdj_self h _ hlG.1).elim
      change E(G₁).ncard ≤ U.ncard + 1
      rw [hU_empty, ncard_empty, zero_add, ← ncard_singleton s(u₀, v₀)]
      exact ncard_le_ncard hE_sub (finite_singleton _)

/-! ## 4. Walk-Connectedness in `elementaryWall h` and Order-≤2 Separations -/

/-- A subset `C ⊆ elementaryWallVerts h` is walk-connected in `elementaryWall h` if any two
vertices in `C` are joined by a walk of `elementaryWall h` whose support lies in `C`. -/
def IsElemWallConn (h : ℕ) (C : Set (ℕ × ℕ)) : Prop :=
  C ⊆ elementaryWallVerts h ∧
    ∀ p ∈ C, ∀ q ∈ C, ∃ w : Surface.GraphWalk (elementaryWall h) p q,
      ∀ z ∈ w.support, z ∈ C

lemma isElemWallConn_singleton {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    IsElemWallConn h {p} := by
  refine ⟨singleton_subset_iff.mpr hp, ?_⟩
  rintro a rfl b rfl
  refine ⟨.nil hp, ?_⟩
  intro z hz
  exact List.mem_singleton.mp hz

lemma IsElemWallConn.union_of_inter {h : ℕ} {C₁ C₂ : Set (ℕ × ℕ)}
    (h1 : IsElemWallConn h C₁) (h2 : IsElemWallConn h C₂) {r : ℕ × ℕ}
    (hr1 : r ∈ C₁) (hr2 : r ∈ C₂) :
    IsElemWallConn h (C₁ ∪ C₂) := by
  refine ⟨union_subset h1.1 h2.1, ?_⟩
  intro p hp q hq
  rcases hp with hp1 | hp2 <;> rcases hq with hq1 | hq2
  · obtain ⟨w, hw⟩ := h1.2 p hp1 q hq1
    exact ⟨w, fun z hz => Or.inl (hw z hz)⟩
  · obtain ⟨w1, hw1⟩ := h1.2 p hp1 r hr1
    obtain ⟨w2, hw2⟩ := h2.2 r hr2 q hq2
    refine ⟨w1.append w2, fun z hz => ?_⟩
    rcases (Surface.GraphWalk.mem_support_append w1 w2).mp hz with hz1 | hz2
    · exact Or.inl (hw1 z hz1)
    · exact Or.inr (hw2 z hz2)
  · obtain ⟨w1, hw1⟩ := h2.2 p hp2 r hr2
    obtain ⟨w2, hw2⟩ := h1.2 r hr1 q hq1
    refine ⟨w1.append w2, fun z hz => ?_⟩
    rcases (Surface.GraphWalk.mem_support_append w1 w2).mp hz with hz1 | hz2
    · exact Or.inr (hw1 z hz1)
    · exact Or.inl (hw2 z hz2)
  · obtain ⟨w, hw⟩ := h2.2 p hp2 q hq2
    exact ⟨w, fun z hz => Or.inr (hw z hz)⟩

lemma IsElemWallConn.union_of_adj {h : ℕ} {C₁ C₂ : Set (ℕ × ℕ)}
    (h1 : IsElemWallConn h C₁) (h2 : IsElemWallConn h C₂) {u v : ℕ × ℕ}
    (hu : u ∈ C₁) (hv : v ∈ C₂) (hadj : elementaryWallAdj h u v) :
    IsElemWallConn h (C₁ ∪ C₂) := by
  have hlink : (elementaryWall h).IsLink s(u, v) u v := ⟨hadj, rfl⟩
  have h1' : IsElemWallConn h (C₁ ∪ {v}) := by
    refine ⟨union_subset h1.1 (singleton_subset_iff.mpr hadj.2.1), ?_⟩
    intro p hp q hq
    rcases hp with hp1 | rfl <;> rcases hq with hq1 | rfl
    · obtain ⟨w, hw⟩ := h1.2 p hp1 q hq1
      exact ⟨w, fun z hz => Or.inl (hw z hz)⟩
    · obtain ⟨w, hw⟩ := h1.2 p hp1 u hu
      refine ⟨w.append (.cons hlink (.nil hadj.2.1)), fun z hz => ?_⟩
      rcases (Surface.GraphWalk.mem_support_append w _).mp hz with hz1 | hz2
      · exact Or.inl (hw z hz1)
      · rcases List.mem_cons.mp hz2 with rfl | hz3
        · exact Or.inl hu
        · exact Or.inr (List.mem_singleton.mp hz3)
    · obtain ⟨w, hw⟩ := h1.2 u hu q hq1
      refine ⟨.cons hlink.symm w, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact Or.inr rfl
      · exact Or.inl (hw z hz')
    · refine ⟨.nil hadj.2.1, fun z hz => ?_⟩
      exact Or.inr (List.mem_singleton.mp hz)
  have heq : C₁ ∪ C₂ = (C₁ ∪ {v}) ∪ C₂ := by
    ext x
    simp only [mem_union, mem_singleton_iff]
    constructor
    · rintro (hx1 | hx2)
      · exact Or.inl (Or.inl hx1)
      · exact Or.inr hx2
    · rintro ((hx1 | rfl) | hx2)
      · exact Or.inl hx1
      · exact Or.inr hv
      · exact Or.inr hx2
  rw [heq]
  exact h1'.union_of_inter h2 (Or.inr rfl) hv

lemma walk_meets_separation_inter {h : ℕ} {G₁ G₂ : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))}
    (hsep : IsGraphSeparation (elementaryWall h) G₁ G₂) :
    ∀ {p q : ℕ × ℕ} (w : Surface.GraphWalk (elementaryWall h) p q),
      p ∈ V(G₁) → q ∈ V(G₂) \ V(G₁) →
      ∃ z ∈ w.support, z ∈ V(G₁) ∩ V(G₂)
  | p, _, .nil _, hp1, hq2 => (hq2.2 hp1).elim
  | p, q, .cons (v := r) hl rest, hp1, hq2 => by
    by_cases hr1 : r ∈ V(G₁)
    · obtain ⟨z, hz_supp, hzX⟩ := walk_meets_separation_inter hsep rest hr1 hq2
      exact ⟨z, List.mem_cons_of_mem _ hz_supp, hzX⟩
    · by_cases hp2 : p ∈ V(G₂)
      · exact ⟨p, List.mem_cons_self .., hp1, hp2⟩
      · have hrX : r ∈ V(G₁) ∩ V(G₂) :=
          mem_separation_inter_of_adj hsep hl ⟨hp1, hp2⟩ (fun hrU => hr1 hrU.1)
        exact ⟨r, List.mem_cons_of_mem _ rest.start_mem_support, hrX⟩

lemma IsElemWallConn.meets_separation_inter {h : ℕ} {G₁ G₂ : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))}
    (hsep : IsGraphSeparation (elementaryWall h) G₁ G₂) {C : Set (ℕ × ℕ)}
    (hC : IsElemWallConn h C) {p q : ℕ × ℕ}
    (hpC : p ∈ C) (hp1 : p ∈ V(G₁)) (hqC : q ∈ C) (hq2 : q ∈ V(G₂) \ V(G₁)) :
    ∃ z ∈ C, z ∈ V(G₁) ∩ V(G₂) := by
  obtain ⟨w, hw⟩ := hC.2 p hpC q hqC
  obtain ⟨z, hz_supp, hzX⟩ := walk_meets_separation_inter hsep w hp1 hq2
  exact ⟨z, hw z hz_supp, hzX⟩

/-- Interval of vertices on row `y` with abscissas in `[a, b]`. -/
def elemRowInterval (h y a b : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ elementaryWallVerts h | p.2 = y ∧ a ≤ p.1 ∧ p.1 ≤ b}

lemma mem_elementaryWallVerts_of_mem_row {h x y : ℕ} (hy : y ≤ h) (hx2h1 : x ≤ 2 * h + 1)
    (hx_lo : y = 0 → 1 ≤ x) (hx_hi : y = h → x ≤ 2 * h) :
    (x, y) ∈ elementaryWallVerts h := by
  refine ⟨hx2h1, hy, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    have := hx_lo rfl
    omega
  · rintro ⟨rfl, rfl⟩
    have := hx_hi rfl
    omega

lemma exists_walk_elemRowInterval_right {h y a : ℕ} (hy : y ≤ h)
    (ha_lo : y = 0 → 1 ≤ a) :
    ∀ d : ℕ, a + d ≤ 2 * h + 1 → (y = h → a + d ≤ 2 * h) →
      ∃ w : Surface.GraphWalk (elementaryWall h) (a, y) (a + d, y),
        ∀ z ∈ w.support, z ∈ elemRowInterval h y a (a + d)
  | 0, h1, h2 => by
    have haV : (a, y) ∈ elementaryWallVerts h :=
      mem_elementaryWallVerts_of_mem_row hy (by omega) ha_lo (by omega)
    refine ⟨.nil haV, fun z hz => ?_⟩
    rcases List.mem_singleton.mp hz with rfl
    exact ⟨haV, rfl, le_rfl, le_rfl⟩
  | d + 1, h1, h2 => by
    obtain ⟨w, hw⟩ := exists_walk_elemRowInterval_right hy ha_lo d (by omega) (by omega)
    have huV : (a + d, y) ∈ elementaryWallVerts h :=
      mem_elementaryWallVerts_of_mem_row hy (by omega) (by omega) (by omega)
    have hvV : (a + (d + 1), y) ∈ elementaryWallVerts h :=
      mem_elementaryWallVerts_of_mem_row hy h1 (by omega) h2
    have hadj : elementaryWallAdj h (a + d, y) (a + (d + 1), y) :=
      ⟨huV, hvV, Or.inl ⟨rfl, Or.inl (by omega)⟩⟩
    have hlink : (elementaryWall h).IsLink s((a + d, y), (a + (d + 1), y)) (a + d, y) (a + (d + 1), y) :=
      ⟨hadj, rfl⟩
    refine ⟨w.append (.cons hlink (.nil hvV)), fun z hz => ?_⟩
    rcases (Surface.GraphWalk.mem_support_append w _).mp hz with hz1 | hz2
    · obtain ⟨hzV, hzy, hza, hzb⟩ := hw z hz1
      exact ⟨hzV, hzy, hza, by omega⟩
    · rcases List.mem_cons.mp hz2 with rfl | hz3
      · exact ⟨huV, rfl, by omega, by omega⟩
      · rcases List.mem_singleton.mp hz3 with rfl
        exact ⟨hvV, rfl, by omega, by omega⟩

lemma isElemWallConn_elemRowInterval {h y a b : ℕ} (hy : y ≤ h) (_hab : a ≤ b)
    (hb : b ≤ 2 * h + 1) (ha_lo : y = 0 → 1 ≤ a) (hb_hi : y = h → b ≤ 2 * h) :
    IsElemWallConn h (elemRowInterval h y a b) := by
  refine ⟨fun p hp => hp.1, ?_⟩
  have hreach : ∀ x : ℕ, a ≤ x → x ≤ b →
      ∃ w : Surface.GraphWalk (elementaryWall h) (a, y) (x, y),
        ∀ z ∈ w.support, z ∈ elemRowInterval h y a b := by
    intro x hax hxb
    have hstep := exists_walk_elemRowInterval_right hy ha_lo (x - a) (by omega) (by omega)
    rw [Nat.add_sub_of_le hax] at hstep
    obtain ⟨w, hw⟩ := hstep
    exact ⟨w, fun z hz => ⟨(hw z hz).1, (hw z hz).2.1, (hw z hz).2.2.1, (hw z hz).2.2.2.trans hxb⟩⟩
  rintro ⟨x₁, y₁⟩ ⟨_, rfl, hx1a, hx1b⟩ ⟨x₂, y₂⟩ ⟨_, hy2, hx2a, hx2b⟩
  dsimp only at hy2
  subst hy2
  obtain ⟨w₁, hw₁⟩ := hreach x₁ hx1a hx1b
  obtain ⟨w₂, hw₂⟩ := hreach x₂ hx2a hx2b
  refine ⟨w₁.reverse.append w₂, fun z hz => ?_⟩
  rcases (Surface.GraphWalk.mem_support_append w₁.reverse w₂).mp hz with hz1 | hz2
  · rw [Surface.GraphWalk.support_reverse, List.mem_reverse] at hz1
    exact hw₁ z hz1
  · exact hw₂ z hz2

/-- All vertices of `elementaryWall h` on row `y`. -/
def elemRow (h y : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ elementaryWallVerts h | p.2 = y}

lemma elemRow_eq_interval {h y : ℕ} (hy : y ≤ h) :
    elemRow h y = elemRowInterval h y (if y = 0 then 1 else 0) (if y = h then 2 * h else 2 * h + 1) := by
  ext ⟨x, y'⟩
  simp only [elemRow, elemRowInterval, mem_ofPred_eq]
  constructor
  · rintro ⟨hpV, rfl⟩
    refine ⟨hpV, rfl, ?_, ?_⟩
    · split_ifs with hy0
      · subst hy0
        have := hpV.2.2.1
        simp only [ne_eq, Prod.mk.injEq, and_true] at this
        omega
      · omega
    · split_ifs with hyh
      · subst hyh
        have := hpV.2.2.2
        simp only [ne_eq, Prod.mk.injEq, and_true] at this
        have := hpV.1
        omega
      · exact hpV.1
  · rintro ⟨hpV, rfl, _, _⟩
    exact ⟨hpV, rfl⟩

lemma isElemWallConn_elemRow {h y : ℕ} (hh : 2 ≤ h) (hy : y ≤ h) :
    IsElemWallConn h (elemRow h y) := by
  rw [elemRow_eq_interval hy]
  refine isElemWallConn_elemRowInterval hy ?_ ?_ ?_ ?_
  · split_ifs <;> omega
  · split_ifs <;> omega
  · intro hy0; simp [hy0]
  · intro hyh; simp [hyh]

/-- The vertical strip `k` of `elementaryWall h`: vertices with abscissa `2 * k` or `2 * k + 1`. -/
def elemStrip (h k : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ elementaryWallVerts h | p.1 = 2 * k ∨ p.1 = 2 * k + 1}

/-- The vertical strip `k` truncated to rows `0..m`. -/
def elemStripUpTo (h k m : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ elemStrip h k | p.2 ≤ m}

lemma elemStripUpTo_zero {h k : ℕ} (hk : k ≤ h) :
    elemStripUpTo h k 0 = elemRowInterval h 0 (if k = 0 then 1 else 2 * k) (2 * k + 1) := by
  ext ⟨x, y⟩
  simp only [elemStripUpTo, elemStrip, elemRowInterval, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hpV, hx⟩, hy0⟩
    have hy : y = 0 := by omega
    subst hy
    refine ⟨hpV, rfl, ?_, by omega⟩
    split_ifs with hk0
    · subst hk0
      have := hpV.2.2.1
      simp only [ne_eq, Prod.mk.injEq, and_true] at this
      omega
    · omega
  · rintro ⟨hpV, rfl, hxa, hxb⟩
    refine ⟨⟨hpV, ?_⟩, le_rfl⟩
    split_ifs at hxa <;> omega

lemma elemStripUpTo_succ {h k m : ℕ} (hk : k ≤ h) (hm : m + 1 ≤ h) :
    elemStripUpTo h k (m + 1) =
      elemStripUpTo h k m ∪
        elemRowInterval h (m + 1) (2 * k) (if m + 1 = h ∧ k = h then 2 * h else 2 * k + 1) := by
  ext ⟨x, y⟩
  simp only [elemStripUpTo, elemStrip, elemRowInterval, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hpV, hx⟩, hym⟩
    rcases Nat.le_or_eq_of_le_succ hym with hle | rfl
    · exact Or.inl ⟨⟨hpV, hx⟩, hle⟩
    · refine Or.inr ⟨hpV, rfl, by omega, ?_⟩
      split_ifs with hkh
      · obtain ⟨hmh, rfl⟩ := hkh
        have hnot := hpV.2.2.2
        simp only [ne_eq, Prod.mk.injEq] at hnot
        omega
      · omega
  · rintro (⟨⟨hpV, hx⟩, hle⟩ | ⟨hpV, rfl, hxa, hxb⟩)
    · exact ⟨⟨hpV, hx⟩, by omega⟩
    · refine ⟨⟨hpV, ?_⟩, le_rfl⟩
      split_ifs at hxb <;> omega

lemma isElemWallConn_elemStripUpTo {h k : ℕ} (hh : 2 ≤ h) (he : Even h) (hk : k ≤ h) :
    ∀ m : ℕ, m ≤ h → IsElemWallConn h (elemStripUpTo h k m)
  | 0, _ => by
    rw [elemStripUpTo_zero hk]
    refine isElemWallConn_elemRowInterval (by omega) ?_ (by omega) ?_ (by omega)
    · split_ifs <;> omega
    · intro _; split_ifs <;> omega
  | m + 1, hm => by
    rw [elemStripUpTo_succ hk hm]
    have ih := isElemWallConn_elemStripUpTo hh he hk m (by omega)
    have htop : IsElemWallConn h
        (elemRowInterval h (m + 1) (2 * k) (if m + 1 = h ∧ k = h then 2 * h else 2 * k + 1)) := by
      refine isElemWallConn_elemRowInterval hm ?_ ?_ (by omega) ?_
      · split_ifs <;> omega
      · split_ifs <;> omega
      · intro hmh; split_ifs <;> omega
    let x₀ : ℕ := if Odd m then 2 * k else 2 * k + 1
    have hx₀_mod : (x₀ + m) % 2 = 1 := by
      simp only [x₀]
      split_ifs with hod <;> simp only [Nat.odd_iff] at hod <;> omega
    have hx₀_not_00 : ¬ (x₀ = 0 ∧ m = 0) := by
      rintro ⟨hx0, rfl⟩
      simp only [x₀, Nat.not_odd_zero, ite_false] at hx0
      omega
    have hx₀_not_2hh1 : ¬ (x₀ = 2 * h + 1 ∧ m + 1 = h) := by
      rintro ⟨hx2h1, hmh⟩
      have hm_odd : Odd m := by
        rw [Nat.odd_iff]
        have := Nat.even_iff.mp he
        omega
      simp only [x₀, hm_odd, ite_true] at hx2h1
      omega
    have huV : (x₀, m) ∈ elementaryWallVerts h := by
      refine ⟨by simp only [x₀]; split_ifs <;> omega, by omega, ?_, ?_⟩
      · simp only [ne_eq, Prod.mk.injEq]; exact hx₀_not_00
      · simp only [ne_eq, Prod.mk.injEq]; omega
    have hvV : (x₀, m + 1) ∈ elementaryWallVerts h := by
      refine ⟨by simp only [x₀]; split_ifs <;> omega, hm, ?_, ?_⟩
      · simp only [ne_eq, Prod.mk.injEq]; omega
      · simp only [ne_eq, Prod.mk.injEq]; exact hx₀_not_2hh1
    have hu_mem : (x₀, m) ∈ elemStripUpTo h k m := by
      refine ⟨⟨huV, ?_⟩, le_rfl⟩
      simp only [x₀]; split_ifs <;> omega
    have hv_mem : (x₀, m + 1) ∈
        elemRowInterval h (m + 1) (2 * k) (if m + 1 = h ∧ k = h then 2 * h else 2 * k + 1) := by
      refine ⟨hvV, rfl, by simp only [x₀]; split_ifs <;> omega, ?_⟩
      split_ifs with hkh
      · obtain ⟨hmh, rfl⟩ := hkh
        have hm_odd : Odd m := by
          rw [Nat.odd_iff]
          have := Nat.even_iff.mp he
          omega
        simp only [x₀, hm_odd, ite_true, le_rfl]
      · simp only [x₀]; split_ifs <;> omega
    have hadj : elementaryWallAdj h (x₀, m) (x₀, m + 1) := by
      refine ⟨huV, hvV, Or.inr ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩⟩
      rwa [Nat.odd_iff]
    exact ih.union_of_adj htop hu_mem hv_mem hadj

lemma isElemWallConn_elemStrip {h k : ℕ} (hh : 2 ≤ h) (he : Even h) (hk : k ≤ h) :
    IsElemWallConn h (elemStrip h k) := by
  have heq : elemStrip h k = elemStripUpTo h k h := by
    ext p
    simp only [elemStripUpTo, elemStrip, mem_ofPred_eq]
    exact ⟨fun hp => ⟨hp, hp.1.2.1⟩, fun hp => hp.1⟩
  rw [heq]
  exact isElemWallConn_elemStripUpTo hh he hk h le_rfl

lemma elemRow_inter_elemStrip_nonempty {h y k : ℕ} (hh : 2 ≤ h) (hy : y ≤ h) (hk : k ≤ h) :
    ∃ r : ℕ × ℕ, r ∈ elemRow h y ∧ r ∈ elemStrip h k := by
  by_cases hk0 : k = 0
  · subst hk0
    have hrV : (1, y) ∈ elementaryWallVerts h := by
      refine ⟨by omega, hy, by simp, ?_⟩
      simp only [ne_eq, Prod.mk.injEq]; omega
    exact ⟨(1, y), ⟨hrV, rfl⟩, ⟨hrV, Or.inr rfl⟩⟩
  · have hrV : (2 * k, y) ∈ elementaryWallVerts h := by
      refine ⟨by omega, hy, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
    exact ⟨(2 * k, y), ⟨hrV, rfl⟩, ⟨hrV, Or.inl rfl⟩⟩

lemma not_ncard_le_two_of_three_mem {α : Type u} {X : Set α} (hX : X.Finite)
    {z₁ z₂ z₃ : α} (hz1 : z₁ ∈ X) (hz2 : z₂ ∈ X) (hz3 : z₃ ∈ X)
    (hne12 : z₁ ≠ z₂) (hne13 : z₁ ≠ z₃) (hne23 : z₂ ≠ z₃) :
    ¬ X.ncard ≤ 2 := by
  intro hle
  have hsub : ({z₁, z₂, z₃} : Set α) ⊆ X := by
    rintro z (rfl | rfl | rfl) <;> assumption
  have hnot1 : z₁ ∉ ({z₂, z₃} : Set α) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne12, hne13⟩
  have hcard3 : ({z₁, z₂, z₃} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem hnot1 (toFinite _), ncard_pair hne23]
  have h3le := ncard_le_ncard hsub hX
  omega

lemma exists_disjoint_elemRow {h : ℕ} (hh : 2 ≤ h) {X : Set (ℕ × ℕ)}
    (hX_fin : X.Finite) (hcard : X.ncard ≤ 2) :
    ∃ y₀ ≤ h, Disjoint (elemRow h y₀) X := by
  by_cases h0 : Disjoint (elemRow h 0) X
  · exact ⟨0, by omega, h0⟩
  · by_cases h1 : Disjoint (elemRow h 1) X
    · exact ⟨1, by omega, h1⟩
    · by_cases h2 : Disjoint (elemRow h 2) X
      · exact ⟨2, by omega, h2⟩
      · exfalso
        rw [not_disjoint_iff] at h0 h1 h2
        obtain ⟨z₁, hz1R, hz1X⟩ := h0
        obtain ⟨z₂, hz2R, hz2X⟩ := h1
        obtain ⟨z₃, hz3R, hz3X⟩ := h2
        have h12 : z₁ ≠ z₂ := fun heq => by have := hz1R.2; have := hz2R.2; subst heq; omega
        have h13 : z₁ ≠ z₃ := fun heq => by have := hz1R.2; have := hz3R.2; subst heq; omega
        have h23 : z₂ ≠ z₃ := fun heq => by have := hz2R.2; have := hz3R.2; subst heq; omega
        exact not_ncard_le_two_of_three_mem hX_fin hz1X hz2X hz3X h12 h13 h23 hcard

lemma exists_disjoint_elemStrip {h : ℕ} (hh : 2 ≤ h) {X : Set (ℕ × ℕ)}
    (hX_fin : X.Finite) (hcard : X.ncard ≤ 2) :
    ∃ k₀ ≤ h, Disjoint (elemStrip h k₀) X := by
  by_cases h0 : Disjoint (elemStrip h 0) X
  · exact ⟨0, by omega, h0⟩
  · by_cases h1 : Disjoint (elemStrip h 1) X
    · exact ⟨1, by omega, h1⟩
    · by_cases h2 : Disjoint (elemStrip h 2) X
      · exact ⟨2, by omega, h2⟩
      · exfalso
        rw [not_disjoint_iff] at h0 h1 h2
        obtain ⟨z₁, hz1S, hz1X⟩ := h0
        obtain ⟨z₂, hz2S, hz2X⟩ := h1
        obtain ⟨z₃, hz3S, hz3X⟩ := h2
        have h12 : z₁ ≠ z₂ := fun heq => by
          have := hz1S.2; have := hz2S.2; subst heq; omega
        have h13 : z₁ ≠ z₃ := fun heq => by
          have := hz1S.2; have := hz3S.2; subst heq; omega
        have h23 : z₂ ≠ z₃ := fun heq => by
          have := hz2S.2; have := hz3S.2; subst heq; omega
        exact not_ncard_le_two_of_three_mem hX_fin hz1X hz2X hz3X h12 h13 h23 hcard

lemma three_paths_contradiction {h : ℕ} {G₁ G₂ : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))}
    (hsep : IsGraphSeparation (elementaryWall h) G₁ G₂)
    (hcard : (V(G₁) ∩ V(G₂)).ncard ≤ 2)
    {C₁ C₂ C₃ : Set (ℕ × ℕ)}
    (hC1 : IsElemWallConn h C₁) (hC2 : IsElemWallConn h C₂) (hC3 : IsElemWallConn h C₃)
    (hd12 : Disjoint C₁ C₂) (hd13 : Disjoint C₁ C₃) (hd23 : Disjoint C₂ C₃)
    {p₁ p₂ p₃ q₁ q₂ q₃ : ℕ × ℕ}
    (hp1C : p₁ ∈ C₁) (hp1G : p₁ ∈ V(G₁)) (hq1C : q₁ ∈ C₁) (hq1G : q₁ ∈ V(G₂) \ V(G₁))
    (hp2C : p₂ ∈ C₂) (hp2G : p₂ ∈ V(G₁)) (hq2C : q₂ ∈ C₂) (hq2G : q₂ ∈ V(G₂) \ V(G₁))
    (hp3C : p₃ ∈ C₃) (hp3G : p₃ ∈ V(G₁)) (hq3C : q₃ ∈ C₃) (hq3G : q₃ ∈ V(G₂) \ V(G₁)) :
    False := by
  have hX_fin : (V(G₁) ∩ V(G₂)).Finite :=
    (finite_elementaryWallVerts h).subset fun p hp => hsep.1.vertexSet_mono hp.1
  obtain ⟨z₁, hz1C, hz1X⟩ := hC1.meets_separation_inter hsep hp1C hp1G hq1C hq1G
  obtain ⟨z₂, hz2C, hz2X⟩ := hC2.meets_separation_inter hsep hp2C hp2G hq2C hq2G
  obtain ⟨z₃, hz3C, hz3X⟩ := hC3.meets_separation_inter hsep hp3C hp3G hq3C hq3G
  exact not_ncard_le_two_of_three_mem hX_fin hz1X hz2X hz3X
    (fun heq => disjoint_left.mp hd12 hz1C (heq ▸ hz2C))
    (fun heq => disjoint_left.mp hd13 hz1C (heq ▸ hz3C))
    (fun heq => disjoint_left.mp hd23 hz2C (heq ▸ hz3C)) hcard

set_option maxHeartbeats 1600000 in
lemma isElemWallDeg2_of_mem_diff_of_disjoint_row_strip {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {G₁ G₂ : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))}
    (hsep : IsGraphSeparation (elementaryWall h) G₁ G₂)
    (hcard : (V(G₁) ∩ V(G₂)).ncard ≤ 2)
    {y₀ k₀ : ℕ} (hy₀ : y₀ ≤ h) (hk₀ : k₀ ≤ h)
    (hRow2 : elemRow h y₀ ⊆ V(G₂) \ V(G₁))
    (hStrip2 : elemStrip h k₀ ⊆ V(G₂) \ V(G₁))
    {p : ℕ × ℕ} (hpU : p ∈ V(G₁) \ V(G₂)) :
    isElemWallDeg2 h p := by
  by_contra hp_not_deg2
  have hpV : p ∈ elementaryWallVerts h := hsep.1.vertexSet_mono hpU.1
  have hdeg : ¬ (p.1 = 0 ∨ p.1 = 2 * h + 1 ∨ p = (1, 0) ∨ p = (2 * h, h) ∨
      (p.2 = 0 ∧ Even p.1) ∨ (p.2 = h ∧ Odd p.1)) := fun h1 => hp_not_deg2 ⟨hpV, h1⟩
  rcases p with ⟨x, y⟩
  dsimp only at hdeg
  push Not at hdeg
  obtain ⟨hx0, hx2h1, hp10, hp2hh, hy0_odd, hyh_even⟩ := hdeg
  have hp_not_strip : (x, y) ∉ elemStrip h k₀ := fun hs => (hStrip2 hs).2 hpU.1
  have hx_strip : x < 2 * k₀ ∨ 2 * k₀ + 1 < x := by
    have : ¬ (x = 2 * k₀ ∨ x = 2 * k₀ + 1) := fun hx => hp_not_strip ⟨hpV, hx⟩
    omega
  -- Neighbours of (x, y) are all in V(G₁)
  have h_nbr_in_G1 : ∀ q, elementaryWallAdj h (x, y) q → q ∈ V(G₁) := by
    intro q hadj
    by_cases hqU : q ∈ V(G₁) \ V(G₂)
    · exact hqU.1
    · exact (mem_separation_inter_of_adj hsep ⟨hadj, rfl⟩ hpU hqU).1
  have hadj_L : elementaryWallAdj h (x, y) (x - 1, y) :=
    (elementaryWallAdj_iff_of_not_deg2 hh he hpV hp_not_deg2 _).mpr (Or.inl rfl)
  have hadj_R : elementaryWallAdj h (x, y) (x + 1, y) :=
    (elementaryWallAdj_iff_of_not_deg2 hh he hpV hp_not_deg2 _).mpr (Or.inr (Or.inl rfl))
  have hadj_V : elementaryWallAdj h (x, y) (elemWallVertNbr (x, y)) :=
    (elementaryWallAdj_iff_of_not_deg2 hh he hpV hp_not_deg2 _).mpr (Or.inr (Or.inr rfl))
  have hL_G1 : (x - 1, y) ∈ V(G₁) := h_nbr_in_G1 _ hadj_L
  have hR_G1 : (x + 1, y) ∈ V(G₁) := h_nbr_in_G1 _ hadj_R
  have hV_G1 : elemWallVertNbr (x, y) ∈ V(G₁) := h_nbr_in_G1 _ hadj_V
  have hLV : (x - 1, y) ∈ elementaryWallVerts h := hadj_L.2.1
  have hRV : (x + 1, y) ∈ elementaryWallVerts h := hadj_R.2.1
  have hVV : elemWallVertNbr (x, y) ∈ elementaryWallVerts h := hadj_V.2.1
  have hx_bound : 1 ≤ x ∧ x ≤ 2 * h := by
    have := hpV.1
    omega
  let y' : ℕ := if Odd (x + y) then y + 1 else y - 1
  have hV_eq : elemWallVertNbr (x, y) = (x, y') := by
    unfold elemWallVertNbr
    dsimp only [y']
    split_ifs <;> rfl
  have hVV' : (x, y') ∈ elementaryWallVerts h := hV_eq ▸ hVV
  have hV_G1' : (x, y') ∈ V(G₁) := hV_eq ▸ hV_G1
  have hy'_ne : y' ≠ y ∧ y' ≤ h := by
    have hy'h : y' ≤ h := hVV'.2.1
    refine ⟨?_, hy'h⟩
    dsimp only [y']
    split_ifs with hodd
    · omega
    · have hy_ne_0 : y ≠ 0 := by
        intro hy0
        subst hy0
        exact hodd (by rw [Nat.odd_iff]; have := hy0_odd rfl; rw [Nat.even_iff] at this; omega)
      omega
  by_cases hy_int : 0 < y ∧ y < h
  · -- Case 1: 0 < y < h
    let y'' : ℕ := if Odd (x + y) then y - 1 else y + 1
    have hy''_props : y'' ≤ h ∧ y'' ≠ y ∧ y'' ≠ y' := by
      dsimp only [y', y'']
      split_ifs <;> omega
    have hadj_Ly'' : elementaryWallAdj h (x - 1, y) (x - 1, y'') := by
      have h_qV : (x - 1, y'') ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy''_props.1, ?_, ?_⟩
        · simp only [ne_eq, Prod.mk.injEq, not_and]
          intro hx1 hy''0
          dsimp only [y''] at hy''0
          split_ifs at hy''0 with hodd
          rw [Nat.odd_iff] at hodd
          omega
        · simp only [ne_eq, Prod.mk.injEq]; omega
      refine ⟨hLV, h_qV, Or.inr ⟨rfl, ?_⟩⟩
      dsimp only [y'']
      split_ifs with hodd
      · right; refine ⟨by omega, ?_⟩
        rw [Nat.odd_iff] at hodd ⊢; omega
      · left; refine ⟨rfl, ?_⟩
        rw [Nat.odd_iff] at hodd ⊢; omega
    have hadj_Ry'' : elementaryWallAdj h (x + 1, y) (x + 1, y'') := by
      have h_qV : (x + 1, y'') ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy''_props.1, ?_, ?_⟩
        · simp only [ne_eq, Prod.mk.injEq]; omega
        · simp only [ne_eq, Prod.mk.injEq, not_and]
          intro hx1 hy''h
          dsimp only [y''] at hy''h
          split_ifs at hy''h with hodd
          · omega
          · have hyh1 : y = h - 1 := by omega
            have hx2h : x = 2 * h := by omega
            have hh_ev := Nat.even_iff.mp he
            have hodd' : Odd (x + y) := by rw [Nat.odd_iff]; omega
            exact hodd hodd'
      refine ⟨hRV, h_qV, Or.inr ⟨rfl, ?_⟩⟩
      dsimp only [y'']
      split_ifs with hodd
      · right; refine ⟨by omega, ?_⟩
        rw [Nat.odd_iff] at hodd ⊢; omega
      · left; refine ⟨rfl, ?_⟩
        rw [Nat.odd_iff] at hodd ⊢; omega
    obtain ⟨q₂, hq₂R, hq₂S⟩ := elemRow_inter_elemStrip_nonempty hh hy'_ne.2 hk₀
    obtain ⟨q₃, hq₃R, hq₃S⟩ := elemRow_inter_elemStrip_nonempty hh hy''_props.1 hk₀
    rcases hx_strip with hx_lt | hx_gt
    · -- Subcase 1a: x < 2 * k₀
      set C₁ := elemRowInterval h y (x + 1) (2 * h + 1)
      set C₂ := elemRow h y'
      set C₃ := {(x - 1, y)} ∪ elemRow h y''
      have hC1 : IsElemWallConn h C₁ :=
        isElemWallConn_elemRowInterval (by omega) (by omega) le_rfl (by omega) (by omega)
      have hC2 : IsElemWallConn h C₂ := isElemWallConn_elemRow hh hy'_ne.2
      have hC3 : IsElemWallConn h C₃ :=
        (isElemWallConn_singleton hLV).union_of_adj
          (isElemWallConn_elemRow hh hy''_props.1) (mem_singleton _) ⟨hadj_Ly''.2.1, rfl⟩ hadj_Ly''
      have hd12 : Disjoint C₁ C₂ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, _, _⟩ ⟨_, hzy'⟩; omega
      have hd13 : Disjoint C₁ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, hzx, _⟩ (rfl | ⟨_, hzy''⟩)
        · dsimp only at hzx; omega
        · omega
      have hd23 : Disjoint C₂ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy'⟩ (rfl | ⟨_, hzy''⟩)
        · dsimp only at hzy'; omega
        · omega
      have hq₁V : (2 * k₀, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, by omega, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hq₁C : (2 * k₀, y) ∈ C₁ := ⟨hq₁V, rfl, by omega, by omega⟩
      have hq₁S : (2 * k₀, y) ∈ elemStrip h k₀ := ⟨hq₁V, Or.inl rfl⟩
      exact three_paths_contradiction hsep hcard hC1 hC2 hC3 hd12 hd13 hd23
        ⟨hRV, rfl, le_rfl, hRV.1⟩ hR_G1 hq₁C (hStrip2 hq₁S)
        ⟨hVV', rfl⟩ hV_G1' hq₂R (hStrip2 hq₂S)
        (Or.inl rfl) hL_G1 (Or.inr hq₃R) (hStrip2 hq₃S)
    · -- Subcase 1b: 2 * k₀ + 1 < x
      set C₁ := elemRowInterval h y 0 (x - 1)
      set C₂ := elemRow h y'
      set C₃ := {(x + 1, y)} ∪ elemRow h y''
      have hC1 : IsElemWallConn h C₁ :=
        isElemWallConn_elemRowInterval (by omega) (by omega) (by omega) (by omega) (by omega)
      have hC2 : IsElemWallConn h C₂ := isElemWallConn_elemRow hh hy'_ne.2
      have hC3 : IsElemWallConn h C₃ :=
        (isElemWallConn_singleton hRV).union_of_adj
          (isElemWallConn_elemRow hh hy''_props.1) (mem_singleton _) ⟨hadj_Ry''.2.1, rfl⟩ hadj_Ry''
      have hd12 : Disjoint C₁ C₂ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, _, _⟩ ⟨_, hzy'⟩; omega
      have hd13 : Disjoint C₁ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, _, hzx⟩ (rfl | ⟨_, hzy''⟩)
        · dsimp only at hzx; omega
        · omega
      have hd23 : Disjoint C₂ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy'⟩ (rfl | ⟨_, hzy''⟩)
        · dsimp only at hzy'; omega
        · omega
      have hq₁V : (2 * k₀ + 1, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, by omega, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hq₁C : (2 * k₀ + 1, y) ∈ C₁ := ⟨hq₁V, rfl, by omega, by omega⟩
      have hq₁S : (2 * k₀ + 1, y) ∈ elemStrip h k₀ := ⟨hq₁V, Or.inr rfl⟩
      exact three_paths_contradiction hsep hcard hC1 hC2 hC3 hd12 hd13 hd23
        ⟨hLV, rfl, by omega, le_rfl⟩ hL_G1 hq₁C (hStrip2 hq₁S)
        ⟨hVV', rfl⟩ hV_G1' hq₂R (hStrip2 hq₂S)
        (Or.inl rfl) hR_G1 (Or.inr hq₃R) (hStrip2 hq₃S)
  · -- Case 2: y = 0 or y = h
    have hy_bd : y = 0 ∨ y = h := by
      have := hpV.2.1; omega
    have hx_bounds : 2 ≤ x ∧ x ≤ 2 * h - 1 := by
      rcases hy_bd with rfl | hy_eq_h
      · have hodd : x % 2 = 1 := by
          have := hy0_odd rfl
          rw [Nat.even_iff] at this
          omega
        have hx1 : x ≠ 1 := fun h1 => hp10 (Prod.ext h1 rfl)
        omega
      · have hev : x % 2 = 0 := by
          have := hyh_even hy_eq_h
          rw [Nat.odd_iff] at this
          omega
        have hx2h : x ≠ 2 * h := fun h2h => hp2hh (Prod.ext h2h hy_eq_h)
        omega
    rcases hx_strip with hx_lt | hx_gt
    · -- Subcase 2a: x < 2 * k₀ (so k₀ ≥ 2)
      set C₁ := elemRowInterval h y (x + 1) (if y = h then 2 * h else 2 * h + 1)
      set C₂ := elemRowInterval h y' x (if y' = h then 2 * h else 2 * h + 1)
      set C₃ := elemRowInterval h y 1 (x - 1) ∪ elemStrip h 0
      have hC1 : IsElemWallConn h C₁ := by
        refine isElemWallConn_elemRowInterval hpV.2.1 ?_ ?_ (by omega) ?_
        · split_ifs <;> omega
        · split_ifs <;> omega
        · intro hyh; simp [hyh]
      have hC2 : IsElemWallConn h C₂ := by
        refine isElemWallConn_elemRowInterval hy'_ne.2 ?_ ?_ (by omega) ?_
        · split_ifs <;> omega
        · split_ifs <;> omega
        · intro hyh; simp [hyh]
      have h1y_V : (1, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hpV.2.1, by simp, ?_⟩
        simp only [ne_eq, Prod.mk.injEq]; omega
      have hC3 : IsElemWallConn h C₃ := by
        refine (isElemWallConn_elemRowInterval hpV.2.1 (by omega) (by omega)
          (by omega) (by omega)).union_of_inter
          (isElemWallConn_elemStrip hh he (by omega))
          ⟨h1y_V, rfl, le_rfl, by omega⟩ ⟨h1y_V, Or.inr rfl⟩
      have hd12 : Disjoint C₁ C₂ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, _, _⟩ ⟨_, hzy', _, _⟩; omega
      have hd13 : Disjoint C₁ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, hzx, _⟩ (⟨_, _, _, hzx'⟩ | ⟨_, hzs⟩) <;> omega
      have hd23 : Disjoint C₂ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy', hzx, _⟩ (⟨_, hzy, _, _⟩ | ⟨_, hzs⟩) <;> omega
      have hq₁V : (2 * k₀, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hpV.2.1, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hq₁C : (2 * k₀, y) ∈ C₁ := by
        refine ⟨hq₁V, rfl, by omega, ?_⟩
        split_ifs <;> omega
      have hq₂V : (2 * k₀, y') ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy'_ne.2, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hq₂C : (2 * k₀, y') ∈ C₂ := by
        refine ⟨hq₂V, rfl, by omega, ?_⟩
        split_ifs <;> omega
      have hq₃V : (1, y₀) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy₀, by simp, ?_⟩
        simp only [ne_eq, Prod.mk.injEq]; omega
      exact three_paths_contradiction hsep hcard hC1 hC2 hC3 hd12 hd13 hd23
        ⟨hRV, rfl, le_rfl, by split_ifs <;> omega⟩ hR_G1 hq₁C (hStrip2 ⟨hq₁V, Or.inl rfl⟩)
        ⟨hVV', rfl, le_rfl, by split_ifs <;> omega⟩ hV_G1'
        hq₂C (hStrip2 ⟨hq₂V, Or.inl rfl⟩)
        (Or.inl ⟨hLV, rfl, by omega, le_rfl⟩) hL_G1
        (Or.inr ⟨hq₃V, Or.inr rfl⟩) (hRow2 ⟨hq₃V, rfl⟩)
    · -- Subcase 2b: 2 * k₀ + 1 < x (so k₀ < h)
      set C₁ := elemRowInterval h y (if y = 0 then 1 else 0) (x - 1)
      set C₂ := elemRowInterval h y' (if y' = 0 then 1 else 0) x
      set C₃ := elemRowInterval h y (x + 1) (2 * h) ∪ elemStrip h h
      have hC1 : IsElemWallConn h C₁ := by
        refine isElemWallConn_elemRowInterval hpV.2.1 ?_ (by omega) ?_ (by omega)
        · split_ifs <;> omega
        · intro hy0; simp [hy0]
      have hC2 : IsElemWallConn h C₂ := by
        refine isElemWallConn_elemRowInterval hy'_ne.2 ?_ (by omega) ?_ (by omega)
        · split_ifs <;> omega
        · intro hy0; simp [hy0]
      have h2hy_V : (2 * h, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hpV.2.1, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hC3 : IsElemWallConn h C₃ := by
        refine (isElemWallConn_elemRowInterval hpV.2.1 (by omega) (by omega)
          (by omega) (by omega)).union_of_inter
          (isElemWallConn_elemStrip hh he le_rfl)
          ⟨h2hy_V, rfl, by omega, le_rfl⟩ ⟨h2hy_V, Or.inl rfl⟩
      have hd12 : Disjoint C₁ C₂ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, _, _⟩ ⟨_, hzy', _, _⟩; omega
      have hd13 : Disjoint C₁ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy, _, hzx⟩ (⟨_, _, hzx', _⟩ | ⟨_, hzs⟩) <;> omega
      have hd23 : Disjoint C₂ C₃ := by
        rw [disjoint_left]
        rintro z ⟨_, hzy', _, hzx⟩ (⟨_, hzy, _, _⟩ | ⟨_, hzs⟩) <;> omega
      have hq₁V : (2 * k₀ + 1, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hpV.2.1, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hq₁C : (2 * k₀ + 1, y) ∈ C₁ := by
        refine ⟨hq₁V, rfl, ?_, by omega⟩
        split_ifs <;> omega
      have hq₂V : (2 * k₀ + 1, y') ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy'_ne.2, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      have hq₂C : (2 * k₀ + 1, y') ∈ C₂ := by
        refine ⟨hq₂V, rfl, ?_, by omega⟩
        split_ifs <;> omega
      have hq₃V : (2 * h, y₀) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy₀, ?_, ?_⟩ <;> (simp only [ne_eq, Prod.mk.injEq]; omega)
      exact three_paths_contradiction hsep hcard hC1 hC2 hC3 hd12 hd13 hd23
        ⟨hLV, rfl, by split_ifs <;> omega, le_rfl⟩ hL_G1 hq₁C (hStrip2 ⟨hq₁V, Or.inr rfl⟩)
        ⟨hVV', rfl, by split_ifs <;> omega, le_rfl⟩ hV_G1'
        hq₂C (hStrip2 ⟨hq₂V, Or.inr rfl⟩)
        (Or.inl ⟨hRV, rfl, le_rfl, by omega⟩) hR_G1
        (Or.inr ⟨hq₃V, Or.inl rfl⟩) (hRow2 ⟨hq₃V, rfl⟩)

/-! ## 5. `elementaryWall h` and `W.graph` are Subdivisions of Simple 3-Connected Graphs -/

lemma sep_thin_elementaryWall {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {G₁ G₂ : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))}
    (hsep : IsGraphSeparation (elementaryWall h) G₁ G₂)
    (hcard : (V(G₁) ∩ V(G₂)).ncard ≤ 2) :
    Thin (elementaryWall h) G₁ G₂ ∨ Thin (elementaryWall h) G₂ G₁ := by
  set X := V(G₁) ∩ V(G₂)
  have hX_fin : X.Finite :=
    (finite_elementaryWallVerts h).subset fun p hp => hsep.1.vertexSet_mono hp.1
  obtain ⟨y₀, hy₀, hdR⟩ := exists_disjoint_elemRow hh hX_fin hcard
  obtain ⟨k₀, hk₀, hdS⟩ := exists_disjoint_elemStrip hh hX_fin hcard
  obtain ⟨r₀, hr₀R, hr₀S⟩ := elemRow_inter_elemStrip_nonempty hh hy₀ hk₀
  set B₀ := elemRow h y₀ ∪ elemStrip h k₀
  have hB₀_conn : IsElemWallConn h B₀ :=
    (isElemWallConn_elemRow hh hy₀).union_of_inter
      (isElemWallConn_elemStrip hh he hk₀) hr₀R hr₀S
  have hdB₀ : Disjoint B₀ X := hdR.union_left hdS
  have hr₀V : r₀ ∈ V(G₁) ∪ V(G₂) := hsep.2.2.1 ▸ hr₀R.1
  have hr₀_not_X : r₀ ∉ X := disjoint_left.mp hdB₀ (Or.inl hr₀R)
  rcases hr₀V with hr₀1 | hr₀2
  · right
    have hsep' : IsGraphSeparation (elementaryWall h) G₂ G₁ :=
      ⟨hsep.2.1, hsep.1, union_comm V(G₁) V(G₂) ▸ hsep.2.2.1,
        union_comm E(G₁) E(G₂) ▸ hsep.2.2.2.1, hsep.2.2.2.2.symm⟩
    have hcard' : (V(G₂) ∩ V(G₁)).ncard ≤ 2 := by
      rw [inter_comm]; exact hcard
    have hr₀_diff : r₀ ∈ V(G₁) \ V(G₂) :=
      ⟨hr₀1, fun hr₀2 => hr₀_not_X ⟨hr₀1, hr₀2⟩⟩
    have hB₀_sub : B₀ ⊆ V(G₁) \ V(G₂) := by
      intro q hqB
      have hqV : q ∈ V(G₁) ∪ V(G₂) := hsep.2.2.1 ▸ hB₀_conn.1 hqB
      have hq_not_X : q ∉ V(G₂) ∩ V(G₁) :=
        fun hqX => disjoint_left.mp hdB₀ hqB ⟨hqX.2, hqX.1⟩
      rcases hqV with hq1 | hq2
      · exact ⟨hq1, fun hq2 => hq_not_X ⟨hq2, hq1⟩⟩
      · exfalso
        obtain ⟨z, hzB, hzX⟩ := hB₀_conn.meets_separation_inter hsep' hqB hq2 (Or.inl hr₀R) hr₀_diff
        exact disjoint_left.mp hdB₀ hzB ⟨hzX.2, hzX.1⟩
    exact thin_of_diff_subset_isElemWallDeg2 hh he hsep' hcard' fun p hp =>
      isElemWallDeg2_of_mem_diff_of_disjoint_row_strip hh he hsep' hcard' hy₀ hk₀
        (subset_union_left.trans hB₀_sub) (subset_union_right.trans hB₀_sub) hp
  · left
    have hr₀_diff : r₀ ∈ V(G₂) \ V(G₁) :=
      ⟨hr₀2, fun hr₀1 => hr₀_not_X ⟨hr₀1, hr₀2⟩⟩
    have hB₀_sub : B₀ ⊆ V(G₂) \ V(G₁) := by
      intro q hqB
      have hqV : q ∈ V(G₁) ∪ V(G₂) := hsep.2.2.1 ▸ hB₀_conn.1 hqB
      have hq_not_X : q ∉ X := disjoint_left.mp hdB₀ hqB
      rcases hqV with hq1 | hq2
      · exfalso
        obtain ⟨z, hzB, hzX⟩ := hB₀_conn.meets_separation_inter hsep hqB hq1 (Or.inl hr₀R) hr₀_diff
        exact disjoint_left.mp hdB₀ hzB hzX
      · exact ⟨hq2, fun hq1 => hq_not_X ⟨hq1, hq2⟩⟩
    exact thin_of_diff_subset_isElemWallDeg2 hh he hsep hcard fun p hp =>
      isElemWallDeg2_of_mem_diff_of_disjoint_row_strip hh he hsep hcard hy₀ hk₀
        (subset_union_left.trans hB₀_sub) (subset_union_right.trans hB₀_sub) hp

/-- For every even `h ≥ 2`, `elementaryWall h` satisfies `GM14.Whitney.Good`. -/
theorem good_elementaryWall {h : ℕ} (hh : 2 ≤ h) (he : Even h) :
    Good (elementaryWall h) where
  finV := finite_elementaryWallVerts h
  finE := finite_elementaryWall_edges h
  no_loop := no_loop_elementaryWall h
  four := four_deg_ne_two_elementaryWall hh he
  sep _ _ hsep hcard := sep_thin_elementaryWall hh he hsep hcard

/-- Every `elementaryWall h` (`h ≥ 2` even) is a subdivision of a simple 3-connected graph. -/
theorem isSubdivisionOfSimpleThreeConnected_elementaryWall {h : ℕ} (hh : 2 ≤ h) (he : Even h) :
    GM14.IsSubdivisionOfSimpleThreeConnected (elementaryWall h) :=
  good_sub (good_elementaryWall hh he)

/-- Every wall `W : GM13.Wall α β` is a subdivision of a simple 3-connected graph
(Hypothesis (i) of Theorem 8.3). -/
theorem isSubdivisionOfSimpleThreeConnected_wall {α : Type u} {β : Type v}
    [Nonempty α] [Nonempty β] (W : Wall α β) :
    GM14.IsSubdivisionOfSimpleThreeConnected W.graph :=
  isSubdivision_wall_of_elementaryWall W
    (isSubdivisionOfSimpleThreeConnected_elementaryWall W.two_le_height W.even_height)

end GraphMinor.GM22




