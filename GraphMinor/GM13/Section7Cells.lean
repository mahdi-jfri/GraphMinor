module

public import GraphMinor.GM13.Section7Figure1
public import GraphMinor.GM07.Section11

/-!
# Graph Minors XIII, Section 7: the distance of a wall as a count on cells

The distance `d(s, t)` of a wall drawn as in Fig. 1 (page 89) is the least number of points of
the drawing on an arc from `s` to `t`. This file turns it into a count on cells, so that bounds on
`d` become counts on the bricks of the wall.

The plane is cut into *cells* by the integer grid: the integer points, the open unit segments
between them, and the open unit squares. A cell is named by a pair of integers: in each
coordinate, the even number `2 i` stands for the point `i`, and the odd number `2 i + 1` stands for
the open interval `(i, i + 1)` (`cellCode`). A cell `c` lies in the closure of a cell `c'`
exactly when `CellLE c c'`. A drawing made of whole cells, none of them a square, is given by its
set `𝒰` of cell names (`cellSet 𝒰`).

A *cell walk* is a sequence of cells in which each cell lies in the closure of the next or the next
lies in its closure. Its *cost* is the number of its cells, counted with repetition, that are in
the drawing. The two main results are:
* `planeWallDist_cellSet_le`: a cell walk from the cell of `s` to the cell of `t` gives an arc
  from `s` to `t` that meets the drawing in at most the cost of the walk;
* `exists_cellWalk_of_line`: an arc from `s` to `t` that meets the drawing in `k` points gives a
  cell walk of cost at most `k`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Topology Filter
open GraphMinor.Surface

/-! ## Cells of the line -/

/-- The name of the cell of the real line that contains `x`: `2 i` if `x = i` is an integer, and
`2 i + 1` if `i < x < i + 1`. -/
noncomputable def cellCode1 (x : ℝ) : ℤ :=
  open Classical in if ((⌊x⌋ : ℤ) : ℝ) = x then 2 * ⌊x⌋ else 2 * ⌊x⌋ + 1

theorem cellCode1_eq_even_iff {x : ℝ} {i : ℤ} : cellCode1 x = 2 * i ↔ x = i := by
  unfold cellCode1
  split_ifs with h
  · constructor
    · intro hc
      have : ⌊x⌋ = i := by omega
      rw [← h, this]
    · intro hx
      subst hx
      simp
  · constructor
    · intro hc; omega
    · intro hx
      subst hx
      simp at h

theorem cellCode1_eq_odd_iff {x : ℝ} {i : ℤ} :
    cellCode1 x = 2 * i + 1 ↔ (i : ℝ) < x ∧ x < i + 1 := by
  unfold cellCode1
  split_ifs with h
  · constructor
    · intro hc; omega
    · rintro ⟨h1, h2⟩
      exfalso
      rw [← h] at h1 h2
      have h3 : i < ⌊x⌋ := by exact_mod_cast h1
      have h4 : ⌊x⌋ < i + 1 := by exact_mod_cast h2
      omega
  · constructor
    · intro hc
      have hi : ⌊x⌋ = i := by omega
      have h1 := Int.floor_le x
      have h2 := Int.lt_floor_add_one x
      rw [hi] at h1 h2
      exact ⟨lt_of_le_of_ne h1 (by rw [← hi]; exact h), h2⟩
    · rintro ⟨h1, h2⟩
      have : ⌊x⌋ = i := Int.floor_eq_iff.mpr ⟨h1.le, h2⟩
      omega

/-- Every real number is an integer or lies strictly between two consecutive integers. -/
theorem cellCode1_cases (x : ℝ) :
    (∃ i : ℤ, cellCode1 x = 2 * i ∧ x = i) ∨
      (∃ i : ℤ, cellCode1 x = 2 * i + 1 ∧ (i : ℝ) < x ∧ x < i + 1) := by
  rcases Int.emod_two_eq_zero_or_one (cellCode1 x) with h | h
  · left
    refine ⟨cellCode1 x / 2, by omega, ?_⟩
    exact cellCode1_eq_even_iff.mp (by omega)
  · right
    refine ⟨cellCode1 x / 2, by omega, ?_⟩
    exact cellCode1_eq_odd_iff.mp (by omega)

/-- The cell named `a` contains the point `a / 2`. -/
theorem cellCode1_half (a : ℤ) : cellCode1 ((a : ℝ) / 2) = a := by
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    apply cellCode1_eq_even_iff.mpr
    push_cast
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
    apply cellCode1_eq_odd_iff.mpr
    push_cast
    constructor <;> linarith

private theorem lt_convex {i x y μ : ℝ} (hx : i < x) (hy : i < y) (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    i < (1 - μ) * x + μ * y := by
  rcases h1.lt_or_eq with h | rfl
  · nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hx), mul_nonneg h0 (sub_pos.2 hy).le]
  · simpa using hy

private theorem convex_lt {j x y μ : ℝ} (hx : x < j) (hy : y < j) (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (1 - μ) * x + μ * y < j := by
  have := lt_convex (neg_lt_neg hx) (neg_lt_neg hy) h0 h1
  linarith

/-- The cell named `a` lies in the closure of the cell named `b`: either `a = b`, or `b` is an
open interval and `a` is one of its two ends. -/
def CellLE1 (a b : ℤ) : Prop :=
  a = b ∨ (b % 2 = 1 ∧ (a = b - 1 ∨ a = b + 1))

theorem CellLE1.refl (a : ℤ) : CellLE1 a a := Or.inl rfl

theorem CellLE1.trans {a b e : ℤ} (h₁ : CellLE1 a b) (h₂ : CellLE1 b e) : CellLE1 a e := by
  unfold CellLE1 at *
  omega

/-- The open interval above the cell named `a`: itself if it is an interval, and the interval to
its right if it is a point. -/
def cellUp1 (a : ℤ) : ℤ := if a % 2 = 1 then a else a + 1

theorem cellLE1_cellUp1 (a : ℤ) : CellLE1 a (cellUp1 a) := by
  unfold CellLE1 cellUp1
  split_ifs <;> omega

theorem cellUp1_odd (a : ℤ) : cellUp1 a % 2 = 1 := by
  unfold cellUp1
  split_ifs <;> omega

/-- Points near `x` lie in cells whose closure contains the cell of `x`. -/
theorem eventually_cellLE1 (x : ℝ) : ∀ᶠ y in 𝓝 x, CellLE1 (cellCode1 x) (cellCode1 y) := by
  rcases cellCode1_cases x with ⟨i, hc, rfl⟩ | ⟨i, hc, h1, h2⟩
  · have hU : Ioo ((i : ℝ) - 1) (i + 1) ∈ 𝓝 (i : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hU] with y hy
    rw [hc]
    rcases lt_trichotomy y i with hlt | rfl | hgt
    · have : cellCode1 y = 2 * (i - 1) + 1 :=
        cellCode1_eq_odd_iff.mpr ⟨by push_cast; linarith [hy.1], by push_cast; linarith⟩
      rw [this]; unfold CellLE1; omega
    · rw [hc]; exact CellLE1.refl _
    · have : cellCode1 y = 2 * i + 1 := cellCode1_eq_odd_iff.mpr ⟨hgt, hy.2⟩
      rw [this]; unfold CellLE1; omega
  · filter_upwards [Ioo_mem_nhds h1 h2] with y hy
    rw [hc, cellCode1_eq_odd_iff.mpr hy]
    exact CellLE1.refl _

/-- If `x` is in a cell in the closure of the cell `b`, then every point of the segment from `x`
to `b / 2`, other than `x`, is in the cell `b`. -/
theorem cellCode1_lineMap {x : ℝ} {b : ℤ} (h : CellLE1 (cellCode1 x) b) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) : cellCode1 ((1 - μ) * x + μ * ((b : ℝ) / 2)) = b := by
  rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
    have hcb : cellCode1 x = 2 * k := by unfold CellLE1 at h; omega
    have hx : x = k := cellCode1_eq_even_iff.mp hcb
    subst hx
    apply cellCode1_eq_even_iff.mpr
    push_cast
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, b = 2 * j + 1 := ⟨b / 2, by omega⟩
    have hxr : (j : ℝ) ≤ x ∧ x ≤ j + 1 := by
      rcases cellCode1_cases x with ⟨i, hc, rfl⟩ | ⟨i, hc, h1, h2⟩
      · unfold CellLE1 at h
        have : i = j ∨ i = j + 1 := by omega
        rcases this with rfl | rfl
        · exact ⟨le_rfl, by linarith⟩
        · push_cast; exact ⟨by linarith, le_rfl⟩
      · unfold CellLE1 at h
        have : i = j := by omega
        subst this
        exact ⟨h1.le, h2.le⟩
    apply cellCode1_eq_odd_iff.mpr
    push_cast
    obtain ⟨hx1, hx2⟩ := hxr
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hμ1) (sub_nonneg.2 hx1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hμ1) (sub_nonneg.2 hx2)]

/-- A segment between two points of the same cell stays in that cell. -/
theorem cellCode1_convex {x y : ℝ} (hxy : cellCode1 x = cellCode1 y) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) : cellCode1 ((1 - μ) * x + μ * y) = cellCode1 x := by
  rcases cellCode1_cases x with ⟨i, hc, rfl⟩ | ⟨i, hc, h1, h2⟩
  · have hy : y = i := cellCode1_eq_even_iff.mp (hxy ▸ hc)
    subst hy
    rw [show (1 - μ) * (i : ℝ) + μ * i = i by ring]
  · obtain ⟨h3, h4⟩ := cellCode1_eq_odd_iff.mp (hxy ▸ hc)
    rw [hc]
    exact cellCode1_eq_odd_iff.mpr ⟨lt_convex h1 h3 hμ0 hμ1, convex_lt h2 h4 hμ0 hμ1⟩

/-! ## Cells of the plane -/

/-- The name of the cell of the plane that contains `p`. -/
noncomputable def cellCode (p : ℝ × ℝ) : ℤ × ℤ := (cellCode1 p.1, cellCode1 p.2)

/-- The cell `c` lies in the closure of the cell `d`. -/
def CellLE (c d : ℤ × ℤ) : Prop := CellLE1 c.1 d.1 ∧ CellLE1 c.2 d.2

/-- Two cells are related if one lies in the closure of the other. -/
def CellRel (c d : ℤ × ℤ) : Prop := CellLE c d ∨ CellLE d c

theorem CellLE.refl (c : ℤ × ℤ) : CellLE c c := ⟨CellLE1.refl _, CellLE1.refl _⟩

theorem CellLE.trans {c d e : ℤ × ℤ} (h₁ : CellLE c d) (h₂ : CellLE d e) : CellLE c e :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem CellRel.symm {c d : ℤ × ℤ} (h : CellRel c d) : CellRel d c := Or.symm h

/-- The point `(a / 2, b / 2)` of the cell named `(a, b)`. -/
noncomputable def cellCenter (c : ℤ × ℤ) : ℝ × ℝ := ((c.1 : ℝ) / 2, (c.2 : ℝ) / 2)

theorem cellCode_cellCenter (c : ℤ × ℤ) : cellCode (cellCenter c) = c := by
  simp [cellCode, cellCenter, cellCode1_half]

/-- A square is a cell whose two names are odd. -/
def IsSquareCell (c : ℤ × ℤ) : Prop := c.1 % 2 = 1 ∧ c.2 % 2 = 1

/-- A square whose closure contains the cell `c`. -/
def cellUp (c : ℤ × ℤ) : ℤ × ℤ := (cellUp1 c.1, cellUp1 c.2)

theorem cellLE_cellUp (c : ℤ × ℤ) : CellLE c (cellUp c) :=
  ⟨cellLE1_cellUp1 _, cellLE1_cellUp1 _⟩

theorem isSquareCell_cellUp (c : ℤ × ℤ) : IsSquareCell (cellUp c) :=
  ⟨cellUp1_odd _, cellUp1_odd _⟩

/-- Points near `p` lie in cells whose closure contains the cell of `p`. -/
theorem eventually_cellLE (p : ℝ × ℝ) : ∀ᶠ q in 𝓝 p, CellLE (cellCode p) (cellCode q) := by
  have h1 := (continuous_fst.tendsto p).eventually (eventually_cellLE1 p.1)
  have h2 := (continuous_snd.tendsto p).eventually (eventually_cellLE1 p.2)
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, hq2⟩

/-- Every point of the segment from `p` to the center of a cell `d` whose closure contains the
cell of `p` is `p` or lies in `d`. -/
theorem cellCode_of_mem_segment_center {p : ℝ × ℝ} {d : ℤ × ℤ} (h : CellLE (cellCode p) d)
    {z : ℝ × ℝ} (hz : z ∈ segment ℝ p (cellCenter d)) : z = p ∨ cellCode z = d := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  rcases hb.eq_or_lt with rfl | hb
  · left
    simp [show a = 1 by linarith]
  · right
    have ha' : a = 1 - b := by linarith
    subst ha'
    have hb1 : b ≤ 1 := by linarith
    refine Prod.ext ?_ ?_
    · simp only [cellCode, cellCenter, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      exact cellCode1_lineMap h.1 hb hb1
    · simp only [cellCode, cellCenter, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      exact cellCode1_lineMap h.2 hb hb1

/-- A segment between two points of the same cell stays in that cell. -/
theorem cellCode_of_mem_segment_same {p q : ℝ × ℝ} (hpq : cellCode p = cellCode q)
    {z : ℝ × ℝ} (hz : z ∈ segment ℝ p q) : cellCode z = cellCode p := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  have ha' : a = 1 - b := by linarith
  subst ha'
  have hb1 : b ≤ 1 := by linarith
  simp only [cellCode, Prod.mk.injEq] at hpq
  refine Prod.ext ?_ ?_
  · simp only [cellCode, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    exact cellCode1_convex hpq.1 hb hb1
  · simp only [cellCode, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact cellCode1_convex hpq.2 hb hb1

/-! ## Drawings made of cells, and cell walks -/

/-- The set of points of the plane whose cell is in `𝒰`. -/
def cellSet (𝒰 : Set (ℤ × ℤ)) : Set (ℝ × ℝ) := {p | cellCode p ∈ 𝒰}

/-- `1` if the cell `c` is in `𝒰`, and `0` otherwise. -/
noncomputable def cellInd (𝒰 : Set (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  open Classical in if c ∈ 𝒰 then 1 else 0

theorem cellInd_of_mem {𝒰 : Set (ℤ × ℤ)} {c : ℤ × ℤ} (h : c ∈ 𝒰) : cellInd 𝒰 c = 1 := by
  simp [cellInd, h]

theorem cellInd_of_not_mem {𝒰 : Set (ℤ × ℤ)} {c : ℤ × ℤ} (h : c ∉ 𝒰) : cellInd 𝒰 c = 0 := by
  simp [cellInd, h]

/-- A walk of cells from `c` to `d`, each cell related to the next. -/
inductive CellWalk : ℤ × ℤ → ℤ × ℤ → Type
  | nil (c : ℤ × ℤ) : CellWalk c c
  | cons {c c' d : ℤ × ℤ} (h : CellRel c c') (w : CellWalk c' d) : CellWalk c d

namespace CellWalk

/-- The number of cells of the walk, counted with repetition, that are in `𝒰`. -/
noncomputable def cost (𝒰 : Set (ℤ × ℤ)) : {c d : ℤ × ℤ} → CellWalk c d → ℕ
  | c, _, nil _ => cellInd 𝒰 c
  | c, _, cons _ w => cellInd 𝒰 c + w.cost 𝒰

/-- The cost of the walk without its first cell. -/
noncomputable def costTail (𝒰 : Set (ℤ × ℤ)) : {c d : ℤ × ℤ} → CellWalk c d → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ w => w.cost 𝒰

/-- The cost of the walk without its last cell. -/
noncomputable def costInit (𝒰 : Set (ℤ × ℤ)) : {c d : ℤ × ℤ} → CellWalk c d → ℕ
  | _, _, nil _ => 0
  | c, _, cons _ w => cellInd 𝒰 c + w.costInit 𝒰

/-- Whether the walk has no step. -/
def isNil : {c d : ℤ × ℤ} → CellWalk c d → Bool
  | _, _, nil _ => true
  | _, _, cons _ _ => false

/-- The walk `w` followed by the walk `w'`. -/
def append : {c d e : ℤ × ℤ} → CellWalk c d → CellWalk d e → CellWalk c e
  | _, _, _, nil _, w' => w'
  | _, _, _, cons h w, w' => cons h (w.append w')

theorem cost_eq_ind_add_costTail (𝒰 : Set (ℤ × ℤ)) :
    ∀ {c d : ℤ × ℤ} (w : CellWalk c d), w.cost 𝒰 = cellInd 𝒰 c + w.costTail 𝒰
  | _, _, nil _ => by simp [cost, costTail]
  | _, _, cons _ _ => rfl

theorem cost_eq_costInit_add_ind (𝒰 : Set (ℤ × ℤ)) :
    ∀ {c d : ℤ × ℤ} (w : CellWalk c d), w.cost 𝒰 = w.costInit 𝒰 + cellInd 𝒰 d
  | _, _, nil _ => by simp [cost, costInit]
  | _, _, cons _ w => by
    simp only [cost, costInit, cost_eq_costInit_add_ind 𝒰 w]
    ring

theorem cost_append (𝒰 : Set (ℤ × ℤ)) :
    ∀ {c d e : ℤ × ℤ} (w : CellWalk c d) (w' : CellWalk d e),
      (w.append w').cost 𝒰 = w.costInit 𝒰 + w'.cost 𝒰
  | _, _, _, nil _, _ => by simp [append, costInit]
  | _, _, _, cons _ w, w' => by
    simp only [append, cost, costInit, cost_append 𝒰 w w']
    ring

theorem eq_of_isNil : ∀ {c d : ℤ × ℤ} (w : CellWalk c d), w.isNil = true → c = d
  | _, _, nil _, _ => rfl
  | _, _, cons _ _, h => by simp [isNil] at h

/-- A walk along which a potential `φ` grows by at most one when the walk enters a cell of `𝒰`,
and does not grow otherwise. The potential at the end is at most the potential at the start plus
the cost of the walk after its first cell. -/
theorem potential_le (𝒰 : Set (ℤ × ℤ)) (φ : ℤ × ℤ → ℤ)
    (hφ : ∀ c c', CellRel c c' → φ c' ≤ φ c + cellInd 𝒰 c') :
    ∀ {c d : ℤ × ℤ} (w : CellWalk c d), φ d ≤ φ c + w.costTail 𝒰
  | _, _, nil _ => by simp [costTail]
  | c, _, cons (c' := c') h w => by
    have h1 := potential_le 𝒰 φ hφ w
    have h2 := hφ c c' h
    have h3 := cost_eq_ind_add_costTail 𝒰 w
    simp only [costTail]
    push_cast [h3]
    linarith

end CellWalk

/-! ## From a cell walk to an arc -/

private theorem planeWallDist_le_ncard' {U : Set EuclideanPlane} {s t : EuclideanPlane}
    (hst : s ≠ t) {L : Set EuclideanPlane} (hL : IsLineWithEnds L s t) (hfin : (L ∩ U).Finite) :
    planeWallDist U s t ≤ (L ∩ U).ncard := by
  simp only [planeWallDist, hst, ↓reduceIte]
  exact Nat.sInf_le ⟨L, hL, hfin, rfl⟩

/-- **A cell walk gives a connected set.** Let `𝒰` contain no square. For a cell walk `w` from
the cell of `s` to the cell of `t`, there is a set joining `s` to `t` that meets `cellSet 𝒰` in
at most `w.cost 𝒰` points, unless `w` has no step and `s ≠ t` lie in one cell of `𝒰`.

The set goes from each cell of the walk to the next through the center of a square whose closure
contains both. A segment from a point to the center of a square containing it in its closure lies
in the square, except for the point, so it meets the drawing only at the point. -/
theorem exists_joinedIn_of_cellWalk {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) :
    ∀ {c d : ℤ × ℤ} (w : CellWalk c d) (s t : ℝ × ℝ), cellCode s = c → cellCode t = d →
      (w.isNil = true → c ∈ 𝒰 → s = t) →
      ∃ P : Set (ℝ × ℝ), JoinedIn P s t ∧ (P ∩ cellSet 𝒰).Finite ∧
        (P ∩ cellSet 𝒰).ncard ≤ w.cost 𝒰
  | _, _, .nil c, s, t, hs, ht, hnil => by
    by_cases hc : c ∈ 𝒰
    · have hst := hnil rfl hc
      subst hst
      refine ⟨{s}, JoinedIn.refl rfl, (finite_singleton s).subset inter_subset_left, ?_⟩
      calc (({s} : Set (ℝ × ℝ)) ∩ cellSet 𝒰).ncard ≤ ({s} : Set (ℝ × ℝ)).ncard :=
            ncard_le_ncard inter_subset_left (finite_singleton s)
        _ = 1 := ncard_singleton s
        _ = (CellWalk.nil c).cost 𝒰 := by simp [CellWalk.cost, cellInd_of_mem hc]
    · have hempty : segment ℝ s t ∩ cellSet 𝒰 = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro hz hzU
        have := cellCode_of_mem_segment_same (hs.trans ht.symm) hz
        exact hc (hs ▸ this ▸ hzU)
      refine ⟨segment ℝ s t, ?_, by rw [hempty]; exact finite_empty, by rw [hempty]; simp⟩
      exact (convex_segment s t).isPathConnected (nonempty_of_mem (left_mem_segment ℝ s t))
        |>.joinedIn s (left_mem_segment ℝ s t) t (right_mem_segment ℝ s t)
  | c, d, .cons (c' := c') hrel w, s, t, hs, ht, _ => by
    classical
    -- the square through which the set passes
    obtain ⟨Q, hcQ, hc'Q, hQ⟩ : ∃ Q, CellLE c Q ∧ CellLE c' Q ∧ IsSquareCell Q := by
      rcases hrel with h | h
      · exact ⟨cellUp c', h.trans (cellLE_cellUp c'), cellLE_cellUp c', isSquareCell_cellUp c'⟩
      · exact ⟨cellUp c, cellLE_cellUp c, h.trans (cellLE_cellUp c), isSquareCell_cellUp c⟩
    have hQU : Q ∉ 𝒰 := fun hmem => h𝒰 Q hmem hQ
    set s' : ℝ × ℝ := if cellCode t = c' then t else cellCenter c' with hs'
    have hs'c : cellCode s' = c' := by
      rw [hs']; split_ifs with h
      · exact h
      · exact cellCode_cellCenter c'
    have hnil' : w.isNil = true → c' ∈ 𝒰 → s' = t := by
      intro hn _
      have := CellWalk.eq_of_isNil w hn
      rw [hs', ite_eq_left_iff.mpr (fun hne => absurd (ht.trans this.symm) hne)]
    obtain ⟨P', hP'j, hP'fin, hP'card⟩ :=
      exists_joinedIn_of_cellWalk h𝒰 w s' t hs'c ht hnil'
    set q := cellCenter Q
    let P := segment ℝ s q ∪ segment ℝ q s' ∪ P'
    have hjoin1 : JoinedIn (segment ℝ s q) s q :=
      (convex_segment s q).isPathConnected (nonempty_of_mem (left_mem_segment ℝ s q))
        |>.joinedIn s (left_mem_segment ℝ s q) q (right_mem_segment ℝ s q)
    have hjoin2 : JoinedIn (segment ℝ q s') q s' :=
      (convex_segment q s').isPathConnected (nonempty_of_mem (left_mem_segment ℝ q s'))
        |>.joinedIn q (left_mem_segment ℝ q s') s' (right_mem_segment ℝ q s')
    have hP : JoinedIn P s t :=
      ((hjoin1.mono (subset_union_left.trans subset_union_left)).trans
        (hjoin2.mono (subset_union_right.trans subset_union_left))).trans
        (hP'j.mono subset_union_right)
    have hs'P' : s' ∈ P' := hP'j.mem.1
    -- the points of the drawing on `P`
    let A : Set (ℝ × ℝ) := if c ∈ 𝒰 then {s} else ∅
    have hsub : P ∩ cellSet 𝒰 ⊆ A ∪ (P' ∩ cellSet 𝒰) := by
      rintro z ⟨hzP, hzU⟩
      rcases hzP with (hz | hz) | hz
      · rcases cellCode_of_mem_segment_center (hs ▸ hcQ) hz with rfl | hzQ
        · left
          have hcU : c ∈ 𝒰 := hs ▸ hzU
          simp [A, hcU]
        · exact (hQU (hzQ ▸ hzU)).elim
      · rw [segment_symm] at hz
        rcases cellCode_of_mem_segment_center (hs'c ▸ hc'Q) hz with rfl | hzQ
        · exact Or.inr ⟨hs'P', hzU⟩
        · exact (hQU (hzQ ▸ hzU)).elim
      · exact Or.inr ⟨hz, hzU⟩
    have hAfin : A.Finite := by
      simp only [A]; split_ifs
      · exact finite_singleton s
      · exact finite_empty
    have hAcard : A.ncard = cellInd 𝒰 c := by
      simp only [A]; split_ifs with h
      · rw [ncard_singleton, cellInd_of_mem h]
      · rw [ncard_empty, cellInd_of_not_mem h]
    refine ⟨P, hP, (hAfin.union hP'fin).subset hsub, ?_⟩
    calc (P ∩ cellSet 𝒰).ncard ≤ (A ∪ (P' ∩ cellSet 𝒰)).ncard :=
          ncard_le_ncard hsub (hAfin.union hP'fin)
      _ ≤ A.ncard + (P' ∩ cellSet 𝒰).ncard := ncard_union_le _ _
      _ ≤ cellInd 𝒰 c + w.cost 𝒰 := by rw [hAcard]; exact Nat.add_le_add_left hP'card _
      _ = (CellWalk.cons hrel w).cost 𝒰 := rfl

/-- **Upper bound on the distance.** Let `𝒰` contain no square, and let `s ≠ t`. A cell walk
from the cell of `s` to the cell of `t` with at least one step bounds the distance `d(s, t)` of the
drawing `cellSet 𝒰` (moved to the plane by `fig1PlaneEquiv`) by its cost. -/
theorem planeWallDist_cellSet_le {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c)
    {s t : ℝ × ℝ} (hst : s ≠ t) (w : CellWalk (cellCode s) (cellCode t))
    (hw : w.isNil = true → cellCode s ∉ 𝒰) :
    planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) ≤
      w.cost 𝒰 := by
  obtain ⟨P, hPj, hPfin, hPcard⟩ := exists_joinedIn_of_cellWalk h𝒰 w s t rfl rfl
    (fun hn hc => (hw hn hc).elim)
  set e := fig1PlaneEquiv
  have hj : JoinedIn (e '' P) (e s) (e t) := hPj.map e.continuous.continuousOn
  have hne : e s ≠ e t := e.injective.ne hst
  obtain ⟨L, hLsub, hL⟩ := ((GraphMinor.GM07.joinedIn_iff_eq_or_exists_isLineWithEnds
    hj.mem.1 hj.mem.2).mp hj).resolve_left hne
  have hsub : L ∩ e '' cellSet 𝒰 ⊆ e '' (P ∩ cellSet 𝒰) := by
    rintro z ⟨hzL, x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hLsub hzL
    rw [e.injective hyx] at hy
    exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hfin : (e '' (P ∩ cellSet 𝒰)).Finite := hPfin.image e
  calc planeWallDist (e '' cellSet 𝒰) (e s) (e t) ≤ (L ∩ e '' cellSet 𝒰).ncard :=
        planeWallDist_le_ncard' hne hL (hfin.subset hsub)
    _ ≤ (e '' (P ∩ cellSet 𝒰)).ncard := ncard_le_ncard hsub hfin
    _ = (P ∩ cellSet 𝒰).ncard := ncard_image_of_injective _ e.injective
    _ ≤ w.cost 𝒰 := hPcard

/-! ## From an arc to a cell walk -/

namespace CellWalk

/-- A walk of cost zero can be extended by a step to a cell outside `𝒰`, keeping cost zero. -/
theorem exists_extend_free {𝒰 : Set (ℤ × ℤ)} {c d d' : ℤ × ℤ} (w : CellWalk c d)
    (hw : w.cost 𝒰 = 0) (h : CellRel d d') (hd' : d' ∉ 𝒰) :
    ∃ w' : CellWalk c d', w'.cost 𝒰 = 0 := by
  refine ⟨w.append (cons h (nil d')), ?_⟩
  have h1 := cost_eq_costInit_add_ind 𝒰 w
  rw [cost_append]
  simp only [cost, cellInd_of_not_mem hd']
  omega

end CellWalk

/-- **Connected free sets.** If a preconnected set `K` meets no cell of `𝒰`, then the cells of
any two of its points are joined by a cell walk of cost zero.

The points of `K` whose cell is reached from the cell of `x` by a walk of cost zero, and the other
points of `K`, are both open in `K`, because points near a point `z` lie in cells whose closure
contains the cell of `z`. -/
theorem exists_cellWalk_of_isPreconnected {𝒰 : Set (ℤ × ℤ)} {K : Set (ℝ × ℝ)}
    (hK : IsPreconnected K) (hfree : ∀ z ∈ K, cellCode z ∉ 𝒰) {x y : ℝ × ℝ}
    (hx : x ∈ K) (hy : y ∈ K) : ∃ w : CellWalk (cellCode x) (cellCode y), w.cost 𝒰 = 0 := by
  classical
  let Reach : ℤ × ℤ → Prop := fun c => ∃ w : CellWalk (cellCode x) c, w.cost 𝒰 = 0
  have hN : ∀ z : ℝ × ℝ, ∃ N : Set (ℝ × ℝ),
      (∀ q ∈ N, CellLE (cellCode z) (cellCode q)) ∧ IsOpen N ∧ z ∈ N :=
    fun z => eventually_nhds_iff.mp (eventually_cellLE z)
  choose N hNle hNopen hNmem using hN
  let u := ⋃ z ∈ {z | z ∈ K ∧ Reach (cellCode z)}, N z
  let v := ⋃ z ∈ {z | z ∈ K ∧ ¬ Reach (cellCode z)}, N z
  have hu : IsOpen u := isOpen_biUnion fun z _ => hNopen z
  have hv : IsOpen v := isOpen_biUnion fun z _ => hNopen z
  have hcov : K ⊆ u ∪ v := by
    intro z hz
    by_cases hr : Reach (cellCode z)
    · exact Or.inl (mem_biUnion ⟨hz, hr⟩ (hNmem z))
    · exact Or.inr (mem_biUnion ⟨hz, hr⟩ (hNmem z))
  have hdisj : K ∩ (u ∩ v) = ∅ := by
    ext q
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hq hqu hqv
    obtain ⟨z₁, ⟨_, hr₁⟩, hq₁⟩ := mem_iUnion₂.mp hqu
    obtain ⟨z₂, ⟨hz₂, hr₂⟩, hq₂⟩ := mem_iUnion₂.mp hqv
    obtain ⟨w₁, hw₁⟩ := hr₁
    obtain ⟨w, hw⟩ := CellWalk.exists_extend_free w₁ hw₁ (Or.inl (hNle z₁ q hq₁)) (hfree q hq)
    exact hr₂ (CellWalk.exists_extend_free w hw (Or.inr (hNle z₂ q hq₂)) (hfree z₂ hz₂))
  have hxr : Reach (cellCode x) :=
    ⟨CellWalk.nil _, by simp [CellWalk.cost, cellInd_of_not_mem (hfree x hx)]⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp hK u v hu hv hcov hdisj with hKu | hKv
  · obtain ⟨z, ⟨hz, ⟨w, hw⟩⟩, hyz⟩ := mem_iUnion₂.mp (hKu hy)
    exact CellWalk.exists_extend_free w hw (Or.inl (hNle z y hyz)) (hfree y hy)
  · obtain ⟨z, ⟨hz, hr⟩, hxz⟩ := mem_iUnion₂.mp (hKv hx)
    obtain ⟨w, hw⟩ := hxr
    exact (hr (CellWalk.exists_extend_free w hw (Or.inr (hNle z x hxz)) (hfree z hz))).elim

/-- The free part of a path: if a path on `[a, b]` meets no cell of `𝒰`, a cell walk of cost
zero joins the cells of its ends. -/
private theorem exists_cellWalk_of_path_free {𝒰 : Set (ℤ × ℤ)} {γ : ℝ → ℝ × ℝ}
    (hγ : Continuous γ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ x ∈ Icc a b, γ x ∉ cellSet 𝒰) :
    ∃ w : CellWalk (cellCode (γ a)) (cellCode (γ b)), w.cost 𝒰 = 0 :=
  exists_cellWalk_of_isPreconnected (isPreconnected_Icc.image γ hγ.continuousOn)
    (by rintro _ ⟨x, hx, rfl⟩; exact hS x hx)
    (mem_image_of_mem γ (left_mem_Icc.2 hab)) (mem_image_of_mem γ (right_mem_Icc.2 hab))

/-- **A path gives a cell walk.** If a path `γ` on `[a, b]` meets `cellSet 𝒰` at no more than
`n` times, then a cell walk of cost at most `n` joins the cells of its ends.

The proof takes the last time `τ` at which the path meets the drawing. After `τ` the path is free.
Just before `τ` the path is free too and lies in cells whose closure contains the cell of `γ τ`,
and the part of the path before that has one fewer time on the drawing. -/
theorem exists_cellWalk_of_path {𝒰 : Set (ℤ × ℤ)} {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ)
    (n : ℕ) (a : ℝ) : ∀ b : ℝ, a ≤ b →
      {x | x ∈ Icc a b ∧ γ x ∈ cellSet 𝒰}.Finite →
      {x | x ∈ Icc a b ∧ γ x ∈ cellSet 𝒰}.ncard ≤ n →
      ∃ w : CellWalk (cellCode (γ a)) (cellCode (γ b)), w.cost 𝒰 ≤ n := by
  induction n with
  | zero =>
    intro b hab hfin hcard
    have hempty := (ncard_eq_zero hfin).mp (Nat.le_zero.mp hcard)
    obtain ⟨w, hw⟩ := exists_cellWalk_of_path_free (𝒰 := 𝒰) hγ hab
      (fun x hx hxU => (eq_empty_iff_forall_notMem.mp hempty) x ⟨hx, hxU⟩)
    exact ⟨w, hw.le⟩
  | succ m ih =>
    intro b hab hfin hcard
    set S := {x | x ∈ Icc a b ∧ γ x ∈ cellSet 𝒰} with hSdef
    by_cases hne : S.Nonempty
    swap
    · obtain ⟨w, hw⟩ := exists_cellWalk_of_path_free (𝒰 := 𝒰) hγ hab
        (fun x hx hxU => hne ⟨x, hx, hxU⟩)
      exact ⟨w, by omega⟩
    set τ := sSup S
    have hτS : τ ∈ S := hne.csSup_mem hfin
    have hτmax : ∀ x ∈ S, x ≤ τ := fun x hx => le_csSup hfin.bddAbove hx
    obtain ⟨⟨haτ, hτb⟩, hτU⟩ := hτS
    have hev : ∀ᶠ x in 𝓝 τ, CellLE (cellCode (γ τ)) (cellCode (γ x)) :=
      (hγ.tendsto τ).eventually (eventually_cellLE (γ τ))
    -- the walk from the cell of `γ τ` to the cell of `γ b`
    obtain ⟨wR, hwR⟩ : ∃ w : CellWalk (cellCode (γ τ)) (cellCode (γ b)), w.cost 𝒰 ≤ 1 := by
      rcases hτb.lt_or_eq with hlt | heq
      · obtain ⟨t₁, ⟨hle, ht₁b⟩, hτt₁⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
          (Ioo_mem_nhdsGT hlt)).and self_mem_nhdsWithin |>.exists
        obtain ⟨wf, hwf⟩ := exists_cellWalk_of_path_free (𝒰 := 𝒰) hγ ht₁b.2.le
          (fun x hx hxU => by
            have := hτmax x ⟨⟨haτ.trans (le_of_lt (lt_of_lt_of_le hτt₁ hx.1)), hx.2⟩, hxU⟩
            exact absurd (lt_of_lt_of_le hτt₁ hx.1) (not_lt.mpr this))
        refine ⟨CellWalk.cons (Or.inl hle) wf, ?_⟩
        simp only [CellWalk.cost, hwf, add_zero]
        unfold cellInd; split_ifs <;> omega
      · rw [heq]
        refine ⟨CellWalk.nil _, ?_⟩
        simp only [CellWalk.cost]
        unfold cellInd; split_ifs <;> omega
    rcases haτ.lt_or_eq with hlt | heq
    swap
    · rw [heq]
      exact ⟨wR, by omega⟩
    -- a free time `t₀` just before `τ`
    have hfin' : (S \ {τ}).Finite := hfin.sdiff
    have hall : ∀ᶠ t in 𝓝[<] τ, ∀ x ∈ S \ {τ}, x < t := by
      refine (hfin'.eventually_all).mpr fun x hx => ?_
      have hxτ : x < τ := lt_of_le_of_ne (hτmax x hx.1) hx.2
      filter_upwards [Ioo_mem_nhdsLT hxτ] with t ht using ht.1
    obtain ⟨t₀, ⟨hle0, ht₀⟩, hsep⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT hlt)).and hall |>.exists
    have hsub : {x | x ∈ Icc a t₀ ∧ γ x ∈ cellSet 𝒰} ⊆ S \ {τ} := by
      rintro x ⟨⟨hax, hxt⟩, hxU⟩
      refine ⟨⟨⟨hax, hxt.trans (ht₀.2.le.trans hτb)⟩, hxU⟩, ?_⟩
      rintro rfl
      exact absurd (hxt.trans_lt ht₀.2) (lt_irrefl _)
    have hcard0 : {x | x ∈ Icc a t₀ ∧ γ x ∈ cellSet 𝒰}.ncard ≤ m := by
      have h1 := ncard_le_ncard hsub hfin'
      have h2 := ncard_sdiff_singleton_of_mem (s := S) (a := τ) ⟨⟨haτ, hτb⟩, hτU⟩
      omega
    obtain ⟨wL, hwL⟩ := ih t₀ ht₀.1.le (hfin'.subset hsub) hcard0
    have ht₀free : cellCode (γ t₀) ∉ 𝒰 := by
      intro hU
      have := hsep t₀ ⟨⟨⟨ht₀.1.le, ht₀.2.le.trans hτb⟩, hU⟩, ht₀.2.ne⟩
      exact lt_irrefl _ this
    refine ⟨wL.append (CellWalk.cons (Or.inr hle0) wR), ?_⟩
    have h1 := CellWalk.cost_eq_costInit_add_ind 𝒰 wL
    rw [CellWalk.cost_append]
    simp only [CellWalk.cost, cellInd_of_not_mem ht₀free]
    omega

/-- **An arc gives a cell walk.** An arc `F` from `s` to `t` that meets the drawing
`fig1PlaneEquiv '' cellSet 𝒰` in finitely many points gives a cell walk from the cell of `s` to
the cell of `t` whose cost is at most the number of these points. -/
theorem exists_cellWalk_of_line {𝒰 : Set (ℤ × ℤ)} {F : Set EuclideanPlane}
    {s t : EuclideanPlane} (hF : IsLineWithEnds F s t)
    (hfin : (F ∩ fig1PlaneEquiv '' cellSet 𝒰).Finite) :
    ∃ w : CellWalk (cellCode (fig1PlaneEquiv.symm s)) (cellCode (fig1PlaneEquiv.symm t)),
      w.cost 𝒰 ≤ (F ∩ fig1PlaneEquiv '' cellSet 𝒰).ncard := by
  obtain ⟨f, hf0, hf1⟩ := hF
  set e := fig1PlaneEquiv
  let g : ℝ → EuclideanPlane := fun x => (f (projIcc (0 : ℝ) 1 zero_le_one x)).1
  have hg : Continuous g := continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  let γ : ℝ → ℝ × ℝ := fun x => e.symm (g x)
  have hγ : Continuous γ := e.symm.continuous.comp hg
  have hmaps : MapsTo g {x | x ∈ Icc (0 : ℝ) 1 ∧ γ x ∈ cellSet 𝒰} (F ∩ e '' cellSet 𝒰) := by
    rintro x ⟨_, hx⟩
    exact ⟨(f _).2, γ x, hx, e.apply_symm_apply _⟩
  have hinj : InjOn g {x | x ∈ Icc (0 : ℝ) 1 ∧ γ x ∈ cellSet 𝒰} := by
    rintro x ⟨hx, _⟩ y ⟨hy, _⟩ hxy
    have := f.injective (Subtype.ext hxy)
    rw [projIcc_of_mem _ hx, projIcc_of_mem _ hy] at this
    exact congrArg Subtype.val this
  have hSfin := Finite.of_injOn hmaps hinj hfin
  obtain ⟨w, hw⟩ := exists_cellWalk_of_path (𝒰 := 𝒰) hγ _ 0 1 zero_le_one hSfin le_rfl
  have hγ0 : γ 0 = e.symm s := by
    simp only [γ, g, projIcc_left]
    rw [← hf0]; rfl
  have hγ1 : γ 1 = e.symm t := by
    simp only [γ, g, projIcc_right]
    rw [← hf1]; rfl
  rw [← hγ0, ← hγ1]
  exact ⟨w, hw.trans (ncard_le_ncard_of_injOn g hmaps hinj hfin)⟩

/-! ## Consequences -/

theorem cellRel_succ_fst (a b : ℤ) : CellRel (a, b) (a + 1, b) := by
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · exact Or.inl ⟨Or.inr ⟨by omega, Or.inl (by omega)⟩, CellLE1.refl _⟩
  · exact Or.inr ⟨Or.inr ⟨h, Or.inr rfl⟩, CellLE1.refl _⟩

theorem cellRel_succ_snd (a b : ℤ) : CellRel (a, b) (a, b + 1) := by
  rcases Int.emod_two_eq_zero_or_one b with h | h
  · exact Or.inl ⟨CellLE1.refl _, Or.inr ⟨by omega, Or.inl (by omega)⟩⟩
  · exact Or.inr ⟨CellLE1.refl _, Or.inr ⟨h, Or.inr rfl⟩⟩

private theorem nonempty_cellWalk_fst (b : ℤ) :
    ∀ (k : ℕ) (a : ℤ), Nonempty (CellWalk (a, b) (a + k, b)) ∧
      Nonempty (CellWalk (a + k, b) (a, b))
  | 0, a => by
    simp only [Nat.cast_zero, add_zero]
    exact ⟨⟨CellWalk.nil _⟩, ⟨CellWalk.nil _⟩⟩
  | k + 1, a => by
    obtain ⟨⟨w₁⟩, ⟨w₂⟩⟩ := nonempty_cellWalk_fst b k (a + 1)
    have e : a + 1 + (k : ℤ) = a + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at w₁ w₂
    exact ⟨⟨CellWalk.cons (cellRel_succ_fst a b) w₁⟩,
      ⟨w₂.append (CellWalk.cons (cellRel_succ_fst a b).symm (CellWalk.nil _))⟩⟩

private theorem nonempty_cellWalk_snd (a : ℤ) :
    ∀ (k : ℕ) (b : ℤ), Nonempty (CellWalk (a, b) (a, b + k)) ∧
      Nonempty (CellWalk (a, b + k) (a, b))
  | 0, b => by
    simp only [Nat.cast_zero, add_zero]
    exact ⟨⟨CellWalk.nil _⟩, ⟨CellWalk.nil _⟩⟩
  | k + 1, b => by
    obtain ⟨⟨w₁⟩, ⟨w₂⟩⟩ := nonempty_cellWalk_snd a k (b + 1)
    have e : b + 1 + (k : ℤ) = b + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at w₁ w₂
    exact ⟨⟨CellWalk.cons (cellRel_succ_snd a b) w₁⟩,
      ⟨w₂.append (CellWalk.cons (cellRel_succ_snd a b).symm (CellWalk.nil _))⟩⟩

/-- Any two cells are joined by a cell walk. -/
theorem nonempty_cellWalk (c d : ℤ × ℤ) : Nonempty (CellWalk c d) := by
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := d
  have h1 : Nonempty (CellWalk (a, b) (a', b)) := by
    rcases le_total a a' with h | h
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
      have := (nonempty_cellWalk_fst b k a).1
      rwa [← hk, add_sub_cancel] at this
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
      have := (nonempty_cellWalk_fst b k a').2
      rwa [← hk, add_sub_cancel] at this
  have h2 : Nonempty (CellWalk (a', b) (a', b')) := by
    rcases le_total b b' with h | h
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
      have := (nonempty_cellWalk_snd a' k b).1
      rwa [← hk, add_sub_cancel] at this
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
      have := (nonempty_cellWalk_snd a' k b').2
      rwa [← hk, add_sub_cancel] at this
  obtain ⟨w₁⟩ := h1
  obtain ⟨w₂⟩ := h2
  exact ⟨w₁.append w₂⟩

/-- **The distance is attained.** For a drawing made of cells, none of them a square, and two
distinct points `s ≠ t`, some arc from `s` to `t` meets the drawing in exactly `d(s, t)` points.
An arc meeting the drawing in finitely many points exists by `exists_joinedIn_of_cellWalk`, applied
to any cell walk with at least one step. -/
theorem exists_line_ncard_eq_planeWallDist_cellSet {𝒰 : Set (ℤ × ℤ)}
    (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) {s t : EuclideanPlane} (hst : s ≠ t) :
    ∃ L : Set EuclideanPlane, IsLineWithEnds L s t ∧
      (L ∩ fig1PlaneEquiv '' cellSet 𝒰).Finite ∧
      (L ∩ fig1PlaneEquiv '' cellSet 𝒰).ncard = planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) s t := by
  set e := fig1PlaneEquiv
  obtain ⟨w₀⟩ := nonempty_cellWalk (cellCode (e.symm s)) (cellCode (e.symm s))
  obtain ⟨w₁⟩ := nonempty_cellWalk (cellCode (e.symm s)) (cellCode (e.symm t))
  let w := CellWalk.cons (Or.inl (CellLE.refl _)) w₁
  obtain ⟨P, hPj, hPfin, -⟩ := exists_joinedIn_of_cellWalk h𝒰 w (e.symm s) (e.symm t) rfl rfl
    (fun h => by simp [w, CellWalk.isNil] at h)
  have hj : JoinedIn (e '' P) s t := by
    have := hPj.map e.continuous.continuousOn
    rwa [e.apply_symm_apply, e.apply_symm_apply] at this
  obtain ⟨L₀, hL₀sub, hL₀⟩ := ((GraphMinor.GM07.joinedIn_iff_eq_or_exists_isLineWithEnds
    hj.mem.1 hj.mem.2).mp hj).resolve_left hst
  have hsub : L₀ ∩ e '' cellSet 𝒰 ⊆ e '' (P ∩ cellSet 𝒰) := by
    rintro z ⟨hzL, x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hL₀sub hzL
    rw [e.injective hyx] at hy
    exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hfin₀ := (hPfin.image e).subset hsub
  let K : Set ℕ := {k | ∃ L : Set EuclideanPlane, IsLineWithEnds L s t ∧
    (L ∩ e '' cellSet 𝒰).Finite ∧ (L ∩ e '' cellSet 𝒰).ncard = k}
  have hK : K.Nonempty := ⟨_, L₀, hL₀, hfin₀, rfl⟩
  have hmem : sInf K ∈ K := Nat.sInf_mem hK
  simpa [planeWallDist, hst, K] using hmem

/-- **Lower bound on the distance by a potential.** Let `φ` be a function on cells that grows by
at most one along a related pair of cells when the second is in `𝒰`, and does not grow otherwise.
Then `φ` at the cell of `t` minus `φ` at the cell of `s` is at most `d(s, t)`. -/
theorem potential_le_planeWallDist_cellSet {𝒰 : Set (ℤ × ℤ)}
    (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) (φ : ℤ × ℤ → ℤ)
    (hφ : ∀ c c', CellRel c c' → φ c' ≤ φ c + cellInd 𝒰 c') (s t : ℝ × ℝ) :
    φ (cellCode t) ≤ φ (cellCode s) + cellInd 𝒰 (cellCode s) +
      planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
  by_cases hst : s = t
  · subst hst
    have : (0 : ℤ) ≤ cellInd 𝒰 (cellCode s) := by positivity
    linarith [Nat.cast_nonneg (α := ℤ) (planeWallDist (fig1PlaneEquiv '' cellSet 𝒰)
      (fig1PlaneEquiv s) (fig1PlaneEquiv s))]
  obtain ⟨L, hL, hfin, hcard⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰
    (fig1PlaneEquiv.injective.ne hst)
  obtain ⟨w, hw⟩ : ∃ w : CellWalk (cellCode s) (cellCode t),
      w.cost 𝒰 ≤ (L ∩ fig1PlaneEquiv '' cellSet 𝒰).ncard := by
    have := exists_cellWalk_of_line hL hfin
    rwa [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at this
  have h1 := CellWalk.potential_le 𝒰 φ hφ w
  have h2 := CellWalk.cost_eq_ind_add_costTail 𝒰 w
  rw [hcard] at hw
  have h3 : (w.costTail 𝒰 : ℤ) + cellInd 𝒰 (cellCode s) ≤ (cellInd 𝒰 (cellCode s) : ℤ) +
      planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
    have : w.costTail 𝒰 ≤
        planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
      omega
    linarith [(Nat.cast_le (α := ℤ)).mpr this]
  linarith

/-! ## The wall of Fig. 1 as a cell drawing -/

open GraphMinor.GM16 (horizontalLatticeLine verticalLatticeLine)

/-- The cells of a closed unit segment of the real line from `i` to `i + 1`. -/
theorem cellCode1_mem_iff {x : ℝ} {i : ℤ} :
    (cellCode1 x = 2 * i ∨ cellCode1 x = 2 * i + 1 ∨ cellCode1 x = 2 * i + 2) ↔
      (i : ℝ) ≤ x ∧ x ≤ i + 1 := by
  constructor
  · rintro (h | h | h)
    · have := cellCode1_eq_even_iff.mp h; subst this; constructor <;> linarith
    · have := cellCode1_eq_odd_iff.mp h; exact ⟨this.1.le, this.2.le⟩
    · have := cellCode1_eq_even_iff.mp (show cellCode1 x = 2 * (i + 1) by omega)
      subst this; push_cast; constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact Or.inr (Or.inl (cellCode1_eq_odd_iff.mpr ⟨h1, h2⟩))
      · right; right
        have : cellCode1 x = 2 * (i + 1) := cellCode1_eq_even_iff.mpr (by rw [h2]; push_cast; ring)
        omega
    · exact Or.inl (cellCode1_eq_even_iff.mpr h1.symm)

/-- The three cells of the horizontal unit segment from `(i, j)` to `(i + 1, j)`. -/
def horizontalCells (i j : ℕ) : Set (ℤ × ℤ) :=
  {(2 * (i : ℤ), 2 * (j : ℤ)), (2 * (i : ℤ) + 1, 2 * (j : ℤ)), (2 * (i : ℤ) + 2, 2 * (j : ℤ))}

/-- The three cells of the vertical unit segment from `(i, j)` to `(i, j + 1)`. -/
def verticalCells (i j : ℕ) : Set (ℤ × ℤ) :=
  {(2 * (i : ℤ), 2 * (j : ℤ)), (2 * (i : ℤ), 2 * (j : ℤ) + 1), (2 * (i : ℤ), 2 * (j : ℤ) + 2)}

theorem horizontalLatticeLine_eq_cellSet (i j : ℕ) :
    horizontalLatticeLine i j = cellSet (horizontalCells i j) := by
  ext p
  simp only [horizontalLatticeLine, cellSet, horizontalCells, cellCode, mem_prod, mem_Icc,
    mem_singleton_iff, mem_insert_iff, Prod.mk.injEq, mem_ofPred_eq]
  have h1 := cellCode1_mem_iff (x := p.1) (i := (i : ℤ))
  have h2 : cellCode1 p.2 = 2 * (j : ℤ) ↔ p.2 = ((j : ℤ) : ℝ) := cellCode1_eq_even_iff
  push_cast at h1 h2
  rw [← h1, h2]
  tauto

theorem verticalLatticeLine_eq_cellSet (i j : ℕ) :
    verticalLatticeLine i j = cellSet (verticalCells i j) := by
  ext p
  simp only [verticalLatticeLine, cellSet, verticalCells, cellCode, mem_prod, mem_Icc,
    mem_singleton_iff, mem_insert_iff, Prod.mk.injEq, mem_ofPred_eq]
  have h1 := cellCode1_mem_iff (x := p.2) (i := (j : ℤ))
  have h2 : cellCode1 p.1 = 2 * (i : ℤ) ↔ p.1 = ((i : ℤ) : ℝ) := cellCode1_eq_even_iff
  push_cast at h1 h2
  rw [← h1, h2]
  tauto

/-- The cells of the segment of an edge `pq` of the elementary wall. -/
def fig1SegmentCells (p q : ℕ × ℕ) : Set (ℤ × ℤ) :=
  if p.2 = q.2 then horizontalCells (min p.1 q.1) (min p.2 q.2)
  else verticalCells (min p.1 q.1) (min p.2 q.2)

theorem fig1Segment_eq_cellSet (p q : ℕ × ℕ) :
    fig1Segment p q = cellSet (fig1SegmentCells p q) := by
  unfold fig1Segment fig1SegmentCells
  split_ifs
  · exact horizontalLatticeLine_eq_cellSet _ _
  · exact verticalLatticeLine_eq_cellSet _ _

/-- The cells of the wall of height `h` drawn as in Fig. 1. -/
def fig1WallCells (h : ℕ) : Set (ℤ × ℤ) :=
  ⋃ (p : ℕ × ℕ) (q : ℕ × ℕ) (_ : elementaryWallAdj h p q), fig1SegmentCells p q

/-- The point set of the wall of Fig. 1 is the drawing made of its cells. -/
theorem fig1WallSet_eq_cellSet (h : ℕ) :
    fig1WallSet h = fig1PlaneEquiv '' cellSet (fig1WallCells h) := by
  have : cellSet (fig1WallCells h) =
      ⋃ (p : ℕ × ℕ) (q : ℕ × ℕ) (_ : elementaryWallAdj h p q), cellSet (fig1SegmentCells p q) := by
    ext x; simp [cellSet, fig1WallCells]
  rw [this]
  simp only [fig1WallSet, image_iUnion, fig1Segment_eq_cellSet]

/-- No cell of the wall of Fig. 1 is a square, since one of its two names is even. -/
theorem fig1WallCells_not_square (h : ℕ) : ∀ c ∈ fig1WallCells h, ¬ IsSquareCell c := by
  intro c hc hsq
  simp only [fig1WallCells, mem_iUnion] at hc
  obtain ⟨p, q, _, hc⟩ := hc
  unfold fig1SegmentCells horizontalCells verticalCells at hc
  unfold IsSquareCell at hsq
  split_ifs at hc <;>
  · simp only [mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl <;> omega

/-- **Comparing two cell drawings.** Let `𝒰` and `𝒰'` contain no square. If every cell walk
`w'` can be replaced by a cell walk `w` with the same ends whose cost for `𝒰` is at most the cost
of `w'` for `𝒰'` plus `k`, and `w` is not a walk with no step on a cell of `𝒰`, then the distance
of `𝒰` is at most the distance of `𝒰'` plus `k`. This is the form in which (7.3)(i) is a count on
cells. -/
theorem planeWallDist_le_of_cellWalk_transform {𝒰 𝒰' : Set (ℤ × ℤ)}
    (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) (h𝒰' : ∀ c ∈ 𝒰', ¬ IsSquareCell c) (k : ℕ)
    (hT : ∀ (c d : ℤ × ℤ) (w' : CellWalk c d), ∃ w : CellWalk c d,
      w.cost 𝒰 ≤ w'.cost 𝒰' + k ∧ (w.isNil = true → c ∉ 𝒰))
    (s t : EuclideanPlane) :
    planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) s t ≤
      planeWallDist (fig1PlaneEquiv '' cellSet 𝒰') s t + k := by
  by_cases hst : s = t
  · subst hst; simp [planeWallDist]
  obtain ⟨L, hL, hfin, hcard⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰' hst
  obtain ⟨w', hw'⟩ := exists_cellWalk_of_line hL hfin
  obtain ⟨w, hw, hnil⟩ := hT _ _ w'
  have hst' : fig1PlaneEquiv.symm s ≠ fig1PlaneEquiv.symm t :=
    fig1PlaneEquiv.symm.injective.ne hst
  have := planeWallDist_cellSet_le h𝒰 hst' w hnil
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at this
  omega

end GraphMinor.GM13
