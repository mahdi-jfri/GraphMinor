module

public import GraphMinor.GM13.Section7Faces

/-!
# Graph Minors XIII, Section 7: the cells and bricks of the wall of Fig. 1

The wall of height `h` drawn as in Fig. 1 is a drawing made of cells (`fig1WallCells h`). This
file describes it by arithmetic on the names of the cells, and names its faces.

* `mem_fig1WallCells_iff`: a cell `(a, b)` is in the drawing exactly when `IsWallCell h (a, b)`.
  A cell with `b` even lies on a row. A cell with `b` odd and `a` even lies on a vertical edge,
  which is there when `a / 2 + (b - 1) / 2` is odd.
* The faces of the drawing are the bricks and the outer face. The brick between rows `y` and
  `y + 1` whose middle has abscissa `X` is named `(X, y)`. Here `X ≡ y (mod 2)`, `1 ≤ X ≤ 2 h`
  and `0 ≤ y < h`. The outer face is named `outFace`. The square `q` lies in the face
  `wallFace h q`. Around a cell off the drawing all squares lie in one face
  (`wallFace_eq_of_not_mem`). Around any cell the faces are equal or touch (`wallFace_eq_or_adj`).
* `faceDist h F G` counts the steps from `F` to `G`: through the bricks (`hexDist`), or out to
  the outer face and back (`outDepth`). It grows by at most one between touching faces
  (`faceDist_le_of_faceAdj`).
* `le_planeWallDist_fig1`, the main result: for `s, t` in different cells, some face `F` at `s`
  and some face `G` at `t` satisfy `[s] + [t] + D(F, G) ≤ d(s, t)`. Here `[s]` is one if `s` is
  on the drawing and zero otherwise. It comes from `le_planeWallDist_of_faces` with `D` as the
  potential.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## The cells of the wall -/

/-- The arithmetic description of the cells of the wall of height `h` drawn as in Fig. 1. A
cell `(a, b)` with `b` even is a point or a segment of row `b / 2`; the two missing corners
`(0, 0)` and `(2 h + 1, h)` remove the cells `a ≤ 1` of the bottom row and `a ≥ 4 h + 1` of the
top row. A cell with `b` odd and `a` even is on the vertical line `x = a / 2` between the rows
`(b - 1) / 2` and `(b + 1) / 2`; the wall has an edge there when `a / 2 + (b - 1) / 2` is odd. -/
def IsWallCell (h : ℕ) (c : ℤ × ℤ) : Prop :=
  0 ≤ c.1 ∧ c.1 ≤ 4 * h + 2 ∧ 0 ≤ c.2 ∧ c.2 ≤ 2 * h ∧
    ((c.2 % 2 = 0 ∧ ¬ (c.1 ≤ 1 ∧ c.2 = 0) ∧ ¬ (4 * h + 1 ≤ c.1 ∧ c.2 = 2 * h)) ∨
      (c.2 % 2 = 1 ∧ c.1 % 2 = 0 ∧ (c.1 / 2 + (c.2 - 1) / 2) % 2 = 1))

instance (h : ℕ) : DecidablePred (IsWallCell h) := fun c => by
  unfold IsWallCell; infer_instance

private theorem exists_nat_eq {z : ℤ} (hz : 0 ≤ z) : ∃ n : ℕ, (n : ℤ) = z :=
  ⟨z.toNat, Int.toNat_of_nonneg hz⟩

/-- The cells of the segment of an edge are cells of the wall. -/
private theorem isWallCell_of_mem_fig1SegmentCells {h : ℕ} {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj h p q) {c : ℤ × ℤ} (hc : c ∈ fig1SegmentCells p q) :
    IsWallCell h c := by
  obtain ⟨⟨hp1, hp2, hp0, hph⟩, ⟨hq1, hq2, hq0, hqh⟩, hpq⟩ := hadj
  have hp0' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun h' => hp0 (Prod.ext h'.1 h'.2)
  have hq0' : ¬ (q.1 = 0 ∧ q.2 = 0) := fun h' => hq0 (Prod.ext h'.1 h'.2)
  have hph' : ¬ (p.1 = 2 * h + 1 ∧ p.2 = h) := fun h' => hph (Prod.ext h'.1 h'.2)
  have hqh' : ¬ (q.1 = 2 * h + 1 ∧ q.2 = h) := fun h' => hqh (Prod.ext h'.1 h'.2)
  unfold fig1SegmentCells at hc
  unfold IsWallCell
  rcases hpq with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · rw [ite_eq_left hy] at hc
    simp only [horizontalCells, mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl <;> simp only <;> omega
  · have hy' : p.2 ≠ q.2 := by omega
    rw [ite_eq_right hy'] at hc
    simp only [verticalCells, mem_insert_iff, mem_singleton_iff] at hc
    rcases hy with ⟨hy, hodd⟩ | ⟨hy, hodd⟩ <;>
    · obtain ⟨k, hk⟩ := hodd
      rcases hc with rfl | rfl | rfl <;> simp only <;> omega

/-- **The cells of the wall.** For `h ≥ 1` even, a cell is in the drawing of the wall of height `h`
exactly when it satisfies `IsWallCell h`. -/
theorem mem_fig1WallCells_iff {h : ℕ} (hh : 1 ≤ h) (he : Even h) (c : ℤ × ℤ) :
    c ∈ fig1WallCells h ↔ IsWallCell h c := by
  obtain ⟨k, hk⟩ := he
  constructor
  · intro hc
    simp only [fig1WallCells, mem_iUnion] at hc
    obtain ⟨p, q, hadj, hc⟩ := hc
    exact isWallCell_of_mem_fig1SegmentCells hadj hc
  · intro hc
    obtain ⟨a, b⟩ := c
    simp only [IsWallCell] at hc
    simp only [fig1WallCells, mem_iUnion]
    obtain ⟨ha0, ha1, hb0, hb1, hrow | hcol⟩ := hc
    · obtain ⟨y, hy⟩ := exists_nat_eq (z := b / 2) (by omega)
      by_cases hae : a % 2 = 0
      · obtain ⟨x, hx⟩ := exists_nat_eq (z := a / 2) (by omega)
        by_cases hright : a ≤ 4 * h ∧ ¬ (b = 2 * h ∧ a = 4 * h)
        · refine ⟨(x, y), (x + 1, y), ?_, ?_⟩
          · refine ⟨⟨by omega, by omega, ?_, ?_⟩, ⟨by omega, by omega, ?_, ?_⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            all_goals (intro h'; simp only [Prod.mk.injEq] at h'; omega)
          · simp only [fig1SegmentCells, ↓reduceIte, horizontalCells, mem_insert_iff,
              mem_singleton_iff, Prod.mk.injEq]
            left; constructor <;> push_cast [min_def] <;> split_ifs <;> omega
        · obtain ⟨x', hx'⟩ := exists_nat_eq (z := a / 2 - 1) (by omega)
          refine ⟨(x', y), (x' + 1, y), ?_, ?_⟩
          · refine ⟨⟨by omega, by omega, ?_, ?_⟩, ⟨by omega, by omega, ?_, ?_⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            all_goals (intro h'; simp only [Prod.mk.injEq] at h'; omega)
          · simp only [fig1SegmentCells, ↓reduceIte, horizontalCells, mem_insert_iff,
              mem_singleton_iff, Prod.mk.injEq]
            right; right; constructor <;> push_cast [min_def] <;> split_ifs <;> omega
      · obtain ⟨x, hx⟩ := exists_nat_eq (z := a / 2) (by omega)
        refine ⟨(x, y), (x + 1, y), ?_, ?_⟩
        · refine ⟨⟨by omega, by omega, ?_, ?_⟩, ⟨by omega, by omega, ?_, ?_⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
          all_goals (intro h'; simp only [Prod.mk.injEq] at h'; omega)
        · simp only [fig1SegmentCells, ↓reduceIte, horizontalCells, mem_insert_iff,
            mem_singleton_iff, Prod.mk.injEq]
          right; left; constructor <;> push_cast [min_def] <;> split_ifs <;> omega
    · obtain ⟨hbo, hae, hpar⟩ := hcol
      obtain ⟨x, hx⟩ := exists_nat_eq (z := a / 2) (by omega)
      obtain ⟨y, hy⟩ := exists_nat_eq (z := (b - 1) / 2) (by omega)
      refine ⟨(x, y), (x, y + 1), ?_, ?_⟩
      · refine ⟨⟨by omega, by omega, ?_, ?_⟩, ⟨by omega, by omega, ?_, ?_⟩,
          Or.inr ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩⟩
        all_goals try (intro h'; simp only [Prod.mk.injEq] at h'; omega)
        · rw [Nat.odd_iff]
          have : ((x : ℤ) + y) % 2 = 1 := by rw [hx, hy]; exact hpar
          show (x + y) % 2 = 1
          omega
      · simp only [fig1SegmentCells, show y ≠ y + 1 by omega, ↓reduceIte, verticalCells,
          mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
        right; left; constructor <;> push_cast [min_def] <;> split_ifs <;> omega

/-! ## The faces of the wall -/

/-- The brick name `(X, y)` of the square `q = (2 x + 1, 2 y + 1)`: the square lies between rows
`y` and `y + 1`, and `X` is the one of `x, x + 1` with `X ≡ y (mod 2)`. -/
def brickOf (q : ℤ × ℤ) : ℤ × ℤ :=
  ((q.1 - 1) / 2 + ((q.1 - 1) / 2 + (q.2 - 1) / 2) % 2, (q.2 - 1) / 2)

/-- `(X, y)` names a brick of the wall of height `h`: the brick between rows `y` and `y + 1`
spanning the abscissas `X - 1` to `X + 1`. -/
def IsBrick (h : ℕ) (F : ℤ × ℤ) : Prop :=
  0 ≤ F.2 ∧ F.2 < h ∧ 1 ≤ F.1 ∧ F.1 ≤ 2 * h ∧ (F.1 - F.2) % 2 = 0

instance (h : ℕ) : DecidablePred (IsBrick h) := fun F => by
  unfold IsBrick; infer_instance

/-- The name of the outer face. -/
def outFace : ℤ × ℤ := (0, -1)

theorem not_isBrick_outFace (h : ℕ) : ¬ IsBrick h outFace := by
  simp [IsBrick, outFace]

/-- The face of the wall of height `h` that contains the square `q`. -/
def wallFace (h : ℕ) (q : ℤ × ℤ) : ℤ × ℤ :=
  if IsBrick h (brickOf q) then brickOf q else outFace

/-- The squares above a cell, in coordinates. -/
theorem mem_squaresAbove_iff {c q : ℤ × ℤ} :
    q ∈ squaresAbove c ↔ q.1 % 2 = 1 ∧ q.2 % 2 = 1 ∧
      (c.1 = q.1 ∨ c.1 = q.1 - 1 ∨ c.1 = q.1 + 1) ∧ (c.2 = q.2 ∨ c.2 = q.2 - 1 ∨ c.2 = q.2 + 1) := by
  simp only [squaresAbove, IsSquareCell, CellLE, CellLE1, mem_ofPred_eq]
  omega

theorem exists_of_mem_squaresAbove {c q : ℤ × ℤ} (hq : q ∈ squaresAbove c) :
    ∃ x y : ℤ, q = (2 * x + 1, 2 * y + 1) ∧ 2 * x ≤ c.1 ∧ c.1 ≤ 2 * x + 2 ∧
      2 * y ≤ c.2 ∧ c.2 ≤ 2 * y + 2 ∧ (c.1 = 2 * x + 1 ∨ c.1 % 2 = 0) ∧
      (c.2 = 2 * y + 1 ∨ c.2 % 2 = 0) := by
  rw [mem_squaresAbove_iff] at hq
  refine ⟨(q.1 - 1) / 2, (q.2 - 1) / 2, Prod.ext (by simp; omega) (by simp; omega), ?_⟩
  omega

/-- The face of the square `(2 x + 1, 2 y + 1)`. -/
theorem wallFace_square (h : ℕ) (x y : ℤ) :
    wallFace h (2 * x + 1, 2 * y + 1) =
      if 0 ≤ y ∧ y < h ∧ 1 ≤ x + (x + y) % 2 ∧ x + (x + y) % 2 ≤ 2 * h
      then (x + (x + y) % 2, y) else outFace := by
  have h1 : (2 * x + 1 - 1) / 2 = x := by omega
  have h2 : (2 * y + 1 - 1) / 2 = y := by omega
  unfold wallFace brickOf IsBrick
  simp only [h1, h2]
  congr 1
  apply propext
  omega

/-- Around a cell outside the wall, all squares are in the same face. -/
theorem wallFace_eq_of_not_mem {h : ℕ} (hh : 1 ≤ h) (he : Even h) {c : ℤ × ℤ}
    (hc : c ∉ fig1WallCells h) {q q' : ℤ × ℤ} (hq : q ∈ squaresAbove c)
    (hq' : q' ∈ squaresAbove c) : wallFace h q = wallFace h q' := by
  rw [mem_fig1WallCells_iff hh he] at hc
  obtain ⟨x, y, rfl, hx1, hx2, hy1, hy2, hxa, hyb⟩ := exists_of_mem_squaresAbove hq
  obtain ⟨x', y', rfl, hx1', hx2', hy1', hy2', hxa', hyb'⟩ := exists_of_mem_squaresAbove hq'
  obtain ⟨a, b⟩ := c
  simp only [IsWallCell] at hc
  simp only at hx1 hx2 hy1 hy2 hxa hyb hx1' hx2' hy1' hy2' hxa' hyb'
  rw [wallFace_square, wallFace_square]
  obtain ⟨k, rfl⟩ := he
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
    simp only [ha, hb, zero_ne_one, one_ne_zero, false_and, and_false, or_false, false_or,
      true_and] at hc hxa hyb hxa' hyb'
  · -- a point
    by_cases hin : 0 ≤ a ∧ a ≤ 4 * ((k + k : ℕ) : ℤ) + 2 ∧ 0 ≤ b ∧ b ≤ 2 * ((k + k : ℕ) : ℤ)
    · have : (a ≤ 1 ∧ b = 0) ∨ (4 * ((k + k : ℕ) : ℤ) + 1 ≤ a ∧ b = 2 * ((k + k : ℕ) : ℤ)) := by
        omega
      split_ifs <;> simp only [outFace, Prod.mk.injEq] <;> omega
    · split_ifs <;> simp only [outFace, Prod.mk.injEq] <;> omega
  · -- a vertical segment
    split_ifs <;> simp only [outFace, Prod.mk.injEq] <;> omega
  · -- a horizontal segment
    split_ifs <;> simp only [outFace, Prod.mk.injEq] <;> omega
  · -- a square
    have : x = x' := by omega
    have : y = y' := by omega
    subst x' y'
    rfl


/-! ## Distances between faces -/

/-- The number of steps between the bricks `F` and `G` in the hexagonal pattern of bricks: one
step goes to a brick of the same row (two units sideways) or to one of the two bricks above or
below that share an edge with it. It is `max (|Δy|, (|ΔX| + |Δy|) / 2)`. -/
def hexDist (F G : ℤ × ℤ) : ℤ :=
  max (max (F.2 - G.2) (G.2 - F.2))
    ((max (F.1 - G.1) (G.1 - F.1) + max (F.2 - G.2) (G.2 - F.2)) / 2)

/-- The number of steps from the brick `F` to the outer face of the wall of height `h`. -/
def outDepth (h : ℕ) (F : ℤ × ℤ) : ℤ :=
  min (min (F.2 + 1) (h - F.2)) (min ((F.1 + 1) / 2) ((2 * h + 2 - F.1) / 2))

/-- Two faces of the wall of height `h` touch: two bricks at one step, or a brick at one step
from the outer face and the outer face. -/
def FaceAdj (h : ℕ) (F G : ℤ × ℤ) : Prop :=
  (IsBrick h F ∧ IsBrick h G ∧ hexDist F G = 1) ∨
    (F = outFace ∧ IsBrick h G ∧ outDepth h G = 1) ∨
    (G = outFace ∧ IsBrick h F ∧ outDepth h F = 1)

/-- The distance between two faces of the wall of height `h`: through the bricks, or out to the
outer face and back. -/
def faceDist (h : ℕ) (F G : ℤ × ℤ) : ℤ :=
  if F = outFace then (if G = outFace then 0 else outDepth h G)
  else if G = outFace then outDepth h F
  else min (hexDist F G) (outDepth h F + outDepth h G)

/-- Each face of the wall is a brick or the outer face. -/
theorem isBrick_or_eq_outFace_wallFace (h : ℕ) (q : ℤ × ℤ) :
    IsBrick h (wallFace h q) ∨ wallFace h q = outFace := by
  unfold wallFace
  split_ifs with hb
  · exact Or.inl hb
  · exact Or.inr rfl

theorem hexDist_nonneg (F G : ℤ × ℤ) : 0 ≤ hexDist F G := by
  unfold hexDist
  omega

/-- The bricks of two squares that share a corner or a side are at most one step apart. -/
theorem hexDist_near_le (x y x' y' : ℤ) (hx : x - 1 ≤ x' ∧ x' ≤ x + 1)
    (hy : y - 1 ≤ y' ∧ y' ≤ y + 1) :
    hexDist (x + (x + y) % 2, y) (x' + (x' + y') % 2, y') ≤ 1 := by
  unfold hexDist
  simp only
  omega

/-- A brick is at least one step from the outer face. -/
theorem one_le_outDepth {h : ℕ} {F : ℤ × ℤ} (hF : IsBrick h F) : 1 ≤ outDepth h F := by
  unfold IsBrick at hF
  unfold outDepth
  omega

/-- If a square lies in a brick and a square that shares a corner or a side with it lies in the
outer face, the brick is one step from the outer face. -/
theorem outDepth_near_le (h : ℕ) (x y x' y' : ℤ) (hx : x - 1 ≤ x' ∧ x' ≤ x + 1)
    (hy : y - 1 ≤ y' ∧ y' ≤ y + 1)
    (hb : 0 ≤ y ∧ y < h ∧ 1 ≤ x + (x + y) % 2 ∧ x + (x + y) % 2 ≤ 2 * h)
    (hb' : ¬ (0 ≤ y' ∧ y' < h ∧ 1 ≤ x' + (x' + y') % 2 ∧ x' + (x' + y') % 2 ≤ 2 * h)) :
    outDepth h (x + (x + y) % 2, y) ≤ 1 := by
  unfold outDepth
  simp only
  omega

/-- Around any cell, the faces of the squares are equal or touch. -/
theorem wallFace_eq_or_adj (h : ℕ) {c q q' : ℤ × ℤ} (hq : q ∈ squaresAbove c)
    (hq' : q' ∈ squaresAbove c) :
    wallFace h q = wallFace h q' ∨ FaceAdj h (wallFace h q) (wallFace h q') := by
  obtain ⟨x, y, rfl, hx1, hx2, hy1, hy2, -, -⟩ := exists_of_mem_squaresAbove hq
  obtain ⟨x', y', rfl, hx1', hx2', hy1', hy2', -, -⟩ := exists_of_mem_squaresAbove hq'
  have hx : x - 1 ≤ x' ∧ x' ≤ x + 1 := by omega
  have hy : y - 1 ≤ y' ∧ y' ≤ y + 1 := by omega
  have hx' : x' - 1 ≤ x ∧ x ≤ x' + 1 := by omega
  have hy' : y' - 1 ≤ y ∧ y ≤ y' + 1 := by omega
  rw [wallFace_square, wallFace_square]
  split_ifs with hb hb'
  · -- two bricks
    have hd := hexDist_near_le x y x' y' hx hy
    by_cases h0 : hexDist (x + (x + y) % 2, y) (x' + (x' + y') % 2, y') = 0
    · left
      unfold hexDist at h0
      simp only at h0
      simp only [Prod.mk.injEq]
      omega
    · right; left
      have := hexDist_nonneg (x + (x + y) % 2, y) (x' + (x' + y') % 2, y')
      refine ⟨?_, ?_, by omega⟩
      · unfold IsBrick; simp only; omega
      · unfold IsBrick; simp only; omega
  · -- a brick and the outer face
    right; right; right
    refine ⟨rfl, by unfold IsBrick; simp only; omega, ?_⟩
    have h1 := outDepth_near_le h x y x' y' hx hy hb hb'
    have h2 := one_le_outDepth (h := h) (F := (x + (x + y) % 2, y))
      (by unfold IsBrick; simp only; omega)
    omega
  · -- the outer face and a brick
    right; right; left
    refine ⟨rfl, by unfold IsBrick; simp only; omega, ?_⟩
    have h1 := outDepth_near_le h x' y' x y hx' hy' (by assumption) hb
    have h2 := one_le_outDepth (h := h) (F := (x' + (x' + y') % 2, y'))
      (by unfold IsBrick; simp only; omega)
    omega
  · left; rfl


/-! ## The face distance grows by at most one between touching faces -/

theorem hexDist_self (F : ℤ × ℤ) : hexDist F F = 0 := by
  unfold hexDist
  omega

theorem hexDist_comm (F G : ℤ × ℤ) : hexDist F G = hexDist G F := by
  unfold hexDist
  omega

/-- The step count written with absolute values. -/
theorem hexDist_eq_abs (F G : ℤ × ℤ) :
    hexDist F G = max |F.2 - G.2| ((|F.1 - G.1| + |F.2 - G.2|) / 2) := by
  unfold hexDist
  simp only [abs_eq_max_neg, neg_sub]

/-- The triangle inequality for the step count between bricks. The parity condition makes
`|ΔX| + |Δy|` even, so the halving is exact. -/
theorem hexDist_triangle {h : ℕ} {E F G : ℤ × ℤ} (hE : IsBrick h E) (hF : IsBrick h F)
    (hG : IsBrick h G) : hexDist E G ≤ hexDist E F + hexDist F G := by
  rw [hexDist_eq_abs, hexDist_eq_abs, hexDist_eq_abs]
  have e1 : E.1 - G.1 = (E.1 - F.1) + (F.1 - G.1) := by ring
  have e2 : E.2 - G.2 = (E.2 - F.2) + (F.2 - G.2) := by ring
  have t1 := abs_add_le (E.1 - F.1) (F.1 - G.1)
  have t2 := abs_add_le (E.2 - F.2) (F.2 - G.2)
  rw [← e1] at t1
  rw [← e2] at t2
  have p1 : (|E.1 - F.1| + |E.2 - F.2|) % 2 = 0 := by
    unfold IsBrick at hE hF
    rcases abs_choice (E.1 - F.1) with h1 | h1 <;> rcases abs_choice (E.2 - F.2) with h2 | h2 <;>
      rw [h1, h2] <;> omega
  have p2 : (|F.1 - G.1| + |F.2 - G.2|) % 2 = 0 := by
    unfold IsBrick at hF hG
    rcases abs_choice (F.1 - G.1) with h1 | h1 <;> rcases abs_choice (F.2 - G.2) with h2 | h2 <;>
      rw [h1, h2] <;> omega
  generalize |E.1 - G.1| = a at *
  generalize |E.2 - G.2| = b at *
  generalize |E.1 - F.1| = c at *
  generalize |E.2 - F.2| = d at *
  generalize |F.1 - G.1| = e at *
  generalize |F.2 - G.2| = f at *
  omega
/-- The step count to the outer face changes by at most the step count between two bricks. -/
theorem outDepth_le_add_hexDist {h : ℕ} {E F : ℤ × ℤ} (hE : IsBrick h E) (hF : IsBrick h F) :
    outDepth h E ≤ outDepth h F + hexDist E F := by
  rw [hexDist_eq_abs]
  have a1 := le_abs_self (E.1 - F.1)
  have a2 := neg_abs_le (E.1 - F.1)
  have a3 := le_abs_self (E.2 - F.2)
  have a4 := neg_abs_le (E.2 - F.2)
  unfold IsBrick at hE hF
  obtain ⟨-, -, -, -, pE⟩ := hE
  obtain ⟨-, -, -, -, pF⟩ := hF
  unfold outDepth
  generalize |E.1 - F.1| = d at *
  generalize |E.2 - F.2| = f at *
  obtain ⟨a, b⟩ := E
  obtain ⟨c, e⟩ := F
  simp only at *
  omega
/-- The distance from a brick or the outer face to itself is zero. -/
theorem faceDist_self {h : ℕ} {F : ℤ × ℤ} (hF : IsBrick h F ∨ F = outFace) :
    faceDist h F F = 0 := by
  rcases hF with hF | rfl
  · have hFo : F ≠ outFace := fun he => not_isBrick_outFace h (he ▸ hF)
    have := one_le_outDepth hF
    unfold faceDist
    simp only [hFo, ↓reduceIte, hexDist_self]
    omega
  · simp [faceDist]

theorem faceDist_out_out (h : ℕ) : faceDist h outFace outFace = 0 := by
  simp [faceDist]

theorem faceDist_out_left {h : ℕ} {G : ℤ × ℤ} (hG : G ≠ outFace) :
    faceDist h outFace G = outDepth h G := by
  simp [faceDist, hG]

theorem faceDist_out_right {h : ℕ} {F : ℤ × ℤ} (hF : F ≠ outFace) :
    faceDist h F outFace = outDepth h F := by
  simp [faceDist, hF]

theorem faceDist_of_ne {h : ℕ} {F G : ℤ × ℤ} (hF : F ≠ outFace) (hG : G ≠ outFace) :
    faceDist h F G = min (hexDist F G) (outDepth h F + outDepth h G) := by
  simp [faceDist, hF, hG]

/-- **Lipschitz step.** If the faces `F` and `G` touch, then the distance from a face `E` to `G`
is at most one more than the distance from `E` to `F`. -/
theorem faceDist_le_of_faceAdj {h : ℕ} {E F G : ℤ × ℤ} (hE : IsBrick h E ∨ E = outFace)
    (hFG : FaceAdj h F G) : faceDist h E G ≤ faceDist h E F + 1 := by
  have hne : ∀ {K : ℤ × ℤ}, IsBrick h K → K ≠ outFace :=
    fun hb he => not_isBrick_outFace h (he ▸ hb)
  rcases hFG with ⟨hF, hG, hd⟩ | ⟨rfl, hG, hd⟩ | ⟨rfl, hF, hd⟩
  · have h1 := outDepth_le_add_hexDist hG hF
    rw [hexDist_comm] at h1
    rcases hE with hE | rfl
    · have h2 := hexDist_triangle hE hF hG
      rw [faceDist_of_ne (hne hE) (hne hG), faceDist_of_ne (hne hE) (hne hF)]
      omega
    · rw [faceDist_out_left (hne hG), faceDist_out_left (hne hF)]
      omega
  · rcases hE with hE | rfl
    · rw [faceDist_of_ne (hne hE) (hne hG), faceDist_out_right (hne hE)]
      omega
    · rw [faceDist_out_left (hne hG), faceDist_out_out]
      omega
  · have h2 := one_le_outDepth hF
    rcases hE with hE | rfl
    · have h1 := outDepth_le_add_hexDist hE hF
      rw [faceDist_of_ne (hne hE) (hne hF), faceDist_out_right (hne hE)]
      omega
    · rw [faceDist_out_left (hne hF), faceDist_out_out]
      omega


/-! ## The lower bound for the wall of Fig. 1 -/

/-- The least distance from a face at the cell `c` to the face `G`. -/
noncomputable def faceDistFrom (h : ℕ) (c : ℤ × ℤ) (G : ℤ × ℤ) : ℕ :=
  sInf ((fun q => (faceDist h (wallFace h q) G).toNat) '' squaresAbove c)

theorem exists_faceDistFrom_eq (h : ℕ) (c G : ℤ × ℤ) :
    ∃ q ∈ squaresAbove c, (faceDist h (wallFace h q) G).toNat = faceDistFrom h c G := by
  have hne : ((fun q => (faceDist h (wallFace h q) G).toNat) '' squaresAbove c).Nonempty :=
    (squaresAbove_nonempty c).image _
  obtain ⟨q, hq, hq'⟩ := Nat.sInf_mem hne
  exact ⟨q, hq, hq'⟩

theorem faceDistFrom_le (h : ℕ) {c q : ℤ × ℤ} (hq : q ∈ squaresAbove c) (G : ℤ × ℤ) :
    faceDistFrom h c G ≤ (faceDist h (wallFace h q) G).toNat :=
  Nat.sInf_le ⟨q, hq, rfl⟩

/-- **Lower bound for the wall of Fig. 1.** For points `s, t` in different cells, some face `F`
at `s` and some face `G` at `t` satisfy `[s] + [t] + D(F, G) ≤ d(s, t)`, where `D` is
`faceDist` and `[s]` is one if `s` is on the drawing. -/
theorem le_planeWallDist_fig1 {h : ℕ} (hh : 1 ≤ h) (he : Even h) {s t : ℝ × ℝ}
    (hst : cellCode s ≠ cellCode t) :
    ∃ q ∈ squaresAbove (cellCode s), ∃ q' ∈ squaresAbove (cellCode t),
      cellInd (fig1WallCells h) (cellCode s) + cellInd (fig1WallCells h) (cellCode t) +
          (faceDist h (wallFace h q) (wallFace h q')).toNat ≤
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h)) (fig1PlaneEquiv s)
          (fig1PlaneEquiv t) := by
  have hψ : ∀ F G, FaceAdj h F G →
      faceDistFrom h (cellCode s) G ≤ faceDistFrom h (cellCode s) F + 1 := by
    intro F G hFG
    obtain ⟨q, hq, hqe⟩ := exists_faceDistFrom_eq h (cellCode s) F
    have h1 := faceDistFrom_le h hq G
    have h2 := faceDist_le_of_faceAdj (isBrick_or_eq_outFace_wallFace h q) hFG
    omega
  have hs : ∀ q ∈ squaresAbove (cellCode s), faceDistFrom h (cellCode s) (wallFace h q) = 0 := by
    intro q hq
    have h1 := faceDistFrom_le h hq (wallFace h q)
    rw [faceDist_self (isBrick_or_eq_outFace_wallFace h q)] at h1
    omega
  obtain ⟨q', hq', hle⟩ := le_planeWallDist_of_faces (fig1WallCells_not_square h) (wallFace h)
    (FaceAdj h) (fun c hc q hq q' hq' => wallFace_eq_of_not_mem hh he hc hq hq')
    (fun c _ q hq q' hq' => wallFace_eq_or_adj h hq hq') (faceDistFrom h (cellCode s)) hψ hst hs
  obtain ⟨q, hq, hqe⟩ := exists_faceDistFrom_eq h (cellCode s) (wallFace h q')
  exact ⟨q, hq, q', hq', by rw [hqe]; exact hle⟩

end GraphMinor.GM13
