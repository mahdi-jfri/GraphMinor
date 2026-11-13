module

public import GraphMinor.GM13.Section7TransK

/-!
# Graph Minors XIII, (7.3): an element near the border of the wall

This file proves (7.3) of Graph Minors XIII (page 90) in the case where the element `mv` that
holds `v` is near the border of the wall. Write `k = r + 1`. The new wall is the moved subwall
`T(i, j)` of `Section7TransK.lean`, of height `h - 2k`. We choose `(i, j)` so that the frame that
`T(i, j)` deletes is wide on the side of the border nearest to `mv`. Then every kept element is
far from `mv` in the sense of `Chain.Far`.

The distances of the cell `mv = (a, b)` from the four sides of the wall of height `h` are
`b / 2` (bottom), `h - (b + 1) / 2` (top), `a / 4` (left) and `(4h + 2 - a) / 4` (right). If the
least of them is `d ≤ k`, we take, for the nearest side:
* bottom: `j = min (2k - 1) (k + 1 + d)` and `i = 2k + j % 2`;
* top: `j = max 1 (k - 1 - d)` and `i = 2k + j % 2`;
* left: `i = min (4k - 1) (2k + 2 + 2d)` and `j = k + (i + k) % 2`;
* right: `i = max 1 (2k - 2 - 2d)` and `j = k + (i + k) % 2`.

The choice was found by a computer search before the proof. The Lean proof does not rely on the
search.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-- The distance of the cell `mv` from the bottom side. -/
def sideB (mv : ℤ × ℤ) : ℤ := mv.2 / 2

/-- The distance of the cell `mv` from the top side of the wall of height `h`. -/
def sideT (h : ℕ) (mv : ℤ × ℤ) : ℤ := h - (mv.2 + 1) / 2

/-- The distance of the cell `mv` from the left side. -/
def sideL (mv : ℤ × ℤ) : ℤ := mv.1 / 4

/-- The distance of the cell `mv` from the right side of the wall of height `h`. -/
def sideR (h : ℕ) (mv : ℤ × ℤ) : ℤ := (4 * h + 2 - mv.1) / 4

/-- The face of a square around a cell `c` is the brick `B` given by `brickOf`, if it is a brick,
and the outer face otherwise. In both cases `B` is near `c`. -/
theorem exists_brick_near (h : ℕ) {c q : ℤ × ℤ} (hq : q ∈ squaresAbove c) :
    ∃ B : ℤ × ℤ, c.2 - 2 ≤ 2 * B.2 ∧ 2 * B.2 ≤ c.2 ∧ c.1 - 2 ≤ 2 * B.1 ∧ 2 * B.1 ≤ c.1 + 2 ∧
      (B.1 - B.2) % 2 = 0 ∧
      ((IsBrick h B ∧ wallFace h q = B) ∨ (¬ IsBrick h B ∧ wallFace h q = outFace)) := by
  refine ⟨brickOf q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_squaresAbove_iff] at hq; simp only [brickOf]; omega
  · rw [mem_squaresAbove_iff] at hq; simp only [brickOf]; omega
  · rw [mem_squaresAbove_iff] at hq; simp only [brickOf]; omega
  · rw [mem_squaresAbove_iff] at hq; simp only [brickOf]; omega
  · simp only [brickOf]; omega
  · unfold wallFace
    split_ifs with hb
    · exact Or.inl ⟨hb, rfl⟩
    · exact Or.inr ⟨hb, rfl⟩

/-- A lower bound on the face distance, case by case. -/
theorem le_faceDist_of {h : ℕ} {F G : ℤ × ℤ} {D : ℤ}
    (hF : (IsBrick h F) ∨ F = outFace) (hG : IsBrick h G ∨ G = outFace)
    (h1 : IsBrick h F → IsBrick h G → D ≤ hexDist F G ∧ D ≤ outDepth h F + outDepth h G)
    (h2 : F = outFace → IsBrick h G → D ≤ outDepth h G)
    (h3 : IsBrick h F → G = outFace → D ≤ outDepth h F)
    (h4 : F = outFace → G = outFace → D ≤ 0) : D ≤ faceDist h F G := by
  have nb : ∀ {X : ℤ × ℤ}, IsBrick h X → X ≠ outFace := fun hX e => not_isBrick_outFace h (e ▸ hX)
  unfold faceDist
  rcases hF with hF | rfl <;> rcases hG with hG | rfl
  · rw [if_neg (nb hF), if_neg (nb hG)]
    exact le_min (h1 hF hG).1 (h1 hF hG).2
  · rw [if_neg (nb hF), if_pos rfl]; exact h3 hF rfl
  · rw [if_pos rfl, if_neg (nb hG)]; exact h2 rfl hG
  · simp only [if_true]; exact h4 rfl rfl

/-- The ranges of a kept cell of the moved subwall. -/
theorem kept_bounds {h' : ℕ} {i j : ℤ} {m : ℤ × ℤ}
    (hm : IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j)) :
    2 * i ≤ m.1 ∧ m.1 ≤ 2 * i + 4 * h' + 2 ∧ 2 * j ≤ m.2 ∧ m.2 ≤ 2 * j + 2 * h' := by
  unfold IsWallCell at hm
  simp only at hm
  omega

theorem le_outDepth {h : ℕ} {F : ℤ × ℤ} {D : ℤ} (h1 : D ≤ F.2 + 1) (h2 : D ≤ h - F.2)
    (h3 : D ≤ (F.1 + 1) / 2) (h4 : D ≤ (2 * h + 2 - F.1) / 2) : D ≤ outDepth h F := by
  unfold outDepth
  omega

theorem le_hexDist_of_le {F G : ℤ × ℤ} {D : ℤ} (h : D ≤ F.2 - G.2 ∨ D ≤ G.2 - F.2 ∨
    2 * D ≤ F.1 - G.1 ∨ 2 * D ≤ G.1 - F.1) : D ≤ hexDist F G := by
  unfold hexDist
  omega

/-- The face distance between two bricks. -/
theorem le_faceDist_bricks {h : ℕ} {F G : ℤ × ℤ} {D : ℤ} (hF : IsBrick h F) (hG : IsBrick h G)
    (h1 : D ≤ hexDist F G) (h2 : D ≤ outDepth h F + outDepth h G) : D ≤ faceDist h F G := by
  unfold faceDist
  have nF : F ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hF)
  have nG : G ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hG)
  rw [if_neg nF, if_neg nG]
  exact le_min h1 h2

/-- The face distance between a brick and the outer face. -/
theorem le_faceDist_brick_out {h : ℕ} {F : ℤ × ℤ} {D : ℤ} (hF : IsBrick h F)
    (h1 : D ≤ outDepth h F) : D ≤ faceDist h F outFace := by
  unfold faceDist
  have nF : F ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hF)
  rw [if_neg nF, if_pos rfl]
  exact h1

/-- **The bottom side.** -/
theorem transK_far_bottom {h' k : ℕ} {i j : ℤ} {m mv q q' : ℤ × ℤ}
    (hm : IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j)) (hmv : IsWallCell (h' + 2 * k) mv)
    (hq : q ∈ squaresAbove m) (hq' : q' ∈ squaresAbove mv) (hk : 2 ≤ k)
    (hd : sideB mv ≤ k) (hT : sideB mv ≤ sideT (h' + 2 * k) mv) (hL : sideB mv ≤ sideL mv)
    (hR : sideB mv ≤ sideR (h' + 2 * k) mv)
    (hj : j = min (2 * (k : ℤ) - 1) (k + 1 + sideB mv)) (hi : i = 2 * k + j % 2) :
    (k : ℤ) ≤ faceDist (h' + 2 * k) (wallFace (h' + 2 * k) q) (wallFace (h' + 2 * k) q') + 2 := by
  have hm' := kept_bounds hm
  obtain ⟨B, b1, b2, b3, b4, b5, hB⟩ := exists_brick_near (h' + 2 * k) hq
  obtain ⟨B', b1', b2', b3', b4', b5', hB'⟩ := exists_brick_near (h' + 2 * k) hq'
  obtain ⟨c, d⟩ := mv
  obtain ⟨X, Y⟩ := B
  obtain ⟨X', Y'⟩ := B'
  have hmv' : 0 ≤ c ∧ c ≤ 4 * ((h' : ℤ) + 2 * k) + 2 ∧ 0 ≤ d ∧ d ≤ 2 * ((h' : ℤ) + 2 * k) := by
    unfold IsWallCell at hmv; simp only at hmv; push_cast at hmv; omega
  clear hmv hq hq' hm
  simp only [sideB, sideT, sideL, sideR] at hd hT hL hR hj
  simp only at *
  push_cast at *
  have hFb : IsBrick (h' + 2 * k) (X, Y) := by
    unfold IsBrick; push_cast; (try simp only); omega
  rcases hB with ⟨-, e⟩ | ⟨hb, -⟩
  swap
  · exact absurd hFb hb
  rw [e]
  have oF : (k : ℤ) - 1 - d / 2 ≤ outDepth (h' + 2 * k) (X, Y) := by
    apply le_outDepth <;> (try simp only) <;> (try push_cast) <;> omega
  rcases hB' with ⟨hb', e'⟩ | ⟨hb', e'⟩ <;> rw [e']
  · have oG : d / 2 ≤ outDepth (h' + 2 * k) (X', Y') := by
      apply le_outDepth <;> (try simp only) <;> (try push_cast) <;> omega
    have hx : (k : ℤ) - 2 ≤ hexDist (X, Y) (X', Y') :=
      le_hexDist_of_le (Or.inl (by (try simp only); omega))
    have := le_faceDist_bricks hFb hb' hx (by omega)
    omega
  · have hd0 : d / 2 ≤ 0 := by
      unfold IsBrick at hb'; (try simp only at hb'); (try push_cast at hb'); omega
    have := le_faceDist_brick_out hFb (D := (k : ℤ) - 2) (by omega)
    omega

/-- A lower bound on the face distance from lower bounds on the depths. The faces `F, G` are
the bricks `B, B'` when these are bricks, and the outer face otherwise. -/
theorem le_faceDist_of_depths {h : ℕ} {B B' F G : ℤ × ℤ} {D DF DG : ℤ}
    (hB : (IsBrick h B ∧ F = B) ∨ (¬ IsBrick h B ∧ F = outFace))
    (hB' : (IsBrick h B' ∧ G = B') ∨ (¬ IsBrick h B' ∧ G = outFace))
    (hx : IsBrick h B → IsBrick h B' → D ≤ hexDist B B')
    (oF : IsBrick h B → DF ≤ outDepth h B) (oG : IsBrick h B' → DG ≤ outDepth h B')
    (hFo : ¬ IsBrick h B → DF ≤ 0) (hGo : ¬ IsBrick h B' → DG ≤ 0) (hs : D ≤ DF + DG) :
    D ≤ faceDist h F G := by
  have nb : ∀ {X : ℤ × ℤ}, IsBrick h X → X ≠ outFace := fun hX e =>
    not_isBrick_outFace h (e ▸ hX)
  unfold faceDist
  rcases hB with ⟨hb, rfl⟩ | ⟨hb, rfl⟩ <;> rcases hB' with ⟨hb', rfl⟩ | ⟨hb', rfl⟩
  · rw [if_neg (nb hb), if_neg (nb hb')]
    have := hx hb hb'; have := oF hb; have := oG hb'
    omega
  · rw [if_neg (nb hb), if_pos rfl]
    have := oF hb; have := hGo hb'
    omega
  · rw [if_pos rfl, if_neg (nb hb')]
    have := oG hb'; have := hFo hb
    omega
  · simp only [if_true]
    have := hFo hb; have := hGo hb'
    omega

set_option hygiene false in
/-- The data of a kept cell `m` and of `mv`, for the proofs of the sides. -/
macro "side_setup" : tactic => `(tactic| (
  have hm' := kept_bounds hm
  obtain ⟨B, b1, b2, b3, b4, b5, hB⟩ := exists_brick_near (h' + 2 * k) hq
  obtain ⟨B', b1', b2', b3', b4', b5', hB'⟩ := exists_brick_near (h' + 2 * k) hq'
  obtain ⟨c, d⟩ := mv
  obtain ⟨X, Y⟩ := B
  obtain ⟨X', Y'⟩ := B'
  have hmv' : 0 ≤ c ∧ c ≤ 4 * ((h' : ℤ) + 2 * k) + 2 ∧ 0 ≤ d ∧ d ≤ 2 * ((h' : ℤ) + 2 * k) := by
    unfold IsWallCell at hmv; simp only at hmv; push_cast at hmv; omega
  clear hmv hq hq' hm
  (try simp only [sideB, sideT, sideL, sideR] at *)
  (try simp only at *)
  (try push_cast at *)))

set_option hygiene false in
/-- The final count for a side, given the depth bounds `DF` and `DG`. -/
macro "side_finish" DF:term:max DG:term:max : tactic => `(tactic| (
  have key := le_faceDist_of_depths (D := (k : ℤ) - 2) (DF := $DF) (DG := $DG) hB hB'
    (fun _ _ => le_hexDist_of_le (by (try simp only); omega))
    (fun _ => le_outDepth (by (try simp only); omega) (by (try simp only); push_cast; omega)
      (by (try simp only); omega) (by (try simp only); push_cast; omega))
    (fun _ => le_outDepth (by (try simp only); omega) (by (try simp only); push_cast; omega)
      (by (try simp only); omega) (by (try simp only); push_cast; omega))
    (fun hb => by unfold IsBrick at hb; (try simp only at hb); (try push_cast at hb); omega)
    (fun hb => by unfold IsBrick at hb; (try simp only at hb); (try push_cast at hb); omega)
    (by omega)
  omega))

/-- **The top side.** -/
theorem transK_far_top {h' k : ℕ} {i j : ℤ} {m mv q q' : ℤ × ℤ}
    (hm : IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j)) (hmv : IsWallCell (h' + 2 * k) mv)
    (hq : q ∈ squaresAbove m) (hq' : q' ∈ squaresAbove mv) (hk : 2 ≤ k)
    (hd : sideT (h' + 2 * k) mv ≤ k) (hB0 : sideT (h' + 2 * k) mv ≤ sideB mv)
    (hL : sideT (h' + 2 * k) mv ≤ sideL mv) (hR : sideT (h' + 2 * k) mv ≤ sideR (h' + 2 * k) mv)
    (hj : j = max 1 ((k : ℤ) - 1 - sideT (h' + 2 * k) mv)) (hi : i = 2 * k + j % 2) :
    (k : ℤ) ≤ faceDist (h' + 2 * k) (wallFace (h' + 2 * k) q) (wallFace (h' + 2 * k) q') + 2 := by
  side_setup
  side_finish ((k : ℤ) - 1 - ((h' : ℤ) + 2 * k - (d + 1) / 2)) ((h' : ℤ) + 2 * k - (d + 1) / 2)

/-- **The left side.** -/
theorem transK_far_left {h' k : ℕ} {i j : ℤ} {m mv q q' : ℤ × ℤ}
    (hm : IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j)) (hmv : IsWallCell (h' + 2 * k) mv)
    (hq : q ∈ squaresAbove m) (hq' : q' ∈ squaresAbove mv) (hk : 2 ≤ k)
    (hd : sideL mv ≤ k) (hB0 : sideL mv ≤ sideB mv) (hT : sideL mv ≤ sideT (h' + 2 * k) mv)
    (hR : sideL mv ≤ sideR (h' + 2 * k) mv)
    (hi : i = min (4 * (k : ℤ) - 1) (2 * k + 2 + 2 * sideL mv)) (hj : j = k + (i + k) % 2) :
    (k : ℤ) ≤ faceDist (h' + 2 * k) (wallFace (h' + 2 * k) q) (wallFace (h' + 2 * k) q') + 2 := by
  side_setup
  side_finish ((k : ℤ) - 1 - c / 4) (c / 4)

/-- **The right side.** -/
theorem transK_far_right {h' k : ℕ} {i j : ℤ} {m mv q q' : ℤ × ℤ}
    (hm : IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j)) (hmv : IsWallCell (h' + 2 * k) mv)
    (hq : q ∈ squaresAbove m) (hq' : q' ∈ squaresAbove mv) (hk : 2 ≤ k)
    (hd : sideR (h' + 2 * k) mv ≤ k) (hB0 : sideR (h' + 2 * k) mv ≤ sideB mv)
    (hT : sideR (h' + 2 * k) mv ≤ sideT (h' + 2 * k) mv) (hL : sideR (h' + 2 * k) mv ≤ sideL mv)
    (hi : i = max 1 (2 * (k : ℤ) - 2 - 2 * sideR (h' + 2 * k) mv)) (hj : j = k + (i + k) % 2) :
    (k : ℤ) ≤ faceDist (h' + 2 * k) (wallFace (h' + 2 * k) q) (wallFace (h' + 2 * k) q') + 2 := by
  side_setup
  side_finish ((k : ℤ) - 1 - (4 * ((h' : ℤ) + 2 * k) + 2 - c) / 4)
    ((4 * ((h' : ℤ) + 2 * k) + 2 - c) / 4)

/-! ## The chain for an element near the border -/

/-- A moved subwall gives a far chain of one step, if its kept cells are far from `mv`. -/
theorem exists_far_chain_of_trans {h' k : ℕ} (hh' : 1 ≤ h') (he' : Even h') {i j : ℕ}
    (hv : TransVecK k i j) (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ 4 * k) (hj1 : 1 ≤ j)
    (hj2 : j + 1 ≤ 2 * k) {mv : ℤ × ℤ}
    (hne : ∀ m, IsWallCell h' (m.1 - 2 * (i : ℤ), m.2 - 2 * (j : ℤ)) → m ≠ mv)
    (hfar : ∀ m q q', IsWallCell h' (m.1 - 2 * (i : ℤ), m.2 - 2 * (j : ℤ)) →
      q ∈ squaresAbove m → q' ∈ squaresAbove mv →
      (k : ℤ) ≤ faceDist (h' + 2 * k) (wallFace (h' + 2 * k) q) (wallFace (h' + 2 * k) q') + 2) :
    ∃ c : Chain (h' + 2 * k) h' (2 * (2 * k)), c.Far mv k := by
  refine ⟨Chain.cons (transStepK h' k hh' he' hv hi1 hi2 hj1 hj2) (Chain.nil h'), ?_⟩
  intro m _ hown
  have hown' : transOwn h' i j m ≠ none := by
    simpa [Chain.own, transStepK, transShapeK', transShapeK] using hown
  have hc : IsWallCell h' (m.1 - 2 * (i : ℤ), m.2 - 2 * (j : ℤ)) := by
    unfold transOwn at hown'
    split_ifs at hown' with h1
    · exact h1
    · exact absurd rfl hown'
  refine ⟨hne m hc, ?_⟩
  rintro F ⟨q, hq, rfl⟩ G ⟨q', hq', rfl⟩
  exact hfar m q q' hc hq hq'

/-- **A far chain for an element near the border.** If the cell `mv` is at distance at most
`k` from a side of the wall, the moved subwall of height drop `2k` chosen by the nearest side is
a chain of one step that is far from `mv`. -/
theorem exists_far_chain_near {h k : ℕ} (hk : 2 ≤ k) (hh : 2 * k + 1 ≤ h) (he : Even h)
    {mv : ℤ × ℤ} (hmv : mv ∈ fig1WallCells h)
    (hnear : sideB mv ≤ k ∨ sideT h mv ≤ k ∨ sideL mv ≤ k ∨ sideR h mv ≤ k) :
    ∃ c : Chain h (h - 2 * k) (2 * (2 * k)), c.Far mv k := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 * k := ⟨h - 2 * k, by omega⟩
  rw [show h' + 2 * k - 2 * k = h' by omega]
  have hh' : 1 ≤ h' := by omega
  have he' : Even h' := by
    obtain ⟨a, ha⟩ := he
    exact ⟨a - k, by omega⟩
  rw [mem_fig1WallCells_iff (by omega) he] at hmv
  have hmv' := hmv
  obtain ⟨c, d⟩ := mv
  unfold IsWallCell at hmv'
  simp only at hmv'
  have hcase : (sideB (c, d) ≤ sideT (h' + 2 * k) (c, d) ∧ sideB (c, d) ≤ sideL (c, d) ∧
        sideB (c, d) ≤ sideR (h' + 2 * k) (c, d) ∧ sideB (c, d) ≤ k) ∨
      (sideT (h' + 2 * k) (c, d) ≤ sideB (c, d) ∧ sideT (h' + 2 * k) (c, d) ≤ sideL (c, d) ∧
        sideT (h' + 2 * k) (c, d) ≤ sideR (h' + 2 * k) (c, d) ∧ sideT (h' + 2 * k) (c, d) ≤ k) ∨
      (sideL (c, d) ≤ sideB (c, d) ∧ sideL (c, d) ≤ sideT (h' + 2 * k) (c, d) ∧
        sideL (c, d) ≤ sideR (h' + 2 * k) (c, d) ∧ sideL (c, d) ≤ k) ∨
      (sideR (h' + 2 * k) (c, d) ≤ sideB (c, d) ∧ sideR (h' + 2 * k) (c, d) ≤ sideT (h' + 2 * k) (c, d) ∧
        sideR (h' + 2 * k) (c, d) ≤ sideL (c, d) ∧ sideR (h' + 2 * k) (c, d) ≤ k) := by
    omega
  have sB : sideB (c, d) = d / 2 := rfl
  have sT : sideT (h' + 2 * k) (c, d) = (h' : ℤ) + 2 * k - (d + 1) / 2 := by
    simp [sideT]
  have sL : sideL (c, d) = c / 4 := rfl
  have sR : sideR (h' + 2 * k) (c, d) = (4 * ((h' : ℤ) + 2 * k) + 2 - c) / 4 := by
    simp [sideR]
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- the bottom side
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = min (2 * (k : ℤ) - 1) (k + 1 + sideB (c, d)) :=
      ⟨(min (2 * (k : ℤ) - 1) (k + 1 + sideB (c, d))).toNat, by rw [sB]; omega⟩
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = 2 * k + (j : ℤ) % 2 := ⟨2 * k + j % 2, by push_cast; omega⟩
    rw [sB] at h1 h2 h3 h4 hj
    rw [sT] at h1; rw [sL] at h2; rw [sR] at h3
    refine exists_far_chain_of_trans hh' he' (i := i) (j := j)
      ⟨by omega, by omega, by omega, by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
      ?_ ?_
    · intro m hm e
      subst e
      have := kept_bounds hm
      simp only at this
      omega
    · intro m q q' hm hq hq'
      exact transK_far_bottom hm hmv hq hq' hk (by rw [sB]; omega) (by rw [sB, sT]; omega)
        (by rw [sB, sL]; omega) (by rw [sB, sR]; omega) (by rw [sB]; omega) (by omega)
  · -- the top side
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = max 1 ((k : ℤ) - 1 - sideT (h' + 2 * k) (c, d)) :=
      ⟨(max 1 ((k : ℤ) - 1 - sideT (h' + 2 * k) (c, d))).toNat, by omega⟩
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = 2 * k + (j : ℤ) % 2 := ⟨2 * k + j % 2, by push_cast; omega⟩
    rw [sT] at h1 h2 h3 h4 hj
    rw [sB] at h1; rw [sL] at h2; rw [sR] at h3
    refine exists_far_chain_of_trans hh' he' (i := i) (j := j)
      ⟨by omega, by omega, by omega, by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
      ?_ ?_
    · intro m hm e
      subst e
      have := kept_bounds hm
      simp only at this
      omega
    · intro m q q' hm hq hq'
      exact transK_far_top hm hmv hq hq' hk (by rw [sT]; omega) (by rw [sB, sT]; omega)
        (by rw [sT, sL]; omega) (by rw [sT, sR]; omega) (by rw [sT]; omega) (by omega)
  · -- the left side
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = min (4 * (k : ℤ) - 1) (2 * k + 2 + 2 * sideL (c, d)) :=
      ⟨(min (4 * (k : ℤ) - 1) (2 * k + 2 + 2 * sideL (c, d))).toNat, by rw [sL]; omega⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = k + ((i : ℤ) + k) % 2 :=
      ⟨k + (i + k) % 2, by push_cast; omega⟩
    rw [sL] at h1 h2 h3 h4 hi
    rw [sB] at h1; rw [sT] at h2; rw [sR] at h3
    refine exists_far_chain_of_trans hh' he' (i := i) (j := j)
      ⟨by omega, by omega, by omega, by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
      ?_ ?_
    · intro m hm e
      subst e
      have := kept_bounds hm
      simp only at this
      omega
    · intro m q q' hm hq hq'
      exact transK_far_left hm hmv hq hq' hk (by rw [sL]; omega) (by rw [sB, sL]; omega)
        (by rw [sT, sL]; omega) (by rw [sL, sR]; omega) (by rw [sL]; omega) (by omega)
  · -- the right side
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = max 1 (2 * (k : ℤ) - 2 - 2 * sideR (h' + 2 * k) (c, d)) :=
      ⟨(max 1 (2 * (k : ℤ) - 2 - 2 * sideR (h' + 2 * k) (c, d))).toNat, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = k + ((i : ℤ) + k) % 2 :=
      ⟨k + (i + k) % 2, by push_cast; omega⟩
    rw [sR] at h1 h2 h3 h4 hi
    rw [sB] at h1; rw [sT] at h2; rw [sL] at h3
    refine exists_far_chain_of_trans hh' he' (i := i) (j := j)
      ⟨by omega, by omega, by omega, by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
      ?_ ?_
    · intro m hm e
      subst e
      have := kept_bounds hm
      simp only at this
      omega
    · intro m q q' hm hq hq'
      exact transK_far_right hm hmv hq hq' hk (by rw [sR]; omega) (by rw [sB, sR]; omega)
        (by rw [sT, sR]; omega) (by rw [sL, sR]; omega) (by rw [sR]; omega) (by omega)

end GraphMinor.GM13
