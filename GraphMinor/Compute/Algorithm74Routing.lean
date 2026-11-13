module

public import GraphMinor.Compute.Algorithm74Primitives

/-!
# Coarse Grid Separation and U-Shape Routing for GM XIII (7.4)

This file formalizes the first half of the constructive proof of the algorithm of
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory
Ser. B **63** (1995), (7.4), page 90:

1. **Coarse grid projection and brick-distance lower bounds (`Section 1`):**
   - `coarseCol h x = min (max ((x + 1) / 2) 1) h` projects any elementary-wall coordinate
     `(x, y) ∈ elemWallCoords h` to a coarse column `c ∈ {1, ..., h}`.
   - `gridDepth h (c, y)` measures the distance in the coarse grid `{1, ..., h} × {0, ..., h}`
     to the boundary.
   - `coarse_sep_of_fig1CellBrickDist` and `coarse_depth_sum_of_fig1CellBrickDist` prove that
     `fig1CellBrickDist h cell₁ cell₂ ≥ r` implies both coordinate separation
     `r - 6 ≤ max (2 |c₁ - c₂|) |y₁ - y₂|` and boundary-depth sum
     `r - 6 ≤ gridDepth h (c₁, y₁) + gridDepth h (c₂, y₂)`.
2. **Greedy safe column selection (`Section 2`):**
   - `safeCol` selects for each interior terminal `i` the minimum column `c*_i ≥ c_i + 1`
     avoiding the endpoint windows `[c_j - 2p, c_j] ∪ [c*_j, c*_j + 2p]` of earlier terminals
     `j < i`.
   - `safeCol_bounds` proves `c_i + 1 ≤ c*_i ≤ c_i + i * (4p + 2) + 1`.
   - `safeCol_not_mem_Icc_of_lt` proves that for `i < j`, `c*_j ∉ [c_i - 2p, c*_i + 2p]`.
3. **Interior connectors, 5-segment U-shape detours, and disjointness (`Section 3`):**
   - `connPath` (the 2-segment L-shape connector `P_a`) and `detourPath` (the 5-segment U-shape
     detour `D_{a, γ}`).
   - `isWalkConnected_connPath` and `isWalkConnected_detourPath`.
   - `disjoint_termRegion` (pairwise disjointness of bounding regions of distinct interior
     terminals processed in decreasing `y`-order) and `disjoint_connPath_detourPath` /
     `disjoint_detourPath_of_ne` (pairwise disjointness across distinct colors at the same
     terminal via the 3-conjunct invariant ` sameTermInv`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Coarse Grid Projection and Brick-Distance Lower Bounds -/

/-- Project an elementary-wall column `0 ≤ x ≤ 2h + 1` to a coarse grid column in `{1, ..., h}`. -/
def coarseCol (h x : ℕ) : ℕ :=
  min (max ((x + 1) / 2) 1) h

theorem coarseCol_bounds {h : ℕ} (hh : 1 ≤ h) (x : ℕ) :
    1 ≤ coarseCol h x ∧ coarseCol h x ≤ h := by
  unfold coarseCol
  omega

theorem coarseCol_approx {h x : ℕ} (hh : 1 ≤ h) (hx : x ≤ 2 * h + 1) :
    2 * coarseCol h x ≤ x + 2 ∧ x ≤ 2 * coarseCol h x + 1 := by
  unfold coarseCol
  omega

/-- If `(x, y) ∈ elemWallCoords h` (with `1 ≤ h`), then either `(x, y) ∈ cellPair (coarseCol h x) y`,
or `(x, y)` is adjacent in `elemWallCoordGraph h` to a vertex of `cellPair (coarseCol h x) y` and
lies outside `liftGrid R` for every `R ⊆ {1, ..., h} × {0, ..., h}`. -/
theorem mem_or_adj_cellPair_coarseCol {h : ℕ} (hh : 1 ≤ h) {p : ℕ × ℕ}
    (hp : p ∈ elemWallCoords h) :
    p ∈ cellPair (coarseCol h p.1) p.2 ∨
      ((p.1 = 0 ∨ p.1 = 2 * h + 1) ∧
        ∃ q ∈ cellPair (coarseCol h p.1) p.2, (elemWallCoordGraph h).Adj p q) := by
  rcases p with ⟨x, y⟩
  have hcoords := (mem_elemWallCoords_iff h (x, y)).mp hp
  dsimp at hcoords ⊢
  by_cases hx0 : x = 0
  · subst hx0
    have hy1 : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with rfl | hpos
      · exact False.elim (hcoords.2.2.1 rfl)
      · exact hpos
    have hc : coarseCol h 0 = 1 := by unfold coarseCol; omega
    right
    refine ⟨Or.inl rfl, (1, y), by rw [hc]; simp [cellPair], ?_⟩
    refine ⟨hp, mem_elemWallCoords_of_internal (by omega) (by omega) hcoords.2.1, Or.inl ?_⟩
    simp [isElemWallEdgeCoord]
  · by_cases hxh : x = 2 * h + 1
    · subst hxh
      have hyh : y < h := by
        by_contra hle
        have heq : y = h := by omega
        exact hcoords.2.2.2 (Prod.ext rfl heq)
      have hc : coarseCol h (2 * h + 1) = h := by unfold coarseCol; omega
      right
      refine ⟨Or.inr rfl, (2 * h, y), by rw [hc]; simp [cellPair], ?_⟩
      refine ⟨hp, mem_elemWallCoords_of_internal (by omega) (by omega) hcoords.2.1, Or.inr ?_⟩
      simp [isElemWallEdgeCoord]
    · left
      have hx_int : 1 ≤ x ∧ x ≤ 2 * h := by omega
      have hc : coarseCol h x = (x + 1) / 2 := by unfold coarseCol; omega
      rw [hc]
      unfold cellPair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
      omega

/-- Boundary depth of a coarse grid cell `p = (c, y)` inside `{1, ..., h} × {0, ..., h}`. -/
def gridDepth (h : ℕ) (p : ℕ × ℕ) : ℤ :=
  min (min (p.2 : ℤ) ((h : ℤ) - (p.2 : ℤ)))
    (min ((p.1 : ℤ) - 1) ((h : ℤ) - (p.1 : ℤ)))

theorem gridDepth_nonneg {h : ℕ} {p : ℕ × ℕ}
    (hp : 1 ≤ p.1 ∧ p.1 ≤ h ∧ p.2 ≤ h) :
    0 ≤ gridDepth h p := by
  unfold gridDepth
  omega

theorem bounds_of_le_gridDepth {h : ℕ} {p : ℕ × ℕ} {d : ℕ}
    (hd : (d : ℤ) ≤ gridDepth h p) :
    d + 1 ≤ p.1 ∧ p.1 + d ≤ h ∧ d ≤ p.2 ∧ p.2 + d ≤ h := by
  unfold gridDepth at hd
  omega

/-- From `r ≤ fig1CellBrickDist h c₁ c₂`, there exist squares `q₁ ∈ squaresAbove c₁` and
`q₂ ∈ squaresAbove c₂` with `(r : ℤ) - 2 ≤ faceDist h (wallFace h q₁) (wallFace h q₂)`. -/
theorem exists_squaresAbove_faceDist_ge_of_fig1CellBrickDist {h r : ℕ} {c₁ c₂ : ℤ × ℤ}
    (hr6 : 6 ≤ r) (hr : r ≤ fig1CellBrickDist h c₁ c₂) :
    ∃ q₁ ∈ GM13.squaresAbove c₁, ∃ q₂ ∈ GM13.squaresAbove c₂,
      (r : ℤ) - 2 ≤ GM13.faceDist h (GM13.wallFace h q₁) (GM13.wallFace h q₂) := by
  unfold fig1CellBrickDist at hr
  set S := (fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
    (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
    (GM13.squaresAbove c₁ ×ˢ GM13.squaresAbove c₂)
  have hS_ne : S.Nonempty :=
    ((GM13.squaresAbove_nonempty c₁).prod (GM13.squaresAbove_nonempty c₂)).image _
  have hmem : sInf S ∈ S := Nat.sInf_mem hS_ne
  rcases hmem with ⟨⟨q₁, q₂⟩, ⟨hq₁, hq₂⟩, hsInf⟩
  have hind₁ : GM13.cellInd (GM13.fig1WallCells h) c₁ ≤ 1 := GM13.cellInd_le_one _ _
  have hind₂ : GM13.cellInd (GM13.fig1WallCells h) c₂ ≤ 1 := GM13.cellInd_le_one _ _
  dsimp at hsInf
  rw [← hsInf] at hr
  refine ⟨q₁, hq₁, q₂, hq₂, ?_⟩
  generalize GM13.faceDist h (GM13.wallFace h q₁) (GM13.wallFace h q₂) = fd at hr ⊢
  omega

/-- Helper 1: For a square `q ∈ squaresAbove cell` near `(x, y)`, `wallFace h q` is either
`outFace` (in which case `gridDepth h (coarseCol h x, y) ≤ 1`), or a brick `(X, v)` within
`|X - 2 * coarseCol h x| ≤ 2` and `y - 1 ≤ v ≤ y`. -/
private theorem wallFace_of_squaresAbove_cell {h x y : ℕ} (hh : 1 ≤ h)
    {cell q : ℤ × ℤ}
    (hcell : 2 * (x : ℤ) ≤ cell.1 ∧ cell.1 ≤ 2 * (x : ℤ) + 1 ∧
      2 * (y : ℤ) ≤ cell.2 ∧ cell.2 ≤ 2 * (y : ℤ) + 1)
    (hq : q ∈ GM13.squaresAbove cell) :
    (GM13.wallFace h q = GM13.outFace ∧ gridDepth h (coarseCol h x, y) ≤ 1) ∨
    ∃ X v : ℤ, GM13.wallFace h q = (X, v) ∧ (X, v) ≠ GM13.outFace ∧
      2 * (coarseCol h x : ℤ) - 2 ≤ X ∧ X ≤ 2 * (coarseCol h x : ℤ) + 2 ∧
      (y : ℤ) - 1 ≤ v ∧ v ≤ (y : ℤ) := by
  rcases GM13.exists_of_mem_squaresAbove hq with ⟨u, v, rfl, hu1, hu2, hv1, hv2, -, -⟩
  rw [GM13.wallFace_square]
  split_ifs with hb
  · right
    refine ⟨u + (u + v) % 2, v, rfl, ?_, ?_, ?_, by omega, by omega⟩
    · unfold GM13.outFace
      intro heq
      have : v = -1 := congrArg Prod.snd heq
      omega
    · unfold coarseCol; omega
    · unfold coarseCol; omega
  · left
    refine ⟨rfl, ?_⟩
    unfold gridDepth coarseCol
    dsimp
    omega

/-- Helper 2: `outDepth h (X, v)` is at most `gridDepth h (c, y) + 2` when
`|X - 2c| ≤ 2` and `y - 1 ≤ v ≤ y`. -/
private theorem outDepth_le_gridDepth {h c y : ℕ} {X v : ℤ}
    (hX1 : 2 * (c : ℤ) - 2 ≤ X) (hX2 : X ≤ 2 * (c : ℤ) + 2)
    (hv1 : (y : ℤ) - 1 ≤ v) (hv2 : v ≤ (y : ℤ)) :
    GM13.outDepth h (X, v) ≤ gridDepth h (c, y) + 2 := by
  unfold GM13.outDepth gridDepth
  dsimp
  omega

/-- Helper 3: `hexDist (X₁, v₁) (X₂, v₂)` is bounded by the coarse coordinate differences. -/
private theorem hexDist_le_coarse {c₁ y₁ c₂ y₂ : ℕ} {X₁ v₁ X₂ v₂ : ℤ}
    (hX₁ : 2 * (c₁ : ℤ) - 2 ≤ X₁ ∧ X₁ ≤ 2 * (c₁ : ℤ) + 2)
    (hv₁ : (y₁ : ℤ) - 1 ≤ v₁ ∧ v₁ ≤ (y₁ : ℤ))
    (hX₂ : 2 * (c₂ : ℤ) - 2 ≤ X₂ ∧ X₂ ≤ 2 * (c₂ : ℤ) + 2)
    (hv₂ : (y₂ : ℤ) - 1 ≤ v₂ ∧ v₂ ≤ (y₂ : ℤ)) :
    (GM13.hexDist (X₁, v₁) (X₂, v₂) ≤ 2 * ((c₁ : ℤ) - (c₂ : ℤ)) + 4 ∨
      GM13.hexDist (X₁, v₁) (X₂, v₂) ≤ 2 * ((c₂ : ℤ) - (c₁ : ℤ)) + 4) ∨
    (GM13.hexDist (X₁, v₁) (X₂, v₂) ≤ ((y₁ : ℤ) - (y₂ : ℤ)) + 4 ∨
      GM13.hexDist (X₁, v₁) (X₂, v₂) ≤ ((y₂ : ℤ) - (y₁ : ℤ)) + 4) := by
  unfold GM13.hexDist
  dsimp
  omega

/-- Helper 4: `gridDepth h (c, y)` is 1-Lipschitz in `(c, y)`. -/
private theorem gridDepth_sub_le {h c₁ y₁ c₂ y₂ : ℕ} :
    (gridDepth h (c₁, y₁) - gridDepth h (c₂, y₂) ≤ 2 * ((c₁ : ℤ) - (c₂ : ℤ)) ∨
      gridDepth h (c₁, y₁) - gridDepth h (c₂, y₂) ≤ 2 * ((c₂ : ℤ) - (c₁ : ℤ))) ∨
    (gridDepth h (c₁, y₁) - gridDepth h (c₂, y₂) ≤ (y₁ : ℤ) - (y₂ : ℤ) ∨
      gridDepth h (c₁, y₁) - gridDepth h (c₂, y₂) ≤ (y₂ : ℤ) - (y₁ : ℤ)) := by
  unfold gridDepth
  dsimp
  omega

/-- **Coarse Grid Separation Lemma:**
If two cells `cell₁, cell₂` associated with elementary-wall coordinates `(x₁, y₁)` and `(x₂, y₂)`
satisfy `r ≤ fig1CellBrickDist h cell₁ cell₂`, then their coarse grid projections
`p₁ = (coarseCol h x₁, y₁)` and `p₂ = (coarseCol h x₂, y₂)` satisfy both:
1. `r - 6 ≤ 2 * |p₁.1 - p₂.1| ∨ r - 6 ≤ |p₁.2 - p₂.2|`, and
2. `(r : ℤ) - 6 ≤ gridDepth h p₁ + gridDepth h p₂` (for `6 ≤ r`). -/
theorem coarse_sep_and_depth_of_fig1CellBrickDist {h r x₁ y₁ x₂ y₂ : ℕ}
    (hh : 1 ≤ h) (hr6 : 6 ≤ r)
    (hy₁ : y₁ ≤ h) (hy₂ : y₂ ≤ h)
    {cell₁ cell₂ : ℤ × ℤ}
    (hc₁ : 2 * (x₁ : ℤ) ≤ cell₁.1 ∧ cell₁.1 ≤ 2 * (x₁ : ℤ) + 1 ∧
      2 * (y₁ : ℤ) ≤ cell₁.2 ∧ cell₁.2 ≤ 2 * (y₁ : ℤ) + 1)
    (hc₂ : 2 * (x₂ : ℤ) ≤ cell₂.1 ∧ cell₂.1 ≤ 2 * (x₂ : ℤ) + 1 ∧
      2 * (y₂ : ℤ) ≤ cell₂.2 ∧ cell₂.2 ≤ 2 * (y₂ : ℤ) + 1)
    (hdist : r ≤ fig1CellBrickDist h cell₁ cell₂) :
    (((r : ℤ) - 6 ≤ 2 * ((coarseCol h x₁ : ℤ) - (coarseCol h x₂ : ℤ)) ∨
        (r : ℤ) - 6 ≤ 2 * ((coarseCol h x₂ : ℤ) - (coarseCol h x₁ : ℤ))) ∨
      ((r : ℤ) - 6 ≤ (y₁ : ℤ) - (y₂ : ℤ) ∨
        (r : ℤ) - 6 ≤ (y₂ : ℤ) - (y₁ : ℤ))) ∧
    (r : ℤ) - 6 ≤ gridDepth h (coarseCol h x₁, y₁) + gridDepth h (coarseCol h x₂, y₂) := by
  rcases exists_squaresAbove_faceDist_ge_of_fig1CellBrickDist hr6 hdist with
    ⟨q₁, hq₁, q₂, hq₂, hfd⟩
  have hcb₁ := coarseCol_bounds hh x₁
  have hcb₂ := coarseCol_bounds hh x₂
  have hgd₁_nn : 0 ≤ gridDepth h (coarseCol h x₁, y₁) :=
    gridDepth_nonneg ⟨hcb₁.1, hcb₁.2, hy₁⟩
  have hgd₂_nn : 0 ≤ gridDepth h (coarseCol h x₂, y₂) :=
    gridDepth_nonneg ⟨hcb₂.1, hcb₂.2, hy₂⟩
  have hsub₁₂ := gridDepth_sub_le (h := h) (c₁ := coarseCol h x₁) (y₁ := y₁)
    (c₂ := coarseCol h x₂) (y₂ := y₂)
  have hsub₂₁ := gridDepth_sub_le (h := h) (c₁ := coarseCol h x₂) (y₁ := y₂)
    (c₂ := coarseCol h x₁) (y₂ := y₁)
  rcases wallFace_of_squaresAbove_cell hh hc₁ hq₁ with
    ⟨hf₁, hd₁⟩ | ⟨X₁, v₁, hf₁, hne₁, hX₁_lo, hX₁_hi, hv₁_lo, hv₁_hi⟩ <;>
  rcases wallFace_of_squaresAbove_cell hh hc₂ hq₂ with
    ⟨hf₂, hd₂⟩ | ⟨X₂, v₂, hf₂, hne₂, hX₂_lo, hX₂_hi, hv₂_lo, hv₂_hi⟩
  · rw [hf₁, hf₂, GM13.faceDist_out_out] at hfd
    omega
  · rw [hf₁, hf₂, GM13.faceDist_out_left hne₂] at hfd
    have hod₂ := outDepth_le_gridDepth (h := h) hX₂_lo hX₂_hi hv₂_lo hv₂_hi
    omega
  · rw [hf₁, hf₂, GM13.faceDist_out_right hne₁] at hfd
    have hod₁ := outDepth_le_gridDepth (h := h) hX₁_lo hX₁_hi hv₁_lo hv₁_hi
    omega
  · rw [hf₁, hf₂, GM13.faceDist_of_ne hne₁ hne₂] at hfd
    have hod₁ := outDepth_le_gridDepth (h := h) hX₁_lo hX₁_hi hv₁_lo hv₁_hi
    have hod₂ := outDepth_le_gridDepth (h := h) hX₂_lo hX₂_hi hv₂_lo hv₂_hi
    have hhex := hexDist_le_coarse ⟨hX₁_lo, hX₁_hi⟩ ⟨hv₁_lo, hv₁_hi⟩
      ⟨hX₂_lo, hX₂_hi⟩ ⟨hv₂_lo, hv₂_hi⟩
    omega

/-! ### Section 2: Greedy Safe Column Selection (`safeCol`) -/

/-- The forbidden endpoint window `[c - 2p, c] ∪ [cStar, cStar + 2p]` of size `≤ 4p + 2`
generated by an interior terminal with initial column `c` and safe column `cStar`. -/
def endpointWindow (p c cStar : ℕ) : Finset ℕ :=
  Finset.Icc (c - 2 * p) c ∪ Finset.Icc cStar (cStar + 2 * p)

theorem card_endpointWindow_le (p c cStar : ℕ) :
    (endpointWindow p c cStar).card ≤ 4 * p + 2 := by
  unfold endpointWindow
  have h1 : (Finset.Icc (c - 2 * p) c).card ≤ 2 * p + 1 := by
    rw [Nat.card_Icc]
    omega
  have h2 : (Finset.Icc cStar (cStar + 2 * p)).card = 2 * p + 1 := by
    rw [Nat.card_Icc]
    omega
  have h3 := Finset.card_union_le (Finset.Icc (c - 2 * p) c) (Finset.Icc cStar (cStar + 2 * p))
  omega

/-- Given a sequence of initial columns `c : ℕ → ℕ`, the structural recursion defining at step `i`
the minimum available safe column `safeCol p c i` and cumulative forbidden set `forbidAfter p c i`. -/
def safeColAux (p : ℕ) (c : ℕ → ℕ) : ℕ → ℕ × Finset ℕ
  | 0 =>
    let s := c 0 + 1
    (s, endpointWindow p (c 0) s)
  | i + 1 =>
    let F := (safeColAux p c i).2
    let cand := Finset.Icc (c (i + 1) + 1) (c (i + 1) + (i + 1) * (4 * p + 2) + 1)
    let diff := cand \ F
    let s := if hne : diff.Nonempty then diff.min' hne else c (i + 1) + 1
    (s, F ∪ endpointWindow p (c (i + 1)) s)

/-- The greedy safe column `c*_i` for the `i`-th interior terminal. -/
def safeCol (p : ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  (safeColAux p c i).1

/-- The cumulative forbidden set after choosing `safeCol p c i` for `0, ..., i`. -/
def forbidAfter (p : ℕ) (c : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  (safeColAux p c i).2

theorem safeCol_zero (p : ℕ) (c : ℕ → ℕ) :
    safeCol p c 0 = c 0 + 1 :=
  rfl

theorem forbidAfter_zero (p : ℕ) (c : ℕ → ℕ) :
    forbidAfter p c 0 = endpointWindow p (c 0) (safeCol p c 0) :=
  rfl

theorem forbidAfter_succ (p : ℕ) (c : ℕ → ℕ) (i : ℕ) :
    forbidAfter p c (i + 1) =
      forbidAfter p c i ∪ endpointWindow p (c (i + 1)) (safeCol p c (i + 1)) :=
  rfl

theorem card_forbidAfter_le (p : ℕ) (c : ℕ → ℕ) :
    ∀ i : ℕ, (forbidAfter p c i).card ≤ (i + 1) * (4 * p + 2)
  | 0 => by
    rw [forbidAfter_zero, Nat.zero_add, one_mul]
    exact card_endpointWindow_le p (c 0) (safeCol p c 0)
  | k + 1 => by
    rw [forbidAfter_succ]
    have ih := card_forbidAfter_le p c k
    have hle := Finset.card_union_le (forbidAfter p c k)
      (endpointWindow p (c (k + 1)) (safeCol p c (k + 1)))
    have hwin := card_endpointWindow_le p (c (k + 1)) (safeCol p c (k + 1))
    calc (forbidAfter p c k ∪ endpointWindow p (c (k + 1)) (safeCol p c (k + 1))).card
      _ ≤ (forbidAfter p c k).card + (endpointWindow p (c (k + 1)) (safeCol p c (k + 1))).card := hle
      _ ≤ (k + 1) * (4 * p + 2) + (4 * p + 2) := Nat.add_le_add ih hwin
      _ = (k + 1 + 1) * (4 * p + 2) := by ring

theorem safeCol_diff_nonempty (p : ℕ) (c : ℕ → ℕ) (k : ℕ) :
    (Finset.Icc (c (k + 1) + 1) (c (k + 1) + (k + 1) * (4 * p + 2) + 1) \
      forbidAfter p c k).Nonempty := by
  let cand := Finset.Icc (c (k + 1) + 1) (c (k + 1) + (k + 1) * (4 * p + 2) + 1)
  have hcard_cand : cand.card = (k + 1) * (4 * p + 2) + 1 := by
    dsimp [cand]
    rw [Nat.card_Icc]
    omega
  have hcard_F := card_forbidAfter_le p c k
  apply Finset.nonempty_of_ne_empty
  intro hemp
  have hsub : cand ⊆ forbidAfter p c k := Finset.sdiff_eq_empty_iff_subset.mp hemp
  have hle := Finset.card_le_card hsub
  omega

theorem forbidAfter_mono (p : ℕ) (c : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    forbidAfter p c i ⊆ forbidAfter p c j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | @step m _ ih =>
    rw [forbidAfter_succ]
    exact ih.trans Finset.subset_union_left

theorem endpointWindow_subset_forbidAfter (p : ℕ) (c : ℕ → ℕ) (i : ℕ) :
    endpointWindow p (c i) (safeCol p c i) ⊆ forbidAfter p c i := by
  cases i with
  | zero => exact Finset.Subset.refl _
  | succ k =>
    rw [forbidAfter_succ]
    exact Finset.subset_union_right

/-- Bounds and minimality of `safeCol p c i`:
1. `c i + 1 ≤ safeCol p c i ≤ c i + i * (4 * p + 2) + 1`,
2. for `i = k + 1`, `safeCol p c (k + 1) ∉ forbidAfter p c k`,
3. every `x` with `c i + 1 ≤ x < safeCol p c i` (for `i = k + 1`) belongs to `forbidAfter p c k`. -/
theorem safeCol_spec (p : ℕ) (c : ℕ → ℕ) (i : ℕ) :
    (c i + 1 ≤ safeCol p c i ∧ safeCol p c i ≤ c i + i * (4 * p + 2) + 1) ∧
    (∀ k : ℕ, i = k + 1 → safeCol p c i ∉ forbidAfter p c k) ∧
    (∀ k x : ℕ, i = k + 1 → c i + 1 ≤ x → x < safeCol p c i → x ∈ forbidAfter p c k) := by
  cases i with
  | zero =>
    rw [safeCol_zero]
    refine ⟨⟨by omega, by omega⟩, fun k hk => by omega, fun k x hk => by omega⟩
  | succ k =>
    have hne := safeCol_diff_nonempty p c k
    have hs : safeCol p c (k + 1) =
        (Finset.Icc (c (k + 1) + 1) (c (k + 1) + (k + 1) * (4 * p + 2) + 1) \
          forbidAfter p c k).min' hne := by
      change (if h : (Finset.Icc (c (k + 1) + 1) (c (k + 1) + (k + 1) * (4 * p + 2) + 1) \
          forbidAfter p c k).Nonempty then
        (Finset.Icc (c (k + 1) + 1) (c (k + 1) + (k + 1) * (4 * p + 2) + 1) \
          forbidAfter p c k).min' h else c (k + 1) + 1) = _
      simp only [hne, ↓reduceDIte]
    set cand := Finset.Icc (c (k + 1) + 1) (c (k + 1) + (k + 1) * (4 * p + 2) + 1)
    set diff := cand \ forbidAfter p c k
    have hmem : safeCol p c (k + 1) ∈ diff := by
      rw [hs]
      exact Finset.min'_mem diff hne
    have hmem_sdiff := Finset.mem_sdiff.mp hmem
    have hmem_Icc := Finset.mem_Icc.mp hmem_sdiff.1
    refine ⟨hmem_Icc, ?_, ?_⟩
    · intro k' hk'
      cases hk'
      exact hmem_sdiff.2
    · intro k' x hk' hx_lo hx_lt
      cases hk'
      have hxcand : x ∈ cand := by
        rw [Finset.mem_Icc]
        omega
      by_contra hxF
      have hxdiff : x ∈ diff := Finset.mem_sdiff.mpr ⟨hxcand, hxF⟩
      have hle : safeCol p c (k + 1) ≤ x := by
        rw [hs]
        exact Finset.min'_le diff x hxdiff
      omega

theorem safeCol_bounds (p : ℕ) (c : ℕ → ℕ) (i : ℕ) :
    c i + 1 ≤ safeCol p c i ∧ safeCol p c i ≤ c i + i * (4 * p + 2) + 1 :=
  (safeCol_spec p c i).1

/-- After step `i`, the entire interval `[c i - 2p, safeCol p c i + 2p]` is contained in
`forbidAfter p c i`. -/
theorem Icc_subset_forbidAfter (p : ℕ) (c : ℕ → ℕ) (i : ℕ) :
    Finset.Icc (c i - 2 * p) (safeCol p c i + 2 * p) ⊆ forbidAfter p c i := by
  intro x hx
  rw [Finset.mem_Icc] at hx
  have hwin := endpointWindow_subset_forbidAfter p c i
  by_cases h1 : x ≤ c i
  · apply hwin
    unfold endpointWindow
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    exact Or.inl ⟨hx.1, h1⟩
  · by_cases h2 : safeCol p c i ≤ x
    · apply hwin
      unfold endpointWindow
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      exact Or.inr ⟨h2, hx.2⟩
    · cases i with
      | zero =>
        have hb := (safeCol_bounds p c 0).2
        omega
      | succ k =>
        have hlt := (safeCol_spec p c (k + 1)).2.2 k x rfl (by omega) (by omega)
        exact forbidAfter_mono p c (Nat.le_succ k) hlt

/-- **Key Safe-Column Separation Lemma:**
For any `i < j`, `safeCol p c j` does NOT lie in `[c i - 2p, safeCol p c i + 2p]`. -/
theorem safeCol_not_mem_Icc_of_lt (p : ℕ) (c : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    safeCol p c j ∉ Finset.Icc (c i - 2 * p) (safeCol p c i + 2 * p) := by
  intro hmem
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0) with ⟨k, rfl⟩
  have hik : i ≤ k := by omega
  have hforb : safeCol p c (k + 1) ∈ forbidAfter p c k :=
    forbidAfter_mono p c hik (Icc_subset_forbidAfter p c i hmem)
  exact (safeCol_spec p c (k + 1)).2.1 k rfl hforb

/-- For any `i < j`, `safeCol p c j < c i - 2p` or `safeCol p c i + 2p < safeCol p c j`. -/
theorem safeCol_sep_of_lt (p : ℕ) (c : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    safeCol p c j < c i - 2 * p ∨ safeCol p c i + 2 * p < safeCol p c j := by
  have hnot := safeCol_not_mem_Icc_of_lt p c hij
  rw [Finset.mem_Icc] at hnot
  omega

/-- For any `i ≠ j`, the `[-p, +p]` windows around `safeCol p c i` and `safeCol p c j` are
strictly separated (`safeCol p c i + 2p < safeCol p c j` or `safeCol p c j + 2p < safeCol p c i`). -/
theorem safeCol_sep_of_ne (p : ℕ) (c : ℕ → ℕ) {i j : ℕ} (hne : i ≠ j) :
    safeCol p c i + 2 * p < safeCol p c j ∨ safeCol p c j + 2 * p < safeCol p c i := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hsep := safeCol_sep_of_lt p c hij
    have hb := (safeCol_bounds p c i).1
    omega
  · have hsep := safeCol_sep_of_lt p c hji
    have hb := (safeCol_bounds p c j).1
    omega

/-! ### Section 3: Interior Connectors `connPath`, U-Shape Detours `detourPath`, and Disjointness -/

/-- The 2-segment L-shape connector `P_a = hSeg y c cStar ∪ vSeg cStar y (y_top - gamma)`
routing an interior terminal `(c, y)` to `(cStar, y_top - gamma)` on its trunk row. -/
def connPath (y_top c cStar y gamma : ℕ) : Finset (ℕ × ℕ) :=
  hSeg y c cStar ∪ vSeg cStar y (y_top - gamma)

theorem mem_connPath {y_top c cStar y gamma : ℕ} {q : ℕ × ℕ} :
    q ∈ connPath y_top c cStar y gamma ↔
      q ∈ hSeg y c cStar ∨ q ∈ vSeg cStar y (y_top - gamma) :=
  Finset.mem_union

theorem start_mem_connPath (y_top c cStar y gamma : ℕ) :
    (c, y) ∈ connPath y_top c cStar y gamma :=
  Finset.mem_union_left _ (left_mem_hSeg y c cStar)

theorem end_mem_connPath (y_top c cStar y gamma : ℕ) :
    (cStar, y_top - gamma) ∈ connPath y_top c cStar y gamma :=
  Finset.mem_union_right _ (right_mem_vSeg cStar y (y_top - gamma))

theorem isWalkConnected_connPath (y_top c cStar y gamma : ℕ) :
    IsWalkConnected rectGridGraph (connPath y_top c cStar y gamma) :=
  (isWalkConnected_hSeg y c cStar).union (isWalkConnected_vSeg cStar y (y_top - gamma))
    (right_mem_hSeg y c cStar) (left_mem_vSeg cStar y (y_top - gamma))

/-- The 5-segment U-shape detour `D_{a, γ}` routing trunk row `y_top - gamma` around `connPath`
between `(cStar - gamma, y_top - gamma)` and `(cStar + gamma, y_top - gamma)`. -/
def detourPath (y_top c cStar y gamma : ℕ) : Finset (ℕ × ℕ) :=
  vSeg (cStar - gamma) (y + gamma) (y_top - gamma) ∪
  hSeg (y + gamma) (c - gamma) (cStar - gamma) ∪
  vSeg (c - gamma) (y - gamma) (y + gamma) ∪
  hSeg (y - gamma) (c - gamma) (cStar + gamma) ∪
  vSeg (cStar + gamma) (y - gamma) (y_top - gamma)

theorem left_mem_detourPath (y_top c cStar y gamma : ℕ) :
    (cStar - gamma, y_top - gamma) ∈ detourPath y_top c cStar y gamma := by
  unfold detourPath
  simp only [Finset.mem_union]
  left; left; left; left
  exact right_mem_vSeg (cStar - gamma) (y + gamma) (y_top - gamma)

theorem right_mem_detourPath (y_top c cStar y gamma : ℕ) :
    (cStar + gamma, y_top - gamma) ∈ detourPath y_top c cStar y gamma := by
  unfold detourPath
  simp only [Finset.mem_union]
  right
  exact right_mem_vSeg (cStar + gamma) (y - gamma) (y_top - gamma)

theorem isWalkConnected_detourPath (y_top c cStar y gamma : ℕ) :
    IsWalkConnected rectGridGraph (detourPath y_top c cStar y gamma) := by
  unfold detourPath
  have h1 := isWalkConnected_vSeg (cStar - gamma) (y + gamma) (y_top - gamma)
  have h2 := isWalkConnected_hSeg (y + gamma) (c - gamma) (cStar - gamma)
  have h3 := isWalkConnected_vSeg (c - gamma) (y - gamma) (y + gamma)
  have h4 := isWalkConnected_hSeg (y - gamma) (c - gamma) (cStar + gamma)
  have h5 := isWalkConnected_vSeg (cStar + gamma) (y - gamma) (y_top - gamma)
  have h12 : IsWalkConnected rectGridGraph
      (vSeg (cStar - gamma) (y + gamma) (y_top - gamma) ∪
        hSeg (y + gamma) (c - gamma) (cStar - gamma)) :=
    h1.union h2 (left_mem_vSeg _ _ _) (right_mem_hSeg _ _ _)
  have h123 : IsWalkConnected rectGridGraph
      (vSeg (cStar - gamma) (y + gamma) (y_top - gamma) ∪
        hSeg (y + gamma) (c - gamma) (cStar - gamma) ∪
        vSeg (c - gamma) (y - gamma) (y + gamma)) :=
    h12.union h3 (Finset.mem_union_right _ (left_mem_hSeg _ _ _)) (right_mem_vSeg _ _ _)
  have h1234 : IsWalkConnected rectGridGraph
      (vSeg (cStar - gamma) (y + gamma) (y_top - gamma) ∪
        hSeg (y + gamma) (c - gamma) (cStar - gamma) ∪
        vSeg (c - gamma) (y - gamma) (y + gamma) ∪
        hSeg (y - gamma) (c - gamma) (cStar + gamma)) :=
    h123.union h4 (Finset.mem_union_right _ (left_mem_vSeg _ _ _)) (left_mem_hSeg _ _ _)
  exact h1234.union h5 (Finset.mem_union_right _ (right_mem_hSeg _ _ _)) (left_mem_vSeg _ _ _)

/-- The 3-conjunct invariant satisfied by every point `q = (x, w)` of `connPath` (`γ = 0`) or
`detourPath` (`γ ≥ 1`):
`c - γ ≤ x ≤ cStar + γ ∧ y - γ ≤ w ≤ y_top ∧ (y + γ < w → cStar - γ ≤ x)`. -/
def sameTermInv (y_top c cStar y gamma : ℕ) (q : ℕ × ℕ) : Prop :=
  c - gamma ≤ q.1 ∧ q.1 ≤ cStar + gamma ∧
  y - gamma ≤ q.2 ∧ q.2 ≤ y_top ∧
  (y + gamma < q.2 → cStar - gamma ≤ q.1)

theorem sameTermInv_of_mem_connPath {y_top c cStar y gamma_a : ℕ}
    (hc : c < cStar) (hy : y ≤ y_top - gamma_a) {q : ℕ × ℕ}
    (hq : q ∈ connPath y_top c cStar y gamma_a) :
    sameTermInv y_top c cStar y 0 q := by
  unfold connPath at hq
  unfold sameTermInv
  simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
  rcases hq with hq | hq <;> omega

theorem sameTermInv_of_mem_detourPath {y_top c cStar y gamma : ℕ}
    (hc : c < cStar) (hy : y + gamma ≤ y_top - gamma) {q : ℕ × ℕ}
    (hq : q ∈ detourPath y_top c cStar y gamma) :
    sameTermInv y_top c cStar y gamma q := by
  unfold detourPath at hq
  unfold sameTermInv
  simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
  rcases hq with (((hq | hq) | hq) | hq) | hq <;> omega

theorem not_sameTermInv_of_mem_detourPath_lt {y_top c cStar y gamma₁ gamma₂ : ℕ}
    (hlt : gamma₁ < gamma₂) (hgc : gamma₂ ≤ c) (hgy : gamma₂ ≤ y)
    (hc : c < cStar) (hy : y + gamma₂ ≤ y_top - gamma₂) {q : ℕ × ℕ}
    (hq : q ∈ detourPath y_top c cStar y gamma₂) :
    ¬ sameTermInv y_top c cStar y gamma₁ q := by
  unfold detourPath at hq
  unfold sameTermInv
  simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
  intro hinv
  rcases hq with (((hq | hq) | hq) | hq) | hq <;> omega

/-- For any `1 ≤ gamma`, `connPath` and `detourPath` for the same terminal `(c, y)` are disjoint. -/
theorem disjoint_connPath_detourPath {y_top c cStar y gamma_a gamma : ℕ}
    (hpos : 1 ≤ gamma) (hgc : gamma ≤ c) (hgy : gamma ≤ y)
    (hc : c < cStar) (hy_a : y ≤ y_top - gamma_a) (hy : y + gamma ≤ y_top - gamma) :
    Disjoint (connPath y_top c cStar y gamma_a) (detourPath y_top c cStar y gamma) := by
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  exact not_sameTermInv_of_mem_detourPath_lt hpos hgc hgy hc hy hq₂
    (sameTermInv_of_mem_connPath hc hy_a hq₁)

/-- For any `gamma₁ ≠ gamma₂`, `detourPath`s for `gamma₁` and `gamma₂` at the same terminal are
disjoint. -/
theorem disjoint_detourPath_of_ne {y_top c cStar y gamma₁ gamma₂ : ℕ}
    (hne : gamma₁ ≠ gamma₂)
    (hgc₁ : gamma₁ ≤ c) (hgy₁ : gamma₁ ≤ y) (hy₁ : y + gamma₁ ≤ y_top - gamma₁)
    (hgc₂ : gamma₂ ≤ c) (hgy₂ : gamma₂ ≤ y) (hy₂ : y + gamma₂ ≤ y_top - gamma₂)
    (hc : c < cStar) :
    Disjoint (detourPath y_top c cStar y gamma₁) (detourPath y_top c cStar y gamma₂) := by
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_sameTermInv_of_mem_detourPath_lt hlt hgc₂ hgy₂ hc hy₂ hq₂
      (sameTermInv_of_mem_detourPath hc hy₁ hq₁)
  · exact not_sameTermInv_of_mem_detourPath_lt hgt hgc₁ hgy₁ hc hy₁ hq₁
      (sameTermInv_of_mem_detourPath hc hy₂ hq₂)

/-- Bounding region in `ℕ × ℕ` containing both `connPath` and all `detourPath`s (`γ < p`) of an
interior terminal `(c, y)` with safe column `cStar`:
- horizontal box `[c - p, cStar + p] × [y - p, y + p]`, union
- vertical stem `[cStar - p, cStar + p] × [y - p, y_top]`. -/
def IsInTermRegion (y_top p c cStar y : ℕ) (q : ℕ × ℕ) : Prop :=
  c - p ≤ q.1 ∧ q.1 ≤ cStar + p ∧ y - p ≤ q.2 ∧ q.2 ≤ y_top ∧
  (y + p < q.2 → cStar - p ≤ q.1)

theorem isInTermRegion_of_sameTermInv {y_top p c cStar y gamma : ℕ}
    (hg : gamma ≤ p) {q : ℕ × ℕ} (h : sameTermInv y_top c cStar y gamma q) :
    IsInTermRegion y_top p c cStar y q := by
  unfold sameTermInv at h
  unfold IsInTermRegion
  omega

/-- **Cross-Terminal Disjointness Theorem:**
If terminal `1` is processed before terminal `2` (so `y₂ ≤ y₁` and
`cStar₂ < c₁ - 2p ∨ cStar₁ + 2p < cStar₂`) and `(c₁, y₁)`, `(c₂, y₂)` satisfy the coarse
separation bound, then no point `q : ℕ × ℕ` can belong to both `IsInTermRegion`s. -/
theorem not_and_isInTermRegion {y_top p W c₁ cStar₁ y₁ c₂ cStar₂ y₂ : ℕ}
    (hy_ord : y₂ ≤ y₁)
    (hb₁ : c₁ + 1 ≤ cStar₁ ∧ cStar₁ ≤ c₁ + W)
    (hb₂ : c₂ + 1 ≤ cStar₂ ∧ cStar₂ ≤ c₂ + W)
    (hsafe : cStar₂ < c₁ - 2 * p ∨ cStar₁ + 2 * p < cStar₂)
    (hsep : ((2 * (W + 2 * p + 1 : ℤ) ≤ 2 * ((c₁ : ℤ) - (c₂ : ℤ)) ∨
        2 * (W + 2 * p + 1 : ℤ) ≤ 2 * ((c₂ : ℤ) - (c₁ : ℤ))) ∨
      ((2 * p + 2 : ℤ) ≤ (y₁ : ℤ) - (y₂ : ℤ) ∨
        (2 * p + 2 : ℤ) ≤ (y₂ : ℤ) - (y₁ : ℤ))))
    {q : ℕ × ℕ}
    (hq₁ : IsInTermRegion y_top p c₁ cStar₁ y₁ q)
    (hq₂ : IsInTermRegion y_top p c₂ cStar₂ y₂ q) :
    False := by
  unfold IsInTermRegion at hq₁ hq₂
  omega

end GraphMinor.Compute
