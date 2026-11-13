module

public import GraphMinor.Compute.Algorithm77Step75
public import GraphMinor.Compute.Algorithm74Scan

/-!
# Pure `ℕ` Arithmetic Layer for Graph Minors XIII, (7.7)

This file provides the pure `ℕ` arithmetic representations and equivalence lemmas needed to execute
Steps (7.3), (7.6), and (7.5) on the Word RAM:

1. **Natural-number cell coordinates (`cellNatOfLoc`, `WallOfHeight.vertCellNat`,
   `WallOfHeight.vertCellOr20Nat`, `natIsWallCell`):**
   Computes the Fig. 1 cell `(cx, cy) : ℕ × ℕ` of any wall vertex from its `termLocCode` and
   elementary-wall coordinates, matching `W.vertCell` and `W.vertCellOr20`.
2. **Pure `ℕ` brick distance (`natCornerIsBrick`, `natOutDepth`, `natHexDist`,
   `natCornerFaceDist`, `natCellBrickDist`):**
   Computes `computeCellBrickDist h ((cx₁ : ℤ), (cy₁ : ℤ)) ((cx₂ : ℤ), (cy₂ : ℤ))` using only
   `ℕ` operations (`+`, `-`, `*`, `/`, `%`, `min`, `max`).
3. **Pure `ℕ` deleting realization code (`RealizationCode`, `chooseRealizationCode`,
   `vmapOfCode`, `innerOfCode`):**
   Encodes the deleting shape choice `chooseDeletingRealization` as a 3-word code `(mode, Y0, c0)`
   and computes `R.vmap` and `R.inner` in `ℕ`.
4. **Elementary-wall edge index characterization (`elemWallEdge_snd_eq`,
   `elemWallEdge_eq_of_fst_eq_of_horiz`, `elemWallEdge_eq_of_fst_eq_of_vert`,
   `stepInternalVerts_of_elementaryWallAdj`):**
   Characterizes the unique edge `k : Fin (elemWallEdges h).length` for any adjacent pair
   `elementaryWallAdj h p q` in terms of `elemWallCoordIdxVal h` and row equality `p.2 = q.2`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Pure `ℕ` Cell Coordinates and `natIsWallCell` -/

/-- Pure `ℕ` decision procedure for `GM13.IsWallCell h ((cx : ℤ), (cy : ℤ))`. -/
def natIsWallCell (h cx cy : ℕ) : Bool :=
  decide (cx ≤ 4 * h + 2 ∧ cy ≤ 2 * h ∧
    ((cy % 2 = 0 ∧ ¬ (cx ≤ 1 ∧ cy = 0) ∧ ¬ (4 * h + 1 ≤ cx ∧ cy = 2 * h)) ∨
      (cy % 2 = 1 ∧ cx % 2 = 0 ∧ (cx / 2 + (cy - 1) / 2) % 2 = 1)))

theorem natIsWallCell_eq_true_iff (h cx cy : ℕ) :
    natIsWallCell h cx cy = true ↔ GM13.IsWallCell h ((cx : ℤ), (cy : ℤ)) := by
  unfold natIsWallCell GM13.IsWallCell
  simp only [decide_eq_true_eq]
  omega

theorem isWallCell_sub_iff (h cx cy dx dy : ℕ) :
    GM13.IsWallCell h ((cx : ℤ) - (dx : ℤ), (cy : ℤ) - (dy : ℤ)) ↔
      dx ≤ cx ∧ dy ≤ cy ∧ natIsWallCell h (cx - dx) (cy - dy) = true := by
  constructor
  · intro hcell
    have hnonneg : 0 ≤ (cx : ℤ) - (dx : ℤ) ∧ 0 ≤ (cy : ℤ) - (dy : ℤ) := by
      unfold GM13.IsWallCell at hcell
      dsimp at hcell
      omega
    have hdx : dx ≤ cx := by omega
    have hdy : dy ≤ cy := by omega
    refine ⟨hdx, hdy, (natIsWallCell_eq_true_iff h (cx - dx) (cy - dy)).mpr ?_⟩
    have h1 : ((cx - dx : ℕ) : ℤ) = (cx : ℤ) - (dx : ℤ) := by omega
    have h2 : ((cy - dy : ℕ) : ℤ) = (cy : ℤ) - (dy : ℤ) := by omega
    rwa [h1, h2]
  · rintro ⟨hdx, hdy, hnat⟩
    have hcell := (natIsWallCell_eq_true_iff h (cx - dx) (cy - dy)).mp hnat
    have h1 : ((cx - dx : ℕ) : ℤ) = (cx : ℤ) - (dx : ℤ) := by omega
    have h2 : ((cy - dy : ℕ) : ℤ) = (cy : ℤ) - (dy : ℤ) := by omega
    rwa [← h1, ← h2]

/-- Pure `ℕ` cell `(2x, 2y)` of the `u`-th branch vertex of `elemWallCoords h`. -/
def elemWallVertCellNat (h : ℕ) (u : Fin (elemWallNumVerts h)) : ℕ × ℕ :=
  let p := (elemWallCoords h)[u.1]'u.2
  (2 * p.1, 2 * p.2)

theorem elemWallVertCell_eq_cast (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallVertCell h u = (((elemWallVertCellNat h u).1 : ℤ), ((elemWallVertCellNat h u).2 : ℤ)) := by
  unfold elemWallVertCell elemWallVertCellNat
  ext <;> dsimp

/-- Pure `ℕ` open-segment cell of the `k`-th edge of `elemWallEdges h`. -/
def elemWallEdgeCellNat (h : ℕ) (k : Fin (elemWallEdges h).length) : ℕ × ℕ :=
  let e := (elemWallEdges h)[k.1]'k.2
  let p₁ := (elemWallCoords h)[e.1.1]'e.1.2
  let p₂ := (elemWallCoords h)[e.2.1]'e.2.2
  if p₁.2 = p₂.2 then
    (2 * p₁.1 + 1, 2 * p₁.2)
  else
    (2 * p₁.1, 2 * p₁.2 + 1)

theorem elemWallEdgeCell_eq_cast (h : ℕ) (k : Fin (elemWallEdges h).length) :
    elemWallEdgeCell h k = (((elemWallEdgeCellNat h k).1 : ℤ), ((elemWallEdgeCellNat h k).2 : ℤ)) := by
  unfold elemWallEdgeCell elemWallEdgeCellNat
  dsimp only
  split_ifs <;> ext <;> dsimp

/-- Pure `ℕ` cell `(cx, cy)` computed from a vertex location code `loc`. -/
def cellNatOfLoc (h loc : ℕ) : ℕ × ℕ :=
  if h1 : loc < elemWallNumVerts h then
    elemWallVertCellNat h ⟨loc, h1⟩
  else if h2 : loc < elemWallNumVerts h + (elemWallEdges h).length then
    elemWallEdgeCellNat h ⟨loc - elemWallNumVerts h, by omega⟩
  else
    (0, 0)

theorem cellNatOfLoc_of_lt_numVerts {h loc : ℕ} (h1 : loc < elemWallNumVerts h) :
    cellNatOfLoc h loc =
      (2 * ((loc + 1) % (2 * h + 2)), 2 * ((loc + 1) / (2 * h + 2))) := by
  unfold cellNatOfLoc
  simp only [h1, ↓reduceDIte]
  unfold elemWallVertCellNat
  rw [getElem_elemWallCoords h loc h1]

theorem cellNatOfLoc_of_edge {h loc : ℕ} (h1 : ¬ loc < elemWallNumVerts h)
    (h2 : loc < elemWallNumVerts h + (elemWallEdges h).length) :
    let k : Fin (elemWallEdges h).length := ⟨loc - elemWallNumVerts h, by omega⟩
    let e := (elemWallEdges h)[k.1]'k.2
    let x₁ := (e.1.1 + 1) % (2 * h + 2)
    let y₁ := (e.1.1 + 1) / (2 * h + 2)
    let y₂ := (e.2.1 + 1) / (2 * h + 2)
    cellNatOfLoc h loc =
      if y₁ = y₂ then (2 * x₁ + 1, 2 * y₁) else (2 * x₁, 2 * y₁ + 1) := by
  intro k e x₁ y₁ y₂
  unfold cellNatOfLoc
  simp only [h1, h2, ↓reduceDIte]
  unfold elemWallEdgeCellNat
  dsimp only
  rw [getElem_elemWallCoords h e.1.1 e.1.2, getElem_elemWallCoords h e.2.1 e.2.2]

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

/-- Pure `ℕ` cell coordinates `(cx, cy)` of `v : Fin n` in `W`. -/
def vertCellNat (v : Fin n) : ℕ × ℕ :=
  cellNatOfLoc h (termLocCode W v)

theorem vertCell_eq_cast_vertCellNat (v : Fin n) :
    W.vertCell v = (((W.vertCellNat v).1 : ℤ), ((W.vertCellNat v).2 : ℤ)) := by
  unfold vertCell vertCellNat cellNatOfLoc termLocCode
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u =>
    simp only [u.2, ↓reduceDIte]
    exact elemWallVertCell_eq_cast h u
  | none =>
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | some k =>
      dsimp only
      have hnot1 : ¬ (elemWallNumVerts h + k.1 < elemWallNumVerts h) := by omega
      have hlt2 : elemWallNumVerts h + k.1 < elemWallNumVerts h + (elemWallEdges h).length := by
        have := k.2; omega
      simp only [hnot1, hlt2, ↓reduceDIte]
      have hsub : (⟨elemWallNumVerts h + k.1 - elemWallNumVerts h, by omega⟩ :
          Fin (elemWallEdges h).length) = k := by
        ext; dsimp; omega
      rw [hsub]
      exact elemWallEdgeCell_eq_cast h k
    | none =>
      dsimp only
      have hnot1 : ¬ (elemWallNumVerts h + (elemWallEdges h).length < elemWallNumVerts h) := by
        omega
      have hnot2 : ¬ (elemWallNumVerts h + (elemWallEdges h).length <
          elemWallNumVerts h + (elemWallEdges h).length) := by omega
      simp only [hnot1, hnot2, ↓reduceDIte]
      rfl

/-- Pure `ℕ` version of `W.vertCellOr20 v`. -/
def vertCellOr20Nat (v : Fin n) : ℕ × ℕ :=
  let c := W.vertCellNat v
  if v ∈ W.vertexFinset ∧ natIsWallCell h c.1 c.2 = true then c else (2, 0)

theorem vertCellOr20_eq_cast_vertCellOr20Nat (v : Fin n) :
    W.vertCellOr20 v = (((W.vertCellOr20Nat v).1 : ℤ), ((W.vertCellOr20Nat v).2 : ℤ)) := by
  unfold vertCellOr20 vertCellOr20Nat
  rw [W.vertCell_eq_cast_vertCellNat v]
  simp only [← natIsWallCell_eq_true_iff]
  split_ifs <;> rfl

theorem vertCellOr20Nat_eq_ite (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (v : Fin n) :
    W.vertCellOr20Nat v = if v ∈ W.vertexFinset then W.vertCellNat v else (2, 0) := by
  unfold vertCellOr20Nat
  by_cases hv : v ∈ W.vertexFinset
  · have hmem := W.vertCell_mem_fig1WallCells h2 he hW hv
    rw [GM13.mem_fig1WallCells_iff (by omega) he, W.vertCell_eq_cast_vertCellNat] at hmem
    have hnat := (natIsWallCell_eq_true_iff h (W.vertCellNat v).1 (W.vertCellNat v).2).mpr hmem
    simp [hv, hnat]
  · simp [hv]

end WallOfHeight

/-! ### Section 2: Pure `ℕ` Formula for `computeCellBrickDist` -/

/-- Whether the corner square `(sx, sy) ∈ {0, 1} × {0, 1}` around `(cx, cy)` lies in a brick of
the wall of height `h`. -/
def natCornerIsBrick (h cx cy sx sy : ℕ) : Bool :=
  let x := if sx = 0 then cx / 2 else (cx - 1) / 2
  let y := if sy = 0 then cy / 2 else (cy - 1) / 2
  let X := x + (x + y) % 2
  let Y := y
  decide ((sx = 0 ∨ 0 < cx) ∧ (sy = 0 ∨ 0 < cy) ∧ Y < h ∧ 1 ≤ X ∧ X ≤ 2 * h)

/-- Corner square `(q.1, q.2) : ℤ × ℤ` of `((cx : ℤ), (cy : ℤ))` indexed by `(sx, sy) ∈ {0, 1}²`. -/
def cornerSquareInt (cx cy sx sy : ℕ) : ℤ × ℤ :=
  let dx := 1 - (cx : ℤ) % 2
  let dy := 1 - (cy : ℤ) % 2
  (if sx = 0 then (cx : ℤ) + dx else (cx : ℤ) - dx,
   if sy = 0 then (cy : ℤ) + dy else (cy : ℤ) - dy)

theorem squaresAboveList_eq_cornerSquareInt (cx cy : ℕ) :
    squaresAboveList ((cx : ℤ), (cy : ℤ)) =
      ([0, 1, 2, 3] : List ℕ).map (fun d => cornerSquareInt cx cy (d / 2) (d % 2)) := rfl

theorem wallFace_cornerSquareInt (h cx cy sx sy : ℕ) (hsx : sx = 0 ∨ sx = 1)
    (hsy : sy = 0 ∨ sy = 1) :
    let x := if sx = 0 then cx / 2 else (cx - 1) / 2
    let y := if sy = 0 then cy / 2 else (cy - 1) / 2
    let X := x + (x + y) % 2
    let Y := y
    GM13.wallFace h (cornerSquareInt cx cy sx sy) =
      if natCornerIsBrick h cx cy sx sy = true then ((X : ℤ), (Y : ℤ)) else GM13.outFace := by
  dsimp only
  by_cases hcx : sx = 0 ∨ 0 < cx
  · by_cases hcy : sy = 0 ∨ 0 < cy
    · set x := if sx = 0 then cx / 2 else (cx - 1) / 2
      set y := if sy = 0 then cy / 2 else (cy - 1) / 2
      set X := x + (x + y) % 2
      have hcorner : cornerSquareInt cx cy sx sy = (2 * (x : ℤ) + 1, 2 * (y : ℤ) + 1) := by
        dsimp only [cornerSquareInt, x, y]
        rcases hsx with rfl | rfl <;> rcases hsy with rfl | rfl <;> ext <;> dsimp <;> omega
      have hX_cast : (x : ℤ) + ((x : ℤ) + (y : ℤ)) % 2 = (X : ℤ) := by
        change (x : ℤ) + ((x : ℤ) + (y : ℤ)) % 2 = ((x + (x + y) % 2 : ℕ) : ℤ)
        omega
      have hnb : natCornerIsBrick h cx cy sx sy = decide (y < h ∧ 1 ≤ X ∧ X ≤ 2 * h) := by
        unfold natCornerIsBrick
        change decide ((sx = 0 ∨ 0 < cx) ∧ (sy = 0 ∨ 0 < cy) ∧ y < h ∧ 1 ≤ X ∧ X ≤ 2 * h) = _
        simp [hcx, hcy]
      rw [hcorner, GM13.wallFace_square, hX_cast, hnb]
      split_ifs with h1 h2 <;> simp_all only [decide_eq_true_eq] <;> omega
    · have hsy1 : sy = 1 ∧ cy = 0 := by omega
      rcases hsy1 with ⟨rfl, rfl⟩
      have hnot : ¬ GM13.IsBrick h (GM13.brickOf (cornerSquareInt cx 0 sx 1)) := by
        unfold GM13.IsBrick GM13.brickOf cornerSquareInt
        dsimp
        omega
      have hnb : natCornerIsBrick h cx 0 sx 1 = false := by
        unfold natCornerIsBrick
        simp
      rw [GM13.wallFace, hnb]
      simp only [hnot, ↓reduceIte, Bool.false_eq_true]
  · have hsx1 : sx = 1 ∧ cx = 0 := by omega
    rcases hsx1 with ⟨rfl, rfl⟩
    have hnot : ¬ GM13.IsBrick h (GM13.brickOf (cornerSquareInt 0 cy 1 sy)) := by
      unfold GM13.IsBrick GM13.brickOf cornerSquareInt
      dsimp
      omega
    have hnb : natCornerIsBrick h 0 cy 1 sy = false := by
      unfold natCornerIsBrick
      simp
    rw [GM13.wallFace, hnb]
    simp only [hnot, ↓reduceIte, Bool.false_eq_true]

/-- Pure `ℕ` formula for `GM13.outDepth h ((X : ℤ), (Y : ℤ))`. -/
def natOutDepth (h X Y : ℕ) : ℕ :=
  min (min (Y + 1) (h - Y)) (min ((X + 1) / 2) ((2 * h + 2 - X) / 2))

theorem outDepth_eq_cast_natOutDepth {h X Y : ℕ} (hY : Y < h) (hX : X ≤ 2 * h) :
    GM13.outDepth h ((X : ℤ), (Y : ℤ)) = (natOutDepth h X Y : ℤ) := by
  unfold GM13.outDepth natOutDepth
  dsimp only
  omega

/-- Pure `ℕ` formula for `GM13.hexDist ((X₁ : ℤ), (Y₁ : ℤ)) ((X₂ : ℤ), (Y₂ : ℤ))`. -/
def natHexDist (X₁ Y₁ X₂ Y₂ : ℕ) : ℕ :=
  let dX := if X₁ ≤ X₂ then X₂ - X₁ else X₁ - X₂
  let dY := if Y₁ ≤ Y₂ then Y₂ - Y₁ else Y₁ - Y₂
  max dY ((dX + dY) / 2)

theorem hexDist_eq_cast_natHexDist (X₁ Y₁ X₂ Y₂ : ℕ) :
    GM13.hexDist ((X₁ : ℤ), (Y₁ : ℤ)) ((X₂ : ℤ), (Y₂ : ℤ)) = (natHexDist X₁ Y₁ X₂ Y₂ : ℤ) := by
  unfold GM13.hexDist natHexDist
  dsimp only
  split_ifs <;> omega

/-- Pure `ℕ` face distance between corner `(sx₁, sy₁)` of `(cx₁, cy₁)` and corner `(sx₂, sy₂)` of
`(cx₂, cy₂)`. -/
def natCornerFaceDist (h cx₁ cy₁ sx₁ sy₁ cx₂ cy₂ sx₂ sy₂ : ℕ) : ℕ :=
  let x₁ := if sx₁ = 0 then cx₁ / 2 else (cx₁ - 1) / 2
  let y₁ := if sy₁ = 0 then cy₁ / 2 else (cy₁ - 1) / 2
  let X₁ := x₁ + (x₁ + y₁) % 2
  let Y₁ := y₁
  let b₁ := natCornerIsBrick h cx₁ cy₁ sx₁ sy₁
  let x₂ := if sx₂ = 0 then cx₂ / 2 else (cx₂ - 1) / 2
  let y₂ := if sy₂ = 0 then cy₂ / 2 else (cy₂ - 1) / 2
  let X₂ := x₂ + (x₂ + y₂) % 2
  let Y₂ := y₂
  let b₂ := natCornerIsBrick h cx₂ cy₂ sx₂ sy₂
  if !b₁ then
    if !b₂ then 0 else natOutDepth h X₂ Y₂
  else if !b₂ then
    natOutDepth h X₁ Y₁
  else
    min (natHexDist X₁ Y₁ X₂ Y₂) (natOutDepth h X₁ Y₁ + natOutDepth h X₂ Y₂)

theorem natCornerFaceDist_eq_faceDist_toNat (h cx₁ cy₁ sx₁ sy₁ cx₂ cy₂ sx₂ sy₂ : ℕ)
    (hsx₁ : sx₁ = 0 ∨ sx₁ = 1) (hsy₁ : sy₁ = 0 ∨ sy₁ = 1)
    (hsx₂ : sx₂ = 0 ∨ sx₂ = 1) (hsy₂ : sy₂ = 0 ∨ sy₂ = 1) :
    natCornerFaceDist h cx₁ cy₁ sx₁ sy₁ cx₂ cy₂ sx₂ sy₂ =
      (GM13.faceDist h (GM13.wallFace h (cornerSquareInt cx₁ cy₁ sx₁ sy₁))
        (GM13.wallFace h (cornerSquareInt cx₂ cy₂ sx₂ sy₂))).toNat := by
  rw [wallFace_cornerSquareInt h cx₁ cy₁ sx₁ sy₁ hsx₁ hsy₁,
      wallFace_cornerSquareInt h cx₂ cy₂ sx₂ sy₂ hsx₂ hsy₂]
  unfold natCornerFaceDist GM13.faceDist
  dsimp only
  set x₁ := if sx₁ = 0 then cx₁ / 2 else (cx₁ - 1) / 2
  set y₁ := if sy₁ = 0 then cy₁ / 2 else (cy₁ - 1) / 2
  set X₁ := x₁ + (x₁ + y₁) % 2
  set Y₁ := y₁
  set x₂ := if sx₂ = 0 then cx₂ / 2 else (cx₂ - 1) / 2
  set y₂ := if sy₂ = 0 then cy₂ / 2 else (cy₂ - 1) / 2
  set X₂ := x₂ + (x₂ + y₂) % 2
  set Y₂ := y₂
  cases hb₁ : natCornerIsBrick h cx₁ cy₁ sx₁ sy₁ <;>
    cases hb₂ : natCornerIsBrick h cx₂ cy₂ sx₂ sy₂
  · simp [GM13.outFace]
  · have h₂ : Y₂ < h ∧ 1 ≤ X₂ ∧ X₂ ≤ 2 * h := by
      unfold natCornerIsBrick at hb₂
      simp only [decide_eq_true_eq] at hb₂
      exact ⟨hb₂.2.2.1, hb₂.2.2.2.1, hb₂.2.2.2.2⟩
    have hne₂ : ((X₂ : ℤ), (Y₂ : ℤ)) ≠ GM13.outFace := by
      unfold GM13.outFace; intro e; injection e with _ e2; omega
    simp only [Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true, hne₂]
    rw [outDepth_eq_cast_natOutDepth h₂.1 h₂.2.2, Int.toNat_natCast]
  · have h₁ : Y₁ < h ∧ 1 ≤ X₁ ∧ X₁ ≤ 2 * h := by
      unfold natCornerIsBrick at hb₁
      simp only [decide_eq_true_eq] at hb₁
      exact ⟨hb₁.2.2.1, hb₁.2.2.2.1, hb₁.2.2.2.2⟩
    have hne₁ : ((X₁ : ℤ), (Y₁ : ℤ)) ≠ GM13.outFace := by
      unfold GM13.outFace; intro e; injection e with _ e2; omega
    simp only [Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, hne₁]
    rw [outDepth_eq_cast_natOutDepth h₁.1 h₁.2.2, Int.toNat_natCast]
  · have h₁ : Y₁ < h ∧ 1 ≤ X₁ ∧ X₁ ≤ 2 * h := by
      unfold natCornerIsBrick at hb₁
      simp only [decide_eq_true_eq] at hb₁
      exact ⟨hb₁.2.2.1, hb₁.2.2.2.1, hb₁.2.2.2.2⟩
    have h₂ : Y₂ < h ∧ 1 ≤ X₂ ∧ X₂ ≤ 2 * h := by
      unfold natCornerIsBrick at hb₂
      simp only [decide_eq_true_eq] at hb₂
      exact ⟨hb₂.2.2.1, hb₂.2.2.2.1, hb₂.2.2.2.2⟩
    have hne₁ : ((X₁ : ℤ), (Y₁ : ℤ)) ≠ GM13.outFace := by
      unfold GM13.outFace; intro e; injection e with _ e2; omega
    have hne₂ : ((X₂ : ℤ), (Y₂ : ℤ)) ≠ GM13.outFace := by
      unfold GM13.outFace; intro e; injection e with _ e2; omega
    simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true, hne₁, hne₂]
    rw [hexDist_eq_cast_natHexDist, outDepth_eq_cast_natOutDepth h₁.1 h₁.2.2,
        outDepth_eq_cast_natOutDepth h₂.1 h₂.2.2]
    omega

/-- All 16 candidate corner face distances in `ℕ` for `(cx₁, cy₁)` and `(cx₂, cy₂)`. -/
def natFaceDistCandidates (h cx₁ cy₁ cx₂ cy₂ : ℕ) : List ℕ :=
  ([0, 1, 2, 3] : List ℕ).flatMap fun d₁ =>
    ([0, 1, 2, 3] : List ℕ).map fun d₂ =>
      natCornerFaceDist h cx₁ cy₁ (d₁ / 2) (d₁ % 2) cx₂ cy₂ (d₂ / 2) (d₂ % 2)

theorem natFaceDistCandidates_eq (h cx₁ cy₁ cx₂ cy₂ : ℕ) :
    natFaceDistCandidates h cx₁ cy₁ cx₂ cy₂ =
      faceDistCandidates h ((cx₁ : ℤ), (cy₁ : ℤ)) ((cx₂ : ℤ), (cy₂ : ℤ)) := by
  unfold natFaceDistCandidates faceDistCandidates
  rw [squaresAboveList_eq_cornerSquareInt cx₁ cy₁, squaresAboveList_eq_cornerSquareInt cx₂ cy₂,
      List.flatMap_map]
  apply List.flatMap_congr
  intro d₁ hd₁
  rw [List.map_map]
  apply List.map_congr_left
  intro d₂ hd₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd₁ hd₂
  exact natCornerFaceDist_eq_faceDist_toNat h cx₁ cy₁ (d₁ / 2) (d₁ % 2) cx₂ cy₂ (d₂ / 2) (d₂ % 2)
    (by omega) (by omega) (by omega) (by omega)

/-- Pure `ℕ` formula for `computeCellBrickDist h ((cx₁ : ℤ), (cy₁ : ℤ)) ((cx₂ : ℤ), (cy₂ : ℤ))`. -/
def natCellBrickDist (h cx₁ cy₁ cx₂ cy₂ : ℕ) : ℕ :=
  (if natIsWallCell h cx₁ cy₁ then 1 else 0) +
  (if natIsWallCell h cx₂ cy₂ then 1 else 0) +
  listMinNat (natFaceDistCandidates h cx₁ cy₁ cx₂ cy₂)

theorem natCellBrickDist_eq_computeCellBrickDist (h cx₁ cy₁ cx₂ cy₂ : ℕ) :
    natCellBrickDist h cx₁ cy₁ cx₂ cy₂ =
      computeCellBrickDist h ((cx₁ : ℤ), (cy₁ : ℤ)) ((cx₂ : ℤ), (cy₂ : ℤ)) := by
  unfold natCellBrickDist computeCellBrickDist
  rw [natFaceDistCandidates_eq]
  simp only [natIsWallCell_eq_true_iff]

/-! ### Section 3: Pure `ℕ` Realization Code (`RealizationCode`, `chooseRealizationCode`) -/

/-- Pure `ℕ` decision procedure for `GM13.Hole.Good h' (Y0 : ℤ) (c0 : ℤ)`. -/
def natHoleGood (h' Y0 c0 : ℕ) : Bool :=
  decide (1 ≤ Y0 ∧ Y0 ≤ h' ∧ 1 ≤ c0 ∧ c0 ≤ 2 * h' + 1 ∧
    (Y0 % 2 = 0 → c0 + 2 * Y0 ≤ 2 * h' + 2) ∧
    (Y0 % 2 = 1 → 2 * Y0 ≤ c0))

theorem natHoleGood_eq_true_iff (h' Y0 c0 : ℕ) :
    natHoleGood h' Y0 c0 = true ↔ GM13.Hole.Good h' (Y0 : ℤ) (c0 : ℤ) := by
  rw [GM13.Hole.good_iff]
  unfold natHoleGood
  simp only [decide_eq_true_eq]
  omega

/-- Pure `ℕ` 3-word code describing the deleting shape realization in step (7.3) with `r = 0`:
- `mode = 0`: `T(1, 1)`
- `mode = 1`: `T(3, 1)`
- `mode = 2`: `Hole(Y0, c0)`
- `mode = 3`: `rot(Hole(Y0, c0))`. -/
structure RealizationCode where
  mode : ℕ
  Y0 : ℕ
  c0 : ℕ
deriving DecidableEq

/-- Pure `ℕ` version of `GM13.Hole.vmap (Y0 : ℤ) (c0 : ℤ)`. -/
def natHoleVmap (Y0 c0 : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 < Y0 then
    if p.1 < c0 then p else (p.1 + 4, p.2)
  else
    (p.1 + 2, p.2 + 2)

theorem natHoleVmap_eq (Y0 c0 : ℕ) (p : ℕ × ℕ) :
    natHoleVmap Y0 c0 p = GM13.Hole.vmap (Y0 : ℤ) (c0 : ℤ) p := by
  unfold natHoleVmap GM13.Hole.vmap
  simp only [Int.ofNat_lt]

/-- Pure `ℕ` version of `GM13.Hole.innerO (Y0 : ℤ) (c0 : ℤ)`. -/
def natHoleInnerO (Y0 c0 : ℕ) (p q : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.2 = q.2 then
    if p.2 < Y0 ∧ q.1 = c0 then
      [(q.1, p.2), (q.1 + 1, p.2), (q.1 + 2, p.2), (q.1 + 3, p.2)]
    else []
  else if q.2 = Y0 then
    if p.1 < c0 then
      [(p.1, q.2), (p.1 + 1, q.2), (p.1 + 1, q.2 + 1), (p.1 + 2, q.2 + 1)]
    else
      [(p.1 + 4, q.2), (p.1 + 3, q.2), (p.1 + 3, q.2 + 1), (p.1 + 2, q.2 + 1)]
  else []

theorem natHoleInnerO_eq (Y0 c0 : ℕ) (p q : ℕ × ℕ) :
    natHoleInnerO Y0 c0 p q = GM13.Hole.innerO (Y0 : ℤ) (c0 : ℤ) p q := by
  unfold natHoleInnerO GM13.Hole.innerO
  simp only [Int.ofNat_lt, Nat.cast_inj]

/-- Pure `ℕ` version of `GM13.Hole.inner (Y0 : ℤ) (c0 : ℤ)`. -/
def natHoleInner (Y0 c0 : ℕ) (p q : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.1 + p.2 < q.1 + q.2 then
    natHoleInnerO Y0 c0 p q
  else
    (natHoleInnerO Y0 c0 q p).reverse

theorem natHoleInner_eq (Y0 c0 : ℕ) (p q : ℕ × ℕ) :
    natHoleInner Y0 c0 p q = GM13.Hole.inner (Y0 : ℤ) (c0 : ℤ) p q := by
  unfold natHoleInner GM13.Hole.inner
  rw [natHoleInnerO_eq, natHoleInnerO_eq]

/-- Evaluate `R.vmap p` from a `RealizationCode`. -/
def vmapOfCode (h' : ℕ) (code : RealizationCode) (p : ℕ × ℕ) : ℕ × ℕ :=
  if code.mode = 0 then
    (p.1 + 1, p.2 + 1)
  else if code.mode = 1 then
    (p.1 + 3, p.2 + 1)
  else if code.mode = 2 then
    natHoleVmap code.Y0 code.c0 p
  else
    GM13.rotV (h' + 2) (natHoleVmap code.Y0 code.c0 (GM13.rotV h' p))

/-- Evaluate `R.inner p q` from a `RealizationCode`. -/
def innerOfCode (h' : ℕ) (code : RealizationCode) (p q : ℕ × ℕ) : List (ℕ × ℕ) :=
  if code.mode = 0 then
    []
  else if code.mode = 1 then
    []
  else if code.mode = 2 then
    natHoleInner code.Y0 code.c0 p q
  else
    (natHoleInner code.Y0 code.c0 (GM13.rotV h' p) (GM13.rotV h' q)).map (GM13.rotV (h' + 2))

/-- Pure `ℕ` deleting realization code for a vertex cell `(2x, 2y)`. -/
def choiceVertexCode (h' x y : ℕ) : RealizationCode :=
  if (x + y) % 2 = 0 then
    if y % 2 = 0 then
      if natHoleGood h' (y - 1) (x - 1) then ⟨2, y - 1, x - 1⟩
      else if natHoleGood h' y (x - 2) then ⟨2, y, x - 2⟩
      else ⟨3, h' + 2 - y, 2 * h' + 4 - x⟩
    else
      if natHoleGood h' (h' + 2 - y) (2 * h' + 4 - x) then ⟨3, h' + 2 - y, 2 * h' + 4 - x⟩
      else ⟨2, y, x⟩
  else
    if y % 2 = 0 then
      if natHoleGood h' (h' + 1 - y) (2 * h' + 4 - x) then ⟨3, h' + 1 - y, 2 * h' + 4 - x⟩
      else if natHoleGood h' y (x - 1) then ⟨2, y, x - 1⟩
      else ⟨3, h' + 2 - y, 2 * h' + 3 - x⟩
    else
      if natHoleGood h' y (x - 1) then ⟨2, y, x - 1⟩
      else ⟨3, h' + 2 - y, 2 * h' + 5 - x⟩

/-- Pure `ℕ` deleting realization code for a horizontal edge cell `(2x + 1, 2y)`. -/
def choiceHorizCode (h' x y : ℕ) : RealizationCode :=
  if (x + y) % 2 = 0 then
    if y % 2 = 0 then
      if natHoleGood h' (y - 1) (x - 1) then ⟨2, y - 1, x - 1⟩
      else ⟨3, h' + 1 - y, 2 * h' + 3 - x⟩
    else
      if natHoleGood h' y x then ⟨2, y, x⟩
      else ⟨3, h' + 2 - y, 2 * h' + 4 - x⟩
  else
    if y % 2 = 0 then
      if natHoleGood h' (y - 1) x then ⟨2, y - 1, x⟩
      else ⟨3, h' + 1 - y, 2 * h' + 4 - x⟩
    else
      if natHoleGood h' y (x + 1) then ⟨2, y, x + 1⟩
      else ⟨3, h' + 2 - y, 2 * h' + 5 - x⟩

/-- Pure `ℕ` deleting realization code for a vertical edge cell `(2x, 2y + 1)`. -/
def choiceVertCode (h' x y : ℕ) : RealizationCode :=
  if y % 2 = 0 then
    if natHoleGood h' (h' + 1 - y) (2 * h' + 4 - x) then ⟨3, h' + 1 - y, 2 * h' + 4 - x⟩
    else ⟨2, y + 1, x⟩
  else
    if natHoleGood h' y (x - 1) then ⟨2, y, x - 1⟩
    else ⟨3, h' + 2 - y, 2 * h' + 5 - x⟩

/-- Pure `ℕ` version of `chooseDeletingRealization`: selects the 3-word `RealizationCode` for cell
`(cx, cy)`. -/
def chooseRealizationCode (h' cx cy : ℕ) : RealizationCode :=
  let x := cx / 2
  let y := cy / 2
  let t1 := decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)
  let t3 := decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)
  if !t1 then ⟨0, 0, 0⟩
  else if !t3 then ⟨1, 0, 0⟩
  else if cx % 2 = 0 ∧ cy % 2 = 0 then
    choiceVertexCode h' x y
  else if cx % 2 = 1 ∧ cy % 2 = 0 then
    choiceHorizCode h' x y
  else
    choiceVertCode h' x y

private theorem hole_good_cast_iff {h' Y0 c0 : ℕ} {Y0' c0' : ℤ}
    (hY : (Y0 : ℤ) = Y0') (hc : (c0 : ℤ) = c0') :
    natHoleGood h' Y0 c0 = true ↔ GM13.Hole.Good h' Y0' c0' := by
  rw [← hY, ← hc, natHoleGood_eq_true_iff]

private theorem vmap_inner_ofHole {h' Y0 c0 : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {Y0' c0' : ℤ} {m : ℤ × ℤ} (hg : GM13.Hole.Good h' Y0' c0')
    (hd : ¬ GM13.IsWallCell h' (GM13.Hole.cell Y0' c0' m))
    (hY : (Y0 : ℤ) = Y0') (hc : (c0 : ℤ) = c0') :
    (∀ p, vmapOfCode h' ⟨2, Y0, c0⟩ p = (DeletingRealization.ofHole hh' he' hg hd).R.vmap p) ∧
    (∀ p q, innerOfCode h' ⟨2, Y0, c0⟩ p q = (DeletingRealization.ofHole hh' he' hg hd).R.inner p q) := by
  subst hY hc
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · dsimp [vmapOfCode, DeletingRealization.ofHole, GM13.Hole.realization,
      GM13.Shape.Realization.ofOriented]
    exact natHoleVmap_eq Y0 c0 p
  · dsimp [innerOfCode, DeletingRealization.ofHole, GM13.Hole.realization,
      GM13.Shape.Realization.ofOriented]
    exact natHoleInner_eq Y0 c0 p q

private theorem vmap_inner_ofRot {h' Y0 c0 : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {Y0' c0' : ℤ} {m : ℤ × ℤ} (hg : GM13.Hole.Good h' Y0' c0')
    (hd : ¬ GM13.IsWallCell h' (GM13.Hole.cell Y0' c0' (GM13.rotC (h' + 2) m)))
    (hY : (Y0 : ℤ) = Y0') (hc : (c0 : ℤ) = c0') :
    (∀ p, vmapOfCode h' ⟨3, Y0, c0⟩ p = (DeletingRealization.ofRot hh' he' hg hd).R.vmap p) ∧
    (∀ p q, innerOfCode h' ⟨3, Y0, c0⟩ p q = (DeletingRealization.ofRot hh' he' hg hd).R.inner p q) := by
  subst hY hc
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · dsimp [vmapOfCode, DeletingRealization.ofRot, GM13.Shape.Realization.rotate,
      GM13.Hole.realization, GM13.Shape.Realization.ofOriented]
    rw [natHoleVmap_eq]
  · dsimp [innerOfCode, DeletingRealization.ofRot, GM13.Shape.Realization.rotate,
      GM13.Hole.realization, GM13.Shape.Realization.ofOriented]
    rw [natHoleInner_eq]

@[simp]
private theorem vmap_dite {h' : ℕ} {m : ℤ × ℤ} (P : Prop) [Decidable P]
    (a : P → DeletingRealization h' m) (b : ¬ P → DeletingRealization h' m) (p : ℕ × ℕ) :
    (if h : P then a h else b h).R.vmap p =
      if h : P then (a h).R.vmap p else (b h).R.vmap p := by
  cases ‹Decidable P› <;> rfl

@[simp]
private theorem inner_dite {h' : ℕ} {m : ℤ × ℤ} (P : Prop) [Decidable P]
    (a : P → DeletingRealization h' m) (b : ¬ P → DeletingRealization h' m) (p q : ℕ × ℕ) :
    (if h : P then a h else b h).R.inner p q =
      if h : P then (a h).R.inner p q else (b h).R.inner p q := by
  cases ‹Decidable P› <;> rfl

@[simp]
private theorem vmap_congrCell {h' : ℕ} {m₁ m₂ : ℤ × ℤ} (heq : m₁ = m₂)
    (d : DeletingRealization h' m₂) (p : ℕ × ℕ) :
    (DeletingRealization.congrCell heq d).R.vmap p = d.R.vmap p := rfl

@[simp]
private theorem inner_congrCell {h' : ℕ} {m₁ m₂ : ℤ × ℤ} (heq : m₁ = m₂)
    (d : DeletingRealization h' m₂) (p q : ℕ × ℕ) :
    (DeletingRealization.congrCell heq d).R.inner p q = d.R.inner p q := rfl

set_option linter.unusedSimpArgs false in
private theorem choiceVertexCode_spec {h' x y : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    (t1 : GM13.IsWallCell h' (2 * ((x : ℤ) - 1), 2 * ((y : ℤ) - 1)))
    (t3 : GM13.IsWallCell h' (2 * ((x : ℤ) - 3), 2 * ((y : ℤ) - 1))) :
    (∀ p, vmapOfCode h' (choiceVertexCode h' x y) p =
      (choiceVertexRealization hh' he' t1 t3).R.vmap p) ∧
    (∀ p q, innerOfCode h' (choiceVertexCode h' x y) p q =
      (choiceVertexRealization hh' he' t1 t3).R.inner p q) := by
  have hb1 : 3 ≤ x ∧ x ≤ 2 * h' + 2 ∧ 1 ≤ y ∧ y ≤ h' + 1 := by
    have h1 := GM13.isWallCell_vertex_iff.mp t1
    have h3 := GM13.isWallCell_vertex_iff.mp t3
    omega
  unfold choiceVertexCode choiceVertexRealization
  simp only [vmap_dite, inner_dite]
  have hp_iff : (x + y) % 2 = 0 ↔ ((x : ℤ) + (y : ℤ)) % 2 = 0 := by omega
  have hq_iff : y % 2 = 0 ↔ (y : ℤ) % 2 = 0 := by omega
  by_cases hp : (x + y) % 2 = 0
  · have hpZ : ((x : ℤ) + (y : ℤ)) % 2 = 0 := hp_iff.mp hp
    simp only [hp, hpZ, ↓reduceIte, ↓reduceDIte]
    by_cases hq : y % 2 = 0
    · have hqZ : (y : ℤ) % 2 = 0 := hq_iff.mp hq
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y - 1) (c0 := x - 1)
        (Y0' := (y : ℤ) - 1) (c0' := (x : ℤ) - 1) (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' ((y : ℤ) - 1) ((x : ℤ) - 1)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' (y - 1) (x - 1) = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        have hg2_iff := hole_good_cast_iff (h' := h') (Y0 := y) (c0 := x - 2)
          (Y0' := (y : ℤ)) (c0' := (x : ℤ) - 2) (by omega) (by omega)
        by_cases hg2 : GM13.Hole.Good h' (y : ℤ) ((x : ℤ) - 2)
        · simp only [hg2, hg2_iff.mpr hg2, ↓reduceIte, ↓reduceDIte]
          refine vmap_inner_ofHole hh' he' hg2 _ ?_ ?_ <;> omega
        · have hg2_f : natHoleGood h' y (x - 2) = false :=
            Bool.eq_false_iff.mpr (fun h => hg2 (hg2_iff.mp h))
          simp only [hg2, hg2_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
          refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega
    · have hqZ : ¬ (y : ℤ) % 2 = 0 := fun h => hq (hq_iff.mpr h)
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := h' + 2 - y) (c0 := 2 * h' + 4 - x)
        (Y0' := (h' : ℤ) + 2 - (y : ℤ)) (c0' := 2 * (h' : ℤ) + 5 - (x : ℤ) - 1)
        (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' ((h' : ℤ) + 2 - (y : ℤ)) (2 * (h' : ℤ) + 5 - (x : ℤ) - 1)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' (h' + 2 - y) (2 * h' + 4 - x) = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' _ _ ?_ ?_ <;> omega
  · have hpZ : ¬ ((x : ℤ) + (y : ℤ)) % 2 = 0 := fun h => hp (hp_iff.mpr h)
    simp only [hp, hpZ, ↓reduceIte, ↓reduceDIte]
    by_cases hq : y % 2 = 0
    · have hqZ : (y : ℤ) % 2 = 0 := hq_iff.mp hq
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := h' + 1 - y) (c0 := 2 * h' + 4 - x)
        (Y0' := (h' : ℤ) + 2 - (y : ℤ) - 1) (c0' := 2 * (h' : ℤ) + 5 - (x : ℤ) - 1)
        (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' ((h' : ℤ) + 2 - (y : ℤ) - 1) (2 * (h' : ℤ) + 5 - (x : ℤ) - 1)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' (h' + 1 - y) (2 * h' + 4 - x) = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        have hg2_iff := hole_good_cast_iff (h' := h') (Y0 := y) (c0 := x - 1)
          (Y0' := (y : ℤ)) (c0' := (x : ℤ) - 1) (by omega) (by omega)
        by_cases hg2 : GM13.Hole.Good h' (y : ℤ) ((x : ℤ) - 1)
        · simp only [hg2, hg2_iff.mpr hg2, ↓reduceIte, ↓reduceDIte]
          refine vmap_inner_ofHole hh' he' hg2 _ ?_ ?_ <;> omega
        · have hg2_f : natHoleGood h' y (x - 1) = false :=
            Bool.eq_false_iff.mpr (fun h => hg2 (hg2_iff.mp h))
          simp only [hg2, hg2_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
          refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega
    · have hqZ : ¬ (y : ℤ) % 2 = 0 := fun h => hq (hq_iff.mpr h)
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y) (c0 := x - 1)
        (Y0' := (y : ℤ)) (c0' := (x : ℤ) - 1) (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' (y : ℤ) ((x : ℤ) - 1)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' y (x - 1) = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega

set_option linter.unusedSimpArgs false in
private theorem choiceHorizCode_spec {h' x y : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    (t1 : GM13.IsWallCell h' (2 * ((x : ℤ) - 1) + 1, 2 * ((y : ℤ) - 1)))
    (t3 : GM13.IsWallCell h' (2 * ((x : ℤ) - 3) + 1, 2 * ((y : ℤ) - 1))) :
    (∀ p, vmapOfCode h' (choiceHorizCode h' x y) p =
      (choiceHorizRealization hh' he' t1 t3).R.vmap p) ∧
    (∀ p q, innerOfCode h' (choiceHorizCode h' x y) p q =
      (choiceHorizRealization hh' he' t1 t3).R.inner p q) := by
  have hb1 : 3 ≤ x ∧ x ≤ 2 * h' + 1 ∧ 1 ≤ y ∧ y ≤ h' + 1 := by
    have h1 := GM13.isWallCell_horiz_iff.mp t1
    have h3 := GM13.isWallCell_horiz_iff.mp t3
    omega
  unfold choiceHorizCode choiceHorizRealization
  simp only [vmap_dite, inner_dite]
  have hp_iff : (x + y) % 2 = 0 ↔ ((x : ℤ) + (y : ℤ)) % 2 = 0 := by omega
  have hq_iff : y % 2 = 0 ↔ (y : ℤ) % 2 = 0 := by omega
  by_cases hp : (x + y) % 2 = 0
  · have hpZ : ((x : ℤ) + (y : ℤ)) % 2 = 0 := hp_iff.mp hp
    simp only [hp, hpZ, ↓reduceIte, ↓reduceDIte]
    by_cases hq : y % 2 = 0
    · have hqZ : (y : ℤ) % 2 = 0 := hq_iff.mp hq
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y - 1) (c0 := x - 1)
        (Y0' := (y : ℤ) - 1) (c0' := (x : ℤ) - 1) (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' ((y : ℤ) - 1) ((x : ℤ) - 1)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' (y - 1) (x - 1) = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega
    · have hqZ : ¬ (y : ℤ) % 2 = 0 := fun h => hq (hq_iff.mpr h)
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y) (c0 := x)
        (Y0' := (y : ℤ)) (c0' := (x : ℤ)) (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' (y : ℤ) (x : ℤ)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' y x = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega
  · have hpZ : ¬ ((x : ℤ) + (y : ℤ)) % 2 = 0 := fun h => hp (hp_iff.mpr h)
    simp only [hp, hpZ, ↓reduceIte, ↓reduceDIte]
    by_cases hq : y % 2 = 0
    · have hqZ : (y : ℤ) % 2 = 0 := hq_iff.mp hq
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y - 1) (c0 := x)
        (Y0' := (y : ℤ) - 1) (c0' := (x : ℤ)) (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' ((y : ℤ) - 1) (x : ℤ)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' (y - 1) x = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega
    · have hqZ : ¬ (y : ℤ) % 2 = 0 := fun h => hq (hq_iff.mpr h)
      simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
      have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y) (c0 := x + 1)
        (Y0' := (y : ℤ)) (c0' := (x : ℤ) + 1) (by omega) (by omega)
      by_cases hg1 : GM13.Hole.Good h' (y : ℤ) ((x : ℤ) + 1)
      · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
      · have hg1_f : natHoleGood h' y (x + 1) = false :=
          Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
        simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega

set_option linter.unusedSimpArgs false in
private theorem choiceVertCode_spec {h' x y : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    (hm : GM13.IsWallCell (h' + 2) (2 * (x : ℤ), 2 * (y : ℤ) + 1))
    (t1 : GM13.IsWallCell h' (2 * ((x : ℤ) - 1), 2 * ((y : ℤ) - 1) + 1))
    (t3 : GM13.IsWallCell h' (2 * ((x : ℤ) - 3), 2 * ((y : ℤ) - 1) + 1)) :
    (∀ p, vmapOfCode h' (choiceVertCode h' x y) p =
      (choiceVertRealization hh' he' hm t1 t3).R.vmap p) ∧
    (∀ p q, innerOfCode h' (choiceVertCode h' x y) p q =
      (choiceVertRealization hh' he' hm t1 t3).R.inner p q) := by
  have hb1 : 3 ≤ x ∧ x ≤ 2 * h' + 2 ∧ 1 ≤ y ∧ y ≤ h' := by
    have h1 := GM13.isWallCell_vert_iff.mp t1
    have h3 := GM13.isWallCell_vert_iff.mp t3
    omega
  unfold choiceVertCode choiceVertRealization
  simp only [vmap_dite, inner_dite]
  have hq_iff : y % 2 = 0 ↔ (y : ℤ) % 2 = 0 := by omega
  by_cases hq : y % 2 = 0
  · have hqZ : (y : ℤ) % 2 = 0 := hq_iff.mp hq
    simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
    have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := h' + 1 - y) (c0 := 2 * h' + 4 - x)
      (Y0' := (h' : ℤ) + 1 - (y : ℤ)) (c0' := 2 * (h' : ℤ) + 5 - (x : ℤ) - 1)
      (by omega) (by omega)
    by_cases hg1 : GM13.Hole.Good h' ((h' : ℤ) + 1 - (y : ℤ)) (2 * (h' : ℤ) + 5 - (x : ℤ) - 1)
    · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
      refine vmap_inner_ofRot hh' he' hg1 _ ?_ ?_ <;> omega
    · have hg1_f : natHoleGood h' (h' + 1 - y) (2 * h' + 4 - x) = false :=
        Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
      simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
      refine vmap_inner_ofHole hh' he' _ _ ?_ ?_ <;> omega
  · have hqZ : ¬ (y : ℤ) % 2 = 0 := fun h => hq (hq_iff.mpr h)
    simp only [hq, hqZ, ↓reduceIte, ↓reduceDIte]
    have hg1_iff := hole_good_cast_iff (h' := h') (Y0 := y) (c0 := x - 1)
      (Y0' := (y : ℤ)) (c0' := (x : ℤ) - 1) (by omega) (by omega)
    by_cases hg1 : GM13.Hole.Good h' (y : ℤ) ((x : ℤ) - 1)
    · simp only [hg1, hg1_iff.mpr hg1, ↓reduceIte, ↓reduceDIte]
      refine vmap_inner_ofHole hh' he' hg1 _ ?_ ?_ <;> omega
    · have hg1_f : natHoleGood h' y (x - 1) = false :=
        Bool.eq_false_iff.mpr (fun h => hg1 (hg1_iff.mp h))
      simp only [hg1, hg1_f, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
      refine vmap_inner_ofRot hh' he' _ _ ?_ ?_ <;> omega

set_option linter.unusedSimpArgs false in
/-- Equivalence between `chooseRealizationCode h' cx cy` and `chooseDeletingRealization`. -/
theorem chooseRealizationCode_spec {h' cx cy : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    (hm : ((cx : ℤ), (cy : ℤ)) ∈ GM13.fig1WallCells (h' + 2)) :
    (∀ p, vmapOfCode h' (chooseRealizationCode h' cx cy) p =
      (chooseDeletingRealization hh' he' ((cx : ℤ), (cy : ℤ)) hm).R.vmap p) ∧
    (∀ p q, innerOfCode h' (chooseRealizationCode h' cx cy) p q =
      (chooseDeletingRealization hh' he' ((cx : ℤ), (cy : ℤ)) hm).R.inner p q) := by
  have hm_cell : GM13.IsWallCell (h' + 2) ((cx : ℤ), (cy : ℤ)) :=
    (GM13.mem_fig1WallCells_iff (by omega) (GM13.Hole.even_succ_succ he') _).mp hm
  let x := cx / 2
  let y := cy / 2
  have hxZ : (cx : ℤ) / 2 = (x : ℤ) := by omega
  have hyZ : (cy : ℤ) / 2 = (y : ℤ) := by omega
  unfold chooseRealizationCode chooseDeletingRealization
  dsimp only
  simp only [vmap_dite, inner_dite, vmap_congrCell, inner_congrCell]
  try simp only [hxZ, hyZ]
  by_cases hpar1 : (cx : ℤ) % 2 = 0 ∧ (cy : ℤ) % 2 = 0
  · have hpar1_nat : cx % 2 = 0 ∧ cy % 2 = 0 := by omega
    have hcx : cx = 2 * x := by dsimp [x]; omega
    have hcy : cy = 2 * y := by dsimp [y]; omega
    have ht1_iff :
        (decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = true ↔
          GM13.IsWallCell h' (2 * ((x : ℤ) - 1), 2 * ((y : ℤ) - 1)) := by
      rw [Bool.and_eq_true, decide_eq_true_eq, and_assoc,
        ← isWallCell_sub_iff h' cx cy 2 2]
      have h1 : (cx : ℤ) - (2 : ℕ) = 2 * ((x : ℤ) - 1) := by omega
      have h2 : (cy : ℤ) - (2 : ℕ) = 2 * ((y : ℤ) - 1) := by omega
      rw [h1, h2]
    have ht3_iff :
        (decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = true ↔
          GM13.IsWallCell h' (2 * ((x : ℤ) - 3), 2 * ((y : ℤ) - 1)) := by
      rw [Bool.and_eq_true, decide_eq_true_eq, and_assoc,
        ← isWallCell_sub_iff h' cx cy 6 2]
      have h1 : (cx : ℤ) - (6 : ℕ) = 2 * ((x : ℤ) - 3) := by omega
      have h2 : (cy : ℤ) - (2 : ℕ) = 2 * ((y : ℤ) - 1) := by omega
      rw [h1, h2]
    simp only [hpar1, hpar1_nat, and_self, ↓reduceIte, ↓reduceDIte]
    by_cases t1 : GM13.IsWallCell h' (2 * ((x : ℤ) - 1), 2 * ((y : ℤ) - 1))
    · simp only [t1, ht1_iff.mpr t1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
      by_cases t3 : GM13.IsWallCell h' (2 * ((x : ℤ) - 3), 2 * ((y : ℤ) - 1))
      · simp only [t3, ht3_iff.mpr t3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        exact choiceVertexCode_spec hh' he' t1 t3
      · have ht3_f : (decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = false :=
          Bool.eq_false_iff.mpr (fun h => t3 (ht3_iff.mp h))
        simp only [t3, ht3_f, Bool.not_false, ↓reduceIte, ↓reduceDIte]
        refine ⟨fun p => ?_, fun p q => ?_⟩ <;>
          simp [vmapOfCode, innerOfCode, DeletingRealization.ofTrans, GM13.transRealization]
    · have ht1_f : (decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = false :=
        Bool.eq_false_iff.mpr (fun h => t1 (ht1_iff.mp h))
      simp only [t1, ht1_f, Bool.not_false, ↓reduceIte, ↓reduceDIte]
      refine ⟨fun p => ?_, fun p q => ?_⟩ <;>
        simp [vmapOfCode, innerOfCode, DeletingRealization.ofTrans, GM13.transRealization]
  · have hpar1_nat : ¬ (cx % 2 = 0 ∧ cy % 2 = 0) := by omega
    by_cases hpar2 : (cx : ℤ) % 2 = 1 ∧ (cy : ℤ) % 2 = 0
    · have hpar2_nat : cx % 2 = 1 ∧ cy % 2 = 0 := by omega
      have hcx : cx = 2 * x + 1 := by dsimp [x]; omega
      have hcy : cy = 2 * y := by dsimp [y]; omega
      have ht1_iff :
          (decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = true ↔
            GM13.IsWallCell h' (2 * ((x : ℤ) - 1) + 1, 2 * ((y : ℤ) - 1)) := by
        rw [Bool.and_eq_true, decide_eq_true_eq, and_assoc,
          ← isWallCell_sub_iff h' cx cy 2 2]
        have h1 : (cx : ℤ) - (2 : ℕ) = 2 * ((x : ℤ) - 1) + 1 := by omega
        have h2 : (cy : ℤ) - (2 : ℕ) = 2 * ((y : ℤ) - 1) := by omega
        rw [h1, h2]
      have ht3_iff :
          (decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = true ↔
            GM13.IsWallCell h' (2 * ((x : ℤ) - 3) + 1, 2 * ((y : ℤ) - 1)) := by
        rw [Bool.and_eq_true, decide_eq_true_eq, and_assoc,
          ← isWallCell_sub_iff h' cx cy 6 2]
        have h1 : (cx : ℤ) - (6 : ℕ) = 2 * ((x : ℤ) - 3) + 1 := by omega
        have h2 : (cy : ℤ) - (2 : ℕ) = 2 * ((y : ℤ) - 1) := by omega
        rw [h1, h2]
      simp only [hpar1, hpar1_nat, hpar2, hpar2_nat, and_self, ↓reduceIte, ↓reduceDIte]
      by_cases t1 : GM13.IsWallCell h' (2 * ((x : ℤ) - 1) + 1, 2 * ((y : ℤ) - 1))
      · simp only [t1, ht1_iff.mpr t1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        by_cases t3 : GM13.IsWallCell h' (2 * ((x : ℤ) - 3) + 1, 2 * ((y : ℤ) - 1))
        · simp only [t3, ht3_iff.mpr t3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
          exact choiceHorizCode_spec hh' he' t1 t3
        · have ht3_f : (decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = false :=
            Bool.eq_false_iff.mpr (fun h => t3 (ht3_iff.mp h))
          simp only [t3, ht3_f, Bool.not_false, ↓reduceIte, ↓reduceDIte]
          refine ⟨fun p => ?_, fun p q => ?_⟩ <;>
            simp [vmapOfCode, innerOfCode, DeletingRealization.ofTrans, GM13.transRealization]
      · have ht1_f : (decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = false :=
          Bool.eq_false_iff.mpr (fun h => t1 (ht1_iff.mp h))
        simp only [t1, ht1_f, Bool.not_false, ↓reduceIte, ↓reduceDIte]
        refine ⟨fun p => ?_, fun p q => ?_⟩ <;>
          simp [vmapOfCode, innerOfCode, DeletingRealization.ofTrans, GM13.transRealization]
    · have hpar2_nat : ¬ (cx % 2 = 1 ∧ cy % 2 = 0) := by omega
      have hpar3 : cx % 2 = 0 ∧ cy % 2 = 1 := by
        unfold GM13.IsWallCell at hm_cell
        dsimp at hm_cell
        omega
      have hcx : cx = 2 * x := by dsimp [x]; omega
      have hcy : cy = 2 * y + 1 := by dsimp [y]; omega
      have ht1_iff :
          (decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = true ↔
            GM13.IsWallCell h' (2 * ((x : ℤ) - 1), 2 * ((y : ℤ) - 1) + 1) := by
        rw [Bool.and_eq_true, decide_eq_true_eq, and_assoc,
          ← isWallCell_sub_iff h' cx cy 2 2]
        have h1 : (cx : ℤ) - (2 : ℕ) = 2 * ((x : ℤ) - 1) := by omega
        have h2 : (cy : ℤ) - (2 : ℕ) = 2 * ((y : ℤ) - 1) + 1 := by omega
        rw [h1, h2]
      have ht3_iff :
          (decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = true ↔
            GM13.IsWallCell h' (2 * ((x : ℤ) - 3), 2 * ((y : ℤ) - 1) + 1) := by
        rw [Bool.and_eq_true, decide_eq_true_eq, and_assoc,
          ← isWallCell_sub_iff h' cx cy 6 2]
        have h1 : (cx : ℤ) - (6 : ℕ) = 2 * ((x : ℤ) - 3) := by omega
        have h2 : (cy : ℤ) - (2 : ℕ) = 2 * ((y : ℤ) - 1) + 1 := by omega
        rw [h1, h2]
      simp only [hpar1, hpar1_nat, hpar2, hpar2_nat, ↓reduceIte, ↓reduceDIte]
      by_cases t1 : GM13.IsWallCell h' (2 * ((x : ℤ) - 1), 2 * ((y : ℤ) - 1) + 1)
      · simp only [t1, ht1_iff.mpr t1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
        by_cases t3 : GM13.IsWallCell h' (2 * ((x : ℤ) - 3), 2 * ((y : ℤ) - 1) + 1)
        · simp only [t3, ht3_iff.mpr t3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
          have hm_vert : GM13.IsWallCell (h' + 2) (2 * (x : ℤ), 2 * (y : ℤ) + 1) := by
            have h1 : (cx : ℤ) = 2 * (x : ℤ) := by omega
            have h2 : (cy : ℤ) = 2 * (y : ℤ) + 1 := by omega
            rwa [← h1, ← h2]
          exact choiceVertCode_spec hh' he' hm_vert t1 t3
        · have ht3_f : (decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = false :=
            Bool.eq_false_iff.mpr (fun h => t3 (ht3_iff.mp h))
          simp only [t3, ht3_f, Bool.not_false, ↓reduceIte, ↓reduceDIte]
          refine ⟨fun p => ?_, fun p q => ?_⟩ <;>
            simp [vmapOfCode, innerOfCode, DeletingRealization.ofTrans, GM13.transRealization]
      · have ht1_f : (decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = false :=
          Bool.eq_false_iff.mpr (fun h => t1 (ht1_iff.mp h))
        simp only [t1, ht1_f, Bool.not_false, ↓reduceIte, ↓reduceDIte]
        refine ⟨fun p => ?_, fun p q => ?_⟩ <;>
          simp [vmapOfCode, innerOfCode, DeletingRealization.ofTrans, GM13.transRealization]

/-! ### Section 4: Elementary-Wall Edge Index Characterization -/

theorem elemWallVertCoord_div_add_mod (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    (2 * h + 2) * (elemWallVertCoord h u).2 + (elemWallVertCoord h u).1 = u.1 + 1 := by
  unfold elemWallVertCoord
  rw [getElem_elemWallCoords h u.1 u.2]
  exact Nat.div_add_mod (u.1 + 1) (2 * h + 2)

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

theorem elemWallEdge_snd_cases (h : ℕ) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    (e.2.1 = e.1.1 + 1 ∧ (elemWallVertCoord h e.1).2 = (elemWallVertCoord h e.2).2) ∨
    (e.2.1 = e.1.1 + (2 * h + 2) ∧ (elemWallVertCoord h e.1).1 = (elemWallVertCoord h e.2).1 ∧
      (elemWallVertCoord h e.1).2 + 1 = (elemWallVertCoord h e.2).2) := by
  dsimp only
  set e := (elemWallEdges h)[k.1]'k.2
  have hedge := elemWallEdge_isElemWallEdgeCoord h k
  change isElemWallEdgeCoord (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) = true at hedge
  have hdu := elemWallVertCoord_div_add_mod h e.1
  have hdv := elemWallVertCoord_div_add_mod h e.2
  unfold isElemWallEdgeCoord at hedge
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hedge
  rcases hedge with ⟨hy, hx⟩ | ⟨⟨hx, hy⟩, _⟩
  · left
    rw [← hy, hx] at hdv
    exact ⟨by omega, hy⟩
  · right
    rw [← hx, hy, Nat.mul_add, Nat.mul_one] at hdv
    exact ⟨by omega, hx, hy.symm⟩

theorem elemWallEdge_snd_eq_add_one_iff (h : ℕ) (k : Fin (elemWallEdges h).length) :
    ((elemWallEdges h)[k.1]'k.2).2.1 = ((elemWallEdges h)[k.1]'k.2).1.1 + 1 ↔
      (elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).1).2 =
        (elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).2).2 := by
  have hcases := elemWallEdge_snd_cases h k
  dsimp only at hcases
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, _, h3⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · constructor <;> omega

theorem elemWallEdge_eq_of_fst_eq_of_horiz (h : ℕ)
    {k₁ k₂ : Fin (elemWallEdges h).length}
    (hfst : ((elemWallEdges h)[k₁.1]'k₁.2).1 = ((elemWallEdges h)[k₂.1]'k₂.2).1)
    (hh₁ : ((elemWallEdges h)[k₁.1]'k₁.2).2.1 = ((elemWallEdges h)[k₁.1]'k₁.2).1.1 + 1)
    (hh₂ : ((elemWallEdges h)[k₂.1]'k₂.2).2.1 = ((elemWallEdges h)[k₂.1]'k₂.2).1.1 + 1) :
    k₁ = k₂ := by
  have hsnd : ((elemWallEdges h)[k₁.1]'k₁.2).2 = ((elemWallEdges h)[k₂.1]'k₂.2).2 := by
    ext
    rw [hh₁, hh₂, hfst]
  have heq : (elemWallEdges h)[k₁.1]'k₁.2 = (elemWallEdges h)[k₂.1]'k₂.2 :=
    Prod.ext hfst hsnd
  exact Fin.ext ((nodup_elemWallEdges h).getElem_inj_iff.mp heq)

theorem elemWallEdge_eq_of_fst_eq_of_vert (h : ℕ)
    {k₁ k₂ : Fin (elemWallEdges h).length}
    (hfst : ((elemWallEdges h)[k₁.1]'k₁.2).1 = ((elemWallEdges h)[k₂.1]'k₂.2).1)
    (hv₁ : ((elemWallEdges h)[k₁.1]'k₁.2).2.1 ≠ ((elemWallEdges h)[k₁.1]'k₁.2).1.1 + 1)
    (hv₂ : ((elemWallEdges h)[k₂.1]'k₂.2).2.1 ≠ ((elemWallEdges h)[k₂.1]'k₂.2).1.1 + 1) :
    k₁ = k₂ := by
  have hs₁ : ((elemWallEdges h)[k₁.1]'k₁.2).2.1 =
      ((elemWallEdges h)[k₁.1]'k₁.2).1.1 + (2 * h + 2) := by
    rcases elemWallEdge_snd_cases h k₁ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact False.elim (hv₁ h1)
    · exact h1
  have hs₂ : ((elemWallEdges h)[k₂.1]'k₂.2).2.1 =
      ((elemWallEdges h)[k₂.1]'k₂.2).1.1 + (2 * h + 2) := by
    rcases elemWallEdge_snd_cases h k₂ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact False.elim (hv₂ h1)
    · exact h1
  have hsnd : ((elemWallEdges h)[k₁.1]'k₁.2).2 = ((elemWallEdges h)[k₂.1]'k₂.2).2 := by
    ext
    rw [hs₁, hs₂, hfst]
  have heq : (elemWallEdges h)[k₁.1]'k₁.2 = (elemWallEdges h)[k₂.1]'k₂.2 :=
    Prod.ext hfst hsnd
  exact Fin.ext ((nodup_elemWallEdges h).getElem_inj_iff.mp heq)

/-- Characterization of `W.stepInternalVerts p q` for an adjacent pair `elementaryWallAdj h p q`:
there is a unique edge `k : Fin (elemWallEdges h).length` with endpoint indices
`u_min = if p.1 + p.2 < q.1 + q.2 then elemWallCoordIdx h p hpq.1 else elemWallCoordIdx h q hpq.2.1`,
`e.2.1 = e.1.1 + 1 ↔ p.2 = q.2`, and
`W.stepInternalVerts p q = if p.1 + p.2 < q.1 + q.2 then W.internalVerts k else (W.internalVerts k).reverse`. -/
theorem stepInternalVerts_of_elementaryWallAdj {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q) :
    ∃ k : Fin (elemWallEdges h).length,
      let e := (elemWallEdges h)[k.1]'k.2
      (e.1 = if p.1 + p.2 < q.1 + q.2 then
          elemWallCoordIdx h p hpq.1
        else
          elemWallCoordIdx h q hpq.2.1) ∧
      (e.2.1 = e.1.1 + 1 ↔ p.2 = q.2) ∧
      W.stepInternalVerts p q =
        (if p.1 + p.2 < q.1 + q.2 then W.internalVerts k else (W.internalVerts k).reverse) := by
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  dsimp only
  set e := (elemWallEdges h)[k.1]'k.2
  have hfind : findElemWallEdgeIdx h s(p, q) = some k := by
    rw [← hk, findElemWallEdgeIdx_elemWallEdgeSym2]
  have hedge := elemWallEdge_isElemWallEdgeCoord h k
  change isElemWallEdgeCoord (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) = true at hedge
  have hlt_e := isElemWallEdgeCoord_lt hedge
  have hrow : e.2.1 = e.1.1 + 1 ↔ (elemWallVertCoord h e.1).2 = (elemWallVertCoord h e.2).2 :=
    elemWallEdge_snd_eq_add_one_iff h k
  have hstep :
      W.stepInternalVerts p q =
        if p.1 + p.2 < q.1 + q.2 then W.internalVerts k else (W.internalVerts k).reverse := by
    unfold WallOfHeight.stepInternalVerts
    rw [hfind]
  change s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) = s(p, q) at hk
  rcases Sym2.eq_iff.mp hk with ⟨hp_eq, hq_eq⟩ | ⟨hp_eq, hq_eq⟩
  · have hlt : p.1 + p.2 < q.1 + q.2 := by
      rwa [hp_eq, hq_eq] at hlt_e
    have he1 : e.1 = elemWallCoordIdx h p hpq.1 := by
      rw [← elemWallCoordIdx_elemWallVertCoord h e.1]
      congr 1
    have hrow' : e.2.1 = e.1.1 + 1 ↔ p.2 = q.2 := by
      rwa [hp_eq, hq_eq] at hrow
    simp only [hlt, ↓reduceIte]
    exact ⟨he1, hrow', by simpa [hlt] using hstep⟩
  · have hlt : q.1 + q.2 < p.1 + p.2 := by
      rwa [hp_eq, hq_eq] at hlt_e
    have hnot : ¬ (p.1 + p.2 < q.1 + q.2) := by omega
    have he1 : e.1 = elemWallCoordIdx h q hpq.2.1 := by
      rw [← elemWallCoordIdx_elemWallVertCoord h e.1]
      congr 1
    have hrow' : e.2.1 = e.1.1 + 1 ↔ p.2 = q.2 := by
      rw [hp_eq, hq_eq] at hrow
      exact hrow.trans eq_comm
    simp only [hnot, ↓reduceIte]
    exact ⟨he1, hrow', by simpa [hnot] using hstep⟩

end GraphMinor.Compute
