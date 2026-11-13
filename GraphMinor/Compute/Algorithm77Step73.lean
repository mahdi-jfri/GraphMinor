module

public import GraphMinor.Compute.Specs13
public import GraphMinor.GM13.Section7ThreeWall
public import GraphMinor.GM13.Section7SixCells

/-!
# Step (7.3) with `r = 0`: Computable Brick Distance, Path Lifting, and Subwall Realization

This file implements the single-step subwall reduction of Graph Minors XIII, (7.3) with `r = 0`
(page 90) on `WallOfHeight`:

1. **Computable brick distance (`computeCellBrickDist`, `WallOfHeight.computeBrickDist`) and
   `CellWall` distance identity (`Section 1`):**
   - Enumerates the four corner squares `squaresAboveList c` of any cell `c : ℤ × ℤ` and gives an
     explicit arithmetic formula `computeCellBrickDist h c₁ c₂` equal to `fig1CellBrickDist h c₁ c₂`.
   - Proves that on any `C : GM13.CellWall h` (`1 ≤ h`, `Even h`), the plane distance
     `GM13.planeWallDist` between points in the cells of distinct elements `m₁ ≠ m₂` equals
     `fig1CellBrickDist h m₁ m₂`.
2. **Element correspondence for `W.toGMWall` (`Section 2`):**
   - Connects `W.vertCell v` to `(W.toGMWall h2 he hW).elemV m` and `V((W.toGMWall h2 he hW).graph)`.
3. **Lifting elementary-wall paths (`WallOfHeight.liftElemPath`, `Section 3`):**
   - Expands a chain of elementary-wall coordinates into a simple walk in `W` by concatenating
     branch vertices and subdivision paths `W.stepInternalVerts`.
4. **Subwall realization (`WallOfHeight.realizeSubwall`, `Section 4`):**
   - Turns any `R : τ.Realization` (`τ : GM13.Shape h h'`) into `W.realizeSubwall R : WallOfHeight h' G`,
     proving `IsValid` and exact element correspondence with `R.wall (W.toGMWall h2 he hW)`.
5. **Computable deleting shape choice (`chooseDeletingRealization`, `WallOfHeight.step73Subwall`,
   `Section 5`):**
   - Makes `GM13.exists_deleting_shape` (`Section7Choice.lean`) computable and constructs the
     1-step subwall `W.step73Subwall hh' he' v_del : WallOfHeight h' G` avoiding `v_del`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph

/-! ### Section 1: Computable `fig1CellBrickDist` and `CellWall` Distance Identity -/

/-- The four corner squares `(a ± (1 - a % 2), b ± (1 - b % 2))` around a cell `c = (a, b)`. -/
def squaresAboveList (c : ℤ × ℤ) : List (ℤ × ℤ) :=
  let dx := 1 - c.1 % 2
  let dy := 1 - c.2 % 2
  [(c.1 + dx, c.2 + dy), (c.1 + dx, c.2 - dy), (c.1 - dx, c.2 + dy), (c.1 - dx, c.2 - dy)]

theorem squaresAboveList_ne_nil (c : ℤ × ℤ) : squaresAboveList c ≠ [] :=
  List.cons_ne_nil _ _

theorem mem_squaresAboveList_iff (c q : ℤ × ℤ) :
    q ∈ squaresAboveList c ↔ q ∈ GM13.squaresAbove c := by
  constructor
  · intro hq
    unfold squaresAboveList at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa using GM13.corner_mem_squaresAbove (a := c.1) (b := c.2) (Or.inl rfl) (Or.inl rfl)
    · simpa [sub_eq_add_neg] using
        GM13.corner_mem_squaresAbove (a := c.1) (b := c.2) (Or.inl rfl) (Or.inr rfl)
    · simpa [sub_eq_add_neg] using
        GM13.corner_mem_squaresAbove (a := c.1) (b := c.2) (Or.inr rfl) (Or.inl rfl)
    · simpa [sub_eq_add_neg] using
        GM13.corner_mem_squaresAbove (a := c.1) (b := c.2) (Or.inr rfl) (Or.inr rfl)
  · intro hq
    rcases c with ⟨a, b⟩
    rcases q with ⟨x, y⟩
    rw [GM13.mem_squaresAbove_iff] at hq
    unfold squaresAboveList
    dsimp only at hq ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    rcases Int.emod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Int.emod_two_eq_zero_or_one b with h2 | h2 <;>
    omega

/-- All 16 candidate face distances `(faceDist h (wallFace h q₁) (wallFace h q₂)).toNat` for
`q₁ ∈ squaresAboveList c₁` and `q₂ ∈ squaresAboveList c₂`. -/
def faceDistCandidates (h : ℕ) (c₁ c₂ : ℤ × ℤ) : List ℕ :=
  (squaresAboveList c₁).flatMap (fun q₁ =>
    (squaresAboveList c₂).map (fun q₂ =>
      (GM13.faceDist h (GM13.wallFace h q₁) (GM13.wallFace h q₂)).toNat))

theorem faceDistCandidates_ne_nil (h : ℕ) (c₁ c₂ : ℤ × ℤ) :
    faceDistCandidates h c₁ c₂ ≠ [] := by
  unfold faceDistCandidates squaresAboveList
  simp

theorem mem_faceDistCandidates_iff (h : ℕ) (c₁ c₂ : ℤ × ℤ) (d : ℕ) :
    d ∈ faceDistCandidates h c₁ c₂ ↔
      d ∈ (fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
        (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
        (GM13.squaresAbove c₁ ×ˢ GM13.squaresAbove c₂) := by
  unfold faceDistCandidates
  simp only [List.mem_flatMap, List.mem_map, Set.mem_image, Set.mem_prod,
    mem_squaresAboveList_iff]
  constructor
  · rintro ⟨q₁, hq₁, q₂, hq₂, rfl⟩
    exact ⟨(q₁, q₂), ⟨hq₁, hq₂⟩, rfl⟩
  · rintro ⟨⟨q₁, q₂⟩, ⟨hq₁, hq₂⟩, rfl⟩
    exact ⟨q₁, hq₁, q₂, hq₂, rfl⟩

/-- Minimum of a list of natural numbers (`0` on `[]`). -/
def listMinNat : List ℕ → ℕ
  | [] => 0
  | a :: rest => rest.foldl min a

theorem foldl_min_le_init (a : ℕ) : ∀ (L : List ℕ), L.foldl min a ≤ a
  | [] => le_rfl
  | b :: rest => (foldl_min_le_init (min a b) rest).trans (Nat.min_le_left a b)

theorem foldl_min_le_of_mem (a : ℕ) : ∀ {L : List ℕ} {x : ℕ}, x ∈ L → L.foldl min a ≤ x
  | [], _, hx => by nomatch hx
  | b :: rest, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact (foldl_min_le_init (min a x) rest).trans (Nat.min_le_right a x)
    · exact foldl_min_le_of_mem (min a b) hmem

theorem listMinNat_le_of_mem {L : List ℕ} {x : ℕ} (hx : x ∈ L) : listMinNat L ≤ x := by
  cases L with
  | nil => nomatch hx
  | cons a rest =>
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact foldl_min_le_init x rest
    · exact foldl_min_le_of_mem a hmem

theorem foldl_min_mem (a : ℕ) : ∀ (L : List ℕ), L.foldl min a = a ∨ L.foldl min a ∈ L
  | [] => Or.inl rfl
  | b :: rest => by
    dsimp only [List.foldl]
    rcases foldl_min_mem (min a b) rest with heq | hmem
    · rw [heq]
      by_cases hle : a ≤ b
      · exact Or.inl (Nat.min_eq_left hle)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Nat.min_eq_right (Nat.le_of_not_le hle))))
    · exact Or.inr (List.mem_cons_of_mem b hmem)

theorem listMinNat_mem {L : List ℕ} (hne : L ≠ []) : listMinNat L ∈ L := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons a rest =>
    rcases foldl_min_mem a rest with heq | hmem
    · rw [listMinNat, heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem a hmem

theorem listMinNat_eq_sInf {L : List ℕ} (hne : L ≠ []) {S : Set ℕ}
    (hS : ∀ x, x ∈ L ↔ x ∈ S) :
    listMinNat L = sInf S := by
  have hmemS : listMinNat L ∈ S := (hS _).mp (listMinNat_mem hne)
  have hS_ne : S.Nonempty := ⟨listMinNat L, hmemS⟩
  apply le_antisymm
  · exact listMinNat_le_of_mem ((hS _).mpr (Nat.sInf_mem hS_ne))
  · exact Nat.sInf_le hmemS

/-- Computable formula for `fig1CellBrickDist h c₁ c₂` when `1 ≤ h` and `Even h`. -/
def computeCellBrickDist (h : ℕ) (c₁ c₂ : ℤ × ℤ) : ℕ :=
  (if GM13.IsWallCell h c₁ then 1 else 0) +
  (if GM13.IsWallCell h c₂ then 1 else 0) +
  listMinNat (faceDistCandidates h c₁ c₂)

theorem computeCellBrickDist_eq_fig1CellBrickDist {h : ℕ} (hh : 1 ≤ h) (he : Even h)
    (c₁ c₂ : ℤ × ℤ) :
    computeCellBrickDist h c₁ c₂ = fig1CellBrickDist h c₁ c₂ := by
  unfold computeCellBrickDist fig1CellBrickDist
  have h1 : (if GM13.IsWallCell h c₁ then 1 else 0) = GM13.cellInd (GM13.fig1WallCells h) c₁ := by
    unfold GM13.cellInd
    rw [GM13.mem_fig1WallCells_iff hh he]
    split_ifs <;> rfl
  have h2 : (if GM13.IsWallCell h c₂ then 1 else 0) = GM13.cellInd (GM13.fig1WallCells h) c₂ := by
    unfold GM13.cellInd
    rw [GM13.mem_fig1WallCells_iff hh he]
    split_ifs <;> rfl
  have h3 : listMinNat (faceDistCandidates h c₁ c₂) =
      sInf ((fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
        (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
        (GM13.squaresAbove c₁ ×ˢ GM13.squaresAbove c₂)) :=
    listMinNat_eq_sInf (faceDistCandidates_ne_nil h c₁ c₂) (mem_faceDistCandidates_iff h c₁ c₂)
  rw [h1, h2, h3]

namespace WallOfHeight

/-- Computable brick distance `d(u, v)` between vertices `u, v` of `W : WallOfHeight h G`. -/
def computeBrickDist {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (u v : Fin n) : ℕ :=
  if u = v then 0 else computeCellBrickDist h (W.vertCell u) (W.vertCell v)

theorem computeBrickDist_eq_brickDist {h n : ℕ} (hh : 1 ≤ h) (he : Even h)
    {G : MultiDigraph n} (W : WallOfHeight h G) (u v : Fin n) :
    W.computeBrickDist u v = W.brickDist u v := by
  unfold computeBrickDist brickDist
  split_ifs
  · rfl
  · exact computeCellBrickDist_eq_fig1CellBrickDist hh he _ _

end WallOfHeight

theorem fig1CellBrickDist_self_le_two (h : ℕ) (c : ℤ × ℤ) :
    fig1CellBrickDist h c c ≤ 2 := by
  unfold fig1CellBrickDist
  have h1 : GM13.cellInd (GM13.fig1WallCells h) c ≤ 1 := by
    unfold GM13.cellInd; split_ifs <;> omega
  have hq : GM13.cellUp c ∈ GM13.squaresAbove c := GM13.cellUp_mem_squaresAbove c
  have h0 : 0 ∈ (fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
      (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
      (GM13.squaresAbove c ×ˢ GM13.squaresAbove c) := by
    refine ⟨(GM13.cellUp c, GM13.cellUp c), ⟨hq, hq⟩, ?_⟩
    dsimp only
    rw [GM13.faceDist_self (GM13.isBrick_or_eq_outFace_wallFace h _)]
    rfl
  have hs : sInf ((fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
      (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
      (GM13.squaresAbove c ×ˢ GM13.squaresAbove c)) ≤ 0 :=
    Nat.sInf_le h0
  omega

/-- For any cell wall `C : GM13.CellWall h` (`1 ≤ h`, `Even h`) and points `s, t : ℝ × ℝ` in the
cells of distinct elements `m₁ ≠ m₂` of `fig1WallCells h`, the plane distance on `C.𝒰` equals
`fig1CellBrickDist h m₁ m₂`. -/
theorem cellWall_planeWallDist_eq_fig1CellBrickDist {h : ℕ} (hh : 1 ≤ h) (he : Even h)
    (C : GM13.CellWall h) {m₁ m₂ : ℤ × ℤ}
    (hm₁ : m₁ ∈ GM13.fig1WallCells h) (hm₂ : m₂ ∈ GM13.fig1WallCells h) (hne : m₁ ≠ m₂)
    {s t : ℝ × ℝ} (hs : GM13.cellCode s ∈ C.cells m₁) (ht : GM13.cellCode t ∈ C.cells m₂) :
    GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C.𝒰)
      (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) =
      fig1CellBrickDist h m₁ m₂ := by
  have hst : s ≠ t := fun e => by
    subst e
    exact Set.disjoint_left.mp (C.disjoint m₁ hm₁ m₂ hm₂ hne) hs ht
  let s₂ := GM13.cellCenter m₁
  let t₂ := GM13.cellCenter m₂
  have hs₂_code : GM13.cellCode s₂ = m₁ := GM13.cellCode_cellCenter m₁
  have ht₂_code : GM13.cellCode t₂ = m₂ := GM13.cellCode_cellCenter m₂
  have hst₂_code : GM13.cellCode s₂ ≠ GM13.cellCode t₂ := by rw [hs₂_code, ht₂_code]; exact hne
  have hst₂ : s₂ ≠ t₂ := fun e => hst₂_code (congrArg GM13.cellCode e)
  have heq := GM13.CellWall.planeWallDist_eq C (GM13.CellWall.fig1 hh he) hm₁ hm₂
    hs ht (by simpa [GM13.CellWall.fig1] using hs₂_code)
    (by simpa [GM13.CellWall.fig1] using ht₂_code) hst hst₂
  have hU : (GM13.CellWall.fig1 hh he).𝒰 = GM13.fig1WallCells h := rfl
  rw [heq, hU, ← GM13.fig1WallSet_eq_cellSet,
    planeWallDist_fig1_eq_fig1CellBrickDist hh he hst₂_code, hs₂_code, ht₂_code]

/-! ### Section 2: `W.vertCell` and `(W.toGMWall h2 he hW).elemV` -/

instance instDecidableMemElementaryWallVerts (h : ℕ) (p : ℕ × ℕ) :
    Decidable (p ∈ GM13.elementaryWallVerts h) := by
  change Decidable (p.1 ≤ 2 * h + 1 ∧ p.2 ≤ h ∧ p ≠ (0, 0) ∧ p ≠ (2 * h + 1, h))
  infer_instance

theorem elemWallVertCell_eq_vCell (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallVertCell h u = GM13.vCell (elemWallVertCoord h u) := rfl

theorem elemWallEdgeCell_eq_eCell (h : ℕ) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    elemWallEdgeCell h k = GM13.eCell (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) := by
  intro e
  have hedge := elemWallEdge_isElemWallEdgeCoord h k
  change isElemWallEdgeCoord (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) = true at hedge
  change (if (elemWallVertCoord h e.1).2 = (elemWallVertCoord h e.2).2 then
      (2 * ((elemWallVertCoord h e.1).1 : ℤ) + 1, 2 * ((elemWallVertCoord h e.1).2 : ℤ))
    else
      (2 * ((elemWallVertCoord h e.1).1 : ℤ), 2 * ((elemWallVertCoord h e.1).2 : ℤ) + 1)) =
    GM13.eCell (elemWallVertCoord h e.1) (elemWallVertCoord h e.2)
  generalize elemWallVertCoord h e.1 = p₁ at hedge ⊢
  generalize elemWallVertCoord h e.2 = p₂ at hedge ⊢
  unfold isElemWallEdgeCoord at hedge
  unfold GM13.eCell
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hedge
  split_ifs with heq <;> rcases hedge with ⟨_, _⟩ | ⟨⟨_, _⟩, _⟩ <;> ext <;> dsimp <;> omega

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

theorem vertCell_branchVert (hW : W.IsValid) (u : Fin (elemWallNumVerts h)) :
    W.vertCell (W.branchVert u) = GM13.vCell (elemWallVertCoord h u) := by
  unfold vertCell
  cases hfind : (List.finRange (elemWallNumVerts h)).find?
      (fun u' => decide (W.branchVert u' = W.branchVert u)) with
  | none =>
    have hnone := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp at hnone
  | some u' =>
    have heq : W.branchVert u' = W.branchVert u := by
      simpa using List.find?_some hfind
    rw [hW.1 heq]
    exact elemWallVertCell_eq_vCell h u

theorem vertCell_of_mem_internalVerts (hW : W.IsValid)
    {k : Fin (elemWallEdges h).length} {v : Fin n} (hv : v ∈ W.internalVerts k) :
    let e := (elemWallEdges h)[k.1]'k.2
    W.vertCell v = GM13.eCell (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) := by
  intro e
  unfold vertCell
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find?
      (fun u => decide (W.branchVert u = v)) with
  | some u =>
    have hu : W.branchVert u = v := by simpa using List.find?_some hfind1
    exact False.elim (hW.2.2.1 k u (hu ▸ hv))
  | none =>
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k' => decide (v ∈ W.internalVerts k')) with
    | none =>
      have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
      simp [hv] at hnone
    | some k' =>
      have hk' : v ∈ W.internalVerts k' := by simpa using List.find?_some hfind2
      have hkeq : k' = k := by
        by_contra hne
        exact hW.2.2.2 k' k hne hk' hv
      rw [hkeq]
      exact elemWallEdgeCell_eq_eCell h k

theorem mem_vertexFinset_cases {v : Fin n} (hv : v ∈ W.vertexFinset) :
    (∃ u : Fin (elemWallNumVerts h), W.branchVert u = v) ∨
    (∃ k : Fin (elemWallEdges h).length, v ∈ W.internalVerts k) := by
  unfold vertexFinset at hv
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    List.mem_toFinset, List.mem_flatMap, List.mem_finRange] at hv
  exact hv

theorem branchVert_mem_vertexFinset (u : Fin (elemWallNumVerts h)) :
    W.branchVert u ∈ W.vertexFinset := by
  unfold vertexFinset
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨u, rfl⟩

theorem mem_vertexFinset_of_mem_internalVerts {k : Fin (elemWallEdges h).length} {v : Fin n}
    (hv : v ∈ W.internalVerts k) :
    v ∈ W.vertexFinset := by
  unfold vertexFinset
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and]
  exact Or.inr ⟨k, hv⟩

theorem vertCell_mem_fig1WallCells (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.vertexFinset) :
    W.vertCell v ∈ GM13.fig1WallCells h := by
  rcases W.mem_vertexFinset_cases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
  · rw [W.vertCell_branchVert hW u]
    exact GM13.mem_fig1WallCells_vCell h2 he (elemWallVertCoord_mem_elementaryWallVerts h u)
  · rw [W.vertCell_of_mem_internalVerts hW hvk]
    exact GM13.mem_fig1WallCells_eCell h2 he (elemWallEdge_elementaryWallAdj h k)

theorem toWallData_P (hh1 : 1 ≤ h) (hW : W.IsValid) :
    (W.toWallData hh1 hW).P = W.subdivPathOfSym2 hW := by
  unfold toWallData
  rfl

theorem toGMWall_subdivisionPaths_baseEdge (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {p q : ℕ × ℕ} (hadj : GM13.elementaryWallAdj (W.toGMWall h2 he hW).height p q) :
    (W.toGMWall h2 he hW).subdivisionPaths ((W.toGMWall h2 he hW).baseEdge hadj) =
      W.subdivPathOfSym2 hW s(p, q) := by
  have h1 := GM13.Wall.ofData_subdivisionPaths_baseEdge h2 he (W.toWallData (by omega) hW) hadj
  rwa [W.toWallData_P (by omega) hW] at h1

theorem val_mem_toGMWall_elemV_vertCell (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.vertexFinset) :
    v.1 ∈ (W.toGMWall h2 he hW).elemV (W.vertCell v) := by
  rcases W.mem_vertexFinset_cases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
  · rw [W.vertCell_branchVert hW u, ← W.toGMWall_branchVertex_elemWallVertCoord h2 he hW u]
    exact (W.toGMWall h2 he hW).branchVertex_mem_elemV
      (elemWallVertCoord_mem_elementaryWallVerts h u)
  · rw [W.vertCell_of_mem_internalVerts hW hvk]
    let e := (elemWallEdges h)[k.1]'k.2
    have hadj : GM13.elementaryWallAdj (W.toGMWall h2 he hW).height
        (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) :=
      elemWallEdge_elementaryWallAdj h k
    rw [(W.toGMWall h2 he hW).mem_elemV_eCell hadj,
      W.toGMWall_subdivisionPaths_baseEdge h2 he hW hadj]
    have h2' : s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) = elemWallEdgeSym2 h k := rfl
    rw [h2', W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, List.mem_map]
      exact ⟨v, (W.mem_subdivPathVerts_iff k v).mpr (Or.inr (Or.inl hvk)), rfl⟩
    · change v.1 ∉ W.branchVertAtCoord '' GM13.elementaryWallVerts h
      rw [W.image_branchVertAtCoord_eq]
      rintro ⟨u, hu⟩
      exact hW.2.2.1 k u (Fin.ext hu ▸ hvk)

theorem val_mem_toGMWall_elemV_iff (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.vertexFinset) (m : ℤ × ℤ) :
    v.1 ∈ (W.toGMWall h2 he hW).elemV m ↔ m = W.vertCell v := by
  constructor
  · intro hm
    exact (W.toGMWall h2 he hW).eq_of_mem_elemV hm (W.val_mem_toGMWall_elemV_vertCell h2 he hW hv)
  · rintro rfl
    exact W.val_mem_toGMWall_elemV_vertCell h2 he hW hv

theorem mem_vertexFinset_iff_val_mem_toGMWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (v : Fin n) :
    v ∈ W.vertexFinset ↔ v.1 ∈ V((W.toGMWall h2 he hW).graph) := by
  constructor
  · intro hv
    exact (W.toGMWall h2 he hW).elemV_subset (W.vertCell v)
      (W.val_mem_toGMWall_elemV_vertCell h2 he hW hv)
  · intro hv
    change v.1 ∈ V((W.toWallData (by omega) hW).graph) at hv
    rw [(W.toWallData (by omega) hW).vertexSet_eq] at hv
    change v.1 ∈ W.branchVertAtCoord '' GM13.elementaryWallVerts h ∪
      ⋃ e ∈ E(GM13.elementaryWall h), V(W.subdivPathOfSym2 hW e) at hv
    rw [W.image_branchVertAtCoord_eq] at hv
    rcases hv with ⟨u, hu⟩ | hv
    · rw [← Fin.ext hu]
      exact W.branchVert_mem_vertexFinset u
    · obtain ⟨e, ⟨p, q, hpq, rfl⟩, hve⟩ := Set.mem_iUnion₂.mp hv
      rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
      rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hve
      rcases List.mem_map.mp hve with ⟨w, hw, hweq⟩
      have hwv : w = v := Fin.ext hweq
      subst hwv
      rcases (W.mem_subdivPathVerts_iff k w).mp hw with rfl | hint | rfl
      · exact W.branchVert_mem_vertexFinset _
      · exact W.mem_vertexFinset_of_mem_internalVerts hint
      · exact W.branchVert_mem_vertexFinset _

/-! ### Section 3: Lifting Elementary-Wall Paths (`liftElemPath`, `liftElemPathInternal`) -/

/-- Single-element list `[W.branchVert (elemWallCoordIdx h p hp)]` if `p ∈ elementaryWallVerts h`,
and `[]` otherwise. -/
def coordBranchVertList (p : ℕ × ℕ) : List (Fin n) :=
  if hp : p ∈ GM13.elementaryWallVerts h then
    [W.branchVert (elemWallCoordIdx h p hp)]
  else
    []

@[simp]
theorem coordBranchVertList_of_mem {p : ℕ × ℕ} (hp : p ∈ GM13.elementaryWallVerts h) :
    W.coordBranchVertList p = [W.branchVert (elemWallCoordIdx h p hp)] := by
  simp [coordBranchVertList, hp]

/-- Internal subdivision vertices of `W` along an elementary-wall step `(p, q)`:
`W.internalVerts k` if `p.1 + p.2 < q.1 + q.2`, and `(W.internalVerts k).reverse` otherwise,
where `elemWallEdgeSym2 h k = s(p, q)`. -/
def stepInternalVerts (p q : ℕ × ℕ) : List (Fin n) :=
  match findElemWallEdgeIdx h s(p, q) with
  | some k =>
    if p.1 + p.2 < q.1 + q.2 then W.internalVerts k else (W.internalVerts k).reverse
  | none => []

theorem stepInternalVerts_symm {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q) :
    W.stepInternalVerts q p = (W.stepInternalVerts p q).reverse := by
  have hne : p.1 + p.2 ≠ q.1 + q.2 := by
    rcases hpq.2.2 with ⟨_, _ | _⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ <;> omega
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
  have h1 : findElemWallEdgeIdx h s(p, q) = some k := by
    rw [← hk, findElemWallEdgeIdx_elemWallEdgeSym2]
  have h2 : findElemWallEdgeIdx h s(q, p) = some k := by
    rw [Sym2.eq_swap, h1]
  unfold stepInternalVerts
  rw [h1, h2]
  dsimp only
  split_ifs with hlt1 hlt2 hlt2
  · omega
  · simp
  · rfl
  · omega

theorem stepSubdiv_eq_subdivPathVerts_or_reverse {p q : ℕ × ℕ}
    (hpq : GM13.elementaryWallAdj h p q) :
    ∃ k : Fin (elemWallEdges h).length,
      elemWallEdgeSym2 h k = s(p, q) ∧
      ((p.1 + p.2 < q.1 + q.2 ∧
          W.branchVert (elemWallCoordIdx h p hpq.1) ::
            (W.stepInternalVerts p q ++ [W.branchVert (elemWallCoordIdx h q hpq.2.1)]) =
            W.subdivPathVerts k) ∨
        (q.1 + q.2 < p.1 + p.2 ∧
          W.branchVert (elemWallCoordIdx h p hpq.1) ::
            (W.stepInternalVerts p q ++ [W.branchVert (elemWallCoordIdx h q hpq.2.1)]) =
            (W.subdivPathVerts k).reverse)) := by
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  have hfind : findElemWallEdgeIdx h s(p, q) = some k := by
    rw [← hk, findElemWallEdgeIdx_elemWallEdgeSym2]
  let e := (elemWallEdges h)[k.1]'k.2
  have hedge := elemWallEdge_isElemWallEdgeCoord h k
  dsimp at hedge
  have hlt_e := isElemWallEdgeCoord_lt hedge
  have hsym : s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) = s(p, q) := hk
  rcases Sym2.eq_iff.mp hsym with ⟨hp_eq, hq_eq⟩ | ⟨hp_eq, hq_eq⟩
  · left
    have hlt : p.1 + p.2 < q.1 + q.2 := by
      dsimp only [e] at hp_eq hq_eq
      rwa [← hp_eq, ← hq_eq]
    refine ⟨hlt, ?_⟩
    have he1 : elemWallCoordIdx h p hpq.1 = e.1 := by
      rw [← elemWallCoordIdx_elemWallVertCoord h e.1]
      congr 1
      exact hp_eq.symm
    have he2 : elemWallCoordIdx h q hpq.2.1 = e.2 := by
      rw [← elemWallCoordIdx_elemWallVertCoord h e.2]
      congr 1
      exact hq_eq.symm
    unfold stepInternalVerts subdivPathVerts
    rw [hfind]
    dsimp only
    simp only [hlt, ↓reduceIte, he1, he2, e, List.cons_append, List.nil_append]
  · right
    have hlt : q.1 + q.2 < p.1 + p.2 := by
      dsimp only [e] at hp_eq hq_eq
      rwa [← hp_eq, ← hq_eq]
    have hnot : ¬ (p.1 + p.2 < q.1 + q.2) := by omega
    refine ⟨hlt, ?_⟩
    have he1 : elemWallCoordIdx h p hpq.1 = e.2 := by
      rw [← elemWallCoordIdx_elemWallVertCoord h e.2]
      congr 1
      exact hq_eq.symm
    have he2 : elemWallCoordIdx h q hpq.2.1 = e.1 := by
      rw [← elemWallCoordIdx_elemWallVertCoord h e.1]
      congr 1
      exact hp_eq.symm
    unfold stepInternalVerts subdivPathVerts
    rw [hfind]
    dsimp only
    simp only [hnot, ↓reduceIte, he1, he2, e]
    simp

theorem mem_stepInternalVerts_iff {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q) (v : Fin n) :
    ∃ k : Fin (elemWallEdges h).length,
      elemWallEdgeSym2 h k = s(p, q) ∧
      (v ∈ W.stepInternalVerts p q ↔ v ∈ W.internalVerts k) := by
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  have hfind : findElemWallEdgeIdx h s(p, q) = some k := by
    rw [← hk, findElemWallEdgeIdx_elemWallEdgeSym2]
  unfold stepInternalVerts
  rw [hfind]
  dsimp only
  split_ifs
  · rfl
  · exact List.mem_reverse

attribute [irreducible] stepInternalVerts

theorem vertCell_of_mem_stepInternalVerts (hW : W.IsValid) {p q : ℕ × ℕ}
    (hpq : GM13.elementaryWallAdj h p q) {v : Fin n} (hv : v ∈ W.stepInternalVerts p q) :
    v ∈ W.vertexFinset ∧ W.vertCell v = GM13.eCell p q := by
  rcases W.mem_stepInternalVerts_iff hpq v with ⟨k, hk, hiff⟩
  have hvk : v ∈ W.internalVerts k := hiff.mp hv
  refine ⟨W.mem_vertexFinset_of_mem_internalVerts hvk, ?_⟩
  rw [W.vertCell_of_mem_internalVerts hW hvk]
  exact GM13.eCell_eq_of_sym2_eq hk

/-- Expand a list of elementary-wall coordinates `L` into a walk in `W`. -/
def liftElemPath (W : WallOfHeight h G) : List (ℕ × ℕ) → List (Fin n)
  | [] => []
  | [p] => W.coordBranchVertList p
  | p :: q :: rest =>
    W.coordBranchVertList p ++ W.stepInternalVerts p q ++ W.liftElemPath (q :: rest)

/-- Internal vertices of `W.liftElemPath (p :: (inner ++ [q]))` between `W.branchVert (idx p)` and
`W.branchVert (idx q)`. -/
def liftElemPathInternal (W : WallOfHeight h G) :
    (p : ℕ × ℕ) → List (ℕ × ℕ) → (q : ℕ × ℕ) → List (Fin n)
  | p, [], q => W.stepInternalVerts p q
  | p, u :: rest, q =>
    W.stepInternalVerts p u ++ W.coordBranchVertList u ++ W.liftElemPathInternal u rest q

theorem liftElemPath_eq_append_liftElemPathInternal (W : WallOfHeight h G) :
    ∀ (p : ℕ × ℕ) (inner : List (ℕ × ℕ)) (q : ℕ × ℕ),
      W.liftElemPath (p :: (inner ++ [q])) =
        W.coordBranchVertList p ++ W.liftElemPathInternal p inner q ++ W.coordBranchVertList q
  | p, [], q => by
    simp [liftElemPath, liftElemPathInternal]
  | p, u :: rest, q => by
    calc
      W.liftElemPath (p :: u :: (rest ++ [q]))
        = W.coordBranchVertList p ++ W.stepInternalVerts p u ++
            W.liftElemPath (u :: (rest ++ [q])) := rfl
      _ = W.coordBranchVertList p ++ W.stepInternalVerts p u ++
            (W.coordBranchVertList u ++ W.liftElemPathInternal u rest q ++
              W.coordBranchVertList q) := by
          rw [liftElemPath_eq_append_liftElemPathInternal W u rest q]
      _ = W.coordBranchVertList p ++ W.liftElemPathInternal p (u :: rest) q ++
            W.coordBranchVertList q := by
          simp [liftElemPathInternal, List.append_assoc]

theorem liftElemPath_ne_nil_and_head (W : WallOfHeight h G) :
    ∀ {a : ℕ × ℕ} {rest : List (ℕ × ℕ)} (ha : a ∈ GM13.elementaryWallVerts h),
      ∃ hne : W.liftElemPath (a :: rest) ≠ [],
        (W.liftElemPath (a :: rest)).head hne = W.branchVert (elemWallCoordIdx h a ha)
  | a, [], ha => by
    simp [liftElemPath, ha]
  | a, b :: rest, ha => by
    simp [liftElemPath, ha]

theorem liftElemPath_getLast (W : WallOfHeight h G) :
    ∀ {a : ℕ × ℕ} {rest : List (ℕ × ℕ)}
      (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
      (ha : a ∈ GM13.elementaryWallVerts h)
      (hne : W.liftElemPath (a :: rest) ≠ []),
      let last := (a :: rest).getLast (List.cons_ne_nil a rest)
      have hlast : last ∈ GM13.elementaryWallVerts h :=
        GM13.mem_verts_of_isChain hc ha last (List.getLast_mem (List.cons_ne_nil a rest))
      (W.liftElemPath (a :: rest)).getLast hne =
        W.branchVert (elemWallCoordIdx h last hlast)
  | a, [], _, ha, hne => by
    simp [liftElemPath, ha]
  | a, b :: rest, hc, ha, hne => by
    have hab : GM13.elementaryWallAdj h a b := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (b :: rest) :=
      (List.isChain_cons_cons.mp hc).2
    obtain ⟨hne_b, _⟩ := W.liftElemPath_ne_nil_and_head (rest := rest) hab.2.1
    have ih := W.liftElemPath_getLast hhc' hab.2.1 hne_b
    dsimp only at ih ⊢
    simp only [liftElemPath]
    rw [List.getLast_append_of_ne_nil _ hne_b, ih]
    simp

theorem isSimpleWalkList_of_append_left {n : ℕ} {G : MultiDigraph n} :
    ∀ {L₁ L₂ : List (Fin n)}, IsSimpleWalkList G (L₁ ++ L₂) → IsSimpleWalkList G L₁
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: v :: rest, _, hw => ⟨hw.1, isSimpleWalkList_of_append_left (L₁ := v :: rest) hw.2⟩

theorem adj_dropLast_getLast_of_isSimpleWalkList {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hdrop : L.dropLast ≠ []),
      IsSimpleWalkList G L →
      G.toSimpleGraph.Adj (L.dropLast.getLast hdrop) (L.getLast hne)
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, hdrop, _ => False.elim (hdrop rfl)
  | [_, _], _, _, hw => hw.1
  | _ :: v :: w :: rest, _, _, hw =>
    adj_dropLast_getLast_of_isSimpleWalkList (L := v :: w :: rest)
      (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hw.2

/-- Appending two `IsSimpleWalkList`s in `G` with adjacent junction yields a `IsSimpleWalkList`. -/
theorem isSimpleWalkList_Append {n : ℕ} {G : MultiDigraph n} :
    ∀ (L₁ L₂ : List (Fin n)) (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ []),
      IsSimpleWalkList G L₁ →
      IsSimpleWalkList G L₂ →
      G.toSimpleGraph.Adj (L₁.getLast hne₁) (L₂.head hne₂) →
      IsSimpleWalkList G (L₁ ++ L₂)
  | [], _, hne₁, _, _, _, _ => False.elim (hne₁ rfl)
  | [_], L₂, _, hne₂, _, hw₂, hadj => by
    cases L₂ with
    | nil => exact False.elim (hne₂ rfl)
    | cons v rest => exact ⟨hadj, hw₂⟩
  | _ :: w :: rest, L₂, _, hne₂, hw₁, hw₂, hadj => by
    have hne' : w :: rest ≠ [] := List.cons_ne_nil w rest
    exact ⟨hw₁.1, isSimpleWalkList_Append (w :: rest) L₂ hne' hne₂ hw₁.2 hw₂ hadj⟩

theorem isSimpleWalkList_concat_overlap {n : ℕ} {G : MultiDigraph n}
    {L₁ L₂ : List (Fin n)} (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ [])
    (hw₁ : IsSimpleWalkList G L₁) (hw₂ : IsSimpleWalkList G L₂)
    (heq : L₁.getLast hne₁ = L₂.head hne₂) :
    IsSimpleWalkList G (L₁.dropLast ++ L₂) := by
  by_cases hdrop : L₁.dropLast = []
  · rw [hdrop, List.nil_append]
    exact hw₂
  · have hw_drop : IsSimpleWalkList G L₁.dropLast := by
      have h1 : L₁.dropLast ++ [L₁.getLast hne₁] = L₁ := List.dropLast_append_getLast hne₁
      rw [← h1] at hw₁
      exact isSimpleWalkList_of_append_left hw₁
    have hadj : G.toSimpleGraph.Adj (L₁.dropLast.getLast hdrop) (L₂.head hne₂) := by
      rw [← heq]
      exact adj_dropLast_getLast_of_isSimpleWalkList hne₁ hdrop hw₁
    exact isSimpleWalkList_Append L₁.dropLast L₂ hdrop hne₂ hw_drop hw₂ hadj

theorem isSimpleWalkList_reverse {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)}, IsSimpleWalkList G L → IsSimpleWalkList G L.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | u :: v :: rest, hw => by
    have ih := isSimpleWalkList_reverse hw.2
    have hne_rev : (v :: rest).reverse ≠ [] := by simp
    have hlast_rev : (v :: rest).reverse.getLast hne_rev = v := by simp
    have hcons : (u :: v :: rest).reverse = (v :: rest).reverse ++ [u] := by simp
    rw [hcons]
    exact isSimpleWalkList_Append (v :: rest).reverse [u] hne_rev (List.cons_ne_nil u []) ih trivial
      (by rw [hlast_rev]; exact hw.1.symm)

theorem isSimpleWalkList_stepSubdiv (hW : W.IsValid) {a b : ℕ × ℕ}
    (hab : GM13.elementaryWallAdj h a b) :
    IsSimpleWalkList G
      (W.branchVert (elemWallCoordIdx h a hab.1) ::
        (W.stepInternalVerts a b ++ [W.branchVert (elemWallCoordIdx h b hab.2.1)])) := by
  rcases W.stepSubdiv_eq_subdivPathVerts_or_reverse hab with
    ⟨k, _, ⟨_, hstep⟩ | ⟨_, hstep⟩⟩
  · rw [hstep]
    exact (hW.2.1 k).2
  · rw [hstep]
    exact isSimpleWalkList_reverse (hW.2.1 k).2

theorem isSimpleWalkList_liftElemPath (hW : W.IsValid) {a : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
    (ha : a ∈ GM13.elementaryWallVerts h) :
    IsSimpleWalkList G (W.liftElemPath (a :: rest)) := by
  induction rest generalizing a with
  | nil =>
    simp [liftElemPath, ha, IsSimpleWalkList]
  | cons b rest ih =>
    have hab : GM13.elementaryWallAdj h a b := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (b :: rest) :=
      (List.isChain_cons_cons.mp hc).2
    have ih_b := ih hhc' hab.2.1
    let L₁ := W.branchVert (elemWallCoordIdx h a hab.1) ::
      (W.stepInternalVerts a b ++ [W.branchVert (elemWallCoordIdx h b hab.2.1)])
    have hne₁ : L₁ ≠ [] := List.cons_ne_nil _ _
    obtain ⟨hne₂, hhead₂⟩ := W.liftElemPath_ne_nil_and_head (rest := rest) hab.2.1
    have hdrop₁ : L₁.dropLast = W.coordBranchVertList a ++ W.stepInternalVerts a b := by
      rw [W.coordBranchVertList_of_mem hab.1]
      dsimp only [L₁]
      rw [← List.cons_append, List.dropLast_concat]
      rfl
    have hlast₁ : L₁.getLast hne₁ = W.branchVert (elemWallCoordIdx h b hab.2.1) := by
      simp [L₁]
    have hw_step : IsSimpleWalkList G L₁ := W.isSimpleWalkList_stepSubdiv hW hab
    rw [liftElemPath, ← hdrop₁]
    exact isSimpleWalkList_concat_overlap hne₁ hne₂ hw_step ih_b (hlast₁.trans hhead₂.symm)

theorem mem_liftElemPath_cases {a : ℕ × ℕ} {rest : List (ℕ × ℕ)} {v : Fin n}
    (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
    (ha : a ∈ GM13.elementaryWallVerts h)
    (hv : v ∈ W.liftElemPath (a :: rest)) :
    (∃ (u : ℕ × ℕ) (hu : u ∈ GM13.elementaryWallVerts h),
      u ∈ a :: rest ∧ v = W.branchVert (elemWallCoordIdx h u hu)) ∨
    (∃ uw ∈ (a :: rest).zip rest, v ∈ W.stepInternalVerts uw.1 uw.2) := by
  induction rest generalizing a with
  | nil =>
    rw [liftElemPath, W.coordBranchVertList_of_mem ha, List.mem_singleton] at hv
    exact Or.inl ⟨a, ha, List.mem_singleton.mpr rfl, hv⟩
  | cons b rest ih =>
    have hab : GM13.elementaryWallAdj h a b := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (b :: rest) :=
      (List.isChain_cons_cons.mp hc).2
    rw [liftElemPath, W.coordBranchVertList_of_mem ha, List.singleton_append, List.cons_append,
      List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv_step | hv_rest
    · exact Or.inl ⟨a, ha, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨(a, b), List.mem_cons_self, hv_step⟩
    · rcases ih hhc' hab.2.1 hv_rest with
        ⟨u, hu, hu_mem, rfl⟩ | ⟨uw, huw, hvuw⟩
      · exact Or.inl ⟨u, hu, List.mem_cons_of_mem a hu_mem, rfl⟩
      · exact Or.inr ⟨uw, List.mem_cons_of_mem (a, b) huw, hvuw⟩

theorem nodup_liftElemPath (hW : W.IsValid) {a : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
    (ha : a ∈ GM13.elementaryWallVerts h)
    (hnd : (a :: rest).Nodup) :
    (W.liftElemPath (a :: rest)).Nodup := by
  induction rest generalizing a with
  | nil =>
    simp [liftElemPath, ha]
  | cons b rest ih =>
    have hab : GM13.elementaryWallAdj h a b := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (b :: rest) :=
      (List.isChain_cons_cons.mp hc).2
    have hnd_a : a ∉ b :: rest := (List.nodup_cons.mp hnd).1
    have hnd_rest : (b :: rest).Nodup := (List.nodup_cons.mp hnd).2
    have ih_b := ih hhc' hab.2.1 hnd_rest
    have hnd_pref : (W.coordBranchVertList a ++ W.stepInternalVerts a b).Nodup := by
      rw [W.coordBranchVertList_of_mem ha, List.singleton_append]
      rcases W.stepSubdiv_eq_subdivPathVerts_or_reverse hab with
        ⟨k, _, ⟨_, hstep⟩ | ⟨_, hstep⟩⟩
      · have hnd_sub : (W.subdivPathVerts k).Nodup := (hW.2.1 k).1
        rw [← hstep, ← List.cons_append] at hnd_sub
        exact hnd_sub.of_append_left
      · have hnd_sub : (W.subdivPathVerts k).reverse.Nodup :=
          List.nodup_reverse.mpr (hW.2.1 k).1
        rw [← hstep, ← List.cons_append] at hnd_sub
        exact hnd_sub.of_append_left
    rw [liftElemPath]
    refine hnd_pref.append ih_b ?_
    intro v hv₁ hv₂
    rw [W.coordBranchVertList_of_mem ha, List.singleton_append, List.mem_cons] at hv₁
    rcases W.mem_liftElemPath_cases hhc' hab.2.1 hv₂ with
      ⟨u, hu, hu_mem, rfl⟩ | ⟨uw, huw, hvuw⟩
    · rcases hv₁ with heq | hv_step
      · have hidx := hW.1 heq.symm
        have hau : a = u := by
          have := congrArg (elemWallVertCoord h) hidx
          rwa [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at this
        exact hnd_a (hau ▸ hu_mem)
      · rcases W.mem_stepInternalVerts_iff hab (W.branchVert (elemWallCoordIdx h u hu)) with
          ⟨k, _, hiff⟩
        exact hW.2.2.1 k _ (hiff.mp hv_step)
    · have huw_adj : GM13.elementaryWallAdj h uw.1 uw.2 :=
        GM13.List.rel_of_mem_zip_of_isChain hhc' uw huw
      rcases W.mem_stepInternalVerts_iff huw_adj v with ⟨k₂, hk₂, hiff₂⟩
      have hvk₂ : v ∈ W.internalVerts k₂ := hiff₂.mp hvuw
      rcases hv₁ with rfl | hv_step
      · exact hW.2.2.1 k₂ _ hvk₂
      · rcases W.mem_stepInternalVerts_iff hab v with ⟨k₁, hk₁, hiff₁⟩
        have hvk₁ : v ∈ W.internalVerts k₁ := hiff₁.mp hv_step
        have hk_ne : k₁ ≠ k₂ := by
          intro hkeq
          have hsym : s(a, b) = s(uw.1, uw.2) := by rw [← hk₁, ← hk₂, hkeq]
          have huw1_mem : uw.1 ∈ b :: rest := (List.of_mem_zip huw).1
          have huw2_mem : uw.2 ∈ b :: rest := List.mem_cons_of_mem b (List.of_mem_zip huw).2
          rcases Sym2.eq_iff.mp hsym with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact hnd_a huw1_mem
          · exact hnd_a huw2_mem
        exact hW.2.2.2 k₁ k₂ hk_ne hvk₁ hvk₂

theorem mem_liftElemPathInternal_cases {p q : ℕ × ℕ} {inner : List (ℕ × ℕ)}
    (hc : List.IsChain (GM13.elementaryWallAdj h) (p :: (inner ++ [q])))
    (hp : p ∈ GM13.elementaryWallVerts h) :
    ∀ {v : Fin n}, v ∈ W.liftElemPathInternal p inner q →
      (∃ (u : ℕ × ℕ) (hu : u ∈ GM13.elementaryWallVerts h),
        u ∈ inner ∧ v = W.branchVert (elemWallCoordIdx h u hu)) ∨
      (∃ uw ∈ (p :: (inner ++ [q])).zip (inner ++ [q]),
        v ∈ W.stepInternalVerts uw.1 uw.2) := by
  induction inner generalizing p with
  | nil =>
    intro v hv
    simp only [liftElemPathInternal] at hv
    exact Or.inr ⟨(p, q), by simp, hv⟩
  | cons u rest ih =>
    intro v hv
    have hpu : GM13.elementaryWallAdj h p u := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (u :: (rest ++ [q])) :=
      (List.isChain_cons_cons.mp hc).2
    simp only [liftElemPathInternal, W.coordBranchVertList_of_mem hpu.2.1,
      List.append_assoc, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv_step | rfl | hv_rest
    · exact Or.inr ⟨(p, u), by simp, hv_step⟩
    · exact Or.inl ⟨u, hpu.2.1, List.mem_cons_self, rfl⟩
    · rcases ih hhc' hpu.2.1 hv_rest with ⟨w, hw, hw_mem, rfl⟩ | ⟨uw, huw, hvuw⟩
      · exact Or.inl ⟨w, hw, List.mem_cons_of_mem u hw_mem, rfl⟩
      · exact Or.inr ⟨uw, List.mem_cons_of_mem (p, u) huw, hvuw⟩

theorem mem_liftElemPathInternal_of_branchVert (W : WallOfHeight h G) {p q : ℕ × ℕ} :
    ∀ {inner : List (ℕ × ℕ)} {u : ℕ × ℕ} (hu : u ∈ GM13.elementaryWallVerts h),
      u ∈ inner →
      W.branchVert (elemWallCoordIdx h u hu) ∈ W.liftElemPathInternal p inner q
  | [], _, _, hu_mem => by nomatch hu_mem
  | w :: rest, u, hu, hu_mem => by
    simp only [liftElemPathInternal, List.append_assoc, List.mem_append]
    rcases List.mem_cons.mp hu_mem with rfl | hu_rest
    · right; left
      simp [W.coordBranchVertList_of_mem hu]
    · right; right
      exact W.mem_liftElemPathInternal_of_branchVert (p := w) hu hu_rest

theorem mem_liftElemPathInternal_of_step (W : WallOfHeight h G) {p q : ℕ × ℕ} :
    ∀ {inner : List (ℕ × ℕ)} {a b : ℕ × ℕ} {v : Fin n},
      (a, b) ∈ (p :: (inner ++ [q])).zip (inner ++ [q]) →
      v ∈ W.stepInternalVerts a b →
      v ∈ W.liftElemPathInternal p inner q
  | [], a, b, v, hab, hv => by
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right,
      List.mem_singleton, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩
    exact hv
  | u :: rest, a, b, v, hab, hv => by
    simp only [liftElemPathInternal, List.append_assoc, List.mem_append]
    rcases List.mem_cons.mp hab with ⟨rfl, rfl⟩ | hab_rest
    · exact Or.inl hv
    · exact Or.inr (Or.inr (W.mem_liftElemPathInternal_of_step (p := u) hab_rest hv))

theorem isWallEdge_of_mem_zip_reverse {L : List (Fin n)}
    (h : ∀ u v, (u, v) ∈ L.zip (L.drop 1) → W.IsWallEdge u v) :
    ∀ u v, (u, v) ∈ L.reverse.zip (L.reverse.drop 1) → W.IsWallEdge u v := by
  intro u v huv
  rw [List.drop_one] at huv
  obtain ⟨l₁, l₂, heq⟩ := GM13.List.mem_zip_tail_iff.mp huv
  have hrev := congrArg List.reverse heq
  simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
    List.append_assoc, List.singleton_append] at hrev
  have hvu : (v, u) ∈ L.zip (L.drop 1) := by
    rw [List.drop_one]
    exact GM13.List.mem_zip_tail_iff.mpr ⟨l₂.reverse, l₁.reverse, hrev⟩
  rcases h v u hvu with ⟨k, h1 | h2⟩
  · exact ⟨k, Or.inr h1⟩
  · exact ⟨k, Or.inl h2⟩

theorem isWallEdge_of_mem_zip_concat_overlap {L₁ L₂ : List (Fin n)}
    (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ [])
    (heq : L₁.getLast hne₁ = L₂.head hne₂)
    (h₁ : ∀ u v, (u, v) ∈ L₁.zip (L₁.drop 1) → W.IsWallEdge u v)
    (h₂ : ∀ u v, (u, v) ∈ L₂.zip (L₂.drop 1) → W.IsWallEdge u v) :
    ∀ u v, (u, v) ∈ (L₁.dropLast ++ L₂).zip ((L₁.dropLast ++ L₂).drop 1) →
      W.IsWallEdge u v := by
  intro u v huv
  rw [List.drop_one] at huv
  obtain ⟨l₁, l₂, hsplit⟩ := GM13.List.mem_zip_tail_iff.mp huv
  rcases List.append_eq_append_iff.mp hsplit with
    ⟨m, _, hm₂⟩ | ⟨m, hm₁, hm₂⟩
  · apply h₂ u v
    rw [List.drop_one]
    exact GM13.List.mem_zip_tail_iff.mpr ⟨m, l₂, hm₂⟩
  · cases m with
    | nil =>
      simp only [List.nil_append] at hm₂
      apply h₂ u v
      rw [List.drop_one]
      exact GM13.List.mem_zip_tail_iff.mpr ⟨[], l₂, hm₂.symm⟩
    | cons z m' =>
      cases m' with
      | nil =>
        simp only [List.singleton_append] at hm₂
        obtain ⟨rfl, hL₂⟩ := List.cons.inj hm₂
        have hhead₂ : L₂.head hne₂ = v := by
          cases L₂ with
          | nil => exact False.elim (hne₂ rfl)
          | cons w rest =>
            exact (List.cons.inj hL₂).1.symm
        have hL₁_eq : L₁ = l₁ ++ u :: v :: [] := by
          calc
            L₁ = L₁.dropLast ++ [L₁.getLast hne₁] := (List.dropLast_append_getLast hne₁).symm
            _ = (l₁ ++ [u]) ++ [v] := by rw [hm₁, heq, hhead₂]
            _ = l₁ ++ u :: v :: [] := by simp
        apply h₁ u v
        rw [List.drop_one]
        exact GM13.List.mem_zip_tail_iff.mpr ⟨l₁, [], hL₁_eq⟩
      | cons w m'' =>
        simp only [List.cons_append] at hm₂
        obtain ⟨rfl, hm₂'⟩ := List.cons.inj hm₂
        obtain ⟨rfl, _⟩ := List.cons.inj hm₂'
        have hL₁_eq : L₁ = l₁ ++ u :: v :: (m'' ++ [L₁.getLast hne₁]) := by
          calc
            L₁ = L₁.dropLast ++ [L₁.getLast hne₁] := (List.dropLast_append_getLast hne₁).symm
            _ = (l₁ ++ u :: v :: m'') ++ [L₁.getLast hne₁] := by rw [hm₁]
            _ = l₁ ++ u :: v :: (m'' ++ [L₁.getLast hne₁]) := by simp
        apply h₁ u v
        rw [List.drop_one]
        exact GM13.List.mem_zip_tail_iff.mpr ⟨l₁, m'' ++ [L₁.getLast hne₁], hL₁_eq⟩

theorem isWallEdge_of_mem_zip_liftElemPath (W : WallOfHeight h G) :
    ∀ {a : ℕ × ℕ} {rest : List (ℕ × ℕ)},
      List.IsChain (GM13.elementaryWallAdj h) (a :: rest) →
      a ∈ GM13.elementaryWallVerts h →
      ∀ u v, (u, v) ∈ (W.liftElemPath (a :: rest)).zip ((W.liftElemPath (a :: rest)).drop 1) →
        W.IsWallEdge u v
  | a, [], _, ha, u, v, huv => by
    simp [liftElemPath, ha] at huv
  | a, b :: rest, hc, ha, u, v, huv => by
    have hab : GM13.elementaryWallAdj h a b := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (b :: rest) :=
      (List.isChain_cons_cons.mp hc).2
    have ih := W.isWallEdge_of_mem_zip_liftElemPath hhc' hab.2.1
    let L₁ := W.branchVert (elemWallCoordIdx h a ha) ::
      (W.stepInternalVerts a b ++ [W.branchVert (elemWallCoordIdx h b hab.2.1)])
    have hne₁ : L₁ ≠ [] := List.cons_ne_nil _ _
    obtain ⟨hne₂, hhead₂⟩ := W.liftElemPath_ne_nil_and_head (rest := rest) hab.2.1
    have hdrop₁ : L₁.dropLast = W.coordBranchVertList a ++ W.stepInternalVerts a b := by
      rw [W.coordBranchVertList_of_mem ha]
      dsimp only [L₁]
      rw [← List.cons_append, List.dropLast_concat]
      rfl
    have hlast₁ : L₁.getLast hne₁ = W.branchVert (elemWallCoordIdx h b hab.2.1) := by
      simp [L₁]
    have h₁ : ∀ x y, (x, y) ∈ L₁.zip (L₁.drop 1) → W.IsWallEdge x y := by
      rcases W.stepSubdiv_eq_subdivPathVerts_or_reverse hab with
        ⟨k, _, ⟨_, hstep⟩ | ⟨_, hstep⟩⟩
      · intro x y hxy
        dsimp only [L₁] at hxy
        rw [hstep] at hxy
        exact ⟨k, Or.inl hxy⟩
      · intro x y hxy
        dsimp only [L₁] at hxy
        rw [hstep] at hxy
        exact W.isWallEdge_of_mem_zip_reverse (fun x' y' h' => ⟨k, Or.inl h'⟩) x y hxy
    have hcomb := W.isWallEdge_of_mem_zip_concat_overlap hne₁ hne₂ (hlast₁.trans hhead₂.symm) h₁ ih
    rw [hdrop₁] at hcomb
    exact hcomb u v huv

/-! ### Section 4: Subwall Realization (`WallOfHeight.realizeSubwall`) -/

/-- Realize a shape `τ : GM13.Shape h h'` via `R : τ.Realization` on `W : WallOfHeight h G`,
yielding a subwall `WallOfHeight h' G`. -/
def realizeSubwall {h' : ℕ} {τ : GM13.Shape h h'} (R : τ.Realization) :
    WallOfHeight h' G where
  branchVert u' :=
    let p := elemWallVertCoord h' u'
    have hp : p ∈ GM13.elementaryWallVerts h' := elemWallVertCoord_mem_elementaryWallVerts h' u'
    W.branchVert (elemWallCoordIdx h (R.vmap p) (R.vmap_mem p hp))
  internalVerts k' :=
    let e' := (elemWallEdges h')[k'.1]'k'.2
    let p := elemWallVertCoord h' e'.1
    let q := elemWallVertCoord h' e'.2
    W.liftElemPathInternal (R.vmap p) (R.inner p q) (R.vmap q)

section RealizeSubwall

variable {h' : ℕ} {τ : GM13.Shape h h'} (R : τ.Realization)

theorem realizeSubwall_subdivPathVerts (k' : Fin (elemWallEdges h').length) :
    let e' := (elemWallEdges h')[k'.1]'k'.2
    let p := elemWallVertCoord h' e'.1
    let q := elemWallVertCoord h' e'.2
    (W.realizeSubwall R).subdivPathVerts k' = W.liftElemPath (R.full p q) := by
  intro e' p q
  have hp : p ∈ GM13.elementaryWallVerts h' := elemWallVertCoord_mem_elementaryWallVerts h' e'.1
  have hq : q ∈ GM13.elementaryWallVerts h' := elemWallVertCoord_mem_elementaryWallVerts h' e'.2
  unfold GM13.Shape.Realization.full
  rw [W.liftElemPath_eq_append_liftElemPathInternal,
    W.coordBranchVertList_of_mem (R.vmap_mem p hp),
    W.coordBranchVertList_of_mem (R.vmap_mem q hq)]
  rfl

theorem own_vertCell_realizeSubwall_branchVert (hW : W.IsValid)
    (u' : Fin (elemWallNumVerts h')) :
    let v := (W.realizeSubwall R).branchVert u'
    v ∈ W.vertexFinset ∧
    W.vertCell v = GM13.vCell (R.vmap (elemWallVertCoord h' u')) ∧
    τ.own (W.vertCell v) = some (GM13.vCell (elemWallVertCoord h' u')) := by
  intro v
  let p := elemWallVertCoord h' u'
  have hp : p ∈ GM13.elementaryWallVerts h' := elemWallVertCoord_mem_elementaryWallVerts h' u'
  have hv_mem : v ∈ W.vertexFinset := W.branchVert_mem_vertexFinset _
  have hv_cell : W.vertCell v = GM13.vCell (R.vmap p) := by
    change W.vertCell (W.branchVert (elemWallCoordIdx h (R.vmap p) (R.vmap_mem p hp))) = _
    rw [W.vertCell_branchVert hW, elemWallVertCoord_elemWallCoordIdx]
  refine ⟨hv_mem, hv_cell, ?_⟩
  rw [hv_cell]
  exact R.own_vmap p hp

theorem own_vertCell_of_mem_realizeSubwall_internalVerts (hW : W.IsValid)
    {k' : Fin (elemWallEdges h').length} {v : Fin n}
    (hv : v ∈ (W.realizeSubwall R).internalVerts k') :
    let e' := (elemWallEdges h')[k'.1]'k'.2
    let p := elemWallVertCoord h' e'.1
    let q := elemWallVertCoord h' e'.2
    v ∈ W.vertexFinset ∧
    τ.own (W.vertCell v) = some (GM13.eCell p q) := by
  intro e' p q
  have hpq : GM13.elementaryWallAdj h' p q := elemWallEdge_elementaryWallAdj h' k'
  have hc := R.chain p q hpq
  have hp_mem := R.vmap_mem p hpq.1
  rcases W.mem_liftElemPathInternal_cases hc hp_mem hv with
    ⟨u, hu, hu_in, rfl⟩ | ⟨uw, huw, hvuw⟩
  · refine ⟨W.branchVert_mem_vertexFinset _, ?_⟩
    rw [W.vertCell_branchVert hW, elemWallVertCoord_elemWallCoordIdx]
    exact R.own_inner p q hpq u hu_in
  · have huw_adj : GM13.elementaryWallAdj h uw.1 uw.2 :=
      GM13.List.rel_of_mem_zip_of_isChain hc uw huw
    obtain ⟨hv_mem, hv_cell⟩ := W.vertCell_of_mem_stepInternalVerts hW huw_adj hvuw
    refine ⟨hv_mem, ?_⟩
    rw [hv_cell]
    exact R.own_step p q hpq uw huw

theorem realizeSubwall_isValid (hW : W.IsValid) :
    (W.realizeSubwall R).IsValid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u₁' u₂' heq
    have h₁ := (W.own_vertCell_realizeSubwall_branchVert R hW u₁').2.2
    have h₂ := (W.own_vertCell_realizeSubwall_branchVert R hW u₂').2.2
    rw [heq] at h₁
    have hcell := Option.some_injective _ (h₁.symm.trans h₂)
    exact elemWallVertCoord_injective h' (GM13.vCell_injective hcell)
  · intro k'
    let e' := (elemWallEdges h')[k'.1]'k'.2
    let p := elemWallVertCoord h' e'.1
    let q := elemWallVertCoord h' e'.2
    have hpq : GM13.elementaryWallAdj h' p q := elemWallEdge_elementaryWallAdj h' k'
    rw [W.realizeSubwall_subdivPathVerts R k']
    exact ⟨W.nodup_liftElemPath hW (R.chain p q hpq) (R.vmap_mem p hpq.1) (R.nodup p q hpq),
      W.isSimpleWalkList_liftElemPath hW (R.chain p q hpq) (R.vmap_mem p hpq.1)⟩
  · intro k' u' hv
    have hbr := (W.own_vertCell_realizeSubwall_branchVert R hW u').2.2
    have hint := (W.own_vertCell_of_mem_realizeSubwall_internalVerts R hW hv).2
    have heq := Option.some_injective _ (hint.symm.trans hbr)
    exact GM13.eCell_ne_vCell (elemWallEdge_elementaryWallAdj h' k') _ heq
  · intro k₁' k₂' hne v hv₁ hv₂
    have h₁ := (W.own_vertCell_of_mem_realizeSubwall_internalVerts R hW hv₁).2
    have h₂ := (W.own_vertCell_of_mem_realizeSubwall_internalVerts R hW hv₂).2
    have heq := Option.some_injective _ (h₁.symm.trans h₂)
    have hsym := GM13.sym2_eq_of_eCell_eq (elemWallEdge_elementaryWallAdj h' k₁')
      (elemWallEdge_elementaryWallAdj h' k₂') heq
    exact hne (elemWallEdgeSym2_injective h' hsym)

theorem own_vertCell_of_mem_realizeSubwall_vertexFinset (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ (W.realizeSubwall R).vertexFinset) :
    v ∈ W.vertexFinset ∧
    τ.own (W.vertCell v) = some ((W.realizeSubwall R).vertCell v) := by
  have hW' := W.realizeSubwall_isValid R hW
  rcases (W.realizeSubwall R).mem_vertexFinset_cases hv with ⟨u', rfl⟩ | ⟨k', hvk'⟩
  · obtain ⟨hmem, _, hown⟩ := W.own_vertCell_realizeSubwall_branchVert R hW u'
    rw [(W.realizeSubwall R).vertCell_branchVert hW' u']
    exact ⟨hmem, hown⟩
  · obtain ⟨hmem, hown⟩ := W.own_vertCell_of_mem_realizeSubwall_internalVerts R hW hvk'
    rw [(W.realizeSubwall R).vertCell_of_mem_internalVerts hW' hvk']
    exact ⟨hmem, hown⟩

theorem mem_realizeSubwall_vertexFinset_iff_own_ne_none (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (v : Fin n) :
    v ∈ (W.realizeSubwall R).vertexFinset ↔
      v ∈ W.vertexFinset ∧ τ.own (W.vertCell v) ≠ none := by
  constructor
  · intro hv
    obtain ⟨hmem, hown⟩ := W.own_vertCell_of_mem_realizeSubwall_vertexFinset R hW hv
    exact ⟨hmem, by rw [hown]; exact Option.some_ne_none _⟩
  · rintro ⟨hv, hown⟩
    have hm := W.vertCell_mem_fig1WallCells h2 he hW hv
    rcases R.own_cover (W.vertCell v) hm hown with
      ⟨p, hp, heq⟩ | ⟨p, q, hpq, ⟨u, hu, heq⟩ | ⟨⟨a, b⟩, hab, heq⟩⟩
    · rcases W.mem_vertexFinset_cases hv with ⟨u₀, rfl⟩ | ⟨k₀, hvk₀⟩
      · rw [W.vertCell_branchVert hW u₀] at heq
        have hu_eq : u₀ = elemWallCoordIdx h (R.vmap p) (R.vmap_mem p hp) := by
          rw [← elemWallCoordIdx_elemWallVertCoord h u₀]
          congr 1
          exact GM13.vCell_injective heq
        let u' := elemWallCoordIdx h' p hp
        have hp_eq : elemWallVertCoord h' u' = p := elemWallVertCoord_elemWallCoordIdx h' hp
        have hbr : (W.realizeSubwall R).branchVert u' = W.branchVert u₀ := by
          rw [hu_eq]
          unfold realizeSubwall
          dsimp only
          congr 3
        rw [← hbr]
        exact (W.realizeSubwall R).branchVert_mem_vertexFinset u'
      · rw [W.vertCell_of_mem_internalVerts hW hvk₀] at heq
        exact False.elim (GM13.eCell_ne_vCell (elemWallEdge_elementaryWallAdj h k₀) _ heq)
    · rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k', hk'⟩
      let e' := (elemWallEdges h')[k'.1]'k'.2
      let p₀ := elemWallVertCoord h' e'.1
      let q₀ := elemWallVertCoord h' e'.2
      have hpq₀ : GM13.elementaryWallAdj h' p₀ q₀ := elemWallEdge_elementaryWallAdj h' k'
      have hu_mem : u ∈ GM13.elementaryWallVerts h :=
        R.mem_verts_of_mem_full hpq (by simp [GM13.Shape.Realization.full, hu])
      have hu_in₀ : u ∈ R.inner p₀ q₀ := by
        rcases Sym2.eq_iff.mp hk' with ⟨hp_eq, hq_eq⟩ | ⟨hp_eq, hq_eq⟩
        · dsimp only [p₀, q₀]
          rwa [hp_eq, hq_eq]
        · dsimp only [p₀, q₀]
          rw [hp_eq, hq_eq, R.inner_symm p q hpq, List.mem_reverse]
          exact hu
      rcases W.mem_vertexFinset_cases hv with ⟨u₀, rfl⟩ | ⟨k₀, hvk₀⟩
      · rw [W.vertCell_branchVert hW u₀] at heq
        have hu_eq : u₀ = elemWallCoordIdx h u hu_mem := by
          rw [← elemWallCoordIdx_elemWallVertCoord h u₀]
          congr 1
          exact GM13.vCell_injective heq
        rw [hu_eq]
        exact (W.realizeSubwall R).mem_vertexFinset_of_mem_internalVerts (k := k')
          (W.mem_liftElemPathInternal_of_branchVert hu_mem hu_in₀)
      · rw [W.vertCell_of_mem_internalVerts hW hvk₀] at heq
        exact False.elim (GM13.eCell_ne_vCell (elemWallEdge_elementaryWallAdj h k₀) _ heq)
    · rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k', hk'⟩
      let e' := (elemWallEdges h')[k'.1]'k'.2
      let p₀ := elemWallVertCoord h' e'.1
      let q₀ := elemWallVertCoord h' e'.2
      have hab_adj : GM13.elementaryWallAdj h a b :=
        GM13.List.rel_of_mem_zip_of_isChain (R.chain p q hpq) (a, b) hab
      rcases W.mem_vertexFinset_cases hv with ⟨u₀, rfl⟩ | ⟨k₀, hvk₀⟩
      · rw [W.vertCell_branchVert hW u₀] at heq
        exact False.elim (GM13.eCell_ne_vCell hab_adj _ heq.symm)
      · rw [W.vertCell_of_mem_internalVerts hW hvk₀] at heq
        have hsym_ab : elemWallEdgeSym2 h k₀ = s(a, b) :=
          GM13.sym2_eq_of_eCell_eq (elemWallEdge_elementaryWallAdj h k₀) hab_adj heq
        rcases W.mem_stepInternalVerts_iff hab_adj v with ⟨k₁, hk₁, hiff₁⟩
        have hk₀_eq : k₀ = k₁ := elemWallEdgeSym2_injective h (hsym_ab.trans hk₁.symm)
        have hv_ab : v ∈ W.stepInternalVerts a b := hiff₁.mpr (hk₀_eq ▸ hvk₀)
        rcases Sym2.eq_iff.mp hk' with ⟨hp_eq, hq_eq⟩ | ⟨hp_eq, hq_eq⟩
        · apply (W.realizeSubwall R).mem_vertexFinset_of_mem_internalVerts (k := k')
          change v ∈ W.liftElemPathInternal (R.vmap p₀) (R.inner p₀ q₀) (R.vmap q₀)
          dsimp only [p₀, q₀]
          rw [hp_eq, hq_eq]
          exact W.mem_liftElemPathInternal_of_step hab hv_ab
        · have hba : (b, a) ∈ (R.full q p).zip (R.inner q p ++ [R.vmap p]) :=
            R.mem_steps_swap (W.toGMWall h2 he hW) hpq hab
          have hv_ba : v ∈ W.stepInternalVerts b a := by
            rw [W.stepInternalVerts_symm hab_adj, List.mem_reverse]
            exact hv_ab
          apply (W.realizeSubwall R).mem_vertexFinset_of_mem_internalVerts (k := k')
          change v ∈ W.liftElemPathInternal (R.vmap p₀) (R.inner p₀ q₀) (R.vmap q₀)
          dsimp only [p₀, q₀]
          rw [hp_eq, hq_eq]
          exact W.mem_liftElemPathInternal_of_step hba hv_ba

theorem val_mem_realizeWall_elemV_vertCell (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hh' : 1 ≤ h') (he' : Even h')
    {v : Fin n} (hv : v ∈ (W.realizeSubwall R).vertexFinset) :
    v.1 ∈ (R.wall (W.toGMWall h2 he hW) hh' he').elemV ((W.realizeSubwall R).vertCell v) := by
  obtain ⟨hvW, hown⟩ := W.own_vertCell_of_mem_realizeSubwall_vertexFinset R hW hv
  rw [R.elemV_wall (W.toGMWall h2 he hW) hh' he']
  exact ⟨W.vertCell v, W.vertCell_mem_fig1WallCells h2 he hW hvW, hown,
    W.val_mem_toGMWall_elemV_vertCell h2 he hW hvW⟩

theorem mem_realizeSubwall_vertexFinset_iff_val_mem_realizeWall
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (hh' : 1 ≤ h') (he' : Even h') (v : Fin n) :
    v ∈ (W.realizeSubwall R).vertexFinset ↔
      v.1 ∈ V((R.wall (W.toGMWall h2 he hW) hh' he').graph) := by
  constructor
  · intro hv
    exact (R.wall (W.toGMWall h2 he hW) hh' he').elemV_subset _
      (W.val_mem_realizeWall_elemV_vertCell R h2 he hW hh' he' hv)
  · intro hv
    obtain ⟨m', _, hvm'⟩ := (R.wall (W.toGMWall h2 he hW) hh' he').exists_mem_elemV hv
    rw [R.elemV_wall (W.toGMWall h2 he hW) hh' he'] at hvm'
    obtain ⟨m, _, hown, hvm⟩ := hvm'
    have hvW : v ∈ W.vertexFinset :=
      (W.mem_vertexFinset_iff_val_mem_toGMWall h2 he hW v).mpr
        ((W.toGMWall h2 he hW).elemV_subset m hvm)
    have hm_eq : m = W.vertCell v := (W.val_mem_toGMWall_elemV_iff h2 he hW hvW m).mp hvm
    subst hm_eq
    exact (W.mem_realizeSubwall_vertexFinset_iff_own_ne_none R h2 he hW v).mpr
      ⟨hvW, by rw [hown]; exact Option.some_ne_none _⟩

theorem isWallEdge_of_realizeSubwall_isWallEdge {u v : Fin n}
    (huv : (W.realizeSubwall R).IsWallEdge u v) :
    W.IsWallEdge u v := by
  rcases huv with ⟨k', h1 | h2⟩
  · let e' := (elemWallEdges h')[k'.1]'k'.2
    let p := elemWallVertCoord h' e'.1
    let q := elemWallVertCoord h' e'.2
    have hpq : GM13.elementaryWallAdj h' p q := elemWallEdge_elementaryWallAdj h' k'
    rw [W.realizeSubwall_subdivPathVerts R k'] at h1
    exact W.isWallEdge_of_mem_zip_liftElemPath (R.chain p q hpq) (R.vmap_mem p hpq.1) u v h1
  · let e' := (elemWallEdges h')[k'.1]'k'.2
    let p := elemWallVertCoord h' e'.1
    let q := elemWallVertCoord h' e'.2
    have hpq : GM13.elementaryWallAdj h' p q := elemWallEdge_elementaryWallAdj h' k'
    rw [W.realizeSubwall_subdivPathVerts R k'] at h2
    rcases W.isWallEdge_of_mem_zip_liftElemPath (R.chain p q hpq) (R.vmap_mem p hpq.1) v u h2 with
      ⟨k, hk1 | hk2⟩
    · exact ⟨k, Or.inr hk1⟩
    · exact ⟨k, Or.inl hk2⟩

end RealizeSubwall

end WallOfHeight

/-! ### Section 5: Computable Deleting Shape Choice (`chooseDeletingRealization`, `step73Subwall`) -/

instance instDecidableHoleGood (h' : ℕ) (Y0 c0 : ℤ) : Decidable (GM13.Hole.Good h' Y0 c0) :=
  decidable_of_iff _ GM13.Hole.good_iff.symm

/-- Computable bundle of a shape `τ : GM13.Shape (h' + 2) h'` and its realization `R` that passes
`τ.DepthTest` and deletes cell `m` (`τ.own m = none`). -/
structure DeletingRealization (h' : ℕ) (m : ℤ × ℤ) where
  /-- The shape `τ : GM13.Shape (h' + 2) h'`. -/
  τ : GM13.Shape (h' + 2) h'
  /-- Path realization of `τ`. -/
  R : τ.Realization
  /-- `τ` passes the depth test (`KI 4`). -/
  hdepth : τ.DepthTest
  /-- `τ` deletes the cell `m`. -/
  hdel : τ.own m = none

namespace DeletingRealization

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- A hole `Hole(Y0, c0)` with good parameters that deletes `m`. -/
def ofHole (hh' : 1 ≤ h') (he' : Even h') {m : ℤ × ℤ} (hg : GM13.Hole.Good h' Y0 c0)
    (hd : ¬ GM13.IsWallCell h' (GM13.Hole.cell Y0 c0 m)) :
    DeletingRealization h' m :=
  ⟨GM13.Hole.shape hg.toParams hh' he',
   GM13.Hole.realization hg.toParams hh' he',
   GM13.Hole.depthTest hg hh' he',
   by rw [GM13.Hole.shape_own]; exact GM13.Hole.own_none hd⟩

/-- A rotated hole `Hole(Y0, c0)` with good parameters that deletes `m`. -/
def ofRot (hh' : 1 ≤ h') (he' : Even h') {m : ℤ × ℤ} (hg : GM13.Hole.Good h' Y0 c0)
    (hd : ¬ GM13.IsWallCell h' (GM13.Hole.cell Y0 c0 (GM13.rotC (h' + 2) m))) :
    DeletingRealization h' m :=
  ⟨(GM13.Hole.shape hg.toParams hh' he').rotate (by omega) (GM13.Hole.even_succ_succ he') hh' he',
   (GM13.Hole.realization hg.toParams hh' he').rotate (by omega)
     (GM13.Hole.even_succ_succ he') hh' he',
   (GM13.Hole.depthTest hg hh' he').rotate (by omega) (GM13.Hole.even_succ_succ he') hh' he',
   by
     change ((GM13.Hole.shape hg.toParams hh' he').own (GM13.rotC (h' + 2) m)).map
       (GM13.rotC h') = none
     rw [GM13.Hole.shape_own, GM13.Hole.own_none hd, Option.map_none]⟩

/-- A translated subwall `T(i, 1)` (`i = 1` or `i = 3`) that deletes `m`. -/
def ofTrans (hh' : 1 ≤ h') (he' : Even h') {i : ℕ} (hi : i = 1 ∨ i = 3)
    {m c : ℤ × ℤ} (hc : c = (m.1 - 2 * (i : ℤ), m.2 - 2 * 1))
    (hd : ¬ GM13.IsWallCell h' c) :
    DeletingRealization h' m :=
  ⟨GM13.transShape1 h' hh' he' (i := (i : ℤ)) (by omega),
   GM13.transRealization h' hh' he' hi,
   GM13.transShape1_depthTest h' hh' he' (i := (i : ℤ)) (by omega),
   by
     change GM13.transOwn h' i 1 m = none
     unfold GM13.transOwn
     rw [ite_eq_right (hc ▸ hd)]⟩

/-- Transport a `DeletingRealization` along an equality of cells without casting `τ` or `R`. -/
def congrCell {h' : ℕ} {m₁ m₂ : ℤ × ℤ} (heq : m₁ = m₂)
    (d : DeletingRealization h' m₂) : DeletingRealization h' m₁ :=
  ⟨d.τ, d.R, d.hdepth, heq ▸ d.hdel⟩

end DeletingRealization

local macro "cdel_tac_local" : tactic => `(tactic| (
  simp only [GM13.rotC_vertex, GM13.rotC_horiz, GM13.rotC_vert, GM13.Hole.cell_vertex,
    GM13.Hole.cell_horiz, GM13.Hole.cell_vert, GM13.Hole.vertexCell, GM13.Hole.horizCell,
    GM13.Hole.vertCell]
  split_ifs <;> simp only [GM13.isWallCell_vertex_iff, GM13.isWallCell_horiz_iff,
    GM13.isWallCell_vert_iff, GM13.Hole.not_isWallCell_odd_odd, not_false_eq_true,
    not_and, not_or] <;> omega))

set_option hygiene false in
local macro "try_hole_real " Y0:term:max c0:term:max : tactic => `(tactic| (
  by_cases g : GM13.Hole.Good h' $Y0 $c0
  · exact DeletingRealization.ofHole hh' he' g (by
      obtain ⟨k, hk⟩ := he'
      rw [GM13.Hole.good_iff] at g
      cdel_tac_local)
  rw [GM13.Hole.good_iff] at g))

set_option hygiene false in
local macro "try_rot_real " Y0:term:max c0:term:max : tactic => `(tactic| (
  by_cases g : GM13.Hole.Good h' $Y0 $c0
  · exact DeletingRealization.ofRot hh' he' g (by
      obtain ⟨k, hk⟩ := he'
      rw [GM13.Hole.good_iff] at g
      cdel_tac_local)
  rw [GM13.Hole.good_iff] at g))

set_option hygiene false in
local macro "last_hole_real " Y0:term:max c0:term:max : tactic => `(tactic| (
  have g : GM13.Hole.Good h' $Y0 $c0 := by
    obtain ⟨k, hk⟩ := he'
    simp only [GM13.isWallCell_vertex_iff, GM13.isWallCell_horiz_iff,
      GM13.isWallCell_vert_iff] at *
    exact GM13.Hole.good_iff.mpr (by omega)
  exact DeletingRealization.ofHole hh' he' g (by
    obtain ⟨k, hk⟩ := he'
    rw [GM13.Hole.good_iff] at g
    cdel_tac_local)))

set_option hygiene false in
local macro "last_rot_real " Y0:term:max c0:term:max : tactic => `(tactic| (
  have g : GM13.Hole.Good h' $Y0 $c0 := by
    obtain ⟨k, hk⟩ := he'
    simp only [GM13.isWallCell_vertex_iff, GM13.isWallCell_horiz_iff,
      GM13.isWallCell_vert_iff] at *
    exact GM13.Hole.good_iff.mpr (by omega)
  exact DeletingRealization.ofRot hh' he' g (by
    obtain ⟨k, hk⟩ := he'
    rw [GM13.Hole.good_iff] at g
    cdel_tac_local)))

/-- Computable deleting realization for a vertex cell `(2x, 2y)`. -/
def choiceVertexRealization {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {x y : ℤ}
    (t1 : GM13.IsWallCell h' (2 * (x - 1), 2 * (y - 1)))
    (t3 : GM13.IsWallCell h' (2 * (x - 3), 2 * (y - 1))) :
    DeletingRealization h' (2 * x, 2 * y) := by
  by_cases p : (x + y) % 2 = 0
  · by_cases q : y % 2 = 0
    · try_hole_real (y - 1) (x - 1)
      try_hole_real y (x - 2)
      last_rot_real ((h' : ℤ) + 2 - y) (2 * (h' : ℤ) + 5 - x - 1)
    · have q : y % 2 = 1 := by omega
      try_rot_real ((h' : ℤ) + 2 - y) (2 * (h' : ℤ) + 5 - x - 1)
      last_hole_real y x
  · have p : (x + y) % 2 = 1 := by omega
    by_cases q : y % 2 = 0
    · try_rot_real ((h' : ℤ) + 2 - y - 1) (2 * (h' : ℤ) + 5 - x - 1)
      try_hole_real y (x - 1)
      last_rot_real ((h' : ℤ) + 2 - y) (2 * (h' : ℤ) + 5 - x - 2)
    · have q : y % 2 = 1 := by omega
      try_hole_real y (x - 1)
      last_rot_real ((h' : ℤ) + 2 - y) (2 * (h' : ℤ) + 5 - x)

/-- Computable deleting realization for a horizontal edge cell `(2x + 1, 2y)`. -/
def choiceHorizRealization {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {x y : ℤ}
    (t1 : GM13.IsWallCell h' (2 * (x - 1) + 1, 2 * (y - 1)))
    (t3 : GM13.IsWallCell h' (2 * (x - 3) + 1, 2 * (y - 1))) :
    DeletingRealization h' (2 * x + 1, 2 * y) := by
  by_cases p : (x + y) % 2 = 0
  · by_cases q : y % 2 = 0
    · try_hole_real (y - 1) (x - 1)
      last_rot_real ((h' : ℤ) + 2 - y - 1) (2 * (h' : ℤ) + 4 - x - 1)
    · have q : y % 2 = 1 := by omega
      try_hole_real y x
      last_rot_real ((h' : ℤ) + 2 - y) (2 * (h' : ℤ) + 4 - x)
  · have p : (x + y) % 2 = 1 := by omega
    by_cases q : y % 2 = 0
    · try_hole_real (y - 1) x
      last_rot_real ((h' : ℤ) + 2 - y - 1) (2 * (h' : ℤ) + 4 - x)
    · have q : y % 2 = 1 := by omega
      try_hole_real y (x + 1)
      last_rot_real ((h' : ℤ) + 2 - y) (2 * (h' : ℤ) + 4 - x + 1)

/-- Computable deleting realization for a vertical edge cell `(2x, 2y + 1)`. -/
def choiceVertRealization {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {x y : ℤ}
    (hm : GM13.IsWallCell (h' + 2) (2 * x, 2 * y + 1))
    (t1 : GM13.IsWallCell h' (2 * (x - 1), 2 * (y - 1) + 1))
    (t3 : GM13.IsWallCell h' (2 * (x - 3), 2 * (y - 1) + 1)) :
    DeletingRealization h' (2 * x, 2 * y + 1) := by
  by_cases q : y % 2 = 0
  · try_rot_real ((h' : ℤ) + 1 - y) (2 * (h' : ℤ) + 5 - x - 1)
    last_hole_real (y + 1) x
  · have q : y % 2 = 1 := by omega
    try_hole_real y (x - 1)
    last_rot_real ((h' : ℤ) + 1 - y + 1) (2 * (h' : ℤ) + 5 - x)

/-- **Computable version of `GM13.exists_deleting_shape` (`Section7Choice.lean`):**
given any cell `m ∈ fig1WallCells (h' + 2)` (`1 ≤ h'`, `Even h'`), selects a shape `τ` and path
realization `R` passing the depth test with `τ.own m = none`. -/
def chooseDeletingRealization {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') (m : ℤ × ℤ)
    (hm : m ∈ GM13.fig1WallCells (h' + 2)) :
    DeletingRealization h' m :=
  let x := m.1 / 2
  let y := m.2 / 2
  if hpar1 : m.1 % 2 = 0 ∧ m.2 % 2 = 0 then
    DeletingRealization.congrCell (m₂ := (2 * x, 2 * y))
      (by ext <;> dsimp [x, y] <;> omega)
      (if t1 : GM13.IsWallCell h' (2 * (x - 1), 2 * (y - 1)) then
        if t3 : GM13.IsWallCell h' (2 * (x - 3), 2 * (y - 1)) then
          choiceVertexRealization hh' he' t1 t3
        else
          DeletingRealization.ofTrans hh' he' (i := 3) (Or.inr rfl)
            (by ext <;> simp only <;> push_cast <;> ring) t3
      else
        DeletingRealization.ofTrans hh' he' (i := 1) (Or.inl rfl)
          (by ext <;> simp only <;> push_cast <;> ring) t1)
  else if hpar2 : m.1 % 2 = 1 ∧ m.2 % 2 = 0 then
    DeletingRealization.congrCell (m₂ := (2 * x + 1, 2 * y))
      (by ext <;> dsimp [x, y] <;> omega)
      (if t1 : GM13.IsWallCell h' (2 * (x - 1) + 1, 2 * (y - 1)) then
        if t3 : GM13.IsWallCell h' (2 * (x - 3) + 1, 2 * (y - 1)) then
          choiceHorizRealization hh' he' t1 t3
        else
          DeletingRealization.ofTrans hh' he' (i := 3) (Or.inr rfl)
            (by ext <;> simp only <;> push_cast <;> ring) t3
      else
        DeletingRealization.ofTrans hh' he' (i := 1) (Or.inl rfl)
          (by ext <;> simp only <;> push_cast <;> ring) t1)
  else
    have hm_cell : GM13.IsWallCell (h' + 2) m :=
      (GM13.mem_fig1WallCells_iff (by omega) (GM13.Hole.even_succ_succ he') m).mp hm
    have hm_eq : m = (2 * x, 2 * y + 1) := by
      rcases GM13.Hole.cell_cases hm_cell with ⟨x', y', heq⟩ | ⟨x', y', heq⟩ | ⟨x', y', heq⟩
      · exfalso; apply hpar1; rw [heq]; dsimp; omega
      · exfalso; apply hpar2; rw [heq]; dsimp; omega
      · have hx : x = x' := by dsimp [x]; rw [heq]; dsimp; omega
        have hy : y = y' := by dsimp [y]; rw [heq]; dsimp; omega
        rw [heq, hx, hy]
    DeletingRealization.congrCell hm_eq
      (if t1 : GM13.IsWallCell h' (2 * (x - 1), 2 * (y - 1) + 1) then
        if t3 : GM13.IsWallCell h' (2 * (x - 3), 2 * (y - 1) + 1) then
          choiceVertRealization hh' he' (hm_eq ▸ hm_cell) t1 t3
        else
          DeletingRealization.ofTrans hh' he' (i := 3) (Or.inr rfl)
            (by ext <;> simp only <;> push_cast <;> ring) t3
      else
        DeletingRealization.ofTrans hh' he' (i := 1) (Or.inl rfl)
          (by ext <;> simp only <;> push_cast <;> ring) t1)

namespace WallOfHeight

/-- Cell `W.vertCell v` if `v ∈ W.vertexFinset` and `IsWallCell h (W.vertCell v)`, and `(2, 0)`
otherwise. Always lies in `fig1WallCells h` when `2 ≤ h` and `Even h`. -/
def vertCellOr20 {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (v : Fin n) : ℤ × ℤ :=
  if v ∈ W.vertexFinset ∧ GM13.IsWallCell h (W.vertCell v) then W.vertCell v else (2, 0)

theorem vertCellOr20_eq_vertCell {h n : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {G : MultiDigraph n} (W : WallOfHeight h G) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.vertexFinset) :
    W.vertCellOr20 v = W.vertCell v := by
  unfold vertCellOr20
  have hcell : GM13.IsWallCell h (W.vertCell v) :=
    (GM13.mem_fig1WallCells_iff (by omega) he _).mp (W.vertCell_mem_fig1WallCells h2 he hW hv)
  simp [hv, hcell]

theorem vertCellOr20_mem_fig1WallCells {h n : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {G : MultiDigraph n} (W : WallOfHeight h G) (v : Fin n) :
    W.vertCellOr20 v ∈ GM13.fig1WallCells h := by
  rw [GM13.mem_fig1WallCells_iff (by omega) he]
  unfold vertCellOr20
  split_ifs with hcond
  · exact hcond.2
  · have h10 : ((1, 0) : ℕ × ℕ) ∈ GM13.elementaryWallVerts h := by
      simp [GM13.elementaryWallVerts]; omega
    exact GM13.isWallCell_vCell h10

/-- The deleting realization for step (7.3) with `r = 0` on `W : WallOfHeight (h' + 2) G` removing
vertex `v_del : Fin n`. -/
def step73DeletingRealization {h' n : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {G : MultiDigraph n} (W : WallOfHeight (h' + 2) G) (v_del : Fin n) :
    DeletingRealization h' (W.vertCellOr20 v_del) :=
  chooseDeletingRealization hh' he' (W.vertCellOr20 v_del)
    (W.vertCellOr20_mem_fig1WallCells (by omega) (GM13.Hole.even_succ_succ he') v_del)

/-- The subwall `WallOfHeight h' G` obtained from `W : WallOfHeight (h' + 2) G` by one application
of (7.3) with `r = 0` removing `v_del : Fin n`. -/
def step73Subwall {h' n : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {G : MultiDigraph n} (W : WallOfHeight (h' + 2) G) (v_del : Fin n) :
    WallOfHeight h' G :=
  W.realizeSubwall (W.step73DeletingRealization hh' he' v_del).R

theorem step73Subwall_isValid {h' n : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {G : MultiDigraph n} (W : WallOfHeight (h' + 2) G) (hW : W.IsValid) (v_del : Fin n) :
    (W.step73Subwall hh' he' v_del).IsValid :=
  W.realizeSubwall_isValid _ hW

theorem step73Subwall_vertexFinset_subset {h' n : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {G : MultiDigraph n} (W : WallOfHeight (h' + 2) G) (hW : W.IsValid) (v_del : Fin n) :
    (W.step73Subwall hh' he' v_del).vertexFinset ⊆ W.vertexFinset := by
  intro v hv
  exact (W.own_vertCell_of_mem_realizeSubwall_vertexFinset _ hW hv).1

theorem not_mem_step73Subwall_vertexFinset {h' n : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {G : MultiDigraph n} (W : WallOfHeight (h' + 2) G) (hW : W.IsValid) (v_del : Fin n) :
    v_del ∉ (W.step73Subwall hh' he' v_del).vertexFinset := by
  intro hmem
  obtain ⟨hvW, hown⟩ := W.own_vertCell_of_mem_realizeSubwall_vertexFinset
    (W.step73DeletingRealization hh' he' v_del).R hW hmem
  have hdel := (W.step73DeletingRealization hh' he' v_del).hdel
  rw [← W.vertCellOr20_eq_vertCell (by omega) (GM13.Hole.even_succ_succ he') hW hvW, hdel] at hown
  nomatch hown

end WallOfHeight

end GraphMinor.Compute
