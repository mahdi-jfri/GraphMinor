module

public import GraphMinor.Compute.Algorithm74GridModel

/-!
# Lifting Coarse-Grid Routing to the Wall $H$ and Attaching $H$-Paths for GM XIII (7.4)

This file lifts the `p` walk-connected, pairwise disjoint coarse-grid sets `routedBranchSet` from
`Algorithm74GridModel.lean` to a complete model of $K_p$ (`UnderlyingGraphModel`) in `x.G` for any
valid input `x : Alg74Input p h r` (`r = alg74LiftRadius p`):

1. **Complete graph edges and terminal indexing (`Section 1`):**
   - Proves `(completeGraphEdges p).length = p.choose 2`.
   - Indexes the `m = 2 * (completeGraphEdges p).length` path ends `alg74TermVert x a` and their
     endpoint colors `alg74RawColor p a : Fin p`.
2. **Elementary-wall coordinates and coarse separation (`Section 2`):**
   - Maps each wall vertex `v ∈ x.W.vertexFinset` to its representative elementary-wall coordinate
     `repCoord x.W v : ℕ × ℕ` and coarse grid cell `termGridCell x.W v : ℕ × ℕ`.
   - Proves that `W.vertCell v` lies in the `2 × 2` cell block of `repCoord x.W v`, and applies
     `coarse_sep_and_depth_of_fig1CellBrickDist` and `routedBranchSet_spec`.
3. **Lifting to the wall `W` in `G` (`Section 3`):**
   - Lifts `routedBranchSet` via `liftGrid` to `wallCoordBranchSet`, then to `wallVertBranchSet`
     in `V(W) ⊆ V(G)`.
4. **Attaching the $H$-paths and building `UnderlyingGraphModel` (`Section 4`):**
   - Unions `(P_e.dropLast).toFinset` into the tail color's branch set and selects the final edge
     of each $H$-path $P_e$ as `edgeMap e`, yielding `alg74UnderlyingModel`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Complete Graph Edges (`completeGraphEdges`) and Path End Indexing -/

theorem nodup_completeGraphEdges (p : ℕ) : (completeGraphEdges p).Nodup :=
  (nodup_allDirectedPairs p).filter _

theorem mem_completeGraphEdges_iff {p : ℕ} (e : Fin p × Fin p) :
    e ∈ completeGraphEdges p ↔ e.1 < e.2 := by
  simp [completeGraphEdges, mem_allDirectedPairs]

theorem length_completeGraphEdges (p : ℕ) :
    (completeGraphEdges p).length = p.choose 2 := by
  rw [← List.toFinset_card_of_nodup (nodup_completeGraphEdges p)]
  have hto :
      (completeGraphEdges p).toFinset =
        Finset.univ.filter (fun x : Fin p × Fin p => x.1 < x.2) := by
    ext x
    simp [mem_completeGraphEdges_iff]
  rw [hto, Fintype.card_product_filter_lt, Fintype.card_fin]

theorem completeGraphEdges_lt {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    ((completeGraphEdges p)[e.1]'e.2).1 < ((completeGraphEdges p)[e.1]'e.2).2 :=
  (mem_completeGraphEdges_iff _).mp (List.getElem_mem e.2)

theorem completeGraphEdges_ne {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    ((completeGraphEdges p)[e.1]'e.2).1 ≠ ((completeGraphEdges p)[e.1]'e.2).2 :=
  ne_of_lt (completeGraphEdges_lt e)

/-- Cast an index `e : Fin (completeGraphEdges p).length` to `Fin (p.choose 2)`. -/
def toChoose2Fin {p : ℕ} (e : Fin (completeGraphEdges p).length) : Fin (p.choose 2) :=
  ⟨e.1, by rw [← length_completeGraphEdges]; exact e.2⟩

/-- The `e`-th $H$-path of `x : Alg74Input p r`, indexed by `e : Fin (completeGraphEdges p).length`. -/
def alg74Path {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) : List (Fin x.n) :=
  x.paths (toChoose2Fin e)

/-- Path index `⟨a.1 / 2, _⟩` of a terminal index `a : Fin (2 * (completeGraphEdges p).length)`. -/
def termPathIdx {p : ℕ} (a : Fin (2 * (completeGraphEdges p).length)) :
    Fin (completeGraphEdges p).length :=
  ⟨a.1 / 2, by omega⟩

/-- Whether terminal `a` is the last vertex (`true`, `a.1 % 2 = 1`) or first vertex
(`false`, `a.1 % 2 = 0`) of its path. -/
def termIsEnd {p : ℕ} (a : Fin (2 * (completeGraphEdges p).length)) : Bool :=
  a.1 % 2 == 1

theorem termPathIdx_termIsEnd_inj {p : ℕ}
    {a₁ a₂ : Fin (2 * (completeGraphEdges p).length)}
    (hidx : termPathIdx a₁ = termPathIdx a₂)
    (hend : termIsEnd a₁ = termIsEnd a₂) :
    a₁ = a₂ := by
  have h1 : a₁.1 / 2 = a₂.1 / 2 := congrArg Fin.val hidx
  have h2 : (a₁.1 % 2 = 1 ↔ a₂.1 % 2 = 1) := by simpa [termIsEnd] using hend
  apply Fin.ext
  omega

/-- Color `Fin p` assigned to terminal `a : Fin (2 * (completeGraphEdges p).length)`. -/
def alg74RawColor (p : ℕ) (a : Fin (2 * (completeGraphEdges p).length)) : Fin p :=
  let idx := termPathIdx a
  let e := (completeGraphEdges p)[idx.1]'idx.2
  if termIsEnd a then e.2 else e.1

theorem alg74Path_ne_nil {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    alg74Path x e ≠ [] :=
  (x.hpaths_valid (toChoose2Fin e)).1

/-- The terminal vertex in `Fin x.n` for terminal index `a : Fin (2 * (completeGraphEdges p).length)`. -/
def alg74TermVert {p r : ℕ} (x : Alg74Input p r)
    (a : Fin (2 * (completeGraphEdges p).length)) : Fin x.n :=
  let P := alg74Path x (termPathIdx a)
  have hne := alg74Path_ne_nil x (termPathIdx a)
  if termIsEnd a then P.getLast hne else P.head hne

theorem getLast_head_congr {α : Type*} (b : Bool) {L₁ L₂ : List α}
    (h : L₁ = L₂) (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ []) :
    (if b then L₁.getLast hne₁ else L₁.head hne₁) =
    (if b then L₂.getLast hne₂ else L₂.head hne₂) := by
  subst h
  rfl

theorem hPathEnd_eq_alg74TermVert {p r : ℕ} (x : Alg74Input p r)
    (a : Fin (2 * (completeGraphEdges p).length)) :
    WallOfHeight.hPathEnd x.paths (toChoose2Fin (termPathIdx a), termIsEnd a) =
      some (alg74TermVert x a) := by
  rcases List.exists_cons_of_ne_nil (alg74Path_ne_nil x (termPathIdx a)) with ⟨u, rest, hP⟩
  have hP' : x.paths (toChoose2Fin (termPathIdx a)) = u :: rest := hP
  unfold WallOfHeight.hPathEnd alg74TermVert
  dsimp only
  rw [hP']
  dsimp only
  exact congrArg some (getLast_head_congr (termIsEnd a) hP.symm (List.cons_ne_nil u rest)
    (alg74Path_ne_nil x (termPathIdx a)))

theorem alg74TermVert_mem_vertexFinset {p r : ℕ} (x : Alg74Input p r)
    (a : Fin (2 * (completeGraphEdges p).length)) :
    alg74TermVert x a ∈ x.W.vertexFinset := by
  have hv := x.hpaths_valid (toChoose2Fin (termPathIdx a))
  rcases hv with ⟨hne, _, _, _, hhead, hlast, _, _⟩
  unfold alg74TermVert alg74Path
  dsimp
  split_ifs
  · exact hlast
  · exact hhead

theorem alg74TermVert_brickDist_ge {p r : ℕ} (x : Alg74Input p r)
    {a₁ a₂ : Fin (2 * (completeGraphEdges p).length)} (hne : a₁ ≠ a₂) :
    r ≤ x.W.brickDist (alg74TermVert x a₁) (alg74TermVert x a₂) := by
  have hne_pair :
      (toChoose2Fin (termPathIdx a₁), termIsEnd a₁) ≠
        (toChoose2Fin (termPathIdx a₂), termIsEnd a₂) := by
    intro heq
    have h1 : termPathIdx a₁ = termPathIdx a₂ :=
      Fin.ext (congrArg (fun p => p.1.1) heq)
    have h2 : termIsEnd a₁ = termIsEnd a₂ := congrArg Prod.snd heq
    exact hne (termPathIdx_termIsEnd_inj h1 h2)
  exact x.hends_dist _ _ hne_pair _ _
    (hPathEnd_eq_alg74TermVert x a₁) (hPathEnd_eq_alg74TermVert x a₂)

theorem alg74TermVert_injective {p r : ℕ} (x : Alg74Input p r) (hr : 1 ≤ r) :
    Function.Injective (alg74TermVert x) := by
  intro a₁ a₂ heq
  by_contra hne
  have hdist := alg74TermVert_brickDist_ge x hne
  rw [heq, WallOfHeight.brickDist] at hdist
  simp at hdist
  omega

/-! ### Section 2: Elementary-Wall Coordinates, `repCoord`, and Coarse Separation -/

/-- Coordinate pair `(x, y)` of the `u`-th elementary-wall vertex. -/
def coordOf (h : ℕ) (u : Fin (elemWallNumVerts h)) : ℕ × ℕ :=
  (elemWallCoords h)[u.1]'u.2

theorem coordOf_mem (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    coordOf h u ∈ elemWallCoords h :=
  List.getElem_mem u.2

theorem coordOf_bounds (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    (coordOf h u).1 ≤ 2 * h + 1 ∧
    (coordOf h u).2 ≤ h ∧
    coordOf h u ≠ (0, 0) ∧
    coordOf h u ≠ (2 * h + 1, h) :=
  (mem_elemWallCoords_iff h (coordOf h u)).mp (coordOf_mem h u)

theorem coordOf_injective (h : ℕ) : Function.Injective (coordOf h) := by
  intro u₁ u₂ heq
  exact Fin.ext ((nodup_elemWallCoords h).getElem_inj_iff.mp heq)

theorem mem_elemWallEdges_coordOf_iff (h : ℕ) (e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :
    e ∈ elemWallEdges h ↔ isElemWallEdgeCoord (coordOf h e.1) (coordOf h e.2) = true := by
  simp [elemWallEdges, mem_allDirectedPairs, coordOf]

theorem isElemWallEdgeCoord_of_getElem (h : ℕ) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    isElemWallEdgeCoord (coordOf h e.1) (coordOf h e.2) = true :=
  (mem_elemWallEdges_coordOf_iff h _).mp (List.getElem_mem k.2)

/-- Representative elementary-wall coordinate `repCoord W v : ℕ × ℕ` of a vertex `v : Fin n` in
`W : WallOfHeight h G`:
- if `v = W.branchVert u`, `coordOf h u`;
- if `v ∈ W.internalVerts k` for edge `e_k = (u₁, u₂)`, `coordOf h u₁`;
- otherwise `(1, 0)`. -/
def repCoord {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (v : Fin n) : ℕ × ℕ :=
  match (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u => coordOf h u
  | none =>
    match (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | some k => coordOf h ((elemWallEdges h)[k.1]'k.2).1
    | none => (1, 0)

/-- Coarse grid cell `(coarseCol h x, y)` in `{1, ..., h} × {0, ..., h}` of a vertex `v : Fin n`
in `W : WallOfHeight h G`. -/
def termGridCell {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (v : Fin n) : ℕ × ℕ :=
  let p := repCoord W v
  (coarseCol h p.1, p.2)

theorem repCoord_mem_and_vertCell_bounds {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {v : Fin n} (hv : v ∈ W.vertexFinset) :
    repCoord W v ∈ elemWallCoords h ∧
    2 * ((repCoord W v).1 : ℤ) ≤ (W.vertCell v).1 ∧
    (W.vertCell v).1 ≤ 2 * ((repCoord W v).1 : ℤ) + 1 ∧
    2 * ((repCoord W v).2 : ℤ) ≤ (W.vertCell v).2 ∧
    (W.vertCell v).2 ≤ 2 * ((repCoord W v).2 : ℤ) + 1 := by
  unfold repCoord WallOfHeight.vertCell
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u =>
    dsimp [elemWallVertCell, coordOf]
    exact ⟨coordOf_mem h u, by omega, by omega, by omega, by omega⟩
  | none =>
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | some k =>
      dsimp
      have hedge := isElemWallEdgeCoord_of_getElem h k
      dsimp at hedge
      unfold isElemWallEdgeCoord at hedge
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hedge
      unfold elemWallEdgeCell
      dsimp [coordOf]
      refine ⟨coordOf_mem h ((elemWallEdges h)[k.1]'k.2).1, ?_⟩
      split_ifs with heq <;> rcases hedge with ⟨_, _⟩ | ⟨⟨_, _⟩, _⟩ <;> omega
    | none =>
      unfold WallOfHeight.vertexFinset at hv
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        List.mem_toFinset, List.mem_flatMap, List.mem_finRange] at hv
      rcases hv with ⟨u, hu⟩ | ⟨k, hk⟩
      · have hnone := List.find?_eq_none.mp hfind1 u (List.mem_finRange u)
        simp [hu] at hnone
      · have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
        simp [hk] at hnone

theorem termGridCell_bounds {h n : ℕ} (hh : 1 ≤ h) {G : MultiDigraph n}
    {W : WallOfHeight h G} {v : Fin n} (hv : v ∈ W.vertexFinset) :
    1 ≤ (termGridCell W v).1 ∧ (termGridCell W v).1 ≤ h ∧ (termGridCell W v).2 ≤ h := by
  have hrep := (repCoord_mem_and_vertCell_bounds hv).1
  have hb := (mem_elemWallCoords_iff h (repCoord W v)).mp hrep
  have hc := coarseCol_bounds hh (repCoord W v).1
  exact ⟨hc.1, hc.2, hb.2.1⟩

/-- If `q` lies outside `IsInInnerBox h B q`, then `gridDepth h q < 2 * B`. -/
theorem gridDepth_lt_of_not_isInInnerBox {h B : ℕ} {q : ℕ × ℕ}
    (hout : ¬ IsInInnerBox h B q) :
    gridDepth h q < 2 * (B : ℤ) := by
  unfold IsInInnerBox at hout
  unfold gridDepth
  rcases q with ⟨c, y⟩
  dsimp at hout ⊢
  omega

/-- If `1 ≤ q.1 ≤ h`, `q.2 ≤ h`, and `2 * (B + D) ≤ gridDepth h q`, then
`B + D + 1 ≤ q.1 ∧ q.1 + D ≤ h - B ∧ 2 * (B + D) ≤ q.2 ∧ q.2 + 2 * D ≤ h - 2 * B`. -/
theorem margin_of_le_gridDepth {h B D : ℕ} {q : ℕ × ℕ}
    (hq : 1 ≤ q.1 ∧ q.1 ≤ h ∧ q.2 ≤ h)
    (hgd : 2 * ((B : ℤ) + (D : ℤ)) ≤ gridDepth h q) :
    B + D + 1 ≤ q.1 ∧ q.1 + D ≤ h - B ∧
    2 * (B + D) ≤ q.2 ∧ q.2 + 2 * D ≤ h - 2 * B := by
  unfold gridDepth at hgd
  rcases q with ⟨c, y⟩
  dsimp at hq hgd ⊢
  omega

/-- Box margin selection for `m` terminals `term : Fin m → ℕ × ℕ`:
uses `B₁ = 2` if all terminals lie inside `IsInInnerBox h B₂` (where
`B₂ = m * (4 * p + 2) + 2 * p + 3`), and `B₂` otherwise. -/
def chooseBoxMargin (p h m : ℕ) (term : Fin m → ℕ × ℕ) : ℕ :=
  let B₂ := m * (4 * p + 2) + 2 * p + 3
  if (List.finRange m).all (fun a => decide (IsInInnerBox h B₂ (term a))) then 2 else B₂

/-- Brick distance threshold `r(p) = 6 * alg74Margin p + 60` used for lifting GM XIII (7.4). -/
def alg74LiftRadius (p : ℕ) : ℕ :=
  6 * alg74Margin p + 60

theorem choose_two_mul_two_le (p : ℕ) : 2 * p.choose 2 ≤ p * (p - 1) := by
  rw [Nat.choose_two_right, Nat.mul_comm]
  exact Nat.div_mul_le_self (p * (p - 1)) 2

/-- Coarse-grid branch set for color `gamma : Fin p` on input `x : Alg74Input p r`. -/
def alg74CoarseBranchSet {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) : Finset (ℕ × ℕ) :=
  let m := 2 * (completeGraphEdges p).length
  let term := fun a : Fin m => termGridCell x.W (alg74TermVert x a)
  let B := chooseBoxMargin p x.h m term
  routedBranchSet p x.h B m (by omega) term (alg74RawColor p) gamma

theorem alg74CoarseBranchSet_spec {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) :
    let m := 2 * (completeGraphEdges p).length
    let R := alg74CoarseBranchSet hp x
    (∀ (gamma : Fin p) {q : ℕ × ℕ}, q ∈ R gamma → 1 ≤ q.1 ∧ q.1 ≤ x.h ∧ q.2 ≤ x.h) ∧
    (∀ a : Fin m, termGridCell x.W (alg74TermVert x a) ∈ R (alg74RawColor p a)) ∧
    (∀ gamma : Fin p, IsWalkConnected rectGridGraph (R gamma)) ∧
    (∀ {gamma₁ gamma₂ : Fin p}, gamma₁ ≠ gamma₂ → Disjoint (R gamma₁) (R gamma₂)) := by
  let h := x.h
  let m := 2 * (completeGraphEdges p).length
  let term : Fin m → ℕ × ℕ := fun a => termGridCell x.W (alg74TermVert x a)
  let B := chooseBoxMargin p h m term
  let B₂ := m * (4 * p + 2) + 2 * p + 3
  have hh1 : 1 ≤ h := by have := x.hW_valid.1; omega
  have hm_le : m ≤ p * (p - 1) := by
    dsimp [m]
    rw [length_completeGraphEdges]
    exact choose_two_mul_two_le p
  have hm_mul_le : m * (4 * p + 2) ≤ p * (p - 1) * (4 * p + 2) :=
    Nat.mul_le_mul_right _ hm_le
  have hr_ge : 6 * B₂ + 60 ≤ alg74LiftRadius p := by
    unfold alg74LiftRadius alg74Margin alg74MaxShift
    dsimp [B₂]
    omega
  have hr6 : 6 ≤ alg74LiftRadius p := by omega
  have hbounds : ∀ a : Fin m, 1 ≤ (term a).1 ∧ (term a).1 ≤ h ∧ (term a).2 ≤ h :=
    fun a => termGridCell_bounds hh1 (alg74TermVert_mem_vertexFinset x a)
  have hpair : ∀ a₁ a₂ : Fin m, a₁ ≠ a₂ →
      (((alg74LiftRadius p - 6 : ℤ) ≤ 2 * (((term a₁).1 : ℤ) - ((term a₂).1 : ℤ)) ∨
          (alg74LiftRadius p - 6 : ℤ) ≤ 2 * (((term a₂).1 : ℤ) - ((term a₁).1 : ℤ))) ∨
        ((alg74LiftRadius p - 6 : ℤ) ≤ ((term a₁).2 : ℤ) - ((term a₂).2 : ℤ) ∨
          (alg74LiftRadius p - 6 : ℤ) ≤ ((term a₂).2 : ℤ) - ((term a₁).2 : ℤ))) ∧
      (alg74LiftRadius p : ℤ) - 6 ≤ gridDepth h (term a₁) + gridDepth h (term a₂) := by
    intro a₁ a₂ hne
    have hdist := alg74TermVert_brickDist_ge x hne
    have hne_v : alg74TermVert x a₁ ≠ alg74TermVert x a₂ :=
      fun heq => hne (alg74TermVert_injective x (by omega) heq)
    rw [WallOfHeight.brickDist, ite_eq_right_iff.mpr (fun h => False.elim (hne_v h))] at hdist
    have hr₁ := repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a₁)
    have hr₂ := repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a₂)
    have hb₁ := (mem_elemWallCoords_iff h _).mp hr₁.1
    have hb₂ := (mem_elemWallCoords_iff h _).mp hr₂.1
    exact coarse_sep_and_depth_of_fig1CellBrickDist hh1 hr6 hb₁.2.1 hb₂.2.1
      hr₁.2 hr₂.2 hdist
  have hm_ge2 : 2 ≤ m := by
    have hlt : (⟨0, by omega⟩ : Fin p) < ⟨1, by omega⟩ := by simp
    have hmem : ((⟨0, by omega⟩ : Fin p), (⟨1, by omega⟩ : Fin p)) ∈ completeGraphEdges p :=
      (mem_completeGraphEdges_iff _).mpr hlt
    have hpos : 0 < (completeGraphEdges p).length := List.length_pos_of_mem hmem
    dsimp [m]
    omega
  have hh_big : 2 * B₂ + 2 * p ≤ h := by
    let a₀ : Fin m := ⟨0, by omega⟩
    let a₁ : Fin m := ⟨1, by omega⟩
    have hne01 : a₀ ≠ a₁ := by
      intro heq
      have : (0 : ℕ) = 1 := congrArg Fin.val heq
      omega
    have hp01 := (hpair a₀ a₁ hne01).1
    have hb0 := hbounds a₀
    have hb1 := hbounds a₁
    rcases hp01 with (h1 | h2) | (h3 | h4) <;> omega
  have hB_bounds : 2 ≤ B ∧ B ≤ B₂ := by
    dsimp [B, chooseBoxMargin, B₂]
    split_ifs <;> omega
  have hh_B : 2 * B + 2 * p ≤ h := by omega
  have hperim_uniq : ∀ a₁ a₂ : Fin m,
      ¬ IsInInnerBox h B (term a₁) → ¬ IsInInnerBox h B (term a₂) → a₁ = a₂ := by
    intro a₁ a₂ hout₁ hout₂
    by_contra hne
    have hgd₁ := gridDepth_lt_of_not_isInInnerBox hout₁
    have hgd₂ := gridDepth_lt_of_not_isInInnerBox hout₂
    have hsum := (hpair a₁ a₂ hne).2
    omega
  have hint_margin : ∀ a : Fin m, IsInInnerBox h B (term a) →
      B + p + 1 ≤ (term a).1 ∧
      (term a).1 + m * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (term a).2 ∧
      (term a).2 + 2 * p + 1 ≤ h - B := by
    intro a hin
    dsimp [B, chooseBoxMargin] at hin ⊢
    split_ifs at hin ⊢ with hall
    · have ha_in : IsInInnerBox h B₂ (term a) := by
        have hmem := List.all_eq_true.mp hall a (List.mem_finRange a)
        simpa using hmem
      unfold IsInInnerBox at ha_in
      dsimp [B₂] at ha_in
      omega
    · have hex : ∃ a₀ : Fin m, ¬ IsInInnerBox h B₂ (term a₀) := by
        by_contra hnot
        push Not at hnot
        have hall' : (List.finRange m).all (fun x => decide (IsInInnerBox h B₂ (term x))) = true := by
          rw [List.all_eq_true]
          intro x _
          simpa using hnot x
        exact hall hall'
      rcases hex with ⟨a₀, ha₀_out⟩
      have hne : a₀ ≠ a := fun heq => ha₀_out (heq ▸ hin)
      have hgd₀ := gridDepth_lt_of_not_isInInnerBox ha₀_out
      have hsum := (hpair a₀ a hne).2
      let D := m * (4 * p + 2) + 2 * p + 1
      have hB₂_eq : B₂ = D + 2 := rfl
      have hgd_a : 2 * ((B₂ : ℤ) + (D : ℤ)) ≤ gridDepth h (term a) := by omega
      have hm_a := margin_of_le_gridDepth (hbounds a) hgd_a
      dsimp [D, B₂] at hm_a ⊢
      omega
  have hsep : ∀ a₁ a₂ : Fin m, a₁ ≠ a₂ →
      ((2 * (m * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((term a₁).1 : ℤ) - ((term a₂).1 : ℤ)) ∨
          2 * (m * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((term a₂).1 : ℤ) - ((term a₁).1 : ℤ))) ∨
        ((2 * p + 2 : ℤ) ≤ ((term a₁).2 : ℤ) - ((term a₂).2 : ℤ) ∨
          (2 * p + 2 : ℤ) ≤ ((term a₂).2 : ℤ) - ((term a₁).2 : ℤ))) := by
    intro a₁ a₂ hne
    have hp12 := (hpair a₁ a₂ hne).1
    have hB₂_def : (B₂ : ℤ) = (m : ℤ) * (4 * (p : ℤ) + 2) + 2 * (p : ℤ) + 3 := rfl
    rcases hp12 with (h1 | h2) | (h3 | h4)
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  exact routedBranchSet_spec (B := B) hp hB_bounds.1 hh_B hbounds hperim_uniq hint_margin hsep

/-! ### Section 3: Lifting to `wallCoordBranchSet` and `wallVertBranchSet` in `G` -/

theorem IsWalkConnected.union_of_forall_mem_or_adj {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S T : Finset V}
    (hS : IsWalkConnected G S)
    (hT : ∀ v ∈ T, v ∈ S ∨ ∃ u ∈ S, G.Adj u v) :
    IsWalkConnected G (S ∪ T) := by
  rcases hS with ⟨⟨v₀, hv₀⟩, hwalkS⟩
  have hv₀_u : v₀ ∈ S ∪ T := Finset.mem_union_left _ hv₀
  have hto : ∀ w ∈ S ∪ T, WalkIn G (S ∪ T) v₀ w := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwS | hwT
    · exact (hwalkS v₀ hv₀ w hwS).mono Finset.subset_union_left
    · rcases hT w hwT with hwS | ⟨u, huS, hadj⟩
      · exact (hwalkS v₀ hv₀ w hwS).mono Finset.subset_union_left
      · exact ((hwalkS v₀ hv₀ u huS).mono Finset.subset_union_left).trans
          (WalkIn.of_adj (Finset.mem_union_left _ huS) hw hadj)
  exact ⟨⟨v₀, hv₀_u⟩, fun u hu v hv => (hto u hu).symm.trans (hto v hv)⟩

/-- Elementary-wall coordinate set for color `gamma : Fin p`:
lifts `alg74CoarseBranchSet hp x gamma` via `liftGrid` and attaches `repCoord` of every terminal
of color `gamma` (handling any boundary terminals at `x = 0` or `x = 2h + 1`). -/
def wallCoordBranchSet {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) : Finset (ℕ × ℕ) :=
  liftGrid (alg74CoarseBranchSet hp x gamma) ∪
  (Finset.univ.filter (fun a : Fin (2 * (completeGraphEdges p).length) =>
    alg74RawColor p a = gamma)).image (fun a => repCoord x.W (alg74TermVert x a))

theorem repCoord_mem_wallCoordBranchSet {p r : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p r) (a : Fin (2 * (completeGraphEdges p).length)) :
    repCoord x.W (alg74TermVert x a) ∈ wallCoordBranchSet hp x (alg74RawColor p a) := by
  unfold wallCoordBranchSet
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl⟩, rfl⟩

theorem mem_elemWallCoords_of_mem_wallCoordBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) {gamma : Fin p} {q : ℕ × ℕ}
    (hq : q ∈ wallCoordBranchSet hp x gamma) :
    q ∈ elemWallCoords x.h := by
  have hspec := alg74CoarseBranchSet_spec hp x
  have hlift := (isWalkConnected_liftGrid (fun r hr => hspec.1 gamma hr) (hspec.2.2.1 gamma)).1
  unfold wallCoordBranchSet at hq
  rcases Finset.mem_union.mp hq with hq_lift | hq_img
  · exact hlift q hq_lift
  · rw [Finset.mem_image] at hq_img
    rcases hq_img with ⟨a, _, rfl⟩
    exact (repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a)).1

theorem isWalkConnected_wallCoordBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) (gamma : Fin p) :
    IsWalkConnected (elemWallCoordGraph x.h) (wallCoordBranchSet hp x gamma) := by
  let h := x.h
  have hspec := alg74CoarseBranchSet_spec hp x
  have hh1 : 1 ≤ h := by have := x.hW_valid.1; omega
  have hconn_lift := (isWalkConnected_liftGrid (fun r hr => hspec.1 gamma hr) (hspec.2.2.1 gamma)).2
  apply hconn_lift.union_of_forall_mem_or_adj
  intro q hq
  rw [Finset.mem_image] at hq
  rcases hq with ⟨a, ha_f, rfl⟩
  have ha_col : alg74RawColor p a = gamma := (Finset.mem_filter.mp ha_f).2
  have hterm_mem : termGridCell x.W (alg74TermVert x a) ∈ alg74CoarseBranchSet hp x gamma := by
    rw [← ha_col]
    exact hspec.2.1 a
  have hpair_sub :
      cellPair (coarseCol h (repCoord x.W (alg74TermVert x a)).1)
        (repCoord x.W (alg74TermVert x a)).2 ⊆
        liftGrid (alg74CoarseBranchSet hp x gamma) := by
    intro r hr
    exact (mem_liftGrid.mpr ⟨termGridCell x.W (alg74TermVert x a), hterm_mem, hr⟩)
  have hrep_mem := (repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a)).1
  rcases mem_or_adj_cellPair_coarseCol hh1 hrep_mem with hmem | ⟨_, u, hu, hadj⟩
  · exact Or.inl (hpair_sub hmem)
  · exact Or.inr ⟨u, hpair_sub hu, hadj.symm⟩

theorem disjoint_wallCoordBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) {gamma₁ gamma₂ : Fin p} (hne : gamma₁ ≠ gamma₂) :
    Disjoint (wallCoordBranchSet hp x gamma₁) (wallCoordBranchSet hp x gamma₂) := by
  let h := x.h
  have hspec := alg74CoarseBranchSet_spec hp x
  have hh1 : 1 ≤ h := by have := x.hW_valid.1; omega
  have hdisj_lift := disjoint_liftGrid
    (fun r hr => (hspec.1 gamma₁ hr).1)
    (fun r hr => (hspec.1 gamma₂ hr).1)
    (hspec.2.2.2 hne)
  have hlift_x : ∀ (gamma : Fin p) {q : ℕ × ℕ},
      q ∈ liftGrid (alg74CoarseBranchSet hp x gamma) → 1 ≤ q.1 ∧ q.1 ≤ 2 * h := by
    intro gamma q hq
    rw [mem_liftGrid] at hq
    rcases hq with ⟨r, hr, hqr⟩
    have hb := hspec.1 gamma hr
    simp only [cellPair, Finset.mem_insert, Finset.mem_singleton] at hqr
    rcases hqr with rfl | rfl <;> omega
  have hrep_in_lift_of_x : ∀ a : Fin (2 * (completeGraphEdges p).length),
      1 ≤ (repCoord x.W (alg74TermVert x a)).1 ∧
        (repCoord x.W (alg74TermVert x a)).1 ≤ 2 * h →
      repCoord x.W (alg74TermVert x a) ∈
        liftGrid (alg74CoarseBranchSet hp x (alg74RawColor p a)) := by
    intro a hx
    have hrep_mem := (repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a)).1
    rcases mem_or_adj_cellPair_coarseCol hh1 hrep_mem with hmem | ⟨hx_out, _⟩
    · exact mem_liftGrid.mpr ⟨termGridCell x.W (alg74TermVert x a), hspec.2.1 a, hmem⟩
    · omega
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  unfold wallCoordBranchSet at hq₁ hq₂
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq₁ hq₂
  rcases hq₁ with hq₁ | ⟨a₁, rfl, rfl⟩ <;> rcases hq₂ with hq₂ | ⟨a₂, heq₂, heq_q⟩
  · exact Finset.disjoint_left.mp hdisj_lift hq₁ hq₂
  · rw [← heq_q] at hq₁
    have hx := hlift_x gamma₁ hq₁
    have hq₂_lift := hrep_in_lift_of_x a₂ hx
    rw [heq₂] at hq₂_lift
    exact Finset.disjoint_left.mp hdisj_lift hq₁ hq₂_lift
  · have hx := hlift_x gamma₂ hq₂
    have hq₁_lift := hrep_in_lift_of_x a₁ hx
    exact Finset.disjoint_left.mp hdisj_lift hq₁_lift hq₂
  · have ha_ne : a₁ ≠ a₂ := fun h => hne (h ▸ heq₂)
    have hdist := alg74TermVert_brickDist_ge x ha_ne
    have hne_v : alg74TermVert x a₁ ≠ alg74TermVert x a₂ :=
      fun h => ha_ne (alg74TermVert_injective x (by unfold alg74LiftRadius; omega) h)
    rw [WallOfHeight.brickDist, ite_eq_right_iff.mpr (fun h => False.elim (hne_v h))] at hdist
    have hr₁ := repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a₁)
    have hr₂ := repCoord_mem_and_vertCell_bounds (alg74TermVert_mem_vertexFinset x a₂)
    have hb₁ := (mem_elemWallCoords_iff h _).mp hr₁.1
    have hb₂ := (mem_elemWallCoords_iff h _).mp hr₂.1
    have hr7 : 7 ≤ alg74LiftRadius p := by unfold alg74LiftRadius; omega
    have hr6 : 6 ≤ alg74LiftRadius p := by omega
    have hsep := (coarse_sep_and_depth_of_fig1CellBrickDist hh1 hr6 hb₁.2.1 hb₂.2.1
      hr₁.2 hr₂.2 hdist).1
    rw [heq_q] at hsep
    rcases hsep with (h1 | h2) | (h3 | h4) <;> omega

attribute [irreducible] wallCoordBranchSet

/-- If `L₁ ++ L₂` is a simple walk list in `G`, then so is its prefix `L₁`. -/
theorem isSimpleWalkList_of_append_left {n : ℕ} {G : MultiDigraph n} :
    ∀ {L₁ L₂ : List (Fin n)},
      WallOfHeight.IsSimpleWalkList G (L₁ ++ L₂) →
      WallOfHeight.IsSimpleWalkList G L₁
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: _ :: _, _, hw => ⟨hw.1, isSimpleWalkList_of_append_left hw.2⟩

/-- Every vertex in a simple walk list `L` in `G` with `L ⊆ S` is connected by a `WalkIn` in
`G.toSimpleGraph` from `L.head hne`. -/
theorem walkIn_of_isSimpleWalkList {n : ℕ} {G : MultiDigraph n} {S : Finset (Fin n)} :
    ∀ {L : List (Fin n)} (hne : L ≠ []),
      WallOfHeight.IsSimpleWalkList G L →
      (∀ v ∈ L, v ∈ S) →
      ∀ v ∈ L, WalkIn G.toSimpleGraph S (L.head hne) v
  | [], hne, _, _, _, _ => False.elim (hne rfl)
  | [u], _, _, hsub, v, hv => by
    simp only [List.mem_singleton] at hv
    subst hv
    exact WalkIn.refl (hsub v (by simp))
  | u :: w :: rest, _, hw, hsub, v, hv => by
    have hu : u ∈ S := hsub u (by simp)
    have hw_mem : w ∈ S := hsub w (by simp)
    rcases List.mem_cons.mp hv with rfl | hv_tail
    · exact WalkIn.refl hu
    · have hstep : WalkIn G.toSimpleGraph S u w := WalkIn.of_adj hu hw_mem hw.1
      have hrest := walkIn_of_isSimpleWalkList (List.cons_ne_nil w rest) hw.2
        (fun z hz => hsub z (List.mem_cons_of_mem u hz)) v hv_tail
      exact hstep.trans hrest

/-- Predicate testing whether the internal subdivision vertices `W.internalVerts k` of the `k`-th
elementary-wall edge `e_k = (u₁, u₂)` belong to color `gamma`'s branch set:
either both endpoints `u₁, u₂` lie in `wallCoordBranchSet hp x gamma`, or `u₁` lies in
`wallCoordBranchSet hp x gamma` and some terminal of color `gamma` lies in `W.internalVerts k`. -/
def wallEdgeActive {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) (k : Fin (elemWallEdges x.h).length) : Prop :=
  let e := (elemWallEdges x.h)[k.1]'k.2
  coordOf x.h e.1 ∈ wallCoordBranchSet hp x gamma ∧
  (coordOf x.h e.2 ∈ wallCoordBranchSet hp x gamma ∨
    ∃ a : Fin (2 * (completeGraphEdges p).length),
      alg74RawColor p a = gamma ∧ alg74TermVert x a ∈ x.W.internalVerts k)

instance instDecidableWallEdgeActive {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) (k : Fin (elemWallEdges x.h).length) :
    Decidable (wallEdgeActive hp x gamma k) := by
  unfold wallEdgeActive
  infer_instance

/-- Vertex subset of the wall `x.W` in `x.G` assigned to color `gamma : Fin p`. -/
def wallVertBranchSet {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) : Finset (Fin x.n) :=
  (Finset.univ.filter (fun u : Fin (elemWallNumVerts x.h) =>
    coordOf x.h u ∈ wallCoordBranchSet hp x gamma)).image x.W.branchVert ∪
  (Finset.univ.filter (fun k : Fin (elemWallEdges x.h).length =>
    wallEdgeActive hp x gamma k)).biUnion (fun k => (x.W.internalVerts k).toFinset)

theorem wallVertBranchSet_subset_vertexFinset {p r : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p r) (gamma : Fin p) :
    wallVertBranchSet hp x gamma ⊆ x.W.vertexFinset := by
  intro v hv
  unfold wallVertBranchSet at hv
  unfold WallOfHeight.vertexFinset
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, List.mem_toFinset, List.mem_flatMap, List.mem_finRange] at hv ⊢
  rcases hv with ⟨u, _, rfl⟩ | ⟨k, _, hk⟩
  · exact Or.inl ⟨u, rfl⟩
  · exact Or.inr ⟨k, hk⟩

theorem alg74TermVert_mem_wallVertBranchSet {p r : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p r) (a : Fin (2 * (completeGraphEdges p).length)) :
    alg74TermVert x a ∈ wallVertBranchSet hp x (alg74RawColor p a) := by
  let h := x.h
  let v := alg74TermVert x a
  let gamma := alg74RawColor p a
  have hv := alg74TermVert_mem_vertexFinset x a
  have hrep := repCoord_mem_wallCoordBranchSet hp x a
  unfold wallVertBranchSet
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, List.mem_toFinset]
  unfold repCoord at hrep
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (x.W.branchVert u = v)) with
  | some u =>
    rw [hfind1] at hrep
    have hu_eq : x.W.branchVert u = v := by
      have hp_some := List.find?_some hfind1
      simpa using hp_some
    exact Or.inl ⟨u, hrep, hu_eq⟩
  | none =>
    rw [hfind1] at hrep
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ x.W.internalVerts k)) with
    | some k =>
      rw [hfind2] at hrep
      have hk_mem : v ∈ x.W.internalVerts k := by
        have hp_some := List.find?_some hfind2
        simpa using hp_some
      exact Or.inr ⟨k, ⟨hrep, Or.inr ⟨a, rfl, hk_mem⟩⟩, hk_mem⟩
    | none =>
      unfold WallOfHeight.vertexFinset at hv
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        List.mem_toFinset, List.mem_flatMap, List.mem_finRange] at hv
      rcases hv with ⟨u, hu⟩ | ⟨k, hk⟩
      · have hnone := List.find?_eq_none.mp hfind1 u (List.mem_finRange u)
        dsimp [v] at hnone
        simp [hu] at hnone
      · have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
        dsimp [v] at hnone
        simp [hk] at hnone

theorem disjoint_wallVertBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) {gamma₁ gamma₂ : Fin p} (hne : gamma₁ ≠ gamma₂) :
    Disjoint (wallVertBranchSet hp x gamma₁) (wallVertBranchSet hp x gamma₂) := by
  have hdisj_coord := disjoint_wallCoordBranchSet hp x hne
  rcases x.hW_valid.2.2 with ⟨hinj_br, _, hnot_in_int, hdisj_int⟩
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  unfold wallVertBranchSet at hv₁ hv₂
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, List.mem_toFinset] at hv₁ hv₂
  rcases hv₁ with ⟨u₁, hu₁, rfl⟩ | ⟨k₁, hk₁, hv_k₁⟩ <;>
  rcases hv₂ with ⟨u₂, hu₂, heq⟩ | ⟨k₂, hk₂, hv_k₂⟩
  · have hu_eq : u₁ = u₂ := hinj_br heq.symm
    subst hu_eq
    exact Finset.disjoint_left.mp hdisj_coord hu₁ hu₂
  · exact hnot_in_int k₂ u₁ hv_k₂
  · rw [← heq] at hv_k₁
    exact hnot_in_int k₁ u₂ hv_k₁
  · by_cases hk_eq : k₁ = k₂
    · subst hk_eq
      exact Finset.disjoint_left.mp hdisj_coord hk₁.1 hk₂.1
    · exact hdisj_int k₁ k₂ hk_eq hv_k₁ hv_k₂

theorem exists_elemWallEdge_index {h : ℕ} {u₁ u₂ : Fin (elemWallNumVerts h)}
    (hedge : isElemWallEdgeCoord (coordOf h u₁) (coordOf h u₂) = true) :
    ∃ k : Fin (elemWallEdges h).length, (elemWallEdges h)[k.1]'k.2 = (u₁, u₂) := by
  have hmem : (u₁, u₂) ∈ elemWallEdges h := (mem_elemWallEdges_coordOf_iff h (u₁, u₂)).mpr hedge
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  exact ⟨⟨i, hi⟩, heq⟩

theorem subdivPathVerts_of_eq {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {k : Fin (elemWallEdges h).length} {u₁ u₂ : Fin (elemWallNumVerts h)}
    (hk : (elemWallEdges h)[k.1]'k.2 = (u₁, u₂)) :
    W.subdivPathVerts k = [W.branchVert u₁] ++ W.internalVerts k ++ [W.branchVert u₂] := by
  unfold WallOfHeight.subdivPathVerts
  dsimp only
  rw [hk]

/-- General wall-vertex subset induced by an elementary-wall coordinate set `C` and an active edge
predicate `edgeAct`. -/
def wallVertSet {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (C : Finset (ℕ × ℕ)) (edgeAct : Fin (elemWallEdges h).length → Prop) [DecidablePred edgeAct] :
    Finset (Fin n) :=
  (Finset.univ.filter (fun u : Fin (elemWallNumVerts h) => coordOf h u ∈ C)).image W.branchVert ∪
  (Finset.univ.filter edgeAct).biUnion (fun k => (W.internalVerts k).toFinset)

theorem mem_wallVertSet_iff {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (C : Finset (ℕ × ℕ)) (edgeAct : Fin (elemWallEdges h).length → Prop) [DecidablePred edgeAct]
    (v : Fin n) :
    v ∈ wallVertSet W C edgeAct ↔
      (∃ u : Fin (elemWallNumVerts h), coordOf h u ∈ C ∧ W.branchVert u = v) ∨
      (∃ k : Fin (elemWallEdges h).length, edgeAct k ∧ v ∈ W.internalVerts k) := by
  unfold wallVertSet
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]

theorem wallVertBranchSet_eq_wallVertSet {p r : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p r) (gamma : Fin p) :
    wallVertBranchSet hp x gamma =
      wallVertSet x.W (wallCoordBranchSet hp x gamma) (wallEdgeActive hp x gamma) :=
  rfl

attribute [irreducible] wallVertSet wallVertBranchSet

theorem isWalkConnected_wallVertSet {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (hvalid_subdiv : ∀ k : Fin (elemWallEdges h).length,
      WallOfHeight.IsSimpleWalkList G (W.subdivPathVerts k))
    (C : Finset (ℕ × ℕ)) (hC_sub : ∀ q ∈ C, q ∈ elemWallCoords h)
    (hconn_C : IsWalkConnected (elemWallCoordGraph h) C)
    (edgeAct : Fin (elemWallEdges h).length → Prop) [DecidablePred edgeAct]
    (hact_of_both : ∀ k : Fin (elemWallEdges h).length,
      coordOf h ((elemWallEdges h)[k.1]'k.2).1 ∈ C →
      coordOf h ((elemWallEdges h)[k.1]'k.2).2 ∈ C → edgeAct k)
    (hact_left : ∀ k : Fin (elemWallEdges h).length,
      edgeAct k → coordOf h ((elemWallEdges h)[k.1]'k.2).1 ∈ C) :
    IsWalkConnected G.toSimpleGraph (wallVertSet W C edgeAct) := by
  have hbr_mem_S : ∀ u : Fin (elemWallNumVerts h),
      coordOf h u ∈ C → W.branchVert u ∈ wallVertSet W C edgeAct := by
    intro u hu
    rw [mem_wallVertSet_iff]
    exact Or.inl ⟨u, hu, rfl⟩
  have hint_sub_S : ∀ k : Fin (elemWallEdges h).length,
      edgeAct k → ∀ v ∈ W.internalVerts k, v ∈ wallVertSet W C edgeAct := by
    intro k hk v hv
    rw [mem_wallVertSet_iff]
    exact Or.inr ⟨k, hk, hv⟩
  have hwalk_dir_edge : ∀ u₁ u₂ : Fin (elemWallNumVerts h),
      coordOf h u₁ ∈ C → coordOf h u₂ ∈ C →
      isElemWallEdgeCoord (coordOf h u₁) (coordOf h u₂) = true →
      WalkIn G.toSimpleGraph (wallVertSet W C edgeAct) (W.branchVert u₁) (W.branchVert u₂) := by
    intro u₁ u₂ hu₁ hu₂ hedge
    rcases exists_elemWallEdge_index hedge with ⟨k, hk_eq⟩
    have hsubdiv := subdivPathVerts_of_eq W hk_eq
    have he1 : ((elemWallEdges h)[k.1]'k.2).1 = u₁ := congrArg Prod.fst hk_eq
    have he2 : ((elemWallEdges h)[k.1]'k.2).2 = u₂ := congrArg Prod.snd hk_eq
    have hk_act : edgeAct k :=
      hact_of_both k (he1.symm ▸ hu₁) (he2.symm ▸ hu₂)
    have hwalk_L : WallOfHeight.IsSimpleWalkList G
        (W.branchVert u₁ :: (W.internalVerts k ++ [W.branchVert u₂])) := by
      have hfull := hvalid_subdiv k
      rwa [hsubdiv, List.singleton_append, List.cons_append] at hfull
    have hsub_L : ∀ v ∈ W.branchVert u₁ :: (W.internalVerts k ++ [W.branchVert u₂]),
        v ∈ wallVertSet W C edgeAct := by
      intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv_int | rfl
      · exact hbr_mem_S u₁ hu₁
      · exact hint_sub_S k hk_act v hv_int
      · exact hbr_mem_S u₂ hu₂
    have hne_L : W.branchVert u₁ :: (W.internalVerts k ++ [W.branchVert u₂]) ≠ [] :=
      List.cons_ne_nil _ _
    have hlast_L : W.branchVert u₂ ∈
        W.branchVert u₁ :: (W.internalVerts k ++ [W.branchVert u₂]) := by
      simp
    exact walkIn_of_isSimpleWalkList hne_L hwalk_L hsub_L (W.branchVert u₂) hlast_L
  have hwalk_adj : ∀ u₁ u₂ : Fin (elemWallNumVerts h),
      coordOf h u₁ ∈ C → coordOf h u₂ ∈ C →
      (elemWallCoordGraph h).Adj (coordOf h u₁) (coordOf h u₂) →
      WalkIn G.toSimpleGraph (wallVertSet W C edgeAct) (W.branchVert u₁) (W.branchVert u₂) := by
    intro u₁ u₂ hu₁ hu₂ hadj
    rcases hadj with ⟨_, _, hdir | hrev⟩
    · exact hwalk_dir_edge u₁ u₂ hu₁ hu₂ hdir
    · exact (hwalk_dir_edge u₂ u₁ hu₂ hu₁ hrev).symm
  have hex_u : ∀ q ∈ C, ∃ u : Fin (elemWallNumVerts h), coordOf h u = q := by
    intro q hq
    rcases List.mem_iff_getElem.mp (hC_sub q hq) with ⟨i, hi, heq⟩
    exact ⟨⟨i, hi⟩, heq⟩
  have hwalk_coord : ∀ {q₁ q₂ : ℕ × ℕ} (w : (elemWallCoordGraph h).Walk q₁ q₂),
      (∀ q ∈ w.support, q ∈ C) →
      ∀ u₁ u₂ : Fin (elemWallNumVerts h),
        coordOf h u₁ = q₁ → coordOf h u₂ = q₂ →
        WalkIn G.toSimpleGraph (wallVertSet W C edgeAct) (W.branchVert u₁) (W.branchVert u₂) := by
    intro q₁ q₂ w
    induction w with
    | nil =>
      intro hsup u₁ u₂ hu₁ hu₂
      have heq : u₁ = u₂ := coordOf_injective h (hu₁.trans hu₂.symm)
      subst heq
      have hq₁ : coordOf h u₁ ∈ C := by
        rw [hu₁]
        exact hsup _ (SimpleGraph.Walk.start_mem_support _)
      exact WalkIn.refl (hbr_mem_S u₁ hq₁)
    | @cons a b c hadj w_rest ih =>
      intro hsup u₁ u₂ hu₁ hu₂
      have ha : a ∈ C := hsup a (by simp)
      have hb : b ∈ C := hsup b (List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support w_rest))
      rcases hex_u b hb with ⟨u_mid, hu_mid⟩
      have hadj' : (elemWallCoordGraph h).Adj (coordOf h u₁) (coordOf h u_mid) := by
        rwa [hu₁, hu_mid]
      have hw1 := hwalk_adj u₁ u_mid (by rwa [hu₁]) (by rwa [hu_mid]) hadj'
      have hw2 := ih (fun q hq => hsup q (List.mem_cons_of_mem a hq)) u_mid u₂ hu_mid hu₂
      exact hw1.trans hw2
  rcases hconn_C with ⟨⟨q₀, hq₀⟩, hwalkC⟩
  rcases hex_u q₀ hq₀ with ⟨u₀, hu₀⟩
  have hv₀_mem : W.branchVert u₀ ∈ wallVertSet W C edgeAct := hbr_mem_S u₀ (by rwa [hu₀])
  have hto_u₀ : ∀ v ∈ wallVertSet W C edgeAct,
      WalkIn G.toSimpleGraph (wallVertSet W C edgeAct) (W.branchVert u₀) v := by
    intro v hv
    rw [mem_wallVertSet_iff] at hv
    rcases hv with ⟨u, hu, rfl⟩ | ⟨k, hk, hv_k⟩
    · rcases hwalkC q₀ hq₀ (coordOf h u) hu with ⟨w, hw⟩
      exact hwalk_coord w hw u₀ u hu₀ rfl
    · let e_k := (elemWallEdges h)[k.1]'k.2
      have hu₁_C : coordOf h e_k.1 ∈ C := hact_left k hk
      rcases hwalkC q₀ hq₀ (coordOf h e_k.1) hu₁_C with ⟨w, hw⟩
      have hw_br := hwalk_coord w hw u₀ e_k.1 hu₀ rfl
      have hsubdiv_eq : W.subdivPathVerts k =
          (W.branchVert e_k.1 :: W.internalVerts k) ++ [W.branchVert e_k.2] := rfl
      have hwalk_pref : WallOfHeight.IsSimpleWalkList G
          (W.branchVert e_k.1 :: W.internalVerts k) := by
        have hfull := hvalid_subdiv k
        rw [hsubdiv_eq] at hfull
        exact isSimpleWalkList_of_append_left hfull
      have hsub_pref : ∀ z ∈ W.branchVert e_k.1 :: W.internalVerts k,
          z ∈ wallVertSet W C edgeAct := by
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz_int
        · exact hbr_mem_S e_k.1 hu₁_C
        · exact hint_sub_S k hk z hz_int
      have hne_pref : W.branchVert e_k.1 :: W.internalVerts k ≠ [] :=
        List.cons_ne_nil _ _
      have hw_int := walkIn_of_isSimpleWalkList hne_pref hwalk_pref hsub_pref v
        (List.mem_cons_of_mem _ hv_k)
      exact hw_br.trans hw_int
  exact ⟨⟨W.branchVert u₀, hv₀_mem⟩, fun u hu v hv => (hto_u₀ u hu).symm.trans (hto_u₀ v hv)⟩

theorem isWalkConnected_wallVertBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) (gamma : Fin p) :
    IsWalkConnected x.G.toSimpleGraph (wallVertBranchSet hp x gamma) := by
  rw [wallVertBranchSet_eq_wallVertSet]
  exact isWalkConnected_wallVertSet x.W (fun k => (x.hW_valid.2.2.2.1 k).2)
    (wallCoordBranchSet hp x gamma)
    (fun _ hq => mem_elemWallCoords_of_mem_wallCoordBranchSet hp x hq)
    (isWalkConnected_wallCoordBranchSet hp x gamma)
    (wallEdgeActive hp x gamma)
    (fun _ h1 h2 => ⟨h1, Or.inl h2⟩)
    (fun _ hk => hk.1)

/-! ### Section 4: Attaching the $H$-Paths and Constructing `alg74UnderlyingModel` -/

/-- Start terminal index `2 * e` of edge `e : Fin (completeGraphEdges p).length`. -/
def edgeStartTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    Fin (2 * (completeGraphEdges p).length) :=
  ⟨2 * e.1, by omega⟩

/-- End terminal index `2 * e + 1` of edge `e : Fin (completeGraphEdges p).length`. -/
def edgeEndTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    Fin (2 * (completeGraphEdges p).length) :=
  ⟨2 * e.1 + 1, by omega⟩

@[simp]
theorem termPathIdx_edgeStartTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    termPathIdx (edgeStartTerm e) = e := by
  apply Fin.ext
  dsimp [termPathIdx, edgeStartTerm]
  omega

@[simp]
theorem termPathIdx_edgeEndTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    termPathIdx (edgeEndTerm e) = e := by
  apply Fin.ext
  dsimp [termPathIdx, edgeEndTerm]
  omega

@[simp]
theorem termIsEnd_edgeStartTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    termIsEnd (edgeStartTerm e) = false := by
  dsimp [termIsEnd, edgeStartTerm]
  rw [beq_eq_false_iff_ne]
  omega

@[simp]
theorem termIsEnd_edgeEndTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    termIsEnd (edgeEndTerm e) = true := by
  dsimp [termIsEnd, edgeEndTerm]
  rw [beq_iff_eq]
  omega

@[simp]
theorem alg74RawColor_edgeStartTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    alg74RawColor p (edgeStartTerm e) = ((completeGraphEdges p)[e.1]'e.2).1 := by
  simp [alg74RawColor]

@[simp]
theorem alg74RawColor_edgeEndTerm {p : ℕ} (e : Fin (completeGraphEdges p).length) :
    alg74RawColor p (edgeEndTerm e) = ((completeGraphEdges p)[e.1]'e.2).2 := by
  simp [alg74RawColor]

theorem alg74TermVert_edgeStartTerm {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    alg74TermVert x (edgeStartTerm e) = (alg74Path x e).head (alg74Path_ne_nil x e) := by
  unfold alg74TermVert
  simp

theorem alg74TermVert_edgeEndTerm {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    alg74TermVert x (edgeEndTerm e) = (alg74Path x e).getLast (alg74Path_ne_nil x e) := by
  unfold alg74TermVert
  simp

theorem mem_dropLast_iff_head_or_mem_drop_one_dropLast {α : Type*} :
    ∀ {L : List α} (hne : L ≠ []), 2 ≤ L.length →
      ∀ v, v ∈ L.dropLast ↔ v = L.head hne ∨ v ∈ (L.drop 1).dropLast
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, hlen, _ => by simp at hlen
  | u :: w :: rest, _, _, v => by
    have hne' : w :: rest ≠ [] := List.cons_ne_nil w rest
    rw [List.dropLast_cons_of_ne_nil hne']
    simp

theorem head_dropLast_eq_head {α : Type*} :
    ∀ {L : List α} (hne : L ≠ []) (hdrop : L.dropLast ≠ []),
      L.dropLast.head hdrop = L.head hne
  | [], hne, _ => False.elim (hne rfl)
  | [_], _, hdrop => False.elim (hdrop rfl)
  | u :: w :: rest, _, _ => by
    have hne' : w :: rest ≠ [] := List.cons_ne_nil w rest
    simp [List.dropLast_cons_of_ne_nil hne']

theorem adj_dropLast_getLast_of_isSimpleWalkList {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hdrop : L.dropLast ≠ []),
      WallOfHeight.IsSimpleWalkList G L →
      G.toSimpleGraph.Adj (L.dropLast.getLast hdrop) (L.getLast hne)
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, hdrop, _ => False.elim (hdrop rfl)
  | [_, _], _, _, hw => hw.1
  | _ :: v :: w :: rest, _, _, hw => by
    have hne' : v :: w :: rest ≠ [] := List.cons_ne_nil _ _
    have hdrop' : (v :: w :: rest).dropLast ≠ [] := by simp
    simpa [List.dropLast_cons_of_ne_nil hne'] using
      adj_dropLast_getLast_of_isSimpleWalkList hne' hdrop' hw.2

theorem alg74Path_dropLast_ne_nil {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    (alg74Path x e).dropLast ≠ [] := by
  rcases x.hpaths_valid (toChoose2Fin e) with ⟨_, hlen, _⟩
  have h1 : (alg74Path x e).dropLast.length = (alg74Path x e).length - 1 :=
    List.length_dropLast
  intro heq
  rw [heq] at h1
  dsimp [alg74Path] at h1
  omega

/-- Full branch set `V(φ(gamma)) ⊆ V(G)` for color `gamma : Fin p`:
unions `wallVertBranchSet hp x gamma` with `(alg74Path x e).dropLast` for every edge `e` of $K_p$
whose first endpoint has color `gamma`. -/
def modelBranchSet {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) : Finset (Fin x.n) :=
  wallVertBranchSet hp x gamma ∪
  (Finset.univ.filter (fun e : Fin (completeGraphEdges p).length =>
    ((completeGraphEdges p)[e.1]'e.2).1 = gamma)).biUnion
    (fun e => (alg74Path x e).dropLast.toFinset)

theorem mem_modelBranchSet_iff {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    {gamma : Fin p} {v : Fin x.n} :
    v ∈ modelBranchSet hp x gamma ↔
      v ∈ wallVertBranchSet hp x gamma ∨
      ∃ e : Fin (completeGraphEdges p).length,
        ((completeGraphEdges p)[e.1]'e.2).1 = gamma ∧ v ∈ (alg74Path x e).dropLast := by
  unfold modelBranchSet
  rw [Finset.mem_union, Finset.mem_biUnion]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]

attribute [irreducible] modelBranchSet

theorem isWalkConnected_modelBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) (gamma : Fin p) :
    IsWalkConnected x.G.toSimpleGraph (modelBranchSet hp x gamma) := by
  have hconn_W := isWalkConnected_wallVertBranchSet hp x gamma
  rcases hconn_W with ⟨⟨v₀, hv₀⟩, hwalkW⟩
  have hsub_W : wallVertBranchSet hp x gamma ⊆ modelBranchSet hp x gamma := by
    intro z hz
    rw [mem_modelBranchSet_iff]
    exact Or.inl hz
  have hv₀_M : v₀ ∈ modelBranchSet hp x gamma := hsub_W hv₀
  have hto_v₀ : ∀ v ∈ modelBranchSet hp x gamma,
      WalkIn x.G.toSimpleGraph (modelBranchSet hp x gamma) v₀ v := by
    intro v hv
    rw [mem_modelBranchSet_iff] at hv
    rcases hv with hv_W | ⟨e, he_col, hv_drop⟩
    · exact (hwalkW v₀ hv₀ v hv_W).mono hsub_W
    · have hne := alg74Path_ne_nil x e
      have hdrop := alg74Path_dropLast_ne_nil x e
      have hstart_W : (alg74Path x e).head hne ∈ wallVertBranchSet hp x gamma := by
        have hmem := alg74TermVert_mem_wallVertBranchSet hp x (edgeStartTerm e)
        have h1 := alg74TermVert_edgeStartTerm x e
        have h2 : alg74RawColor p (edgeStartTerm e) = gamma :=
          (alg74RawColor_edgeStartTerm e).trans he_col
        rwa [h1, h2] at hmem
      have hw_start : WalkIn x.G.toSimpleGraph (modelBranchSet hp x gamma)
          v₀ ((alg74Path x e).head hne) :=
        (hwalkW v₀ hv₀ _ hstart_W).mono hsub_W
      have hwalk_P : WallOfHeight.IsSimpleWalkList x.G (alg74Path x e) :=
        (x.hpaths_valid (toChoose2Fin e)).choose_spec.2.2.1
      have hwalk_drop : WallOfHeight.IsSimpleWalkList x.G (alg74Path x e).dropLast := by
        rw [← List.dropLast_append_getLast hne] at hwalk_P
        exact isSimpleWalkList_of_append_left hwalk_P
      have hsub_drop : ∀ z ∈ (alg74Path x e).dropLast, z ∈ modelBranchSet hp x gamma := by
        intro z hz
        rw [mem_modelBranchSet_iff]
        exact Or.inr ⟨e, he_col, hz⟩
      have hw_path := walkIn_of_isSimpleWalkList hdrop hwalk_drop hsub_drop v hv_drop
      rw [head_dropLast_eq_head hne hdrop] at hw_path
      exact hw_start.trans hw_path
  exact ⟨⟨v₀, hv₀_M⟩, fun u hu v hv => (hto_v₀ u hu).symm.trans (hto_v₀ v hv)⟩

theorem disjoint_modelBranchSet {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) {gamma₁ gamma₂ : Fin p} (hne : gamma₁ ≠ gamma₂) :
    Disjoint (modelBranchSet hp x gamma₁) (modelBranchSet hp x gamma₂) := by
  have hdisj_W := disjoint_wallVertBranchSet hp x hne
  have hmem_drop : ∀ (e : Fin (completeGraphEdges p).length) {gamma : Fin p},
      ((completeGraphEdges p)[e.1]'e.2).1 = gamma →
      ∀ v : Fin x.n, v ∈ (alg74Path x e).dropLast →
      v ∈ wallVertBranchSet hp x gamma ∨ v ∉ x.W.vertexFinset := by
    intro e gamma he_col v hv
    have hv_valid : x.W.IsHPath (alg74Path x e) := x.hpaths_valid (toChoose2Fin e)
    rcases hv_valid with ⟨hne_e, hlen_e, _, _, _, _, hint_e, _⟩
    rw [mem_dropLast_iff_head_or_mem_drop_one_dropLast hne_e hlen_e] at hv
    rcases hv with rfl | hv_int
    · left
      have hmem := alg74TermVert_mem_wallVertBranchSet hp x (edgeStartTerm e)
      have h1 := alg74TermVert_edgeStartTerm x e
      have h2 : alg74RawColor p (edgeStartTerm e) = gamma :=
        (alg74RawColor_edgeStartTerm e).trans he_col
      rwa [h1, h2] at hmem
    · right
      exact hint_e v hv_int
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  rw [mem_modelBranchSet_iff] at hv₁
  rw [mem_modelBranchSet_iff] at hv₂
  rcases hv₁ with hv₁_W | ⟨e₁, he₁_col, hv₁_drop⟩ <;>
  rcases hv₂ with hv₂_W | ⟨e₂, he₂_col, hv₂_drop⟩
  · exact Finset.disjoint_left.mp hdisj_W hv₁_W hv₂_W
  · rcases hmem_drop e₂ he₂_col v hv₂_drop with hv₂_W | hv₂_notW
    · exact Finset.disjoint_left.mp hdisj_W hv₁_W hv₂_W
    · exact hv₂_notW (wallVertBranchSet_subset_vertexFinset hp x gamma₁ hv₁_W)
  · rcases hmem_drop e₁ he₁_col v hv₁_drop with hv₁_W | hv₁_notW
    · exact Finset.disjoint_left.mp hdisj_W hv₁_W hv₂_W
    · exact hv₁_notW (wallVertBranchSet_subset_vertexFinset hp x gamma₂ hv₂_W)
  · have he_ne : toChoose2Fin e₁ ≠ toChoose2Fin e₂ := by
      intro heq
      have hval : (toChoose2Fin e₁).1 = (toChoose2Fin e₂).1 := congrArg Fin.val heq
      have he_eq : e₁ = e₂ := Fin.ext hval
      subst he_eq
      exact hne (he₁_col.symm.trans he₂_col)
    exact x.hpaths_disj (toChoose2Fin e₁) (toChoose2Fin e₂) he_ne
      (List.mem_of_mem_dropLast hv₁_drop) (List.mem_of_mem_dropLast hv₂_drop)

/-- Penultimate vertex of `alg74Path x e`. -/
def alg74PenultVert {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) : Fin x.n :=
  (alg74Path x e).dropLast.getLast (alg74Path_dropLast_ne_nil x e)

/-- Last vertex of `alg74Path x e`. -/
def alg74LastVert {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) : Fin x.n :=
  (alg74Path x e).getLast (alg74Path_ne_nil x e)

/-- Directed endpoint pair `(tail, head)` in `x.G.toComputeDigraph` for edge `e` of $K_p$. -/
def alg74EdgePair {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) : Fin x.n × Fin x.n :=
  let u := alg74PenultVert x e
  let v := alg74LastVert x e
  if 0 < x.G.edgeMult u v then (u, v) else (v, u)

theorem alg74EdgePair_fst_of_pos {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)) :
    (alg74EdgePair x e).1 = alg74PenultVert x e := by
  simp only [alg74EdgePair, hpos, ↓reduceIte]

theorem alg74EdgePair_snd_of_pos {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)) :
    (alg74EdgePair x e).2 = alg74LastVert x e := by
  simp only [alg74EdgePair, hpos, ↓reduceIte]

theorem alg74EdgePair_fst_of_not_pos {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (hnot : ¬ 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)) :
    (alg74EdgePair x e).1 = alg74LastVert x e := by
  simp only [alg74EdgePair, hnot, ↓reduceIte]

theorem alg74EdgePair_snd_of_not_pos {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length)
    (hnot : ¬ 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)) :
    (alg74EdgePair x e).2 = alg74PenultVert x e := by
  simp only [alg74EdgePair, hnot, ↓reduceIte]

theorem alg74PenultVert_mem_modelBranchSet {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    alg74PenultVert x e ∈ modelBranchSet hp x ((completeGraphEdges p)[e.1]'e.2).1 := by
  rw [mem_modelBranchSet_iff]
  exact Or.inr ⟨e, rfl, List.getLast_mem _⟩

theorem alg74LastVert_mem_modelBranchSet {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    alg74LastVert x e ∈ modelBranchSet hp x ((completeGraphEdges p)[e.1]'e.2).2 := by
  rw [mem_modelBranchSet_iff]
  left
  have hmem := alg74TermVert_mem_wallVertBranchSet hp x (edgeEndTerm e)
  have h1 : alg74TermVert x (edgeEndTerm e) = alg74LastVert x e :=
    alg74TermVert_edgeEndTerm x e
  have h2 := alg74RawColor_edgeEndTerm e
  rwa [h1, h2] at hmem

theorem alg74EdgePair_fst_mem_path {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    (alg74EdgePair x e).1 ∈ alg74Path x e := by
  by_cases hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)
  · rw [alg74EdgePair_fst_of_pos x e hpos]
    exact List.mem_of_mem_dropLast (List.getLast_mem (alg74Path_dropLast_ne_nil x e))
  · rw [alg74EdgePair_fst_of_not_pos x e hpos]
    exact List.getLast_mem (alg74Path_ne_nil x e)

theorem exists_alg74Edge {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    ∃ idx : Fin x.G.toComputeDigraph.numEdges,
      x.G.toComputeDigraph.tail idx = (alg74EdgePair x e).1 ∧
      x.G.toComputeDigraph.head idx = (alg74EdgePair x e).2 := by
  rw [x.G.exists_toComputeDigraph_edge_iff]
  have hwalk : WallOfHeight.IsSimpleWalkList x.G (alg74Path x e) :=
    (x.hpaths_valid (toChoose2Fin e)).choose_spec.2.2.1
  have hadj := adj_dropLast_getLast_of_isSimpleWalkList
    (alg74Path_ne_nil x e) (alg74Path_dropLast_ne_nil x e) hwalk
  rw [MultiDigraph.toSimpleGraph_adj] at hadj
  by_cases hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)
  · rw [alg74EdgePair_fst_of_pos x e hpos, alg74EdgePair_snd_of_pos x e hpos]
    exact hpos
  · rw [alg74EdgePair_fst_of_not_pos x e hpos, alg74EdgePair_snd_of_not_pos x e hpos]
    rcases hadj.2 with h1 | h2
    · exact False.elim (hpos h1)
    · exact h2

/-- Selected edge in `x.G.toComputeDigraph` for edge `e` of $K_p$. -/
noncomputable def alg74EdgeMap {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) : Fin x.G.toComputeDigraph.numEdges :=
  (exists_alg74Edge x e).choose

theorem alg74EdgeMap_tail {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    x.G.toComputeDigraph.tail (alg74EdgeMap x e) = (alg74EdgePair x e).1 :=
  (exists_alg74Edge x e).choose_spec.1

theorem alg74EdgeMap_head {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    x.G.toComputeDigraph.head (alg74EdgeMap x e) = (alg74EdgePair x e).2 :=
  (exists_alg74Edge x e).choose_spec.2

theorem isNonNullConnected_of_isWalkConnected {n : ℕ}
    {G : MultiDigraph n} {V_sub : Finset (Fin n)}
    (hconn : IsWalkConnected G.toSimpleGraph V_sub) :
    (inducedDigraphSubgraph G V_sub).IsNonNullConnected := by
  refine ⟨hconn.1, fun u hu v hv => ?_⟩
  rcases hconn.2 u hu v hv with ⟨w, hw⟩
  have hwalk : ∀ {a b : Fin n} (w : G.toSimpleGraph.Walk a b),
      (∀ z ∈ w.support, z ∈ V_sub) →
      (inducedDigraphSubgraph G V_sub).underlyingSimpleGraph.Reachable a b := by
    intro a b w
    induction w with
    | nil => intro _; exact Reachable.refl _
    | @cons x y z hadj rest ih =>
      intro hsup
      have hx : x ∈ V_sub := hsup x (by simp)
      have hy : y ∈ V_sub :=
        hsup y (List.mem_cons_of_mem x (SimpleGraph.Walk.start_mem_support rest))
      have hadj_ind := adj_underlyingSimpleGraph_inducedDigraphSubgraph G V_sub hx hy hadj
      exact hadj_ind.reachable.trans (ih (fun q hq => hsup q (List.mem_cons_of_mem x hq)))
  exact hwalk w hw

theorem alg74EdgeMap_injective {p r : ℕ} (x : Alg74Input p r) :
    Function.Injective (alg74EdgeMap x) := by
  intro e₁ e₂ heq
  by_contra hne
  have hne_c : toChoose2Fin e₁ ≠ toChoose2Fin e₂ := by
    intro hc
    have hval : (toChoose2Fin e₁).1 = (toChoose2Fin e₂).1 := congrArg Fin.val hc
    exact hne (Fin.ext hval)
  have htl : (alg74EdgePair x e₁).1 = (alg74EdgePair x e₂).1 := by
    have h1 := alg74EdgeMap_tail x e₁
    have h2 := alg74EdgeMap_tail x e₂
    rw [heq] at h1
    exact h1.symm.trans h2
  have hm1 := alg74EdgePair_fst_mem_path x e₁
  have hm2 := alg74EdgePair_fst_mem_path x e₂
  rw [← htl] at hm2
  exact x.hpaths_disj (toChoose2Fin e₁) (toChoose2Fin e₂) hne_c hm1 hm2

theorem mem_edges_inducedDigraphSubgraph_iff {n : ℕ} (G : MultiDigraph n)
    (V_sub : Finset (Fin n)) (idx : Fin G.toComputeDigraph.numEdges) :
    idx ∈ (inducedDigraphSubgraph G V_sub).edges ↔
      G.toComputeDigraph.head idx ∈ V_sub ∧ G.toComputeDigraph.tail idx ∈ V_sub := by
  change idx ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ idx, h⟩⟩

theorem alg74EdgeMap_notMem_vert {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (gamma : Fin p) (e : Fin (completeGraphEdges p).length) :
    alg74EdgeMap x e ∉ (inducedDigraphSubgraph x.G (modelBranchSet hp x gamma)).edges := by
  intro he_mem
  rw [mem_edges_inducedDigraphSubgraph_iff, alg74EdgeMap_head, alg74EdgeMap_tail] at he_mem
  have h1 : alg74PenultVert x e ∈ modelBranchSet hp x gamma ∧
      alg74LastVert x e ∈ modelBranchSet hp x gamma := by
    by_cases hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)
    · rw [alg74EdgePair_fst_of_pos x e hpos, alg74EdgePair_snd_of_pos x e hpos] at he_mem
      exact ⟨he_mem.2, he_mem.1⟩
    · rw [alg74EdgePair_fst_of_not_pos x e hpos, alg74EdgePair_snd_of_not_pos x e hpos] at he_mem
      exact ⟨he_mem.1, he_mem.2⟩
  have hp_mem := alg74PenultVert_mem_modelBranchSet hp x e
  have hl_mem := alg74LastVert_mem_modelBranchSet hp x e
  have hcol1 : gamma = ((completeGraphEdges p)[e.1]'e.2).1 := by
    by_contra hne1
    exact Finset.disjoint_left.mp (disjoint_modelBranchSet hp x hne1) h1.1 hp_mem
  have hcol2 : gamma = ((completeGraphEdges p)[e.1]'e.2).2 := by
    by_contra hne2
    exact Finset.disjoint_left.mp (disjoint_modelBranchSet hp x hne2) h1.2 hl_mem
  exact completeGraphEdges_ne e (hcol1.symm.trans hcol2)

theorem alg74EdgeMap_ends_mem {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (e : Fin (completeGraphEdges p).length) :
    (x.G.toComputeDigraph.tail (alg74EdgeMap x e) ∈
        (modelBranchSet hp x ((completeGraphEdges p)[e.1]'e.2).1) ∧
      x.G.toComputeDigraph.head (alg74EdgeMap x e) ∈
        (modelBranchSet hp x ((completeGraphEdges p)[e.1]'e.2).2)) ∨
    (x.G.toComputeDigraph.head (alg74EdgeMap x e) ∈
        (modelBranchSet hp x ((completeGraphEdges p)[e.1]'e.2).1) ∧
      x.G.toComputeDigraph.tail (alg74EdgeMap x e) ∈
        (modelBranchSet hp x ((completeGraphEdges p)[e.1]'e.2).2)) := by
  rw [alg74EdgeMap_tail, alg74EdgeMap_head]
  have hp_mem := alg74PenultVert_mem_modelBranchSet hp x e
  have hl_mem := alg74LastVert_mem_modelBranchSet hp x e
  by_cases hpos : 0 < x.G.edgeMult (alg74PenultVert x e) (alg74LastVert x e)
  · rw [alg74EdgePair_fst_of_pos x e hpos, alg74EdgePair_snd_of_pos x e hpos]
    exact Or.inl ⟨hp_mem, hl_mem⟩
  · rw [alg74EdgePair_fst_of_not_pos x e hpos, alg74EdgePair_snd_of_not_pos x e hpos]
    exact Or.inr ⟨hp_mem, hl_mem⟩

/-- Complete model of $K_p$ (`completeComputeDigraph p`) in `x.G.toComputeDigraph` constructed from
`x : Alg74Input p (alg74LiftRadius p)`. -/
noncomputable def alg74UnderlyingModel {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) :
    UnderlyingGraphModel (completeComputeDigraph p) x.G.toComputeDigraph where
  vertMap gamma := inducedDigraphSubgraph x.G (modelBranchSet hp x gamma)
  edgeMap e := alg74EdgeMap x e
  connected gamma :=
    isNonNullConnected_of_isWalkConnected (isWalkConnected_modelBranchSet hp x gamma)
  vert_disjoint _ _ hne := disjoint_modelBranchSet hp x hne
  edge_injective := alg74EdgeMap_injective x
  edge_notMem_vert gamma e := alg74EdgeMap_notMem_vert hp x gamma e
  ends_mem_vertMap e := alg74EdgeMap_ends_mem hp x e

theorem alg74EdgeMap_pair_list {p r : ℕ} (x : Alg74Input p r)
    (e : Fin (completeGraphEdges p).length) :
    [(x.G.toComputeDigraph.tail (alg74EdgeMap x e)).1,
      (x.G.toComputeDigraph.head (alg74EdgeMap x e)).1] =
    [(alg74EdgePair x e).1.1, (alg74EdgePair x e).2.1] := by
  rw [alg74EdgeMap_tail, alg74EdgeMap_head]

theorem encUnderlyingGraphModel_alg74 {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) :
    encUnderlyingGraphModel (alg74UnderlyingModel hp x) =
      [p, (completeGraphEdges p).length] ++
      (List.finRange (completeGraphEdges p).length).flatMap (fun e =>
        [(alg74EdgePair x e).1.1, (alg74EdgePair x e).2.1]) ++
      (List.finRange p).flatMap (fun gamma =>
        bitSetList (modelBranchSet hp x gamma)) := by
  unfold encUnderlyingGraphModel alg74UnderlyingModel
  dsimp only [completeComputeDigraph, verts_inducedDigraphSubgraph]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro e _
  exact alg74EdgeMap_pair_list x e

/-! ### Section 5: Closed-Form Arithmetic and Fixed-Size Routing Equivalences for Word RAM -/

/-- Closed-form arithmetic for `coordOf h u`. -/
theorem coordOf_eq (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    coordOf h u = ((u.1 + 1) % (2 * h + 2), (u.1 + 1) / (2 * h + 2)) :=
  getElem_elemWallCoords h u.1 u.2

/-- Arithmetic characterization of `q ∈ liftGrid R` when `R ⊆ {1, ..., h} × ℕ`. -/
theorem mem_liftGrid_iff_div_two {h : ℕ} {R : Finset (ℕ × ℕ)}
    (hR : ∀ p ∈ R, 1 ≤ p.1 ∧ p.1 ≤ h) (q : ℕ × ℕ) :
    q ∈ liftGrid R ↔ 1 ≤ q.1 ∧ q.1 ≤ 2 * h ∧ ((q.1 + 1) / 2, q.2) ∈ R := by
  constructor
  · intro hq
    rw [mem_liftGrid] at hq
    rcases hq with ⟨p, hp, hqp⟩
    have hb := hR p hp
    have hdiv := div_two_eq_of_mem_cellPair hb.1 hqp
    have hcell : q.1 = 2 * p.1 - 1 ∨ q.1 = 2 * p.1 := by
      unfold cellPair at hqp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqp
      rcases hqp with hqp | hqp
      · left; exact congrArg Prod.fst hqp
      · right; exact congrArg Prod.fst hqp
    refine ⟨by omega, by omega, ?_⟩
    rw [hdiv.1, hdiv.2]
    exact hp
  · rintro ⟨hq1, hq2, hmem⟩
    rcases q with ⟨qx, qy⟩
    rw [mem_liftGrid]
    refine ⟨((qx + 1) / 2, qy), hmem, ?_⟩
    unfold cellPair
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
    omega

/-- `safeColAux p c i` depends only on `c 0, ..., c i`. -/
theorem safeColAux_congr (p : ℕ) {c₁ c₂ : ℕ → ℕ} :
    ∀ (i : ℕ), (∀ j ≤ i, c₁ j = c₂ j) → safeColAux p c₁ i = safeColAux p c₂ i
  | 0, h => by
    have h0 := h 0 (le_refl 0)
    simp [safeColAux, h0]
  | i + 1, h => by
    have ih := safeColAux_congr p i (fun j hj => h j (Nat.le_succ_of_le hj))
    have hi1 := h (i + 1) (le_refl (i + 1))
    simp [safeColAux, ih, hi1]

theorem safeCol_congr (p : ℕ) {c₁ c₂ : ℕ → ℕ} {i : ℕ} (h : ∀ j ≤ i, c₁ j = c₂ j) :
    safeCol p c₁ i = safeCol p c₂ i :=
  congrArg Prod.fst (safeColAux_congr p i h)

theorem mem_endpointWindow_iff (p c cStar x : ℕ) :
    x ∈ endpointWindow p c cStar ↔
      (c ≤ x + 2 * p ∧ x ≤ c) ∨ (cStar ≤ x ∧ x ≤ cStar + 2 * p) := by
  unfold endpointWindow
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

theorem mem_forbidAfter_iff (p : ℕ) (c : ℕ → ℕ) :
    ∀ (k x : ℕ), x ∈ forbidAfter p c k ↔
      ∃ j ≤ k, x ∈ endpointWindow p (c j) (safeCol p c j)
  | 0, x => by
    rw [forbidAfter_zero]
    simp
  | k + 1, x => by
    rw [forbidAfter_succ, Finset.mem_union, mem_forbidAfter_iff p c k x]
    constructor
    · rintro (⟨j, hj, hmem⟩ | hmem)
      · exact ⟨j, Nat.le_succ_of_le hj, hmem⟩
      · exact ⟨k + 1, le_refl _, hmem⟩
    · rintro ⟨j, hj, hmem⟩
      rcases Nat.of_le_succ hj with hle | rfl
      · exact Or.inl ⟨j, hle, hmem⟩
      · exact Or.inr hmem

/-- Single step of incrementing candidate column `x` whenever `x ∈ F`. -/
def bumpForb (F : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ F then x + 1 else x

theorem iterate_bumpForb_eq (F : Finset ℕ) {x₀ s : ℕ}
    (hle : x₀ ≤ s) (hs : s ∉ F) (hmin : ∀ x, x₀ ≤ x → x < s → x ∈ F) :
    ∀ t : ℕ, (bumpForb F)^[t] x₀ = min (x₀ + t) s
  | 0 => by simp [hle]
  | t + 1 => by
    rw [Function.iterate_succ_apply', iterate_bumpForb_eq F hle hs hmin t]
    unfold bumpForb
    by_cases hlt : x₀ + t < s
    · have hmin_eq : min (x₀ + t) s = x₀ + t := Nat.min_eq_left (le_of_lt hlt)
      have hmem : x₀ + t ∈ F := hmin (x₀ + t) (by omega) hlt
      simp only [hmin_eq, hmem, ↓reduceIte]
      omega
    · have hmin_eq : min (x₀ + t) s = s := Nat.min_eq_right (by omega)
      simp only [hmin_eq, hs, ↓reduceIte]
      omega

/-- Iterating `bumpForb (forbidAfter p c k)` `(k + 1) * (4 * p + 2)` times from `c (k + 1) + 1`
computes `safeCol p c (k + 1)`. -/
theorem iterate_bumpForb_eq_safeCol (p : ℕ) (c : ℕ → ℕ) (k : ℕ) :
    (bumpForb (forbidAfter p c k))^[(k + 1) * (4 * p + 2)] (c (k + 1) + 1) =
      safeCol p c (k + 1) := by
  have hspec := safeCol_spec p c (k + 1)
  rw [iterate_bumpForb_eq (forbidAfter p c k) hspec.1.1 (hspec.2.1 k rfl)
    (fun x hx1 hx2 => hspec.2.2 k x rfl hx1 hx2)]
  have hhi := hspec.1.2
  omega

/-- Sort key for terminal `q : ℕ × ℕ`: `q.2 + 1` if `IsInInnerBox h B q`, and `0` otherwise. -/
def termSortKey (h B : ℕ) (q : ℕ × ℕ) : ℕ :=
  if IsInInnerBox h B q then q.2 + 1 else 0

theorem termSortKey_pos_iff (h B : ℕ) (q : ℕ × ℕ) :
    0 < termSortKey h B q ↔ IsInInnerBox h B q := by
  unfold termSortKey
  split_ifs with hbox <;> simp [hbox]

theorem termSortKey_eq_zero_iff (h B : ℕ) (q : ℕ × ℕ) :
    termSortKey h B q = 0 ↔ ¬ IsInInnerBox h B q := by
  unfold termSortKey
  split_ifs with hbox <;> simp [hbox]

/-- Full list of all `m` terminals `0, ..., m - 1` sorted in decreasing order of `termSortKey`. -/
def fullSortedList (h B m : ℕ) (term : Fin m → ℕ × ℕ) : List (Fin m) :=
  (List.finRange m).insertionSort
    (fun a b => termSortKey h B (term b) ≤ termSortKey h B (term a))

@[simp]
theorem length_fullSortedList (h B m : ℕ) (term : Fin m → ℕ × ℕ) :
    (fullSortedList h B m term).length = m := by
  unfold fullSortedList
  rw [List.length_insertionSort, List.length_finRange]

private theorem orderedInsert_append_of_pos {α : Type*} (key : α → ℕ)
    (r : α → α → Prop) [DecidableRel r]
    (hr : ∀ a b, 0 < key a → 0 < key b → (key b ≤ key a ↔ r a b))
    {a : α} (ha : 0 < key a) :
    ∀ (xs ys : List α),
      (∀ x ∈ xs, 0 < key x) →
      (∀ y ∈ ys, key y = 0) →
      List.orderedInsert (fun u v => key v ≤ key u) a (xs ++ ys) =
        List.orderedInsert r a xs ++ ys
  | [], [], _, _ => by
    simp only [List.orderedInsert_nil, List.append_nil]
  | [], y :: ys, _, hys => by
    have hy0 : key y = 0 := hys y List.mem_cons_self
    have hle : key y ≤ key a := by omega
    simp only [List.nil_append, List.orderedInsert_nil, List.orderedInsert_cons,
      hle, ↓reduceIte, List.cons_append]
  | x :: xs, ys, hxs, hys => by
    have hx : 0 < key x := hxs x List.mem_cons_self
    have hiff : (key x ≤ key a) ↔ r a x := hr a x ha hx
    simp only [List.cons_append, List.orderedInsert_cons, hiff]
    split_ifs
    · rfl
    · rw [List.cons_append,
        orderedInsert_append_of_pos key r hr ha xs ys
          (fun z hz => hxs z (List.mem_cons_of_mem x hz)) hys]

private theorem orderedInsert_append_of_zero {α : Type*} (key : α → ℕ)
    {a : α} (ha : key a = 0) :
    ∀ (xs ys : List α),
      (∀ x ∈ xs, 0 < key x) →
      List.orderedInsert (fun u v => key v ≤ key u) a (xs ++ ys) =
        xs ++ List.orderedInsert (fun u v => key v ≤ key u) a ys
  | [], ys, _ => rfl
  | x :: xs, ys, hxs => by
    have hx : 0 < key x := hxs x List.mem_cons_self
    have hnot : ¬ key x ≤ key a := by omega
    simp only [List.cons_append, List.orderedInsert_cons, hnot, ↓reduceIte,
      orderedInsert_append_of_zero key ha xs ys
        (fun z hz => hxs z (List.mem_cons_of_mem x hz))]

private theorem insertionSort_key_eq_append {α : Type*} (P : α → Bool) (key : α → ℕ)
    (r : α → α → Prop) [DecidableRel r]
    (hpos : ∀ a, P a = true ↔ 0 < key a)
    (hr : ∀ a b, 0 < key a → 0 < key b → (key b ≤ key a ↔ r a b)) :
    ∀ (l : List α),
      l.insertionSort (fun u v => key v ≤ key u) =
        (l.filter P).insertionSort r ++
        (l.filter (fun a => !P a)).insertionSort (fun u v => key v ≤ key u)
  | [] => by simp only [List.filter_nil, List.insertionSort_nil, List.nil_append]
  | a :: l => by
    have ih := insertionSort_key_eq_append P key r hpos hr l
    have hxs : ∀ x ∈ (l.filter P).insertionSort r, 0 < key x := by
      intro x hx
      rw [List.mem_insertionSort, List.mem_filter] at hx
      exact (hpos x).mp hx.2
    have hys : ∀ y ∈ (l.filter (fun z => !P z)).insertionSort (fun u v => key v ≤ key u),
        key y = 0 := by
      intro y hy
      rw [List.mem_insertionSort, List.mem_filter] at hy
      have hnot : ¬ 0 < key y := by
        intro hp
        have hPy := (hpos y).mpr hp
        simp [hPy] at hy
      omega
    cases hPa : P a
    · have ha0 : key a = 0 := by
        by_contra hne
        have hPy := (hpos a).mpr (by omega)
        rw [hPa] at hPy
        nomatch hPy
      simp only [List.insertionSort_cons, ih, List.filter_cons, hPa, Bool.false_eq_true,
        ↓reduceIte, Bool.not_false]
      exact orderedInsert_append_of_zero key ha0 _ _ hxs
    · have ha_pos : 0 < key a := (hpos a).mp hPa
      simp only [List.insertionSort_cons, ih, List.filter_cons, hPa, ↓reduceIte,
        Bool.not_true, Bool.false_eq_true]
      exact orderedInsert_append_of_pos key r hr ha_pos _ _ hxs hys

/-- `fullSortedList h B m term` consists of `sortedIntList h B m term` followed by the exterior
terminals (which all have `termSortKey = 0`). -/
theorem fullSortedList_eq_sortedIntList_append (h B m : ℕ) (term : Fin m → ℕ × ℕ) :
    fullSortedList h B m term =
      sortedIntList h B m term ++
      ((List.finRange m).filter (fun a => !decide (IsInInnerBox h B (term a)))).insertionSort
        (fun u v => termSortKey h B (term v) ≤ termSortKey h B (term u)) := by
  unfold fullSortedList sortedIntList
  apply insertionSort_key_eq_append
    (fun a => decide (IsInInnerBox h B (term a)))
    (fun a => termSortKey h B (term a))
    (fun a b => (term b).2 ≤ (term a).2)
  · intro a
    rw [decide_eq_true_eq, termSortKey_pos_iff]
  · intro a b ha hb
    rw [termSortKey_pos_iff] at ha hb
    unfold termSortKey
    simp only [ha, hb, ↓reduceIte]
    omega

/-- The `i`-th element (`i : Fin m`) of `fullSortedList h B m term`. -/
def fullSortedGet (h B m : ℕ) (term : Fin m → ℕ × ℕ) (i : Fin m) : Fin m :=
  (fullSortedList h B m term)[i.1]'(by rw [length_fullSortedList]; exact i.2)

theorem getElem_fullSortedList_of_lt (h B m : ℕ) (term : Fin m → ℕ × ℕ)
    {i : ℕ} (hi : i < (sortedIntList h B m term).length) :
    (fullSortedList h B m term)[i]'(by
      rw [length_fullSortedList]
      exact Nat.lt_of_lt_of_le hi (sortedIntList_length_le h B m term)) =
    (sortedIntList h B m term)[i] := by
  simp only [fullSortedList_eq_sortedIntList_append, List.getElem_append_left hi]

theorem fullSortedGet_eq_get_sortedIntList (h B m : ℕ) (term : Fin m → ℕ × ℕ)
    (i : Fin (sortedIntList h B m term).length) :
    fullSortedGet h B m term ⟨i.1, Nat.lt_of_lt_of_le i.2 (sortedIntList_length_le h B m term)⟩ =
      (sortedIntList h B m term).get i := by
  unfold fullSortedGet
  simp only [List.get_eq_getElem, getElem_fullSortedList_of_lt h B m term i.2]

theorem lt_length_sortedIntList_iff (h B m : ℕ) (term : Fin m → ℕ × ℕ)
    (i : Fin m) :
    i.1 < (sortedIntList h B m term).length ↔
      0 < termSortKey h B (term (fullSortedGet h B m term i)) := by
  have happ := fullSortedList_eq_sortedIntList_append h B m term
  unfold fullSortedGet
  constructor
  · intro hlt
    rw [getElem_fullSortedList_of_lt h B m term hlt, termSortKey_pos_iff]
    exact (mem_sortedIntList_iff h B m term _).mp (List.getElem_mem hlt)
  · intro hpos
    by_contra hge
    have hle : (sortedIntList h B m term).length ≤ i.1 := by omega
    have hmem_right :
        (fullSortedList h B m term)[i.1]'(by rw [length_fullSortedList]; exact i.2) ∈
          ((List.finRange m).filter (fun a => !decide (IsInInnerBox h B (term a)))).insertionSort
            (fun u v => termSortKey h B (term v) ≤ termSortKey h B (term u)) := by
      have hget :
          (fullSortedList h B m term)[i.1]'(by rw [length_fullSortedList]; exact i.2) =
            (((List.finRange m).filter (fun a => !decide (IsInInnerBox h B (term a)))).insertionSort
              (fun u v => termSortKey h B (term v) ≤ termSortKey h B (term u)))[
                i.1 - (sortedIntList h B m term).length]'(by
              have hlen_tot := length_fullSortedList h B m term
              rw [happ, List.length_append] at hlen_tot
              exact Nat.sub_lt_left_of_lt_add hle (by omega)) := by
        simp only [happ, List.getElem_append_right hle]
      rw [hget]
      exact List.getElem_mem _
    rw [List.mem_insertionSort, List.mem_filter] at hmem_right
    have hout : ¬ IsInInnerBox h B (term ((fullSortedList h B m term)[i.1]'(by
        rw [length_fullSortedList]; exact i.2))) := by
      simpa using hmem_right.2
    exact hout ((termSortKey_pos_iff h B _).mp hpos)

/-- Sequence of initial columns of `fullSortedList h B m term`. -/
def fullColSeq (h B m : ℕ) (term : Fin m → ℕ × ℕ) (j : ℕ) : ℕ :=
  if hj : j < m then
    (term (fullSortedGet h B m term ⟨j, hj⟩)).1
  else 0

theorem intSafeCol_eq_safeCol_fullColSeq (p h B m : ℕ) (term : Fin m → ℕ × ℕ)
    (i : Fin (sortedIntList h B m term).length) :
    intSafeCol p (sortedIntList h B m term).length
      (fun j => term ((sortedIntList h B m term).get j)) i =
      safeCol p (fullColSeq h B m term) i.1 := by
  unfold intSafeCol
  apply safeCol_congr
  intro j hj
  have hj_lt_L : j < (sortedIntList h B m term).length := Nat.lt_of_le_of_lt hj i.2
  have hj_lt_m : j < m := Nat.lt_of_lt_of_le hj_lt_L (sortedIntList_length_le h B m term)
  unfold intColSeq fullColSeq fullSortedGet
  simp only [hj_lt_L, hj_lt_m, ↓reduceDIte, List.get_eq_getElem,
    getElem_fullSortedList_of_lt h B m term hj_lt_L]

theorem find?_foldr_ite_some {α β : Type} (xs : List α) (P : α → Prop) [DecidablePred P]
    (f : α → β) (d : β) (x : α) (h : xs.find? (fun y => decide (P y)) = some x) :
    xs.foldr (fun y acc => if P y then f y else acc) d = f x := by
  induction xs with
  | nil => simp at h
  | cons y rest ih =>
    simp only [List.find?_cons] at h
    simp only [List.foldr_cons]
    by_cases hy : P y
    · simp only [decide_eq_true hy, Option.some.injEq] at h
      subst h
      simp [hy]
    · simp only [decide_eq_false hy] at h
      simp [hy, ih h]

theorem find?_foldr_ite_none {α β : Type} (xs : List α) (P : α → Prop) [DecidablePred P]
    (f : α → β) (d : β) (h : xs.find? (fun y => decide (P y)) = none) :
    xs.foldr (fun y acc => if P y then f y else acc) d = d := by
  induction xs with
  | nil => rfl
  | cons y rest ih =>
    simp only [List.find?_cons] at h
    simp only [List.foldr_cons]
    by_cases hy : P y
    · simp [decide_eq_true hy] at h
    · simp only [decide_eq_false hy] at h
      simp [hy, ih h]

theorem chooseBoxMargin_eq_ite (p h m : ℕ) (term : Fin m → ℕ × ℕ) :
    let B₂ := m * (4 * p + 2) + 2 * p + 3
    chooseBoxMargin p h m term =
      if ∀ a ∈ List.finRange m, IsInInnerBox h B₂ (term a) then 2 else B₂ := by
  intro B₂
  unfold chooseBoxMargin
  dsimp only [B₂]
  have hiff : ((List.finRange m).all (fun a => decide (IsInInnerBox h B₂ (term a))) = true) ↔
      (∀ a ∈ List.finRange m, IsInInnerBox h B₂ (term a)) := by
    simp [List.all_eq_true]
  exact if_congr hiff rfl rfl

/-- Tuple `(hasPerim, perimC, perimY, perimColor)` computed by folding over `List.finRange m`. -/
def perimTermInfo {p : ℕ} (h B m : ℕ) (term : Fin m → ℕ × ℕ) (rawColor : Fin m → Fin p) :
    ℕ × ℕ × ℕ × ℕ :=
  (List.finRange m).foldr
    (fun a acc => if ¬ IsInInnerBox h B (term a) then
      (1, (term a).1, (term a).2, (rawColor a).1) else acc)
    (0, 0, 0, 0)

theorem perimTermInfo_eq_of_find?_some {p : ℕ} (h B m : ℕ) (term : Fin m → ℕ × ℕ)
    (rawColor : Fin m → Fin p) {a₀ : Fin m}
    (ha₀ : perimTermIdx? h B m term = some a₀) :
    perimTermInfo h B m term rawColor = (1, (term a₀).1, (term a₀).2, (rawColor a₀).1) := by
  unfold perimTermIdx? at ha₀
  have hfind : (List.finRange m).find? (fun a => decide (¬ IsInInnerBox h B (term a))) = some a₀ := by
    simpa [decide_not] using ha₀
  exact find?_foldr_ite_some _ (fun a => ¬ IsInInnerBox h B (term a)) _ _ a₀ hfind

theorem perimTermInfo_eq_of_find?_none {p : ℕ} (h B m : ℕ) (term : Fin m → ℕ × ℕ)
    (rawColor : Fin m → Fin p)
    (hnone : perimTermIdx? h B m term = none) :
    perimTermInfo h B m term rawColor = (0, 0, 0, 0) := by
  unfold perimTermIdx? at hnone
  have hfind : (List.finRange m).find? (fun a => decide (¬ IsInInnerBox h B (term a))) = none := by
    simpa [decide_not] using hnone
  exact find?_foldr_ite_none _ (fun a => ¬ IsInInnerBox h B (term a)) _ _ hfind

theorem colorPerm_val_eq_perimTermInfo {p : ℕ} (h B m : ℕ) (hp0 : 0 < p)
    (term : Fin m → ℕ × ℕ) (rawColor : Fin m → Fin p) (g : Fin p) :
    (colorPerm p h B m hp0 term rawColor g).1 =
      if g.1 = 0 then (perimTermInfo h B m term rawColor).2.2.2
      else if g.1 = (perimTermInfo h B m term rawColor).2.2.2 then 0
      else g.1 := by
  unfold colorPerm
  cases hfind : perimTermIdx? h B m term with
  | none =>
    rw [perimTermInfo_eq_of_find?_none h B m term rawColor hfind]
    dsimp
    split_ifs with h0 <;> omega
  | some a₀ =>
    rw [perimTermInfo_eq_of_find?_some h B m term rawColor hfind]
    dsimp
    by_cases hg0 : g.1 = 0
    · have hg_eq : g = ⟨0, hp0⟩ := Fin.ext hg0
      subst hg_eq
      simp
    · simp only [hg0, ↓reduceIte]
      by_cases hga : g.1 = (rawColor a₀).1
      · have hg_eq : g = rawColor a₀ := Fin.ext hga
        subst hg_eq
        simp
      · have hne1 : g ≠ rawColor a₀ := fun heq => hga (congrArg Fin.val heq)
        have hne2 : g ≠ ⟨0, hp0⟩ := fun heq => hg0 (congrArg Fin.val heq)
        simp [hga, Equiv.swap_apply_of_ne_of_ne hne1 hne2]

theorem mem_interiorBranchSet_iff_fullSortedGet {p : ℕ} (h B m : ℕ) (hp0 : 0 < p)
    (term : Fin m → ℕ × ℕ) (rawColor : Fin m → Fin p) (gamma : Fin p) (q : ℕ × ℕ) :
    let L := sortedIntList h B m term
    let perm := colorPerm p h B m hp0 term rawColor
    let g := (perm gamma).1
    q ∈ interiorBranchSet p h B L.length (fun i => term (L.get i))
        (fun i => perm (rawColor (L.get i))) (perm gamma) ↔
      (q ∈ hSeg (h - B - g) B (h - B) ∧
        ∀ i ∈ List.finRange m,
          0 < termSortKey h B (term (fullSortedGet h B m term i)) ∧
          (perm (rawColor (fullSortedGet h B m term i))).1 < g →
          ¬ IsPuncturedBy g (safeCol p (fullColSeq h B m term) i.1) q.1) ∨
      (∃ i ∈ List.finRange m,
        (0 < termSortKey h B (term (fullSortedGet h B m term i)) ∧
          (perm (rawColor (fullSortedGet h B m term i))).1 = g) ∧
        q ∈ connPath (h - B) (term (fullSortedGet h B m term i)).1
          (safeCol p (fullColSeq h B m term) i.1)
          (term (fullSortedGet h B m term i)).2 g) ∨
      (∃ i ∈ List.finRange m,
        (0 < termSortKey h B (term (fullSortedGet h B m term i)) ∧
          (perm (rawColor (fullSortedGet h B m term i))).1 < g) ∧
        q ∈ detourPath (h - B) (term (fullSortedGet h B m term i)).1
          (safeCol p (fullColSeq h B m term) i.1)
          (term (fullSortedGet h B m term i)).2 g) := by
  intro L perm g
  have hlen_le : L.length ≤ m := sortedIntList_length_le h B m term
  unfold interiorBranchSet puncturedTrunkRow
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    ← or_assoc]
  refine or_congr (or_congr ?_ ?_) ?_
  · refine and_congr_right fun _ =>
      ⟨fun hall i _ ⟨hkey, hlt_col⟩ => ?_, fun hall j hlt_col => ?_⟩
    · have hi_lt : i.1 < L.length := (lt_length_sortedIntList_iff h B m term i).mpr hkey
      let j : Fin L.length := ⟨i.1, hi_lt⟩
      have hget : fullSortedGet h B m term i = L.get j :=
        fullSortedGet_eq_get_sortedIntList h B m term j
      have hsafe : intSafeCol p L.length (fun r => term (L.get r)) j =
          safeCol p (fullColSeq h B m term) i.1 :=
        intSafeCol_eq_safeCol_fullColSeq p h B m term j
      rw [← hsafe]
      apply hall j
      rwa [← hget]
    · let i : Fin m := ⟨j.1, Nat.lt_of_lt_of_le j.2 hlen_le⟩
      have hget : fullSortedGet h B m term i = L.get j :=
        fullSortedGet_eq_get_sortedIntList h B m term j
      have hkey : 0 < termSortKey h B (term (fullSortedGet h B m term i)) :=
        (lt_length_sortedIntList_iff h B m term i).mp j.2
      have hsafe : intSafeCol p L.length (fun r => term (L.get r)) j =
          safeCol p (fullColSeq h B m term) i.1 :=
        intSafeCol_eq_safeCol_fullColSeq p h B m term j
      rw [hsafe]
      apply hall i (List.mem_finRange i) ⟨hkey, ?_⟩
      rwa [hget]
  · constructor
    · rintro ⟨j, heq_col, hq_conn⟩
      let i : Fin m := ⟨j.1, Nat.lt_of_lt_of_le j.2 hlen_le⟩
      have hget : fullSortedGet h B m term i = L.get j :=
        fullSortedGet_eq_get_sortedIntList h B m term j
      have hkey : 0 < termSortKey h B (term (fullSortedGet h B m term i)) :=
        (lt_length_sortedIntList_iff h B m term i).mp j.2
      have hsafe : intSafeCol p L.length (fun r => term (L.get r)) j =
          safeCol p (fullColSeq h B m term) i.1 :=
        intSafeCol_eq_safeCol_fullColSeq p h B m term j
      refine ⟨i, List.mem_finRange i, ⟨hkey, by rw [hget, heq_col]⟩, ?_⟩
      rwa [hget, ← hsafe]
    · rintro ⟨i, _, ⟨hkey, heq_col⟩, hq_conn⟩
      have hi_lt : i.1 < L.length := (lt_length_sortedIntList_iff h B m term i).mpr hkey
      let j : Fin L.length := ⟨i.1, hi_lt⟩
      have hget : fullSortedGet h B m term i = L.get j :=
        fullSortedGet_eq_get_sortedIntList h B m term j
      have hsafe : intSafeCol p L.length (fun r => term (L.get r)) j =
          safeCol p (fullColSeq h B m term) i.1 :=
        intSafeCol_eq_safeCol_fullColSeq p h B m term j
      refine ⟨j, Fin.ext (by rw [← hget, heq_col]), ?_⟩
      rwa [← hget, hsafe]
  · constructor
    · rintro ⟨j, hlt_col, hq_det⟩
      let i : Fin m := ⟨j.1, Nat.lt_of_lt_of_le j.2 hlen_le⟩
      have hget : fullSortedGet h B m term i = L.get j :=
        fullSortedGet_eq_get_sortedIntList h B m term j
      have hkey : 0 < termSortKey h B (term (fullSortedGet h B m term i)) :=
        (lt_length_sortedIntList_iff h B m term i).mp j.2
      have hsafe : intSafeCol p L.length (fun r => term (L.get r)) j =
          safeCol p (fullColSeq h B m term) i.1 :=
        intSafeCol_eq_safeCol_fullColSeq p h B m term j
      refine ⟨i, List.mem_finRange i, ⟨hkey, by rwa [hget]⟩, ?_⟩
      rwa [hget, ← hsafe]
    · rintro ⟨i, _, ⟨hkey, hlt_col⟩, hq_det⟩
      have hi_lt : i.1 < L.length := (lt_length_sortedIntList_iff h B m term i).mpr hkey
      let j : Fin L.length := ⟨i.1, hi_lt⟩
      have hget : fullSortedGet h B m term i = L.get j :=
        fullSortedGet_eq_get_sortedIntList h B m term j
      have hsafe : intSafeCol p L.length (fun r => term (L.get r)) j =
          safeCol p (fullColSeq h B m term) i.1 :=
        intSafeCol_eq_safeCol_fullColSeq p h B m term j
      refine ⟨j, by rwa [← hget], ?_⟩
      rwa [← hget, hsafe]

theorem mem_routedBranchSet_iff_perimTermInfo {p : ℕ} (h B m : ℕ) (hp0 : 0 < p)
    (term : Fin m → ℕ × ℕ) (rawColor : Fin m → Fin p) (gamma : Fin p) (q : ℕ × ℕ) :
    let L := sortedIntList h B m term
    let perm := colorPerm p h B m hp0 term rawColor
    let info := perimTermInfo h B m term rawColor
    q ∈ routedBranchSet p h B m hp0 term rawColor gamma ↔
      (info.1 = 1 ∧ (perm gamma).1 = 0 ∧ q ∈ perimPath h B info.2.1 info.2.2.1) ∨
      q ∈ interiorBranchSet p h B L.length (fun i => term (L.get i))
        (fun i => perm (rawColor (L.get i))) (perm gamma) := by
  intro L perm info
  unfold routedBranchSet fullCoarseBranchSet
  dsimp only [L, perm, info]
  cases hfind : perimTermIdx? h B m term with
  | none =>
    rw [perimTermInfo_eq_of_find?_none h B m term rawColor hfind]
    simp
  | some a₀ =>
    rw [perimTermInfo_eq_of_find?_some h B m term rawColor hfind]
    dsimp
    by_cases hg0 : (colorPerm p h B m hp0 term rawColor gamma).1 = 0
    · simp only [hg0, ↓reduceIte, Finset.mem_union, true_and]
      exact or_comm
    · simp only [hg0, ↓reduceIte, false_and, and_false, false_or]

/-! ### Section 6: Boolean Expression Combinators for Word RAM -/

/-- Expression testing `e₁ ≤ e₂` (`1` if true, `0` if false). -/
def exprLe (e₁ e₂ : Expr) : Expr := .op .le e₁ e₂

/-- Expression testing `e₁ < e₂` (`1` if true, `0` if false). -/
def exprLt (e₁ e₂ : Expr) : Expr := .op .lt e₁ e₂

/-- Expression testing `e₁ = e₂` (`1` if true, `0` if false). -/
def exprEq (e₁ e₂ : Expr) : Expr := .op .eq e₁ e₂

/-- Logical negation of a `0`/`1`-valued expression. -/
def exprNot (e : Expr) : Expr := .op .eq e (.const 0)

/-- Logical conjunction of two `0`/`1`-valued expressions. -/
def exprAnd (e₁ e₂ : Expr) : Expr := .op .mul e₁ e₂

/-- Logical disjunction of two `0`/`1`-valued expressions. -/
def exprOr (e₁ e₂ : Expr) : Expr := .op .lt (.const 0) (.op .add e₁ e₂)

/-- Logical implication `e₁ → e₂` of two `0`/`1`-valued expressions. -/
def exprImp (e₁ e₂ : Expr) : Expr := exprOr (exprNot e₁) e₂

/-- Conjunction over a finite list `xs`. -/
def exprAll {α : Type*} (xs : List α) (f : α → Expr) : Expr :=
  xs.foldr (fun x acc => exprAnd (f x) acc) (.const 1)

/-- Disjunction over a finite list `xs`. -/
def exprAny {α : Type*} (xs : List α) (f : α → Expr) : Expr :=
  xs.foldr (fun x acc => exprOr (f x) acc) (.const 0)

theorem eval_exprLe {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (hw1 : 1 < 2 ^ w) (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprLe e₁ e₂).eval w s = some (if v₁ ≤ v₂ then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  unfold exprLe
  simp only [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord]
  split_ifs <;> simp

theorem eval_exprLt {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (hw1 : 1 < 2 ^ w) (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprLt e₁ e₂).eval w s = some (if v₁ < v₂ then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  unfold exprLt
  simp only [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord]
  split_ifs <;> simp

theorem eval_exprEq {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (hw1 : 1 < 2 ^ w) (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprEq e₁ e₂).eval w s = some (if v₁ = v₂ then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  unfold exprEq
  simp only [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord]
  split_ifs <;> simp

theorem eval_exprNot {w : ℕ} {s : State} {e : Expr} {P : Prop} [Decidable P]
    (hw1 : 1 < 2 ^ w) (he : e.eval w s = some (if P then 1 else 0)) :
    (exprNot e).eval w s = some (if ¬ P then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  unfold exprNot
  simp only [Expr.eval, he, BinOp.eval, BinOp.raw, checkWord, h0, ↓reduceIte]
  by_cases hP : P <;> simp [hP, hw1, h0]

theorem eval_exprAnd {w : ℕ} {s : State} {e₁ e₂ : Expr} {P₁ P₂ : Prop}
    [Decidable P₁] [Decidable P₂]
    (hw1 : 1 < 2 ^ w)
    (h₁ : e₁.eval w s = some (if P₁ then 1 else 0))
    (h₂ : e₂.eval w s = some (if P₂ then 1 else 0)) :
    (exprAnd e₁ e₂).eval w s = some (if P₁ ∧ P₂ then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  unfold exprAnd
  simp only [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord]
  by_cases hP₁ : P₁ <;> by_cases hP₂ : P₂ <;> simp [hP₁, hP₂, hw1, h0]

theorem eval_exprOr {w : ℕ} {s : State} {e₁ e₂ : Expr} {P₁ P₂ : Prop}
    [Decidable P₁] [Decidable P₂]
    (hw2 : 2 < 2 ^ w)
    (h₁ : e₁.eval w s = some (if P₁ then 1 else 0))
    (h₂ : e₂.eval w s = some (if P₂ then 1 else 0)) :
    (exprOr e₁ e₂).eval w s = some (if P₁ ∨ P₂ then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  unfold exprOr
  simp only [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, h0, ↓reduceIte]
  by_cases hP₁ : P₁ <;> by_cases hP₂ : P₂ <;> simp [hP₁, hP₂, hw2, h1, h0]

theorem eval_exprImp {w : ℕ} {s : State} {e₁ e₂ : Expr} {P₁ P₂ : Prop}
    [Decidable P₁] [Decidable P₂]
    (hw2 : 2 < 2 ^ w)
    (h₁ : e₁.eval w s = some (if P₁ then 1 else 0))
    (h₂ : e₂.eval w s = some (if P₂ then 1 else 0)) :
    (exprImp e₁ e₂).eval w s = some (if P₁ → P₂ then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  unfold exprImp
  rw [eval_exprOr hw2 (eval_exprNot hw1 h₁) h₂]
  by_cases hP₁ : P₁ <;> by_cases hP₂ : P₂ <;> simp [hP₁, hP₂]

theorem eval_exprAll {α : Type*} {w : ℕ} {s : State} (xs : List α) (f : α → Expr)
    (P : α → Prop) [∀ a, Decidable (P a)]
    (hw1 : 1 < 2 ^ w)
    (hf : ∀ a ∈ xs, (f a).eval w s = some (if P a then 1 else 0)) :
    (exprAll xs f).eval w s = some (if ∀ a ∈ xs, P a then 1 else 0) := by
  induction xs with
  | nil =>
    simp [exprAll, checkWord, hw1]
  | cons a rest ih =>
    change (exprAnd (f a) (exprAll rest f)).eval w s = _
    have ha := hf a List.mem_cons_self
    have hrest := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
    rw [eval_exprAnd hw1 ha hrest]
    simp only [List.forall_mem_cons]

theorem eval_exprAny {α : Type*} {w : ℕ} {s : State} (xs : List α) (f : α → Expr)
    (P : α → Prop) [∀ a, Decidable (P a)]
    (hw2 : 2 < 2 ^ w)
    (hf : ∀ a ∈ xs, (f a).eval w s = some (if P a then 1 else 0)) :
    (exprAny xs f).eval w s = some (if ∃ a ∈ xs, P a then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  induction xs with
  | nil =>
    simp [exprAny, checkWord, h0]
  | cons a rest ih =>
    change (exprOr (f a) (exprAny rest f)).eval w s = _
    have ha := hf a List.mem_cons_self
    have hrest := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
    rw [eval_exprOr hw2 ha hrest]
    simp only [List.exists_mem_cons_iff]

end GraphMinor.Compute
