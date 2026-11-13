module

public import GraphMinor.GM13.Section9Subwalls
public import GraphMinor.GM13.Section9Claim7
public import GraphMinor.GM13.Section9Claim91Order

/-!
# Graph Minors XIII, (9.1): Horizontal Stubs, Subwall Box Separation, and Punctured Wall Edges

This file provides geometric and graph-theoretic helpers for the proof of **(9.1)** (page 98):
1. Horizontal walks `Wall.exists_horizontal_walk` along interior rows of a wall `W`, used to extend
   a cross `(P'_a, Q'_a)` over `H'_a = H.toWall.subwallAt i_a j_a h'_a` to the four perimeter
   attachment vertices `(1, 2)`, `(1, ĥ_a - 2)`, `(2 ĥ_a, ĥ_a - 2)`, `(2 ĥ_a, 2)` of the enlarged
   subwall `Ĥ_a = H.toWall.subwallAt (i_a - 4) (j_a - 2) (h'_a + 4)`.
2. Coordinate separation `IsFigure1CoordDrawing.subwallAt_shift_sep` between subwalls at large
   `wallSubgraphDist`, and disjointness of their concentric shifted `fig1EnclosedSet`s.
3. The syntactic characterization `isInteriorBaseEdge` of the base edges of `H` whose segments meet
   `interior (wallShiftRealHomeomorph î ĵ '' fig1EnclosedSet ĥ)`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM06
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Interior Rows of an Elementary Wall -/

/-- Any lattice point `(x, y₀)` on an interior row `1 ≤ y₀ < h` with `x ≤ 2h + 1` belongs to
`elementaryWallVerts h`. -/
lemma mem_elementaryWallVerts_of_row_interior {h x y₀ : ℕ}
    (hy_lo : 1 ≤ y₀) (hy_hi : y₀ < h) (hx : x ≤ 2 * h + 1) :
    (x, y₀) ∈ elementaryWallVerts h := by
  refine ⟨hx, by omega, ?_, ?_⟩ <;>
  · intro heq
    have := congrArg Prod.snd heq
    dsimp at this
    omega

/-- Any unit horizontal step `(x, y₀)` to `(x + 1, y₀)` on an interior row `1 ≤ y₀ < h` with
`x + 1 ≤ 2h + 1` is an edge of `elementaryWall h`. -/
lemma elementaryWallAdj_horiz_of_row_interior {h x y₀ : ℕ}
    (hy_lo : 1 ≤ y₀) (hy_hi : y₀ < h) (hx : x + 1 ≤ 2 * h + 1) :
    elementaryWallAdj h (x, y₀) (x + 1, y₀) := by
  refine ⟨mem_elementaryWallVerts_of_row_interior hy_lo hy_hi (by omega),
    mem_elementaryWallVerts_of_row_interior hy_lo hy_hi hx,
    Or.inl ⟨rfl, Or.inl rfl⟩⟩

/-! ## 2. Coordinate Separation of Far-Apart Subwalls -/

/-- If two subwalls `W₁ = H.toWall.subwallAt i₁ j₁ h₁ ...` and
`W₂ = H.toWall.subwallAt i₂ j₂ h₂ ...` of a Fig. 1 drawn wall `H` satisfy
`3 * δ + 6 < wallSubgraphDist H W₁.graph W₂.graph`, then their shift boxes are separated by more
than `2δ` horizontally or more than `δ` vertically. -/
theorem IsFigure1CoordDrawing.subwallAt_shift_sep
    {H : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U)
    (hV : ∀ (v : α) (hv : v ∈ V(H.graph)), H.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    {i₁ j₁ h₁ i₂ j₂ h₂ δ : ℕ}
    (h2₁ : 2 ≤ h₁) (heven₁ : Even h₁) (hle₁ : h₁ ≤ H.height)
    (hi₁_even : Even i₁) (hj₁_even : Even j₁)
    (hi₁_le : i₁ ≤ 2 * H.height - 2 * h₁) (hj₁_le : j₁ ≤ H.height - h₁)
    (h2₂ : 2 ≤ h₂) (heven₂ : Even h₂) (hle₂ : h₂ ≤ H.height)
    (hi₂_even : Even i₂) (hj₂_even : Even j₂)
    (hi₂_le : i₂ ≤ 2 * H.height - 2 * h₂) (hj₂_le : j₂ ≤ H.height - h₂)
    (hdist : 3 * δ + 6 < wallSubgraphDist H
      (H.toWall.subwallAt i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le).graph
      (H.toWall.subwallAt i₂ j₂ h₂ h2₂ heven₂ hle₂ hi₂_even hj₂_even hi₂_le hj₂_le).graph) :
    i₁ + 2 * h₁ + 2 * δ < i₂ ∨ i₂ + 2 * h₂ + 2 * δ < i₁ ∨
      j₁ + h₁ + δ < j₂ ∨ j₂ + h₂ + δ < j₁ := by
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨hi₁₂, hi₂₁, hj₁₂, hj₂₁⟩
  let W₁ := H.toWall.subwallAt i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  let W₂ := H.toWall.subwallAt i₂ j₂ h₂ h2₂ heven₂ hle₂ hi₂_even hj₂_even hi₂_le hj₂_le
  change 3 * δ + 6 < wallSubgraphDist H W₁.graph W₂.graph at hdist
  let x₁ : ℕ := min (max 1 (i₂ + 1 - i₁)) (2 * h₁ - 1)
  let y₁ : ℕ := min (j₂ - j₁) (h₁ - 1)
  let x₂ : ℕ := min (max 1 (i₁ + x₁ - i₂)) (2 * h₂ - 1)
  let y₂ : ℕ := min (j₁ + y₁ - j₂) (h₂ - 1)
  have hp₁ : (x₁, y₁) ∈ elementaryWallVerts h₁ := by
    refine ⟨by dsimp [x₁]; omega, by dsimp [y₁]; omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.fst h; dsimp [x₁] at this; omega
  have hp₂ : (x₂, y₂) ∈ elementaryWallVerts h₂ := by
    refine ⟨by dsimp [x₂]; omega, by dsimp [y₂]; omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.fst h; dsimp [x₂] at this; omega
  let pH₁ := wallShift i₁ j₁ (x₁, y₁)
  let pH₂ := wallShift i₂ j₂ (x₂, y₂)
  have hpH₁ : pH₁ ∈ elementaryWallVerts H.height :=
    wallShift_mem_elementaryWallVerts' h2₁ hle₁ hi₁_le hj₁_le hp₁
  have hpH₂ : pH₂ ∈ elementaryWallVerts H.height :=
    wallShift_mem_elementaryWallVerts' h2₂ hle₂ hi₂_le hj₂_le hp₂
  have hv₁_W₁ : H.branchVertex pH₁ hpH₁ ∈ V(W₁.graph) := W₁.branchVertex_mem_vertexSet (x₁, y₁) hp₁
  have hv₂_W₂ : H.branchVertex pH₂ hpH₂ ∈ V(W₂.graph) := W₂.branchVertex_mem_vertexSet (x₂, y₂) hp₂
  have hv₁_H : H.branchVertex pH₁ hpH₁ ∈ V(H.graph) := H.toWall.branchVertex_mem_vertexSet pH₁ hpH₁
  have hv₂_H : H.branchVertex pH₂ hpH₂ ∈ V(H.graph) := H.toWall.branchVertex_mem_vertexSet pH₂ hpH₂
  have hle_sub : wallSubgraphDist H W₁.graph W₂.graph ≤
      H.dist (H.branchVertex pH₁ hpH₁) (H.branchVertex pH₂ hpH₂) :=
    Nat.sInf_le ⟨H.branchVertex pH₁ hpH₁, hv₁_W₁, H.branchVertex pH₂ hpH₂, hv₂_W₂, rfl⟩
  have hvp₁ : H.vertexPoint (H.branchVertex pH₁ hpH₁) = φ (fig1PlaneEquiv (latticePoint pH₁)) := by
    rw [hV _ hv₁_H, hΓ.branchVertex_point pH₁ hpH₁ hv₁_H]
  have hvp₂ : H.vertexPoint (H.branchVertex pH₂ hpH₂) = φ (fig1PlaneEquiv (latticePoint pH₂)) := by
    rw [hV _ hv₂_H, hΓ.branchVertex_point pH₂ hpH₂ hv₂_H]
  have hdist_eq : H.dist (H.branchVertex pH₁ hpH₁) (H.branchVertex pH₂ hpH₂) =
      planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
        (fig1PlaneEquiv (latticePoint pH₁)) (fig1PlaneEquiv (latticePoint pH₂)) := by
    dsimp [DrawnWall.dist, DrawnWall.planeDist]
    rw [hU, hvp₁, hvp₂, planeWallDist_image_homeomorph, hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
  have hdist_lt : 3 * δ + 6 <
      planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
        (fig1PlaneEquiv (latticePoint pH₁)) (fig1PlaneEquiv (latticePoint pH₂)) := by
    omega
  clear W₁ W₂ hv₁_W₁ hv₂_W₂ hv₁_H hv₂_H hle_sub hvp₁ hvp₂ hdist_eq hdist hp₁ hp₂ hpH₁ hpH₂ hΓ hU hV
  have hx_diff : ((pH₁.1 : ℤ) - (pH₂.1 : ℤ) ≤ 2 * (δ : ℤ) + 2) ∧
      ((pH₂.1 : ℤ) - (pH₁.1 : ℤ) ≤ 2 * (δ : ℤ) + 2) := by
    change (((x₁ + i₁ : ℕ) : ℤ) - ((x₂ + i₂ : ℕ) : ℤ) ≤ 2 * (δ : ℤ) + 2) ∧
      (((x₂ + i₂ : ℕ) : ℤ) - ((x₁ + i₁ : ℕ) : ℤ) ≤ 2 * (δ : ℤ) + 2)
    dsimp [x₂, x₁]
    omega
  have hy_diff : ((pH₁.2 : ℤ) - (pH₂.2 : ℤ) ≤ (δ : ℤ) + 1) ∧
      ((pH₂.2 : ℤ) - (pH₁.2 : ℤ) ≤ (δ : ℤ) + 1) := by
    change (((y₁ + j₁ : ℕ) : ℤ) - ((y₂ + j₂ : ℕ) : ℤ) ≤ (δ : ℤ) + 1) ∧
      (((y₂ + j₂ : ℕ) : ℤ) - ((y₁ + j₁ : ℕ) : ℤ) ≤ (δ : ℤ) + 1)
    dsimp [y₂, y₁]
    omega
  have hx₁_bounds : 1 ≤ x₁ ∧ x₁ ≤ 2 * h₁ - 1 := ⟨by dsimp [x₁]; omega, by dsimp [x₁]; omega⟩
  have hy₁_bounds : y₁ ≤ h₁ - 1 := by dsimp [y₁]; omega
  have hx₂_bounds : 1 ≤ x₂ ∧ x₂ ≤ 2 * h₂ - 1 := ⟨by dsimp [x₂]; omega, by dsimp [x₂]; omega⟩
  have hy₂_bounds : y₂ ≤ h₂ - 1 := by dsimp [y₂]; omega
  have hpH₁_fst : pH₁.1 = x₁ + i₁ := rfl
  have hpH₁_snd : pH₁.2 = y₁ + j₁ := rfl
  have hpH₂_fst : pH₂.1 = x₂ + i₂ := rfl
  have hpH₂_snd : pH₂.2 = y₂ + j₂ := rfl
  clear_value x₁ y₁ x₂ y₂ pH₁ pH₂
  by_cases hcode : cellCode (latticePoint pH₁) = cellCode (latticePoint pH₂)
  · have hle2 := planeWallDist_fig1_le_two_of_cellCode_eq H.height hcode
    omega
  · have hh1 : 1 ≤ H.height := by have := H.two_le_height; omega
    have hq₁ : cellUp (cellCode (latticePoint pH₁)) ∈ squaresAbove (cellCode (latticePoint pH₁)) :=
      ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
    have hq₂ : cellUp (cellCode (latticePoint pH₂)) ∈ squaresAbove (cellCode (latticePoint pH₂)) :=
      ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
    have hle_fig := planeWallDist_fig1_le hh1 H.even_height hcode hq₁ hq₂
    have hind₁ := cellInd_le_one (fig1WallCells H.height) (cellCode (latticePoint pH₁))
    have hind₂ := cellInd_le_one (fig1WallCells H.height) (cellCode (latticePoint pH₂))
    have hup₁ : cellUp (cellCode (latticePoint pH₁)) = (2 * (pH₁.1 : ℤ) + 1, 2 * (pH₁.2 : ℤ) + 1) := by
      rw [cellCode_latticePoint]
      dsimp [cellUp, cellUp1]
      ext <;> split_ifs <;> omega
    have hup₂ : cellUp (cellCode (latticePoint pH₂)) = (2 * (pH₂.1 : ℤ) + 1, 2 * (pH₂.2 : ℤ) + 1) := by
      rw [cellCode_latticePoint]
      dsimp [cellUp, cellUp1]
      ext <;> split_ifs <;> omega
    rw [hup₁, hup₂, wallFace_square, wallFace_square] at hle_fig
    have hbrick₁ : 0 ≤ (pH₁.2 : ℤ) ∧ (pH₁.2 : ℤ) < (H.height : ℤ) ∧
        1 ≤ (pH₁.1 : ℤ) + ((pH₁.1 : ℤ) + (pH₁.2 : ℤ)) % 2 ∧
        (pH₁.1 : ℤ) + ((pH₁.1 : ℤ) + (pH₁.2 : ℤ)) % 2 ≤ 2 * (H.height : ℤ) := by
      omega
    have hbrick₂ : 0 ≤ (pH₂.2 : ℤ) ∧ (pH₂.2 : ℤ) < (H.height : ℤ) ∧
        1 ≤ (pH₂.1 : ℤ) + ((pH₂.1 : ℤ) + (pH₂.2 : ℤ)) % 2 ∧
        (pH₂.1 : ℤ) + ((pH₂.1 : ℤ) + (pH₂.2 : ℤ)) % 2 ≤ 2 * (H.height : ℤ) := by
      omega
    rw [ite_eq_left_iff.mpr fun h => (h hbrick₁).elim,
      ite_eq_left_iff.mpr fun h => (h hbrick₂).elim] at hle_fig
    have hFo : ((pH₁.1 : ℤ) + ((pH₁.1 : ℤ) + (pH₁.2 : ℤ)) % 2, (pH₁.2 : ℤ)) ≠ outFace := by
      dsimp [outFace]; intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hGo : ((pH₂.1 : ℤ) + ((pH₂.1 : ℤ) + (pH₂.2 : ℤ)) % 2, (pH₂.2 : ℤ)) ≠ outFace := by
      dsimp [outFace]; intro h; have := congrArg Prod.snd h; dsimp at this; omega
    rw [faceDist_of_ne hFo hGo] at hle_fig
    let F₁ : ℤ := (pH₁.1 : ℤ) + ((pH₁.1 : ℤ) + (pH₁.2 : ℤ)) % 2
    let F₂ : ℤ := (pH₂.1 : ℤ) + ((pH₂.1 : ℤ) + (pH₂.2 : ℤ)) % 2
    have hF_diff : F₁ - F₂ ≤ 2 * (δ : ℤ) + 3 ∧ F₂ - F₁ ≤ 2 * (δ : ℤ) + 3 := by
      dsimp [F₁, F₂]
      omega
    have hhex : hexDist (F₁, (pH₁.2 : ℤ)) (F₂, (pH₂.2 : ℤ)) ≤ 3 * (δ : ℤ) + 4 := by
      rw [hexDist_eq_abs]
      rcases abs_choice (F₁ - F₂) with h1 | h1 <;>
        rcases abs_choice ((pH₁.2 : ℤ) - (pH₂.2 : ℤ)) with h2 | h2 <;>
        · rw [h1, h2]
          omega
    have hface_le :
        min (hexDist (F₁, (pH₁.2 : ℤ)) (F₂, (pH₂.2 : ℤ)))
          (outDepth H.height (F₁, (pH₁.2 : ℤ)) + outDepth H.height (F₂, (pH₂.2 : ℤ))) ≤ 3 * (δ : ℤ) + 4 :=
      (min_le_left _ _).trans hhex
    dsimp [F₁, F₂] at hface_le
    omega

/-- If two coordinate boxes `(i₁, j₁, h₁)` and `(i₂, j₂, h₂)` are separated by
`i₁ + 2 * h₁ + 1 < i₂ ∨ i₂ + 2 * h₂ + 1 < i₁ ∨ j₁ + h₁ < j₂ ∨ j₂ + h₂ < j₁`, then their shifted
enclosed sets `wallShiftRealHomeomorph i₁ j₁ '' fig1EnclosedSet h₁` and
`wallShiftRealHomeomorph i₂ j₂ '' fig1EnclosedSet h₂` are disjoint. -/
theorem disjoint_wallShiftRealHomeomorph_fig1EnclosedSet
    {i₁ j₁ h₁ i₂ j₂ h₂ : ℕ}
    (hsep : i₁ + 2 * h₁ + 1 < i₂ ∨ i₂ + 2 * h₂ + 1 < i₁ ∨ j₁ + h₁ < j₂ ∨ j₂ + h₂ < j₁) :
    Disjoint (wallShiftRealHomeomorph i₁ j₁ '' fig1EnclosedSet h₁)
      (wallShiftRealHomeomorph i₂ j₂ '' fig1EnclosedSet h₂) := by
  rw [Set.disjoint_left]
  rintro _ ⟨⟨x₁, y₁⟩, hxy₁, rfl⟩ ⟨⟨x₂, y₂⟩, hxy₂, heq⟩
  obtain ⟨⟨hx₁0, hx₁1⟩, ⟨hy₁0, hy₁1⟩⟩ := fig1EnclosedSet_subset_Icc h₁ hxy₁
  obtain ⟨⟨hx₂0, hx₂1⟩, ⟨hy₂0, hy₂1⟩⟩ := fig1EnclosedSet_subset_Icc h₂ hxy₂
  have hx_eq : x₂ + (i₂ : ℝ) = x₁ + (i₁ : ℝ) := congrArg Prod.fst heq
  have hy_eq : y₂ + (j₂ : ℝ) = y₁ + (j₁ : ℝ) := congrArg Prod.snd heq
  rcases hsep with h | h | h | h
  · have hr : (i₁ : ℝ) + 2 * (h₁ : ℝ) + 1 < (i₂ : ℝ) := by exact_mod_cast h
    linarith
  · have hr : (i₂ : ℝ) + 2 * (h₂ : ℝ) + 1 < (i₁ : ℝ) := by exact_mod_cast h
    linarith
  · have hr : (j₁ : ℝ) + (h₁ : ℝ) < (j₂ : ℝ) := by exact_mod_cast h
    linarith
  · have hr : (j₂ : ℝ) + (h₂ : ℝ) < (j₁ : ℝ) := by exact_mod_cast h
    linarith

/-! ## 3. Syntactic Characterization of Interior Base Edges of `fig1EnclosedSet` -/

/-- A base edge `(p, q)` is an *interior base edge* of the shifted enclosed set at `(i₀, j₀)` of
height `h₀` if either:
- it is horizontal (`p.2 = q.2`) with `j₀ < p.2 < j₀ + h₀` and `i₀ + 1 ≤ min p.1 q.1`,
  `max p.1 q.1 ≤ i₀ + 2 * h₀`, or
- it is vertical (`p.1 = q.1`) with `j₀ ≤ min p.2 q.2`, `max p.2 q.2 ≤ j₀ + h₀`, and
  `i₀ + 2 ≤ p.1 ≤ i₀ + 2 * h₀ - 1`. -/
def isInteriorBaseEdge (i₀ j₀ h₀ : ℕ) (p q : ℕ × ℕ) : Prop :=
  (p.2 = q.2 ∧ j₀ < p.2 ∧ p.2 < j₀ + h₀ ∧ i₀ + 1 ≤ min p.1 q.1 ∧ max p.1 q.1 ≤ i₀ + 2 * h₀) ∨
    (p.1 = q.1 ∧ j₀ ≤ min p.2 q.2 ∧ max p.2 q.2 ≤ j₀ + h₀ ∧ i₀ + 2 ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀ - 1)

theorem isInteriorBaseEdge_symm (i₀ j₀ h₀ : ℕ) (p q : ℕ × ℕ) :
    isInteriorBaseEdge i₀ j₀ h₀ p q ↔ isInteriorBaseEdge i₀ j₀ h₀ q p := by
  unfold isInteriorBaseEdge
  rw [min_comm p.1 q.1, max_comm p.1 q.1, min_comm p.2 q.2, max_comm p.2 q.2]
  constructor <;> rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
  · exact Or.inl ⟨h1.symm, h1 ▸ h2, h1 ▸ h3, h4, h5⟩
  · exact Or.inr ⟨h1.symm, h2, h3, h1 ▸ h4, h1 ▸ h5⟩
  · exact Or.inl ⟨h1.symm, h1 ▸ h2, h1 ▸ h3, h4, h5⟩
  · exact Or.inr ⟨h1.symm, h2, h3, h1 ▸ h4, h1 ▸ h5⟩

/-- For any point `(x, y) ∈ interior (fig1EnclosedSet h)`, we have `0 < y < h`, and if `y = (k : ℝ)`
for an integer `1 ≤ k < h` then `1 < x < 2h`. -/
lemma interior_fig1EnclosedSet_horiz_bounds {h k : ℕ} {x : ℝ}
    (hint : (x, (k : ℝ)) ∈ interior (fig1EnclosedSet h)) :
    1 ≤ k ∧ k < h ∧ 1 < x ∧ x < 2 * (h : ℝ) := by
  have hsub_Icc := fig1EnclosedSet_subset_Icc h (interior_subset hint)
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hε, hball⟩ := hint
  let δ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hball_pt : ∀ dx dy : ℝ, |dx| ≤ δ → |dy| ≤ δ →
      (x + dx, (k : ℝ) + dy) ∈ fig1EnclosedSet h := by
    intro dx dy hdx hdy
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · simpa [Real.dist_eq] using hdx.trans_lt hδ_lt_ε
    · simpa [Real.dist_eq] using hdy.trans_lt hδ_lt_ε
  have hk_pos : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    have hmem := hball_pt 0 (-δ) (by simp [le_of_lt hδ_pos]) (by simp [abs_of_pos hδ_pos])
    have hy_neg := (fig1EnclosedSet_subset_Icc h hmem).2.1
    rw [hk_eq] at hy_neg
    push_cast at hy_neg
    linarith
  have hk_lt : k < h := by
    by_contra hkh
    have hmem := hball_pt 0 δ (by simp [le_of_lt hδ_pos]) (by simp [abs_of_pos hδ_pos])
    have hy_hi := (fig1EnclosedSet_subset_Icc h hmem).2.2
    have hle : (h : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_not_lt hkh
    linarith
  -- Bounds from row `k` (using `dy = δ`) and row `k - 1` (using `dy = -δ`)
  have hrow_k_lo : fig1RowLeft k ≤ x - δ :=
    (row_bounds_of_mem_fig1EnclosedSet
      (hball_pt (-δ) δ (by simp [abs_of_pos hδ_pos]) (by simp [abs_of_pos hδ_pos]))
      (k := k) (by linarith) (by linarith)).1
  have hrow_k_hi : x + δ ≤ fig1RowRight h k :=
    (row_bounds_of_mem_fig1EnclosedSet
      (hball_pt δ δ (by simp [abs_of_pos hδ_pos]) (by simp [abs_of_pos hδ_pos]))
      (k := k) (by linarith) (by linarith)).2
  have hk1_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
    have h1 : (((k - 1) + 1 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast this
    push_cast at h1; linarith
  have hrow_k1_lo : fig1RowLeft (k - 1) ≤ x - δ :=
    (row_bounds_of_mem_fig1EnclosedSet
      (hball_pt (-δ) (-δ) (by simp [abs_of_pos hδ_pos]) (by simp [abs_of_pos hδ_pos]))
      (k := k - 1) (by linarith) (by linarith)).1
  have hrow_k1_hi : x + δ ≤ fig1RowRight h (k - 1) :=
    (row_bounds_of_mem_fig1EnclosedSet
      (hball_pt δ (-δ) (by simp [abs_of_pos hδ_pos]) (by simp [abs_of_pos hδ_pos]))
      (k := k - 1) (by linarith) (by linarith)).2
  refine ⟨hk_pos, hk_lt, ?_, ?_⟩
  · by_cases hev : Even k
    · have : fig1RowLeft k = 1 := by simp [fig1RowLeft, hev]
      linarith
    · have hev1 : Even (k - 1) := by
        obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hev
        exact ⟨m, by omega⟩
      have : fig1RowLeft (k - 1) = 1 := by simp [fig1RowLeft, hev1]
      linarith
  · by_cases hev : Even k
    · have hnot1 : ¬ Even (k - 1) := by
        rcases hev with ⟨m, hm⟩
        intro ⟨m', hm'⟩
        omega
      have : fig1RowRight h (k - 1) = 2 * (h : ℝ) := by
        unfold fig1RowRight fig1RowLeft
        rw [ite_eq_right_iff.mpr fun h => (hnot1 h).elim, add_zero]
      linarith
    · have : fig1RowRight h k = 2 * (h : ℝ) := by
        unfold fig1RowRight fig1RowLeft
        rw [ite_eq_right_iff.mpr fun h => (hev h).elim, add_zero]
      linarith

/-- For any vertical segment `{m} × [k, k + 1]` containing a point `(m, y) ∈ interior (fig1EnclosedSet h)`,
we have `k < h` and `fig1RowLeft k < (m : ℝ) < fig1RowRight h k`. -/
lemma interior_fig1EnclosedSet_vert_bounds {h m k : ℕ} {y : ℝ}
    (hy_lo : (k : ℝ) ≤ y) (hy_hi : y ≤ (k : ℝ) + 1)
    (hint : ((m : ℝ), y) ∈ interior (fig1EnclosedSet h)) :
    k < h ∧ fig1RowLeft k < (m : ℝ) ∧ (m : ℝ) < fig1RowRight h k := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hε, hball⟩ := hint
  let δ := min (ε / 2) (1 / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le : δ ≤ 1 / 4 := min_le_right _ _
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let y' : ℝ := if y < (k : ℝ) + 1 / 2 then y + δ else y - δ
  have hy'_bounds : (k : ℝ) < y' ∧ y' < (k : ℝ) + 1 := by
    dsimp [y']
    split_ifs <;> constructor <;> linarith
  have hy'_dist : |y' - y| < ε := by
    dsimp [y']
    split_ifs <;> simp [abs_of_pos hδ_pos, hδ_lt_ε]
  have hmem_lo : ((m : ℝ) - δ, y') ∈ fig1EnclosedSet h := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (by simp [abs_of_pos hδ_pos, hδ_lt_ε]) hy'_dist
  have hmem_hi : ((m : ℝ) + δ, y') ∈ fig1EnclosedSet h := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (by simp [abs_of_pos hδ_pos, hδ_lt_ε]) hy'_dist
  have hk_lt : k < h := by
    have hy_max := (fig1EnclosedSet_subset_Icc h hmem_lo).2.2
    have hlt_r : (k : ℝ) < (h : ℝ) := by linarith [hy'_bounds.1]
    exact_mod_cast hlt_r
  have hlo := (row_bounds_of_mem_fig1EnclosedSet hmem_lo hy'_bounds.1 hy'_bounds.2).1
  have hhi := (row_bounds_of_mem_fig1EnclosedSet hmem_hi hy'_bounds.1 hy'_bounds.2).2
  exact ⟨hk_lt, by linarith, by linarith⟩

/-- If `hadj : elementaryWallAdj h p q` is NOT an interior base edge of `(i₀, j₀, h₀)` (with `i₀, j₀`
even), then `fig1Segment p q` is disjoint from
`interior (wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀)`. -/
theorem disjoint_fig1Segment_interior_of_not_isInteriorBaseEdge
    {h i₀ j₀ h₀ : ℕ} (hi_even : Even i₀) (hj_even : Even j₀)
    {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q)
    (hnot : ¬ isInteriorBaseEdge i₀ j₀ h₀ p q) :
    Disjoint (fig1Segment p q)
      (interior (wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀)) := by
  rw [← (wallShiftRealHomeomorph i₀ j₀).image_interior, Set.disjoint_left]
  rintro ⟨x, y⟩ hseg ⟨⟨x_loc, y_loc⟩, hint, heq⟩
  have hx_eq : x_loc = x - (i₀ : ℝ) := by
    have := congrArg Prod.fst heq; dsimp at this; linarith
  have hy_eq : y_loc = y - (j₀ : ℝ) := by
    have := congrArg Prod.snd heq; dsimp at this; linarith
  obtain ⟨⟨hx_loc0, hx_loc1⟩, ⟨hy_loc0, hy_loc1⟩⟩ :=
    fig1EnclosedSet_subset_Icc h₀ (interior_subset hint)
  rcases hadj.2.2 with ⟨hpq2, hpq1⟩ | ⟨hpq1, hpq2⟩
  · -- Horizontal base edge
    unfold fig1Segment horizontalLatticeLine at hseg
    rw [ite_eq_left_iff.mpr fun h => (h hpq2).elim] at hseg
    rcases hseg with ⟨⟨hx_lo, hx_hi⟩, hy_val⟩
    rw [mem_singleton_iff] at hy_val
    have hp2_eq : min p.2 q.2 = p.2 := by rw [hpq2, min_self]
    rw [hp2_eq] at hy_val
    have hj_le : j₀ ≤ p.2 := by
      have : (j₀ : ℝ) ≤ (p.2 : ℝ) := by linarith
      exact_mod_cast this
    let k : ℕ := p.2 - j₀
    have hk_cast : (k : ℝ) = y_loc := by
      have : (k : ℕ) + j₀ = p.2 := Nat.sub_add_cancel hj_le
      have h1 : (((k : ℕ) + j₀ : ℕ) : ℝ) = (p.2 : ℝ) := by exact_mod_cast this
      push_cast at h1; linarith
    rw [← hk_cast] at hint
    obtain ⟨hk1, hkh, hx1, hx2⟩ := interior_fig1EnclosedSet_horiz_bounds hint
    have hmax_eq : max p.1 q.1 = min p.1 q.1 + 1 := by omega
    have hmin_ge : i₀ + 1 ≤ min p.1 q.1 := by
      have : (i₀ : ℝ) < ((min p.1 q.1 : ℕ) : ℝ) := by linarith
      have hlt : i₀ < min p.1 q.1 := by exact_mod_cast this
      omega
    have hmax_le : max p.1 q.1 ≤ i₀ + 2 * h₀ := by
      have : ((min p.1 q.1 : ℕ) : ℝ) < (i₀ : ℝ) + 2 * (h₀ : ℝ) := by linarith
      have hlt : min p.1 q.1 < i₀ + 2 * h₀ := by exact_mod_cast this
      omega
    exact hnot (Or.inl ⟨hpq2, by omega, by omega, hmin_ge, hmax_le⟩)
  · -- Vertical base edge
    have hpq2_ne : p.2 ≠ q.2 := by
      rcases hpq2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    unfold fig1Segment verticalLatticeLine at hseg
    rw [ite_eq_right_iff.mpr fun h => (hpq2_ne h).elim] at hseg
    rcases hseg with ⟨hx_val, ⟨hy_lo, hy_hi⟩⟩
    rw [mem_singleton_iff] at hx_val
    have hp1_eq : min p.1 q.1 = p.1 := by rw [hpq1, min_self]
    rw [hp1_eq] at hx_val
    have hi_le : i₀ ≤ p.1 := by
      have : (i₀ : ℝ) ≤ (p.1 : ℝ) := by linarith
      exact_mod_cast this
    have hj_le : j₀ ≤ min p.2 q.2 := by
      have hy_pos : 0 < y_loc := by
        by_contra hy0
        have hy_eq0 : y_loc = ((0 : ℕ) : ℝ) := by push_cast; linarith
        have := (interior_fig1EnclosedSet_horiz_bounds (hy_eq0 ▸ hint)).1
        omega
      have : (j₀ : ℝ) < ((min p.2 q.2 : ℕ) : ℝ) + 1 := by linarith
      have hlt : j₀ < min p.2 q.2 + 1 := by exact_mod_cast this
      omega
    let m : ℕ := p.1 - i₀
    let k : ℕ := min p.2 q.2 - j₀
    have hm_cast : (m : ℝ) = x_loc := by
      have : m + i₀ = p.1 := Nat.sub_add_cancel hi_le
      have h1 : ((m + i₀ : ℕ) : ℝ) = (p.1 : ℝ) := by exact_mod_cast this
      push_cast at h1; linarith
    have hk_cast : (k : ℝ) = ((min p.2 q.2 : ℕ) : ℝ) - (j₀ : ℝ) := by
      have : k + j₀ = min p.2 q.2 := Nat.sub_add_cancel hj_le
      have h1 : ((k + j₀ : ℕ) : ℝ) = ((min p.2 q.2 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_add] at h1; linarith
    rw [← hm_cast] at hint
    obtain ⟨hkh, hleft, hright⟩ :=
      interior_fig1EnclosedSet_vert_bounds (k := k) (by linarith) (by linarith) hint
    have hmax2 : max p.2 q.2 = min p.2 q.2 + 1 := by
      rcases hpq2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hodd : Odd (p.1 + min p.2 q.2) := by
      rcases hpq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : min p.2 q.2 = p.2 := by omega
        rwa [this]
      · have : min p.2 q.2 = q.2 := by omega
        rwa [this, hpq1]
    rcases hi_even with ⟨ki, hki⟩
    rcases hj_even with ⟨kj, hkj⟩
    rcases hodd with ⟨ko, hko⟩
    have hm_bounds : 2 ≤ m ∧ m ≤ 2 * h₀ - 1 := by
      by_cases hev_k : Even k
      · rcases hev_k with ⟨kk, hkk⟩
        have hL : fig1RowLeft k = 1 := by simp [fig1RowLeft, hkk]
        have hR : fig1RowRight h₀ k = 2 * (h₀ : ℝ) + 1 := by simp [fig1RowRight, fig1RowLeft, hkk]
        rw [hL] at hleft
        rw [hR] at hright
        have hm1 : 1 < m := by exact_mod_cast hleft
        have hm2 : m < 2 * h₀ + 1 := by exact_mod_cast hright
        omega
      · obtain ⟨kk, hkk⟩ := Nat.not_even_iff_odd.mp hev_k
        have hL : fig1RowLeft k = 0 := by
          unfold fig1RowLeft; rw [ite_eq_right_iff.mpr fun h => (hev_k h).elim]
        have hR : fig1RowRight h₀ k = 2 * (h₀ : ℝ) := by
          unfold fig1RowRight fig1RowLeft
          rw [ite_eq_right_iff.mpr fun h => (hev_k h).elim, add_zero]
        rw [hL] at hleft
        rw [hR] at hright
        have hm1 : 0 < m := by exact_mod_cast hleft
        have hm2 : m < 2 * h₀ := by exact_mod_cast hright
        omega
    exact hnot (Or.inr ⟨hpq1, hj_le, by omega, by omega, by omega⟩)

/-- Every interior base edge of `(i₀, j₀, h₀)` has its segment contained in
`wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀`, and any point on its segment that is not in
`interior (wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀)` lies on a non-interior horizontal
base edge of `(i₀, j₀, h₀)` whose segment also lies in
`wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀`. -/
theorem exists_nonInterior_baseEdge_of_not_mem_interior
    {h i₀ j₀ h₀ : ℕ} (hi_pos : 1 ≤ i₀) (hj_pos : 1 ≤ j₀) (hh₀ : 2 ≤ h₀) (heven_h₀ : Even h₀)
    (hi_hi : i₀ + 2 * h₀ + 1 ≤ 2 * h + 1) (hj_hi : j₀ + h₀ < h)
    {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q)
    (hint_edge : isInteriorBaseEdge i₀ j₀ h₀ p q)
    {z : ℝ × ℝ} (hz_seg : z ∈ fig1Segment p q)
    (hz_not_int : z ∉ interior (wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀)) :
    ∃ (p' q' : ℕ × ℕ) (_hadj' : elementaryWallAdj h p' q'),
      ¬ isInteriorBaseEdge i₀ j₀ h₀ p' q' ∧
      fig1Segment p' q' ⊆ wallShiftRealHomeomorph i₀ j₀ '' fig1EnclosedSet h₀ ∧
      z ∈ fig1Segment p' q' := by
  rw [← (wallShiftRealHomeomorph i₀ j₀).image_interior] at hz_not_int
  have hz_not_open : (z.1 - (i₀ : ℝ), z.2 - (j₀ : ℝ)) ∉
      Ioo (1 : ℝ) (2 * (h₀ : ℝ)) ×ˢ Ioo (0 : ℝ) (h₀ : ℝ) := by
    intro hopen
    apply hz_not_int
    refine ⟨(z.1 - (i₀ : ℝ), z.2 - (j₀ : ℝ)),
      open_rect_subset_interior_fig1EnclosedSet h₀ hopen, ?_⟩
    ext <;> dsimp <;> linarith
  rcases hint_edge with ⟨hpq2, hj_lo, hj_lt, hi_lo, hi_le⟩ | ⟨hpq1, hj_lo, hj_le, hi_lo, hi_le⟩
  · -- Horizontal interior edge: `z.2 = p.2` with `j₀ < p.2 < j₀ + h₀`, so `z.1 = i₀ + 1` or `z.1 = i₀ + 2 * h₀`
    unfold fig1Segment horizontalLatticeLine at hz_seg
    rw [ite_eq_left_iff.mpr fun h => (h hpq2).elim] at hz_seg
    rcases hz_seg with ⟨⟨hz1_lo, hz1_hi⟩, hz2_eq⟩
    rw [mem_singleton_iff] at hz2_eq
    have hp2_min : min p.2 q.2 = p.2 := by rw [hpq2, min_self]
    rw [hp2_min] at hz2_eq
    have hmax1 : max p.1 q.1 = min p.1 q.1 + 1 := by
      rcases hadj.2.2 with ⟨_, h1⟩ | ⟨h1, h2⟩
      · omega
      · rcases h2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    have hz1_bounds : (i₀ : ℝ) + 1 ≤ z.1 ∧ z.1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
      have h1 : (i₀ : ℝ) + 1 ≤ ((min p.1 q.1 : ℕ) : ℝ) := by exact_mod_cast hi_lo
      have h2 : ((min p.1 q.1 : ℕ) : ℝ) + 1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
        have : min p.1 q.1 + 1 ≤ i₀ + 2 * h₀ := by omega
        exact_mod_cast this
      exact ⟨by linarith, by linarith⟩
    have hz2_bounds : 0 < z.2 - (j₀ : ℝ) ∧ z.2 - (j₀ : ℝ) < (h₀ : ℝ) := by
      have h1 : (j₀ : ℝ) < (p.2 : ℝ) := by exact_mod_cast hj_lo
      have h2 : (p.2 : ℝ) < (j₀ : ℝ) + (h₀ : ℝ) := by exact_mod_cast hj_lt
      exact ⟨by linarith, by linarith⟩
    have hz1_end : z.1 = (i₀ : ℝ) + 1 ∨ z.1 = (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
      by_contra hne
      push Not at hne
      exact hz_not_open ⟨⟨by linarith [lt_of_le_of_ne hz1_bounds.1 hne.1.symm],
        by linarith [lt_of_le_of_ne hz1_bounds.2 hne.2]⟩, hz2_bounds⟩
    rcases hz1_end with hz1 | hz1
    · -- `z = (i₀ + 1, p.2)`: use the horizontal edge from `(i₀, p.2)` to `(i₀ + 1, p.2)`
      have hadj' : elementaryWallAdj h (i₀, p.2) (i₀ + 1, p.2) :=
        elementaryWallAdj_horiz_of_row_interior (by omega) (by omega) (by omega)
      refine ⟨(i₀, p.2), (i₀ + 1, p.2), hadj', ?_, ?_, ?_⟩
      · rintro (⟨_, _, _, hmin, _⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
      · rintro ⟨x, y⟩ hxy
        unfold fig1Segment horizontalLatticeLine at hxy
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim] at hxy
        rcases hxy with ⟨⟨hx1, hx2⟩, hy1⟩
        rw [mem_singleton_iff] at hy1
        have hmin_i : min i₀ (i₀ + 1) = i₀ := Nat.min_eq_left (by omega)
        rw [hmin_i] at hx1 hx2
        rw [min_self] at hy1
        refine ⟨(x - (i₀ : ℝ), y - (j₀ : ℝ)), fig1Set_subset_enclosed heven_h₀ hh₀ ?_, ?_⟩
        · let k := p.2 - j₀
          have hk_cast : (k : ℝ) = (p.2 : ℝ) - (j₀ : ℝ) := by
            have : k + j₀ = p.2 := Nat.sub_add_cancel (by omega)
            have h1 : ((k + j₀ : ℕ) : ℝ) = (p.2 : ℝ) := by exact_mod_cast this
            push_cast at h1; linarith
          apply horizontalLatticeLine_subset_fig1Set (i := 0) (j := k)
          · exact mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)
          · exact mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)
          · refine ⟨⟨by simp; linarith, by simp; linarith⟩, ?_⟩
            rw [mem_singleton_iff, hk_cast]
            dsimp at hy1 ⊢
            linarith
        · ext <;> dsimp <;> linarith
      · unfold fig1Segment horizontalLatticeLine
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim, Nat.min_eq_left (by omega), min_self]
        exact ⟨⟨by linarith, by linarith⟩, hz2_eq⟩
    · -- `z = (i₀ + 2 * h₀, p.2)`: use the horizontal edge from `(i₀ + 2 * h₀, p.2)` to
      -- `(i₀ + 2 * h₀ + 1, p.2)`
      have hadj' : elementaryWallAdj h (i₀ + 2 * h₀, p.2) (i₀ + 2 * h₀ + 1, p.2) :=
        elementaryWallAdj_horiz_of_row_interior (by omega) (by omega) (by omega)
      refine ⟨(i₀ + 2 * h₀, p.2), (i₀ + 2 * h₀ + 1, p.2), hadj', ?_, ?_, ?_⟩
      · rintro (⟨_, _, _, _, hmax⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
      · rintro ⟨x, y⟩ hxy
        unfold fig1Segment horizontalLatticeLine at hxy
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim] at hxy
        rcases hxy with ⟨⟨hx1, hx2⟩, hy1⟩
        rw [mem_singleton_iff] at hy1
        have hmin_i : min (i₀ + 2 * h₀) (i₀ + 2 * h₀ + 1) = i₀ + 2 * h₀ := Nat.min_eq_left (by omega)
        rw [hmin_i] at hx1 hx2
        rw [min_self] at hy1
        refine ⟨(x - (i₀ : ℝ), y - (j₀ : ℝ)), fig1Set_subset_enclosed heven_h₀ hh₀ ?_, ?_⟩
        · let k := p.2 - j₀
          have hk_cast : (k : ℝ) = (p.2 : ℝ) - (j₀ : ℝ) := by
            have : k + j₀ = p.2 := Nat.sub_add_cancel (by omega)
            have h1 : ((k + j₀ : ℕ) : ℝ) = (p.2 : ℝ) := by exact_mod_cast this
            push_cast at h1; linarith
          apply horizontalLatticeLine_subset_fig1Set (i := 2 * h₀) (j := k)
          · exact mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)
          · exact mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)
          · refine ⟨⟨by push_cast; push_cast at hx1; linarith,
              by push_cast; push_cast at hx2; linarith⟩, ?_⟩
            rw [mem_singleton_iff, hk_cast]
            dsimp at hy1 ⊢
            linarith
        · ext <;> dsimp <;> linarith
      · unfold fig1Segment horizontalLatticeLine
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim, Nat.min_eq_left (by omega), min_self]
        exact ⟨⟨by push_cast; linarith, by push_cast; linarith⟩, hz2_eq⟩
  · -- Vertical interior edge: `z.1 = p.1` with `i₀ + 2 ≤ p.1 ≤ i₀ + 2 * h₀ - 1`, so `z.2 = j₀` or `z.2 = j₀ + h₀`
    have hpq2_ne : p.2 ≠ q.2 := by
      rcases hadj.2.2 with ⟨h1, _⟩ | ⟨_, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
    unfold fig1Segment verticalLatticeLine at hz_seg
    rw [ite_eq_right_iff.mpr fun h => (hpq2_ne h).elim] at hz_seg
    rcases hz_seg with ⟨hz1_eq, ⟨hz2_lo, hz2_hi⟩⟩
    rw [mem_singleton_iff] at hz1_eq
    have hp1_min : min p.1 q.1 = p.1 := by rw [hpq1, min_self]
    rw [hp1_min] at hz1_eq
    have hmax2 : max p.2 q.2 = min p.2 q.2 + 1 := by
      rcases hadj.2.2 with ⟨h1, _⟩ | ⟨_, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
    have hz1_bounds : 1 < z.1 - (i₀ : ℝ) ∧ z.1 - (i₀ : ℝ) < 2 * (h₀ : ℝ) := by
      have h1 : (i₀ : ℝ) + 2 ≤ (p.1 : ℝ) := by exact_mod_cast hi_lo
      have h2 : (p.1 : ℝ) + 1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
        have : p.1 + 1 ≤ i₀ + 2 * h₀ := by omega
        exact_mod_cast this
      exact ⟨by linarith, by linarith⟩
    have hz2_bounds : (j₀ : ℝ) ≤ z.2 ∧ z.2 ≤ (j₀ : ℝ) + (h₀ : ℝ) := by
      have h1 : (j₀ : ℝ) ≤ ((min p.2 q.2 : ℕ) : ℝ) := by exact_mod_cast hj_lo
      have h2 : ((min p.2 q.2 : ℕ) : ℝ) + 1 ≤ (j₀ : ℝ) + (h₀ : ℝ) := by
        have : min p.2 q.2 + 1 ≤ j₀ + h₀ := by omega
        exact_mod_cast this
      exact ⟨by linarith, by linarith⟩
    have hz2_end : z.2 = (j₀ : ℝ) ∨ z.2 = (j₀ : ℝ) + (h₀ : ℝ) := by
      by_contra hne
      push Not at hne
      exact hz_not_open ⟨hz1_bounds, ⟨by linarith [lt_of_le_of_ne hz2_bounds.1 hne.1.symm],
        by linarith [lt_of_le_of_ne hz2_bounds.2 hne.2]⟩⟩
    rcases hz2_end with hz2 | hz2
    · -- `z = (p.1, j₀)`: use the horizontal edge from `(p.1 - 1, j₀)` to `(p.1, j₀)`
      have hadj' : elementaryWallAdj h (p.1 - 1, j₀) (p.1, j₀) := by
        have := elementaryWallAdj_horiz_of_row_interior (h := h) (x := p.1 - 1) (y₀ := j₀)
          hj_pos (by omega) (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
      refine ⟨(p.1 - 1, j₀), (p.1, j₀), hadj', ?_, ?_, ?_⟩
      · rintro (⟨_, hj_lt', _⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
      · rintro ⟨x, y⟩ hxy
        unfold fig1Segment horizontalLatticeLine at hxy
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim] at hxy
        rcases hxy with ⟨⟨hx1, hx2⟩, hy1⟩
        rw [mem_singleton_iff] at hy1
        have hmin_p : min (p.1 - 1) p.1 = p.1 - 1 := Nat.min_eq_left (by omega)
        rw [hmin_p] at hx1 hx2
        rw [min_self] at hy1
        refine ⟨(x - (i₀ : ℝ), y - (j₀ : ℝ)), rect_subset_fig1EnclosedSet ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
        · have : (i₀ : ℝ) + 1 ≤ ((p.1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i₀ + 1 ≤ p.1 - 1)
          linarith
        · have : ((p.1 - 1 : ℕ) : ℝ) + 1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
            have : (p.1 - 1) + 1 ≤ i₀ + 2 * h₀ := by omega
            exact_mod_cast this
          linarith
        · linarith
        · have : (0 : ℝ) ≤ (h₀ : ℝ) := Nat.cast_nonneg h₀
          linarith
        · ext <;> dsimp <;> linarith
      · unfold fig1Segment horizontalLatticeLine
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim, Nat.min_eq_left (by omega), min_self]
        have hp1_sub : ((p.1 - 1 : ℕ) : ℝ) + 1 = (p.1 : ℝ) := by
          have : (p.1 - 1) + 1 = p.1 := Nat.sub_add_cancel (by omega)
          exact_mod_cast this
        exact ⟨⟨by linarith, by linarith⟩, hz2⟩
    · -- `z = (p.1, j₀ + h₀)`: use the horizontal edge from `(p.1 - 1, j₀ + h₀)` to `(p.1, j₀ + h₀)`
      have hadj' : elementaryWallAdj h (p.1 - 1, j₀ + h₀) (p.1, j₀ + h₀) := by
        have := elementaryWallAdj_horiz_of_row_interior (h := h) (x := p.1 - 1) (y₀ := j₀ + h₀)
          (by omega) hj_hi (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
      refine ⟨(p.1 - 1, j₀ + h₀), (p.1, j₀ + h₀), hadj', ?_, ?_, ?_⟩
      · rintro (⟨_, _, hj_lt', _⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
      · rintro ⟨x, y⟩ hxy
        unfold fig1Segment horizontalLatticeLine at hxy
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim] at hxy
        rcases hxy with ⟨⟨hx1, hx2⟩, hy1⟩
        rw [mem_singleton_iff] at hy1
        have hmin_p : min (p.1 - 1) p.1 = p.1 - 1 := Nat.min_eq_left (by omega)
        rw [hmin_p] at hx1 hx2
        rw [min_self] at hy1
        refine ⟨(x - (i₀ : ℝ), y - (j₀ : ℝ)), rect_subset_fig1EnclosedSet ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
        · have : (i₀ : ℝ) + 1 ≤ ((p.1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i₀ + 1 ≤ p.1 - 1)
          linarith
        · have : ((p.1 - 1 : ℕ) : ℝ) + 1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
            have : (p.1 - 1) + 1 ≤ i₀ + 2 * h₀ := by omega
            exact_mod_cast this
          linarith
        · push_cast at hy1
          have : (0 : ℝ) ≤ (h₀ : ℝ) := Nat.cast_nonneg h₀
          linarith
        · push_cast at hy1
          linarith
        · ext <;> dsimp <;> linarith
      · unfold fig1Segment horizontalLatticeLine
        rw [ite_eq_left_iff.mpr fun h => (h rfl).elim, Nat.min_eq_left (by omega), min_self]
        have hp1_sub : ((p.1 - 1 : ℕ) : ℝ) + 1 = (p.1 : ℝ) := by
          have : (p.1 - 1) + 1 = p.1 := Nat.sub_add_cancel (by omega)
          exact_mod_cast this
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [mem_singleton_iff]
        dsimp
        push_cast
        linarith

/-! ## 4. Extending Crosses over Subwalls to the Perimeter of the Enlarged Punctured Box -/

/-- Generalization of `disjoint_subwallRegionVerts`: if no base edge of `W` has both endpoints in
`S₁ ∩ S₂`, then `subwallRegionVerts W S₁ ∩ subwallRegionVerts W S₂` consists only of branch vertices
`W.branchVertex p hp` with `p ∈ S₁ ∩ S₂`. -/
lemma subwallRegionVerts_inter_subset {W : Wall α β} {S₁ S₂ : Set (ℕ × ℕ)}
    (hno_edge : ∀ p q : ℕ × ℕ, elementaryWallAdj W.height p q → ¬ (p ∈ S₁ ∩ S₂ ∧ q ∈ S₁ ∩ S₂)) :
    subwallRegionVerts W S₁ ∩ subwallRegionVerts W S₂ ⊆
      {z : α | ∃ p ∈ S₁ ∩ S₂, ∃ hp : p ∈ elementaryWallVerts W.height, z = W.branchVertex p hp} := by
  have hmem_S : ∀ {S : Set (ℕ × ℕ)} {z : α},
      z ∈ subwallRegionVerts W S → z ∈ V(W.baseGraph) →
      ∃ p ∈ S, ∃ hp : p ∈ elementaryWallVerts W.height, z = W.branchVertex p hp := by
    intro S z hz hz_base
    rcases hz with ⟨p, hpS, hp, hzp⟩ | ⟨p, hpS, q, hqS, hadj, hzq⟩
    · exact ⟨p, hpS, hp, hzp⟩
    · have h_ends : z = W.branchVertex p hadj.1 ∨ z = W.branchVertex q hadj.2.1 := by
        have : z ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) := ⟨hzq, hz_base⟩
        rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
      rcases h_ends with rfl | rfl
      · exact ⟨p, hpS, hadj.1, rfl⟩
      · exact ⟨q, hqS, hadj.2.1, rfl⟩
  rintro z ⟨hz₁, hz₂⟩
  have hz_base : z ∈ V(W.baseGraph) := by
    rcases hz₁ with ⟨p, _, hp, rfl⟩ | ⟨p₁, hp₁S₁, q₁, hq₁S₁, hadj₁, hzq₁⟩
    · exact (W.baseIso.vertexEquiv ⟨p, hp⟩).2
    · rcases hz₂ with ⟨p, _, hp, rfl⟩ | ⟨p₂, hp₂S₂, q₂, hq₂S₂, hadj₂, hzq₂⟩
      · exact (W.baseIso.vertexEquiv ⟨p, hp⟩).2
      · have he_ne : W.baseEdge hadj₁ ≠ W.baseEdge hadj₂ := by
          intro heq
          have hsub : W.baseIso.edgeEquiv (elementaryWallEdge hadj₁) =
              W.baseIso.edgeEquiv (elementaryWallEdge hadj₂) := Subtype.ext heq
          have hsym2 : s(p₁, q₁) = s(p₂, q₂) :=
            congrArg Subtype.val (W.baseIso.edgeEquiv.injective hsub)
          have hp₁_eq : p₁ = p₂ ∨ p₁ = q₂ := by
            have : p₁ ∈ (s(p₂, q₂) : Sym2 (ℕ × ℕ)) := by rw [← hsym2]; exact Sym2.mem_mk_left p₁ q₁
            simpa using this
          have hq₁_eq : q₁ = p₂ ∨ q₁ = q₂ := by
            have : q₁ ∈ (s(p₂, q₂) : Sym2 (ℕ × ℕ)) := by rw [← hsym2]; exact Sym2.mem_mk_right p₁ q₁
            simpa using this
          have hp₁S₂ : p₁ ∈ S₂ := by rcases hp₁_eq with rfl | rfl <;> assumption
          have hq₁S₂ : q₁ ∈ S₂ := by rcases hq₁_eq with rfl | rfl <;> assumption
          exact hno_edge p₁ q₁ hadj₁ ⟨⟨hp₁S₁, hp₁S₂⟩, ⟨hq₁S₁, hq₁S₂⟩⟩
        exact (W.paths_disjoint _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj₁)).2
          _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj₂)).2 he_ne).2 ⟨hzq₁, hzq₂⟩
  obtain ⟨p₁, hp₁S₁, hp₁, rfl⟩ := hmem_S hz₁ hz_base
  obtain ⟨p₂, hp₂S₂, hp₂, heq⟩ := hmem_S hz₂ hz_base
  have hp12 : p₁ = p₂ :=
    congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext heq))
  exact ⟨p₁, ⟨hp₁S₁, hp12 ▸ hp₂S₂⟩, hp₁, rfl⟩

/-- Every vertex of `W.subwallAt i j h' ...` lies in
`subwallRegionVerts W (wallShift i j '' elementaryWallVerts h')`. -/
lemma subwallAt_vertexSet_subset_subwallRegionVerts (W : Wall α β)
    (i j h' : ℕ) (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W.height - 2 * h') (hj_le : j ≤ W.height - h') :
    V((W.subwallAt i j h' h2 heven hle hi_even hj_even hi_le hj_le).graph) ⊆
      subwallRegionVerts W (wallShift i j '' elementaryWallVerts h') := by
  let W' := W.subwallAt i j h' h2 heven hle hi_even hj_even hi_le hj_le
  intro u hu
  obtain ⟨p', q', hadj', f, _, _, hlink⟩ := W'.exists_inc_baseEdge hu
  have hadjW : elementaryWallAdj W.height (wallShift i j p') (wallShift i j q') :=
    (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le hadj'.1 hadj'.2.1).mp hadj'
  exact Or.inr ⟨wallShift i j p', ⟨p', hadj'.1, rfl⟩,
    wallShift i j q', ⟨q', hadj'.2.1, rfl⟩, hadjW, hlink.left_mem⟩

/-- Extracting a `GraphWalk` with rewritten endpoints from `ReachableInRegion`. -/
lemma ReachableInRegion.walk_eq_endpoints {W : Wall α β} {S : Set (ℕ × ℕ)}
    {p₁ p₂ p₁' p₂' : ℕ × ℕ}
    (hp₁' : p₁' ∈ elementaryWallVerts W.height)
    (hp₂' : p₂' ∈ elementaryWallVerts W.height)
    (heq₁ : p₁ = p₁') (heq₂ : p₂ = p₂')
    (h : ReachableInRegion W S p₁ p₂) :
    ∃ w : GraphWalk W.graph (W.branchVertex p₁' hp₁') (W.branchVertex p₂' hp₂'),
      {z | z ∈ w.support} ⊆ subwallRegionVerts W S := by
  subst heq₁; subst heq₂
  rcases h with ⟨hp₁, hp₂, w, hw⟩
  cases Subsingleton.elim hp₁ hp₁'
  cases Subsingleton.elim hp₂ hp₂'
  exact ⟨w, hw⟩

/-- If `hadj : elementaryWallAdj W.height p q` satisfies `¬ isInteriorBaseEdge i₀ j₀ h₀ p q`, then
neither `p` nor `q` lies in the inner box
`{r : ℕ × ℕ | i₀ + 2 ≤ r.1 ∧ r.1 ≤ i₀ + 2 * h₀ - 1 ∧ j₀ + 1 ≤ r.2 ∧ r.2 ≤ j₀ + h₀ - 1}`. -/
lemma not_mem_innerBox_of_not_isInteriorBaseEdge {h i₀ j₀ h₀ : ℕ}
    {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q)
    (hnot : ¬ isInteriorBaseEdge i₀ j₀ h₀ p q) :
    ¬ (i₀ + 2 ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀ - 1 ∧ j₀ + 1 ≤ p.2 ∧ p.2 ≤ j₀ + h₀ - 1) ∧
    ¬ (i₀ + 2 ≤ q.1 ∧ q.1 ≤ i₀ + 2 * h₀ - 1 ∧ j₀ + 1 ≤ q.2 ∧ q.2 ≤ j₀ + h₀ - 1) := by
  constructor
  · rintro ⟨hp1_lo, hp1_hi, hp2_lo, hp2_hi⟩
    apply hnot
    rcases hadj.2.2 with ⟨hpq2, hpq1 | hpq1⟩ | ⟨hpq1, ⟨hpq2, _⟩ | ⟨hpq2, _⟩⟩
    · exact Or.inl ⟨hpq2, by omega, by omega, by omega, by omega⟩
    · exact Or.inl ⟨hpq2, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨hpq1, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨hpq1, by omega, by omega, by omega, by omega⟩
  · rintro ⟨hq1_lo, hq1_hi, hq2_lo, hq2_hi⟩
    apply hnot
    rcases hadj.2.2 with ⟨hpq2, hpq1 | hpq1⟩ | ⟨hpq1, ⟨hpq2, _⟩ | ⟨hpq2, _⟩⟩
    · exact Or.inl ⟨hpq2, by omega, by omega, by omega, by omega⟩
    · exact Or.inl ⟨hpq2, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨hpq1, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨hpq1, by omega, by omega, by omega, by omega⟩

/-- Extending a cross `(P', Q')` over `H' = W.subwallAt (i₀ + 4) (j₀ + 2) h' ...` in `G₀` along the
four horizontal stubs on rows `j₀ + 2` and `j₀ + 2 + h'` to the four attachment vertices
`(i₀ + 1, j₀ + 2)`, `(i₀ + 1, j₀ + 2 + h')`, `(i₀ + 2 * (h' + 4), j₀ + 2 + h')`,
`(i₀ + 2 * (h' + 4), j₀ + 2)` of the punctured wall subgraph `Γ_graph ≤ W.graph ≤ G₀`. -/
theorem exists_extended_cross_hPaths
    {W : Wall α β} {G₀ Γ_graph : Graph α β}
    (hWG₀ : W.graph ≤ G₀) (hΓW : Γ_graph ≤ W.graph)
    {i₀ j₀ h' : ℕ} (h2 : 2 ≤ h') (heven : Even h')
    (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀_pos : 1 ≤ i₀) (hj₀_pos : 1 ≤ j₀)
    (hi₀_hi : i₀ + 2 * (h' + 4) + 1 ≤ 2 * W.height + 1)
    (hj₀_hi : j₀ + (h' + 4) < W.height)
    {H' P' Q' : Graph α β}
    (hH'_eq : H' = (W.subwallAt (i₀ + 4) (j₀ + 2) h' h2 heven (by omega)
      (hi₀_even.add (by decide)) (hj₀_even.add (by decide)) (by omega) (by omega)).graph)
    (hcross : IsCrossOverWall G₀
      (W.subwallAt (i₀ + 4) (j₀ + 2) h' h2 heven (by omega)
        (hi₀_even.add (by decide)) (hj₀_even.add (by decide)) (by omega) (by omega)) P' Q')
    (hinter : (V(P') ∪ V(Q')) ∩ V(W.graph) ⊆ V(H'))
    (hva_mem : W.branchVertex (i₀ + 1, j₀ + 2)
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)) ∈ V(Γ_graph))
    (hvb_mem : W.branchVertex (i₀ + 1, j₀ + 2 + h')
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)) ∈ V(Γ_graph))
    (hvc_mem : W.branchVertex (i₀ + 2 * (h' + 4), j₀ + 2 + h')
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)) ∈ V(Γ_graph))
    (hvd_mem : W.branchVertex (i₀ + 2 * (h' + 4), j₀ + 2)
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)) ∈ V(Γ_graph))
    (hΓ_verts : ∀ z ∈ V(Γ_graph), ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      ¬ isInteriorBaseEdge i₀ j₀ (h' + 4) p q ∧ z ∈ V(W.subdivisionPaths (W.baseEdge hadj)))
    (hΓ_edges : ∀ e ∈ E(Γ_graph), ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      ¬ isInteriorBaseEdge i₀ j₀ (h' + 4) p q ∧ e ∈ E(W.subdivisionPaths (W.baseEdge hadj))) :
    let h₀ := h' + 4
    let v_a := W.branchVertex (i₀ + 1, j₀ + 2)
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega))
    let v_b := W.branchVertex (i₀ + 1, j₀ + 2 + h')
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega))
    let v_c := W.branchVertex (i₀ + 2 * h₀, j₀ + 2 + h')
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega))
    let v_d := W.branchVertex (i₀ + 2 * h₀, j₀ + 2)
      (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega))
    ∃ P_hat Q_hat : Graph α β,
      IsHPathWithEnds G₀ Γ_graph P_hat v_a v_c ∧
      IsHPathWithEnds G₀ Γ_graph Q_hat v_b v_d ∧
      Disjoint V(P_hat) V(Q_hat) ∧
      (V(P_hat) ∪ V(Q_hat)) \ V(W.graph) ⊆ V(P') ∪ V(Q') ∧
      (V(P_hat) ∪ V(Q_hat)) ∩ V(W.graph) ⊆
        subwallRegionVerts W
          {p : ℕ × ℕ | i₀ + 1 ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀ ∧ j₀ + 2 ≤ p.2 ∧ p.2 ≤ j₀ + 2 + h'} := by
  intro h₀ v_a v_b v_c v_d
  let W' := W.subwallAt (i₀ + 4) (j₀ + 2) h' h2 heven (by omega)
    (hi₀_even.add (by decide)) (hj₀_even.add (by decide)) (by omega) (by omega)
  have hH'_sub : V(H') ⊆ subwallRegionVerts W (wallShift (i₀ + 4) (j₀ + 2) '' elementaryWallVerts h') := by
    rw [hH'_eq]
    exact subwallAt_vertexSet_subset_subwallRegionVerts W (i₀ + 4) (j₀ + 2) h'
      h2 heven (by omega) (hi₀_even.add (by decide)) (hj₀_even.add (by decide)) (by omega) (by omega)
  let S_H' : Set (ℕ × ℕ) := wallShift (i₀ + 4) (j₀ + 2) '' elementaryWallVerts h'
  let S_a : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.2 = j₀ + 2 ∧ i₀ + 1 ≤ p.1 ∧ p.1 ≤ i₀ + 5}
  let S_b : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.2 = j₀ + 2 + h' ∧ i₀ + 1 ≤ p.1 ∧ p.1 ≤ i₀ + 4}
  let S_c : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.2 = j₀ + 2 + h' ∧ i₀ + 4 + 2 * h' ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀}
  let S_d : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.2 = j₀ + 2 ∧ i₀ + 5 + 2 * h' ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀}
  let S_box : Set (ℕ × ℕ) :=
    {p : ℕ × ℕ | i₀ + 1 ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀ ∧ j₀ + 2 ≤ p.2 ∧ p.2 ≤ j₀ + 2 + h'}
  -- Horizontal stub reachability
  have hreach_a : ReachableInRegion W S_a (i₀ + 1, j₀ + 2) (i₀ + 5, j₀ + 2) := by
    refine ReachableInRegion.horiz (j₀ + 2) (i₀ + 1) (i₀ + 5) (by omega) ?_
    intro x hx1 hx2
    exact ⟨mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega), ⟨rfl, hx1, hx2⟩⟩
  have hreach_b : ReachableInRegion W S_b (i₀ + 1, j₀ + 2 + h') (i₀ + 4, j₀ + 2 + h') := by
    refine ReachableInRegion.horiz (j₀ + 2 + h') (i₀ + 1) (i₀ + 4) (by omega) ?_
    intro x hx1 hx2
    exact ⟨mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega), ⟨rfl, hx1, hx2⟩⟩
  have hreach_c : ReachableInRegion W S_c (i₀ + 4 + 2 * h', j₀ + 2 + h') (i₀ + 2 * h₀, j₀ + 2 + h') := by
    refine ReachableInRegion.horiz (j₀ + 2 + h') (i₀ + 4 + 2 * h') (i₀ + 2 * h₀) (by omega) ?_
    intro x hx1 hx2
    exact ⟨mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega), ⟨rfl, hx1, hx2⟩⟩
  have hreach_d : ReachableInRegion W S_d (i₀ + 5 + 2 * h', j₀ + 2) (i₀ + 2 * h₀, j₀ + 2) := by
    refine ReachableInRegion.horiz (j₀ + 2) (i₀ + 5 + 2 * h') (i₀ + 2 * h₀) (by omega) ?_
    intro x hx1 hx2
    exact ⟨mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega), ⟨rfl, hx1, hx2⟩⟩
  -- Corners of `W'`
  have hcorner_mem : ∀ k : Fin 4, elementaryWallCorner h' k ∈ elementaryWallVerts h' := by
    intro k; fin_cases k <;> simp [elementaryWallCorner, elementaryWallVerts] <;> omega
  have hc0_mem : wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 0) ∈ elementaryWallVerts W.height :=
    wallShift_mem_elementaryWallVerts' h2 (by omega) (by omega) (by omega) (hcorner_mem 0)
  have hc1_mem : wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 1) ∈ elementaryWallVerts W.height :=
    wallShift_mem_elementaryWallVerts' h2 (by omega) (by omega) (by omega) (hcorner_mem 1)
  have hc2_mem : wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 2) ∈ elementaryWallVerts W.height :=
    wallShift_mem_elementaryWallVerts' h2 (by omega) (by omega) (by omega) (hcorner_mem 2)
  have hc3_mem : wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 3) ∈ elementaryWallVerts W.height :=
    wallShift_mem_elementaryWallVerts' h2 (by omega) (by omega) (by omega) (hcorner_mem 3)
  obtain ⟨w_a, hw_a⟩ := hreach_a.walk_eq_endpoints
    (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)) hc0_mem rfl
    (by ext <;> dsimp [wallShift, elementaryWallCorner] <;> omega)
  obtain ⟨w_b, hw_b⟩ := hreach_b.walk_eq_endpoints
    (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega)) hc1_mem rfl
    (by ext <;> dsimp [wallShift, elementaryWallCorner] <;> omega)
  obtain ⟨w_c, hw_c⟩ := hreach_c.walk_eq_endpoints hc2_mem
    (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega))
    (by ext <;> dsimp [wallShift, elementaryWallCorner] <;> omega) rfl
  obtain ⟨w_d, hw_d⟩ := hreach_d.walk_eq_endpoints hc3_mem
    (mem_elementaryWallVerts_of_row_interior (by omega) (by omega) (by omega))
    (by ext <;> dsimp [wallShift, elementaryWallCorner] <;> omega) rfl
  -- Walks for `P'` and `Q'` in `G₀`
  rcases hcross with ⟨hdisj_PQ', ⟨hP'_le, w_P', _, hVP', _⟩, ⟨hQ'_le, w_Q', _, hVQ', _⟩⟩
  let w_a_G := w_a.mono hWG₀
  let w_b_G := w_b.mono hWG₀
  let w_c_G := w_c.mono hWG₀
  let w_d_G := w_d.mono hWG₀
  let w_P'_G := w_P'.mono hP'_le
  let w_Q'_G := w_Q'.mono hQ'_le
  -- Note `W'.corner k = W.branchVertex (wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' k)) _` by `rfl`
  let W_P : GraphWalk G₀ v_a v_c := w_a_G.append (w_P'_G.append w_c_G)
  let W_Q : GraphWalk G₀ v_b v_d := w_b_G.append (w_Q'_G.append w_d_G)
  obtain ⟨P_hat, hP_hat, hVP_hat, _⟩ := exists_isGraphPathWithEnds_of_walk W_P
  obtain ⟨Q_hat, hQ_hat, hVQ_hat, _⟩ := exists_isGraphPathWithEnds_of_walk W_Q
  -- Vertex support inclusions
  have hVP_sub : V(P_hat) ⊆ subwallRegionVerts W (S_a ∪ S_c) ∪ V(P') := by
    intro z hz
    rcases GraphWalk.mem_support_append _ _ (hVP_hat hz) with hza | hz_rest
    · rw [GraphWalk.support_mono] at hza
      exact Or.inl (subwallRegionVerts_mono W subset_union_left (hw_a hza))
    · change z ∈ (w_P'_G.append w_c_G).support at hz_rest
      rcases GraphWalk.mem_support_append _ _ hz_rest with hzP' | hzc
      · rw [GraphWalk.support_mono] at hzP'
        rw [hVP']
        exact Or.inr hzP'
      · change z ∈ w_c_G.support at hzc
        rw [GraphWalk.support_mono] at hzc
        exact Or.inl (subwallRegionVerts_mono W subset_union_right (hw_c hzc))
  have hVQ_sub : V(Q_hat) ⊆ subwallRegionVerts W (S_b ∪ S_d) ∪ V(Q') := by
    intro z hz
    rcases GraphWalk.mem_support_append _ _ (hVQ_hat hz) with hzb | hz_rest
    · rw [GraphWalk.support_mono] at hzb
      exact Or.inl (subwallRegionVerts_mono W subset_union_left (hw_b hzb))
    · change z ∈ (w_Q'_G.append w_d_G).support at hz_rest
      rcases GraphWalk.mem_support_append _ _ hz_rest with hzQ' | hzd
      · rw [GraphWalk.support_mono] at hzQ'
        rw [hVQ']
        exact Or.inr hzQ'
      · change z ∈ w_d_G.support at hzd
        rw [GraphWalk.support_mono] at hzd
        exact Or.inl (subwallRegionVerts_mono W subset_union_right (hw_d hzd))
  -- Corner memberships in `V(P')` and `V(Q')`
  have hc0_P' : W'.corner 0 ∈ V(P') := by
    rw [hVP']; exact w_P'.start_mem_support
  have hc2_P' : W'.corner 2 ∈ V(P') := by
    rw [hVP']; exact w_P'.end_mem_support
  have hc1_Q' : W'.corner 1 ∈ V(Q') := by
    rw [hVQ']; exact w_Q'.start_mem_support
  have hc3_Q' : W'.corner 3 ∈ V(Q') := by
    rw [hVQ']; exact w_Q'.end_mem_support
  -- Disjointness of `(S_a ∪ S_c)` and `(S_b ∪ S_d)`
  have hdisj_ac_bd : Disjoint (S_a ∪ S_c) (S_b ∪ S_d) := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [S_a, S_b, S_c, S_d, h₀, mem_union, mem_ofPred_eq] at h1 h2
    omega
  -- Intersection of `S_a ∪ S_c` with `S_H'`
  have hinter_ac_H' : (S_a ∪ S_c) ∩ S_H' ⊆
      {wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 0),
       wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 2)} := by
    rintro p ⟨hac, ⟨q, hq, rfl⟩⟩
    rcases hq with ⟨hq1, hq2, hq_ne0, hq_ne1⟩
    have hq_not_00 : ¬ (q.1 = 0 ∧ q.2 = 0) := fun ⟨h1, h2⟩ => hq_ne0 (Prod.ext h1 h2)
    have hq_not_top : ¬ (q.1 = 2 * h' + 1 ∧ q.2 = h') := fun ⟨h1, h2⟩ => hq_ne1 (Prod.ext h1 h2)
    simp only [S_a, S_c, wallShift, elementaryWallCorner, h₀, mem_union, mem_ofPred_eq,
      mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hac ⊢
    omega
  -- Intersection of `S_b ∪ S_d` with `S_H'`
  have hinter_bd_H' : (S_b ∪ S_d) ∩ S_H' ⊆
      {wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 1),
       wallShift (i₀ + 4) (j₀ + 2) (elementaryWallCorner h' 3)} := by
    rintro p ⟨hbd, ⟨q, hq, rfl⟩⟩
    rcases hq with ⟨hq1, hq2, hq_ne0, hq_ne1⟩
    have hq_not_00 : ¬ (q.1 = 0 ∧ q.2 = 0) := fun ⟨h1, h2⟩ => hq_ne0 (Prod.ext h1 h2)
    have hq_not_top : ¬ (q.1 = 2 * h' + 1 ∧ q.2 = h') := fun ⟨h1, h2⟩ => hq_ne1 (Prod.ext h1 h2)
    simp only [S_b, S_d, wallShift, elementaryWallCorner, h₀, mem_union, mem_ofPred_eq,
      mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hbd ⊢
    omega
  -- `Disjoint V(P_hat) V(Q_hat)`
  have hdisj_PQ_hat : Disjoint V(P_hat) V(Q_hat) := by
    rw [Set.disjoint_left]
    intro z hzP hzQ
    rcases hVP_sub hzP with hz_ac | hzP'
    · rcases hVQ_sub hzQ with hz_bd | hzQ'
      · exact Set.disjoint_left.mp (disjoint_subwallRegionVerts hdisj_ac_bd) hz_ac hz_bd
      · have hzW : z ∈ V(W.graph) := subwallRegionVerts_subset_vertexSet W _ hz_ac
        have hzH' : z ∈ subwallRegionVerts W S_H' :=
          hH'_sub (hinter ⟨Or.inr hzQ', hzW⟩)
        have hno_edge : ∀ p q : ℕ × ℕ, elementaryWallAdj W.height p q →
            ¬ (p ∈ (S_a ∪ S_c) ∩ S_H' ∧ q ∈ (S_a ∪ S_c) ∩ S_H') := by
          intro p q hadj ⟨hp, hq⟩
          have hp' := hinter_ac_H' hp
          have hq' := hinter_ac_H' hq
          dsimp [wallShift, elementaryWallCorner] at hp' hq'
          simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hp' hq'
          rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
        obtain ⟨p, hp, hp_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hz_ac, hzH'⟩
        rcases hinter_ac_H' hp with rfl | h_eq
        · exact Set.disjoint_left.mp hdisj_PQ' hc0_P' hzQ'
        · rw [mem_singleton_iff] at h_eq
          subst h_eq
          exact Set.disjoint_left.mp hdisj_PQ' hc2_P' hzQ'
    · rcases hVQ_sub hzQ with hz_bd | hzQ'
      · have hzW : z ∈ V(W.graph) := subwallRegionVerts_subset_vertexSet W _ hz_bd
        have hzH' : z ∈ subwallRegionVerts W S_H' :=
          hH'_sub (hinter ⟨Or.inl hzP', hzW⟩)
        have hno_edge : ∀ p q : ℕ × ℕ, elementaryWallAdj W.height p q →
            ¬ (p ∈ (S_b ∪ S_d) ∩ S_H' ∧ q ∈ (S_b ∪ S_d) ∩ S_H') := by
          intro p q hadj ⟨hp, hq⟩
          have hp' := hinter_bd_H' hp
          have hq' := hinter_bd_H' hq
          dsimp [wallShift, elementaryWallCorner] at hp' hq'
          simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hp' hq'
          rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
        obtain ⟨p, hp, hp_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hz_bd, hzH'⟩
        rcases hinter_bd_H' hp with rfl | h_eq
        · exact Set.disjoint_left.mp hdisj_PQ' hzP' hc1_Q'
        · rw [mem_singleton_iff] at h_eq
          subst h_eq
          exact Set.disjoint_left.mp hdisj_PQ' hzP' hc3_Q'
      · exact Set.disjoint_left.mp hdisj_PQ' hzP' hzQ'
  -- Region of `Γ_graph`
  let S_kept : Set (ℕ × ℕ) :=
    {p : ℕ × ℕ | ¬ (i₀ + 2 ≤ p.1 ∧ p.1 ≤ i₀ + 2 * h₀ - 1 ∧ j₀ + 1 ≤ p.2 ∧ p.2 ≤ j₀ + h₀ - 1)}
  have hΓ_sub_kept : V(Γ_graph) ⊆ subwallRegionVerts W S_kept := by
    intro z hz
    obtain ⟨p, q, hadj, hnot, hz_path⟩ := hΓ_verts z hz
    have hnot_inner := not_mem_innerBox_of_not_isInteriorBaseEdge hadj hnot
    exact Or.inr ⟨p, hnot_inner.1, q, hnot_inner.2, hadj, hz_path⟩
  have hVP_W_sub : V(P_hat) ∩ V(W.graph) ⊆ subwallRegionVerts W (S_a ∪ S_c ∪ S_H') := by
    rintro z ⟨hzP, hzW⟩
    rcases hVP_sub hzP with hz_ac | hzP'
    · exact subwallRegionVerts_mono W subset_union_left hz_ac
    · exact subwallRegionVerts_mono W subset_union_right (hH'_sub (hinter ⟨Or.inl hzP', hzW⟩))
  have hVQ_W_sub : V(Q_hat) ∩ V(W.graph) ⊆ subwallRegionVerts W (S_b ∪ S_d ∪ S_H') := by
    rintro z ⟨hzQ, hzW⟩
    rcases hVQ_sub hzQ with hz_bd | hzQ'
    · exact subwallRegionVerts_mono W subset_union_left hz_bd
    · exact subwallRegionVerts_mono W subset_union_right (hH'_sub (hinter ⟨Or.inr hzQ', hzW⟩))
  have hinter_P_kept : (S_a ∪ S_c ∪ S_H') ∩ S_kept ⊆ {(i₀ + 1, j₀ + 2), (i₀ + 2 * h₀, j₀ + 2 + h')} := by
    rintro p ⟨hp_P, hp_kept⟩
    simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff]
    rcases hp_P with (hp_a | hp_c) | ⟨q, hq, rfl⟩
    · dsimp [S_a, S_kept, h₀] at hp_a hp_kept; omega
    · dsimp [S_c, S_kept, h₀] at hp_c hp_kept; omega
    · rcases hq with ⟨hq1, hq2, _⟩
      dsimp [wallShift, S_kept, h₀] at hp_kept
      omega
  have hinter_Q_kept : (S_b ∪ S_d ∪ S_H') ∩ S_kept ⊆ {(i₀ + 1, j₀ + 2 + h'), (i₀ + 2 * h₀, j₀ + 2)} := by
    rintro p ⟨hp_Q, hp_kept⟩
    simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff]
    rcases hp_Q with (hp_b | hp_d) | ⟨q, hq, rfl⟩
    · dsimp [S_b, S_kept, h₀] at hp_b hp_kept; omega
    · dsimp [S_d, S_kept, h₀] at hp_d hp_kept; omega
    · rcases hq with ⟨hq1, hq2, _⟩
      dsimp [wallShift, S_kept, h₀] at hp_kept
      omega
  -- `V(P_hat) ∩ V(Γ_graph) = {v_a, v_c}` and `V(Q_hat) ∩ V(Γ_graph) = {v_b, v_d}`
  have hVP_inter_Γ : V(P_hat) ∩ V(Γ_graph) = {v_a, v_c} := by
    apply Subset.antisymm
    · rintro z ⟨hzP, hzΓ⟩
      have hzW : z ∈ V(W.graph) := hΓW.vertexSet_mono hzΓ
      have hz1 := hVP_W_sub ⟨hzP, hzW⟩
      have hz2 := hΓ_sub_kept hzΓ
      have hno_edge : ∀ p q : ℕ × ℕ, elementaryWallAdj W.height p q →
          ¬ (p ∈ (S_a ∪ S_c ∪ S_H') ∩ S_kept ∧ q ∈ (S_a ∪ S_c ∪ S_H') ∩ S_kept) := by
        intro p q hadj ⟨hp, hq⟩
        have hp' := hinter_P_kept hp
        have hq' := hinter_P_kept hq
        simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hp' hq'
        rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
      obtain ⟨p, hp, hp_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hz1, hz2⟩
      rcases hinter_P_kept hp with rfl | h_eq
      · exact Or.inl rfl
      · rw [mem_singleton_iff] at h_eq
        subst h_eq
        exact Or.inr rfl
    · rintro z (rfl | rfl)
      · rcases hP_hat with ⟨_, w, _, hV, _⟩
        rw [hV]
        exact ⟨w.start_mem_support, hva_mem⟩
      · rcases hP_hat with ⟨_, w, _, hV, _⟩
        rw [hV]
        exact ⟨w.end_mem_support, hvc_mem⟩
  have hVQ_inter_Γ : V(Q_hat) ∩ V(Γ_graph) = {v_b, v_d} := by
    apply Subset.antisymm
    · rintro z ⟨hzQ, hzΓ⟩
      have hzW : z ∈ V(W.graph) := hΓW.vertexSet_mono hzΓ
      have hz1 := hVQ_W_sub ⟨hzQ, hzW⟩
      have hz2 := hΓ_sub_kept hzΓ
      have hno_edge : ∀ p q : ℕ × ℕ, elementaryWallAdj W.height p q →
          ¬ (p ∈ (S_b ∪ S_d ∪ S_H') ∩ S_kept ∧ q ∈ (S_b ∪ S_d ∪ S_H') ∩ S_kept) := by
        intro p q hadj ⟨hp, hq⟩
        have hp' := hinter_Q_kept hp
        have hq' := hinter_Q_kept hq
        simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hp' hq'
        rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
      obtain ⟨p, hp, hp_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hz1, hz2⟩
      rcases hinter_Q_kept hp with rfl | h_eq
      · exact Or.inl rfl
      · rw [mem_singleton_iff] at h_eq
        subst h_eq
        exact Or.inr rfl
    · rintro z (rfl | rfl)
      · rcases hQ_hat with ⟨_, w, _, hV, _⟩
        rw [hV]
        exact ⟨w.start_mem_support, hvb_mem⟩
      · rcases hQ_hat with ⟨_, w, _, hV, _⟩
        rw [hV]
        exact ⟨w.end_mem_support, hvd_mem⟩
  -- Edge disjointness `Disjoint E(P_hat) E(Γ_graph)` and `Disjoint E(Q_hat) E(Γ_graph)`
  have hdisj_EP : Disjoint E(P_hat) E(Γ_graph) := by
    rw [Set.disjoint_left]
    intro e heP heΓ
    obtain ⟨p, q, hadj, hnot, he_sub⟩ := hΓ_edges e heΓ
    obtain ⟨u, v, hlink_sub⟩ := (W.subdivisionPaths (W.baseEdge hadj)).exists_isLink_of_mem_edgeSet he_sub
    have hlink_W : W.graph.IsLink e u v := hlink_sub.mono (W.isGraphPathWithEnds_baseEdge hadj).le
    have hlink_G₀ : G₀.IsLink e u v := hlink_W.mono hWG₀
    obtain ⟨u', v', hlink_P⟩ := P_hat.exists_isLink_of_mem_edgeSet heP
    have hlink_G₀' : G₀.IsLink e u' v' := hlink_P.mono hP_hat.le
    have huv_P : u ∈ V(P_hat) ∧ v ∈ V(P_hat) := by
      rcases G₀.eq_or_eq_of_isLink_of_isLink hlink_G₀ hlink_G₀' with rfl | rfl
      · rw [hlink_G₀.right_unique hlink_G₀']
        exact ⟨hlink_P.left_mem, hlink_P.right_mem⟩
      · rw [hlink_G₀.right_unique hlink_G₀'.symm]
        exact ⟨hlink_P.right_mem, hlink_P.left_mem⟩
    have hu_W : u ∈ V(W.graph) := hlink_W.left_mem
    have hv_W : v ∈ V(W.graph) := hlink_W.right_mem
    have hu_P_reg := hVP_W_sub ⟨huv_P.1, hu_W⟩
    have hv_P_reg := hVP_W_sub ⟨huv_P.2, hv_W⟩
    have hnot_inner := not_mem_innerBox_of_not_isInteriorBaseEdge hadj hnot
    have hu_kept : u ∈ subwallRegionVerts W S_kept :=
      Or.inr ⟨p, hnot_inner.1, q, hnot_inner.2, hadj, hlink_sub.left_mem⟩
    have hv_kept : v ∈ subwallRegionVerts W S_kept :=
      Or.inr ⟨p, hnot_inner.1, q, hnot_inner.2, hadj, hlink_sub.right_mem⟩
    have hno_edge : ∀ p' q' : ℕ × ℕ, elementaryWallAdj W.height p' q' →
        ¬ (p' ∈ (S_a ∪ S_c ∪ S_H') ∩ S_kept ∧ q' ∈ (S_a ∪ S_c ∪ S_H') ∩ S_kept) := by
      intro p' q' hadj' ⟨hp', hq'⟩
      have hp'' := hinter_P_kept hp'
      have hq'' := hinter_P_kept hq'
      simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hp'' hq''
      rcases hadj'.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
    obtain ⟨pu, hpu, hpu_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hu_P_reg, hu_kept⟩
    obtain ⟨pv, hpv, hpv_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hv_P_reg, hv_kept⟩
    have hu_base : W.branchVertex pu hpu_vert ∈ V(W.baseGraph) := (W.baseIso.vertexEquiv ⟨pu, hpu_vert⟩).2
    have hv_base : W.branchVertex pv hpv_vert ∈ V(W.baseGraph) := (W.baseIso.vertexEquiv ⟨pv, hpv_vert⟩).2
    have hu_ends : W.branchVertex pu hpu_vert = W.branchVertex p hadj.1 ∨
        W.branchVertex pu hpu_vert = W.branchVertex q hadj.2.1 := by
      have : W.branchVertex pu hpu_vert ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) :=
        ⟨hlink_sub.left_mem, hu_base⟩
      rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
    have hv_ends : W.branchVertex pv hpv_vert = W.branchVertex p hadj.1 ∨
        W.branchVertex pv hpv_vert = W.branchVertex q hadj.2.1 := by
      have : W.branchVertex pv hpv_vert ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) :=
        ⟨hlink_sub.right_mem, hv_base⟩
      rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
    have hpu_pq : pu = p ∨ pu = q := by
      rcases hu_ends with h1 | h1
      · exact Or.inl (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
      · exact Or.inr (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
    have hpv_pq : pv = p ∨ pv = q := by
      rcases hv_ends with h1 | h1
      · exact Or.inl (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
      · exact Or.inr (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
    have huv_ne : W.branchVertex pu hpu_vert ≠ W.branchVertex pv hpv_vert :=
      ne_of_isLink_of_isGraphPathWithEnds (W.isGraphPathWithEnds_baseEdge hadj) hlink_sub
    have hpupv_ne : pu ≠ pv := fun h => huv_ne (by subst h; rfl)
    have hpu_cases := hinter_P_kept hpu
    have hpv_cases := hinter_P_kept hpv
    simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hpu_cases hpv_cases
    rcases hpu_pq with rfl | rfl <;> rcases hpv_pq with rfl | rfl
    · exact hpupv_ne rfl
    · rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
    · rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
    · exact hpupv_ne rfl
  have hdisj_EQ : Disjoint E(Q_hat) E(Γ_graph) := by
    rw [Set.disjoint_left]
    intro e heQ heΓ
    obtain ⟨p, q, hadj, hnot, he_sub⟩ := hΓ_edges e heΓ
    obtain ⟨u, v, hlink_sub⟩ := (W.subdivisionPaths (W.baseEdge hadj)).exists_isLink_of_mem_edgeSet he_sub
    have hlink_W : W.graph.IsLink e u v := hlink_sub.mono (W.isGraphPathWithEnds_baseEdge hadj).le
    have hlink_G₀ : G₀.IsLink e u v := hlink_W.mono hWG₀
    obtain ⟨u', v', hlink_Q⟩ := Q_hat.exists_isLink_of_mem_edgeSet heQ
    have hlink_G₀' : G₀.IsLink e u' v' := hlink_Q.mono hQ_hat.le
    have huv_Q : u ∈ V(Q_hat) ∧ v ∈ V(Q_hat) := by
      rcases G₀.eq_or_eq_of_isLink_of_isLink hlink_G₀ hlink_G₀' with rfl | rfl
      · rw [hlink_G₀.right_unique hlink_G₀']
        exact ⟨hlink_Q.left_mem, hlink_Q.right_mem⟩
      · rw [hlink_G₀.right_unique hlink_G₀'.symm]
        exact ⟨hlink_Q.right_mem, hlink_Q.left_mem⟩
    have hu_W : u ∈ V(W.graph) := hlink_W.left_mem
    have hv_W : v ∈ V(W.graph) := hlink_W.right_mem
    have hu_Q_reg := hVQ_W_sub ⟨huv_Q.1, hu_W⟩
    have hv_Q_reg := hVQ_W_sub ⟨huv_Q.2, hv_W⟩
    have hnot_inner := not_mem_innerBox_of_not_isInteriorBaseEdge hadj hnot
    have hu_kept : u ∈ subwallRegionVerts W S_kept :=
      Or.inr ⟨p, hnot_inner.1, q, hnot_inner.2, hadj, hlink_sub.left_mem⟩
    have hv_kept : v ∈ subwallRegionVerts W S_kept :=
      Or.inr ⟨p, hnot_inner.1, q, hnot_inner.2, hadj, hlink_sub.right_mem⟩
    have hno_edge : ∀ p' q' : ℕ × ℕ, elementaryWallAdj W.height p' q' →
        ¬ (p' ∈ (S_b ∪ S_d ∪ S_H') ∩ S_kept ∧ q' ∈ (S_b ∪ S_d ∪ S_H') ∩ S_kept) := by
      intro p' q' hadj' ⟨hp', hq'⟩
      have hp'' := hinter_Q_kept hp'
      have hq'' := hinter_Q_kept hq'
      simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hp'' hq''
      rcases hadj'.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
    obtain ⟨pu, hpu, hpu_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hu_Q_reg, hu_kept⟩
    obtain ⟨pv, hpv, hpv_vert, rfl⟩ := subwallRegionVerts_inter_subset hno_edge ⟨hv_Q_reg, hv_kept⟩
    have hu_base : W.branchVertex pu hpu_vert ∈ V(W.baseGraph) := (W.baseIso.vertexEquiv ⟨pu, hpu_vert⟩).2
    have hv_base : W.branchVertex pv hpv_vert ∈ V(W.baseGraph) := (W.baseIso.vertexEquiv ⟨pv, hpv_vert⟩).2
    have hu_ends : W.branchVertex pu hpu_vert = W.branchVertex p hadj.1 ∨
        W.branchVertex pu hpu_vert = W.branchVertex q hadj.2.1 := by
      have : W.branchVertex pu hpu_vert ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) :=
        ⟨hlink_sub.left_mem, hu_base⟩
      rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
    have hv_ends : W.branchVertex pv hpv_vert = W.branchVertex p hadj.1 ∨
        W.branchVertex pv hpv_vert = W.branchVertex q hadj.2.1 := by
      have : W.branchVertex pv hpv_vert ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) :=
        ⟨hlink_sub.right_mem, hv_base⟩
      rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
    have hpu_pq : pu = p ∨ pu = q := by
      rcases hu_ends with h1 | h1
      · exact Or.inl (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
      · exact Or.inr (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
    have hpv_pq : pv = p ∨ pv = q := by
      rcases hv_ends with h1 | h1
      · exact Or.inl (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
      · exact Or.inr (congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext h1)))
    have huv_ne : W.branchVertex pu hpu_vert ≠ W.branchVertex pv hpv_vert :=
      ne_of_isLink_of_isGraphPathWithEnds (W.isGraphPathWithEnds_baseEdge hadj) hlink_sub
    have hpupv_ne : pu ≠ pv := fun h => huv_ne (by subst h; rfl)
    have hpu_cases := hinter_Q_kept hpu
    have hpv_cases := hinter_Q_kept hpv
    simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff] at hpu_cases hpv_cases
    rcases hpu_pq with rfl | rfl <;> rcases hpv_pq with rfl | rfl
    · exact hpupv_ne rfl
    · rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
    · rcases hadj.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> dsimp [h₀] at * <;> omega
    · exact hpupv_ne rfl
  have hva_ne_vc : v_a ≠ v_c := by
    intro heq
    have hsub := congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext heq))
    have := congrArg Prod.fst hsub
    dsimp [h₀] at this
    omega
  have hvb_ne_vd : v_b ≠ v_d := by
    intro heq
    have hsub := congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext heq))
    have := congrArg Prod.fst hsub
    dsimp [h₀] at this
    omega
  refine ⟨P_hat, Q_hat,
    ⟨hΓW.trans hWG₀, hP_hat, hva_ne_vc, hva_mem, hvc_mem, hVP_inter_Γ, hdisj_EP⟩,
    ⟨hΓW.trans hWG₀, hQ_hat, hvb_ne_vd, hvb_mem, hvd_mem, hVQ_inter_Γ, hdisj_EQ⟩,
    hdisj_PQ_hat, ?_, ?_⟩
  · rintro z ⟨hz_PQ, hz_not_W⟩
    rcases hz_PQ with hzP | hzQ
    · rcases hVP_sub hzP with hz_ac | hzP'
      · exact (hz_not_W (subwallRegionVerts_subset_vertexSet W _ hz_ac)).elim
      · exact Or.inl hzP'
    · rcases hVQ_sub hzQ with hz_bd | hzQ'
      · exact (hz_not_W (subwallRegionVerts_subset_vertexSet W _ hz_bd)).elim
      · exact Or.inr hzQ'
  · rintro z ⟨hz_PQ, hzW⟩
    have hsub_box : (S_a ∪ S_c ∪ S_H') ∪ (S_b ∪ S_d ∪ S_H') ⊆ S_box := by
      rintro p (hp_P | hp_Q)
      · rcases hp_P with (hp_a | hp_c) | ⟨q, hq, rfl⟩
        · dsimp [S_a, S_box, h₀] at hp_a ⊢; omega
        · dsimp [S_c, S_box, h₀] at hp_c ⊢; omega
        · rcases hq with ⟨hq1, hq2, _⟩
          dsimp [wallShift, S_box, h₀]; omega
      · rcases hp_Q with (hp_b | hp_d) | ⟨q, hq, rfl⟩
        · dsimp [S_b, S_box, h₀] at hp_b ⊢; omega
        · dsimp [S_d, S_box, h₀] at hp_d ⊢; omega
        · rcases hq with ⟨hq1, hq2, _⟩
          dsimp [wallShift, S_box, h₀]; omega
    rcases hz_PQ with hzP | hzQ
    · exact subwallRegionVerts_mono W (subset_union_left.trans hsub_box) (hVP_W_sub ⟨hzP, hzW⟩)
    · exact subwallRegionVerts_mono W (subset_union_right.trans hsub_box) (hVQ_W_sub ⟨hzQ, hzW⟩)

end GraphMinor.GM13
