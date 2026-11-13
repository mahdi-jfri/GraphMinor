module

public import GraphMinor.GM22.Section8To13c3
public import GraphMinor.GM13.Section7FourWalk
public import GraphMinor.GM13.Section7WallCells
public import GraphMinor.GM14.Section9a

/-!
# Derivation of Graph Minors XIII (10.2) from XXII (8.3), Part C4: Tangle Distance Bounds in
Subwalls

This file proves the two tangle-metric distance bounds needed to verify Hypotheses (xiii) and (xiv)
of Theorem (8.3) for a subwall `H'` of a Fig. 1 drawn wall `W`:
1. **Upper bound inside a height-`h` subwall (`hyp_xiii`)**: Any two vertices
   `v, w ∈ Γ.drawing.V ∩ ((fig1Sph φ ∘ shiftHomeo i₀ j₀) '' fig1EnclosedSet h)` satisfy
   `subsetTangleDist Γ.drawing W.height d {v} {w} ≤ 6 * h + 2`.
2. **Lower bound from a middle vertex of `H'` to `D_disc` (`hyp_xiv`)**: When
   `2 * (4 * θ + 11) ≤ H'.height`, both middle vertices `v_star` of `H'` satisfy
   `θ ≤ subsetTangleDist Γ.drawing W.height d {v_star} D_disc`.
-/

@[expose] public section

set_option autoImplicit false

namespace GraphMinor
namespace GM22

open Classical
open Set Function
open Graph
open Surface
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM13
open GraphMinor.GM14
open GraphMinor.GM16

universe u v

/-! ## 1. Brick Regions and Tangle Distance Upper Bound `≤ 6 * h + 2` (`hyp_xiii`) -/

/-- The open region in the sphere corresponding to the brick with lower-left corner `(x, y)`. -/
def brickReg (φ : EuclideanPlane ≃ₜ EuclideanPlane) (x y : ℕ) : Set (OnePoint EuclideanPlane) :=
  interior (fig1Sph φ '' fig1Brick x y)

/-- Each valid brick `IsFig1Brick W.height x y` defines a region `brickReg φ x y ∈ Γ.drawing.R`
whose closure is `fig1Sph φ '' fig1Brick x y`. -/
theorem brickReg_mem_R_and_closure {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    {x y : ℕ} (hb : IsFig1Brick W.height x y) :
    brickReg φ x y ∈ Γ.drawing.R ∧ closure (brickReg φ x y) = fig1Sph φ '' fig1Brick x y := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hf : Topology.IsEmbedding (fig1Sph φ) := (isOpenEmbedding_fig1Sph φ).isEmbedding
  obtain ⟨hD, hBd⟩ := discBd_image_fig1Brick hf x y
  refine GM16.empty_disc_is_region hS hD ?_ ?_
  · rw [hBd, hΓU]
    exact image_mono (frontier_brick_subset_fig1Set W.toWall.even_height hb.2.1 hb.2.2 hb.1)
  · rw [hΓU, Set.disjoint_left]
    intro z hz hzU
    obtain ⟨w, hw, rfl⟩ := GM16.interior_image_rectangle_subset hf _ _ _ _ hz
    obtain ⟨w', hw', hww'⟩ := hzU
    rw [hf.injective hww'] at hw'
    exact Set.disjoint_left.mp (disjoint_open_brick_fig1Set (h := W.height) hb.1) hw hw'

/-- If two regions `r₁, r₂ ∈ Γ.drawing.R` share a vertex `v ∈ Γ.drawing.V` in their closures,
then `d r₁ r₂ ≤ 2`. -/
theorem dist_regions_le_two_of_common_vertex {α : Type u} {β : Type v}
    {W : DrawnWall α β} {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {r₁ r₂ : Set (OnePoint EuclideanPlane)} (hr₁ : r₁ ∈ Γ.drawing.R) (hr₂ : r₂ ∈ Γ.drawing.R)
    {v : OnePoint EuclideanPlane} (hv : v ∈ Γ.drawing.V)
    (hv₁ : v ∈ closure r₁) (hv₂ : v ∈ closure r₂) :
    d r₁ r₂ ≤ 2 := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have h91 := GM11.gm15_theorem_9_1 Γ.drawing W.height T d hS inferInstance hd
  have hsymm := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hv_reg := h91.2.2.2.2.2.1
  have hE : Γ.drawing.E.Nonempty :=
    GM14.edgeSet_nonempty_of_isTangle hd.1.2.1 W.toWall.two_le_height
  have hr₁A : r₁ ∈ Γ.drawing.A := Or.inr hr₁
  have hr₂A : r₂ ∈ Γ.drawing.A := Or.inr hr₂
  have hvA : ({v} : Set (OnePoint EuclideanPlane)) ∈ Γ.drawing.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hd₁ : d r₁ {v} ≤ 1 := by
    rw [hsymm r₁ hr₁A {v} hvA]
    exact hv_reg hE v hv r₁ hr₁ hv₁
  have hd₂ : d {v} r₂ ≤ 1 := hv_reg hE v hv r₂ hr₂ hv₂
  have hle := htri r₁ hr₁A {v} hvA r₂ hr₂A
  omega

/-- The `(k, y)`-th brick region inside the shifted enclosed set `shiftHomeo i₀ j₀ '' fig1EnclosedSet h`. -/
def shiftedBrickReg (φ : EuclideanPlane ≃ₜ EuclideanPlane) (i₀ j₀ k y : ℕ) :
    Set (OnePoint EuclideanPlane) :=
  brickReg φ ((if Even y then 1 else 0) + 2 * k + i₀) (y + j₀)

theorem isFig1Brick_shiftedBrick {W_h h i₀ j₀ k y : ℕ}
    (hh_le : h ≤ W_h) (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀ : i₀ ≤ 2 * W_h - 2 * h) (hj₀ : j₀ ≤ W_h - h)
    (hk : k < h) (hy : y < h) :
    IsFig1Brick W_h ((if Even y then 1 else 0) + 2 * k + i₀) (y + j₀) := by
  refine isFig1Brick_shift hh_le hi₀_even hj₀_even hi₀ hj₀ ⟨?_, ?_, by omega⟩
  · by_cases hye : Even y
    · obtain ⟨t, ht⟩ := hye
      rw [ite_eq_left ⟨t, ht⟩]
      exact ⟨k + t, by omega⟩
    · obtain ⟨t, ht⟩ := Nat.not_even_iff_odd.mp hye
      rw [ite_eq_right hye]
      exact ⟨k + t, by omega⟩
  · split_ifs <;> omega

/-- Horizontally adjacent shifted bricks `(k, y)` and `(k + 1, y)` have `d`-distance at most `2`. -/
theorem dist_shiftedBrickReg_horiz_step {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {h i₀ j₀ k y : ℕ}
    (hh_le : h ≤ W.height) (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀ : i₀ ≤ 2 * W.height - 2 * h) (hj₀ : j₀ ≤ W.height - h)
    (hk : k + 1 < h) (hy : y < h) :
    d (shiftedBrickReg φ i₀ j₀ k y) (shiftedBrickReg φ i₀ j₀ (k + 1) y) ≤ 2 := by
  have hb₁ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ (by omega : k < h) hy
  have hb₂ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk hy
  obtain ⟨hr₁, hcl₁⟩ := brickReg_mem_R_and_closure hΓU hb₁
  obtain ⟨hr₂, hcl₂⟩ := brickReg_mem_R_and_closure hΓU hb₂
  let x₁ := (if Even y then 1 else 0) + 2 * k + i₀
  let p : ℕ × ℕ := (x₁ + 2, y + j₀)
  have hp : p ∈ elementaryWallVerts W.height := by
    have hx₁ : x₁ + 2 ≤ 2 * W.height + 1 := hb₁.2.1
    have hy₁ : y + j₀ + 1 ≤ W.height := hb₁.2.2
    dsimp [p, elementaryWallVerts]
    refine ⟨hx₁, by omega, ?_, ?_⟩ <;>
      (simp only [Prod.mk.injEq, not_and]; omega)
  have huW : W.branchVertex p hp ∈ V(W.graph) := W.toWall.branchVertex_mem_graph p hp
  have hvV : fig1Sph φ (pos (W.branchVertex p hp)) ∈ Γ.drawing.V := by
    rw [← hΓv ⟨W.branchVertex p hp, huW⟩]
    exact (Γ.iso.vertexEquiv _).2
  refine dist_regions_le_two_of_common_vertex hd hr₁ hr₂ hvV ?_ ?_
  · rw [shiftedBrickReg, hcl₁, hpos_branch p hp]
    refine ⟨GM16.latticePoint p, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change (x₁ : ℝ) ≤ ((x₁ + 2 : ℕ) : ℝ); push_cast; linarith
    · change ((x₁ + 2 : ℕ) : ℝ) ≤ (x₁ : ℝ) + 2; push_cast; linarith
    · change ((y + j₀ : ℕ) : ℝ) ≤ ((y + j₀ : ℕ) : ℝ); linarith
    · change ((y + j₀ : ℕ) : ℝ) ≤ ((y + j₀ : ℕ) : ℝ) + 1; linarith
  · rw [shiftedBrickReg, hcl₂, hpos_branch p hp]
    have hx₂_eq : (if Even y then 1 else 0) + 2 * (k + 1) + i₀ = x₁ + 2 := by dsimp [x₁]; omega
    rw [hx₂_eq]
    refine ⟨GM16.latticePoint p, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change ((x₁ + 2 : ℕ) : ℝ) ≤ ((x₁ + 2 : ℕ) : ℝ); linarith
    · change ((x₁ + 2 : ℕ) : ℝ) ≤ ((x₁ + 2 : ℕ) : ℝ) + 2; linarith
    · change ((y + j₀ : ℕ) : ℝ) ≤ ((y + j₀ : ℕ) : ℝ); linarith
    · change ((y + j₀ : ℕ) : ℝ) ≤ ((y + j₀ : ℕ) : ℝ) + 1; linarith

/-- Vertically adjacent shifted bricks `(0, y)` and `(0, y + 1)` have `d`-distance at most `2`. -/
theorem dist_shiftedBrickReg_vert_step {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {h i₀ j₀ y : ℕ}
    (hh_le : h ≤ W.height) (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀ : i₀ ≤ 2 * W.height - 2 * h) (hj₀ : j₀ ≤ W.height - h)
    (hy : y + 1 < h) :
    d (shiftedBrickReg φ i₀ j₀ 0 y) (shiftedBrickReg φ i₀ j₀ 0 (y + 1)) ≤ 2 := by
  have hk0 : 0 < h := by omega
  have hb₁ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 (by omega : y < h)
  have hb₂ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hy
  obtain ⟨hr₁, hcl₁⟩ := brickReg_mem_R_and_closure hΓU hb₁
  obtain ⟨hr₂, hcl₂⟩ := brickReg_mem_R_and_closure hΓU hb₂
  let p : ℕ × ℕ := (1 + i₀, y + 1 + j₀)
  have hp : p ∈ elementaryWallVerts W.height := by
    dsimp [p, elementaryWallVerts]
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      (simp only [Prod.mk.injEq, not_and]; omega)
  have huW : W.branchVertex p hp ∈ V(W.graph) := W.toWall.branchVertex_mem_graph p hp
  have hvV : fig1Sph φ (pos (W.branchVertex p hp)) ∈ Γ.drawing.V := by
    rw [← hΓv ⟨W.branchVertex p hp, huW⟩]
    exact (Γ.iso.vertexEquiv _).2
  refine dist_regions_le_two_of_common_vertex hd hr₁ hr₂ hvV ?_ ?_
  · rw [shiftedBrickReg, hcl₁, hpos_branch p hp]
    refine ⟨GM16.latticePoint p, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change (((if Even y then 1 else 0) + 2 * 0 + i₀ : ℕ) : ℝ) ≤ ((1 + i₀ : ℕ) : ℝ)
      have : (if Even y then 1 else 0) + 2 * 0 + i₀ ≤ 1 + i₀ := by split_ifs <;> omega
      exact_mod_cast this
    · change ((1 + i₀ : ℕ) : ℝ) ≤ (((if Even y then 1 else 0) + 2 * 0 + i₀ : ℕ) : ℝ) + 2
      have : 1 + i₀ ≤ (if Even y then 1 else 0) + 2 * 0 + i₀ + 2 := by split_ifs <;> omega
      exact_mod_cast this
    · change ((y + j₀ : ℕ) : ℝ) ≤ ((y + 1 + j₀ : ℕ) : ℝ); push_cast; linarith
    · change ((y + 1 + j₀ : ℕ) : ℝ) ≤ ((y + j₀ : ℕ) : ℝ) + 1; push_cast; linarith
  · rw [shiftedBrickReg, hcl₂, hpos_branch p hp]
    refine ⟨GM16.latticePoint p, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change (((if Even (y + 1) then 1 else 0) + 2 * 0 + i₀ : ℕ) : ℝ) ≤ ((1 + i₀ : ℕ) : ℝ)
      have : (if Even (y + 1) then 1 else 0) + 2 * 0 + i₀ ≤ 1 + i₀ := by split_ifs <;> omega
      exact_mod_cast this
    · change ((1 + i₀ : ℕ) : ℝ) ≤ (((if Even (y + 1) then 1 else 0) + 2 * 0 + i₀ : ℕ) : ℝ) + 2
      have : 1 + i₀ ≤ (if Even (y + 1) then 1 else 0) + 2 * 0 + i₀ + 2 := by split_ifs <;> omega
      exact_mod_cast this
    · change ((y + 1 + j₀ : ℕ) : ℝ) ≤ ((y + 1 + j₀ : ℕ) : ℝ); linarith
    · change ((y + 1 + j₀ : ℕ) : ℝ) ≤ ((y + 1 + j₀ : ℕ) : ℝ) + 1; linarith

/-- By induction on `k < h`, `d (shiftedBrickReg φ i₀ j₀ 0 y) (shiftedBrickReg φ i₀ j₀ k y) ≤ 2 * k`. -/
theorem dist_shiftedBrickReg_horiz {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {h i₀ j₀ k y : ℕ}
    (hh_le : h ≤ W.height) (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀ : i₀ ≤ 2 * W.height - 2 * h) (hj₀ : j₀ ≤ W.height - h)
    (hk : k < h) (hy : y < h) :
    d (shiftedBrickReg φ i₀ j₀ 0 y) (shiftedBrickReg φ i₀ j₀ k y) ≤ 2 * k := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have h91 := GM11.gm15_theorem_9_1 Γ.drawing W.height T d hS inferInstance hd
  have hrefl := h91.2.1
  have htri := h91.2.2.2.2.1
  induction k with
  | zero =>
    have hb₀ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk hy
    have hr₀A : shiftedBrickReg φ i₀ j₀ 0 y ∈ Γ.drawing.A :=
      Or.inr (brickReg_mem_R_and_closure hΓU hb₀).1
    rw [hrefl _ hr₀A]
  | succ k ih =>
    have hk' : k < h := by omega
    have hstep := dist_shiftedBrickReg_horiz_step hpos_branch hΓU hΓv hd
      hh_le hi₀_even hj₀_even hi₀ hj₀ hk hy
    have hb₀ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ (by omega : 0 < h) hy
    have hbk := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk' hy
    have hbk1 := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk hy
    have hr₀ : shiftedBrickReg φ i₀ j₀ 0 y ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₀).1
    have hrk : shiftedBrickReg φ i₀ j₀ k y ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hbk).1
    have hrk1 : shiftedBrickReg φ i₀ j₀ (k + 1) y ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hbk1).1
    have hle := htri _ (Or.inr hr₀) _ (Or.inr hrk) _ (Or.inr hrk1)
    have hih := ih hk'
    omega

/-- By induction on `y < h`, `d (shiftedBrickReg φ i₀ j₀ 0 0) (shiftedBrickReg φ i₀ j₀ 0 y) ≤ 2 * y`. -/
theorem dist_shiftedBrickReg_vert {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {h i₀ j₀ y : ℕ}
    (hh_le : h ≤ W.height) (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀ : i₀ ≤ 2 * W.height - 2 * h) (hj₀ : j₀ ≤ W.height - h)
    (hy : y < h) :
    d (shiftedBrickReg φ i₀ j₀ 0 0) (shiftedBrickReg φ i₀ j₀ 0 y) ≤ 2 * y := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have h91 := GM11.gm15_theorem_9_1 Γ.drawing W.height T d hS inferInstance hd
  have hrefl := h91.2.1
  have htri := h91.2.2.2.2.1
  have hk0 : 0 < h := by omega
  induction y with
  | zero =>
    have hb₀ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hy
    have hr₀A : shiftedBrickReg φ i₀ j₀ 0 0 ∈ Γ.drawing.A :=
      Or.inr (brickReg_mem_R_and_closure hΓU hb₀).1
    rw [hrefl _ hr₀A]
  | succ y ih =>
    have hy' : y < h := by omega
    have hstep := dist_shiftedBrickReg_vert_step hpos_branch hΓU hΓv hd
      hh_le hi₀_even hj₀_even hi₀ hj₀ hy
    have hb₀ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hk0
    have hby := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hy'
    have hby1 := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hy
    have hr₀ : shiftedBrickReg φ i₀ j₀ 0 0 ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₀).1
    have hry : shiftedBrickReg φ i₀ j₀ 0 y ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hby).1
    have hry1 : shiftedBrickReg φ i₀ j₀ 0 (y + 1) ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hby1).1
    have hle := htri _ (Or.inr hr₀) _ (Or.inr hry) _ (Or.inr hry1)
    have hih := ih hy'
    omega

/-- **Tangle distance upper bound inside a shifted `fig1EnclosedSet h` (`hyp_xiii`)**:
Any two vertices `v, w ∈ Γ.drawing.V` belonging to `(fig1Sph φ ∘ shiftHomeo i₀ j₀) '' fig1EnclosedSet h`
satisfy `d {v} {w} ≤ 8 * h + 2` and `subsetTangleDist Γ.drawing W.height d {v} {w} ≤ 8 * h + 2`. -/
theorem subsetTangleDist_le_of_mem_shifted_enclosed {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {h i₀ j₀ : ℕ}
    (hh_le : h ≤ W.height) (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀ : i₀ ≤ 2 * W.height - 2 * h) (hj₀ : j₀ ≤ W.height - h)
    {v w : OnePoint EuclideanPlane} (hvV : v ∈ Γ.drawing.V) (hwV : w ∈ Γ.drawing.V)
    (hv_enc : v ∈ (fig1Sph φ ∘ shiftHomeo i₀ j₀) '' fig1EnclosedSet h)
    (hw_enc : w ∈ (fig1Sph φ ∘ shiftHomeo i₀ j₀) '' fig1EnclosedSet h) :
    d {v} {w} ≤ 8 * h + 2 ∧
    subsetTangleDist Γ.drawing W.height d {v} {w} ≤ 8 * h + 2 := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have h91 := GM11.gm15_theorem_9_1 Γ.drawing W.height T d hS inferInstance hd
  have hsymm := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hv_reg := h91.2.2.2.2.2.1
  have hE : Γ.drawing.E.Nonempty :=
    GM14.edgeSet_nonempty_of_isTangle hd.1.2.1 W.toWall.two_le_height
  -- Find shifted bricks containing `v` and `w`
  have hex_brick : ∀ u : OnePoint EuclideanPlane,
      u ∈ (fig1Sph φ ∘ shiftHomeo i₀ j₀) '' fig1EnclosedSet h →
      ∃ k < h, ∃ y < h, u ∈ closure (shiftedBrickReg φ i₀ j₀ k y) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hzRow⟩ := mem_iUnion₂.mp hz
    have hh1 : 1 ≤ h := by omega
    set L : ℕ := if Even y then 1 else 0 with hL
    have hLr : fig1RowLeft y = (L : ℝ) := by
      simp only [fig1RowLeft, hL]; split_ifs <;> simp
    have hRow : z ∈ Icc (L : ℝ) ((L : ℝ) + 2 * (h : ℝ)) ×ˢ Icc (y : ℝ) ((y : ℝ) + 1) := by
      simpa only [fig1RowRight, hLr, add_comm (2 * (h : ℝ))] using hzRow
    have hTile := GM16.rectangle_eq_union_width_two (L : ℝ) (y : ℝ) ((y : ℝ) + 1) hh1
    obtain ⟨k, hk, hzB⟩ := mem_iUnion₂.mp (hTile ▸ hRow)
    have hbrick : z ∈ fig1Brick (L + 2 * k) y := by
      simpa only [fig1Brick, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hzB
    have hb := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk hy
    obtain ⟨_, hcl⟩ := brickReg_mem_R_and_closure hΓU hb
    refine ⟨k, hk, y, hy, ?_⟩
    change fig1Sph φ (shiftHomeo i₀ j₀ z) ∈ closure (shiftedBrickReg φ i₀ j₀ k y)
    rw [shiftedBrickReg, hcl, ← shiftHomeo_image_fig1Brick]
    exact ⟨shiftHomeo i₀ j₀ z, ⟨z, hbrick, rfl⟩, rfl⟩
  obtain ⟨k₁, hk₁, y₁, hy₁, hv_cl⟩ := hex_brick v hv_enc
  obtain ⟨k₂, hk₂, y₂, hy₂, hw_cl⟩ := hex_brick w hw_enc
  have hk0 : 0 < h := by omega
  have hb₀₀ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hk0
  have hb₀₁ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hy₁
  have hb₁ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk₁ hy₁
  have hb₀₂ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk0 hy₂
  have hb₂ := isFig1Brick_shiftedBrick hh_le hi₀_even hj₀_even hi₀ hj₀ hk₂ hy₂
  have hr₀₀ : shiftedBrickReg φ i₀ j₀ 0 0 ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₀₀).1
  have hr₀₁ : shiftedBrickReg φ i₀ j₀ 0 y₁ ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₀₁).1
  have hr₁ : shiftedBrickReg φ i₀ j₀ k₁ y₁ ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₁).1
  have hr₀₂ : shiftedBrickReg φ i₀ j₀ 0 y₂ ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₀₂).1
  have hr₂ : shiftedBrickReg φ i₀ j₀ k₂ y₂ ∈ Γ.drawing.R := (brickReg_mem_R_and_closure hΓU hb₂).1
  have hvA : ({v} : Set (OnePoint EuclideanPlane)) ∈ Γ.drawing.A := Or.inl (Or.inl ⟨v, hvV, rfl⟩)
  have hwA : ({w} : Set (OnePoint EuclideanPlane)) ∈ Γ.drawing.A := Or.inl (Or.inl ⟨w, hwV, rfl⟩)
  have hd_v_r₁ : d {v} (shiftedBrickReg φ i₀ j₀ k₁ y₁) ≤ 1 := hv_reg hE v hvV _ hr₁ hv_cl
  have hd_r₂_w : d (shiftedBrickReg φ i₀ j₀ k₂ y₂) {w} ≤ 1 := by
    rw [hsymm _ (Or.inr hr₂) {w} hwA]
    exact hv_reg hE w hwV _ hr₂ hw_cl
  have hd_r₁_0 : d (shiftedBrickReg φ i₀ j₀ k₁ y₁) (shiftedBrickReg φ i₀ j₀ 0 y₁) ≤ 2 * k₁ := by
    rw [hsymm _ (Or.inr hr₁) _ (Or.inr hr₀₁)]
    exact dist_shiftedBrickReg_horiz hpos_branch hΓU hΓv hd hh_le hi₀_even hj₀_even hi₀ hj₀ hk₁ hy₁
  have hd_01_00 : d (shiftedBrickReg φ i₀ j₀ 0 y₁) (shiftedBrickReg φ i₀ j₀ 0 0) ≤ 2 * y₁ := by
    rw [hsymm _ (Or.inr hr₀₁) _ (Or.inr hr₀₀)]
    exact dist_shiftedBrickReg_vert hpos_branch hΓU hΓv hd hh_le hi₀_even hj₀_even hi₀ hj₀ hy₁
  have hd_00_02 : d (shiftedBrickReg φ i₀ j₀ 0 0) (shiftedBrickReg φ i₀ j₀ 0 y₂) ≤ 2 * y₂ :=
    dist_shiftedBrickReg_vert hpos_branch hΓU hΓv hd hh_le hi₀_even hj₀_even hi₀ hj₀ hy₂
  have hd_02_r₂ : d (shiftedBrickReg φ i₀ j₀ 0 y₂) (shiftedBrickReg φ i₀ j₀ k₂ y₂) ≤ 2 * k₂ :=
    dist_shiftedBrickReg_horiz hpos_branch hΓU hΓv hd hh_le hi₀_even hj₀_even hi₀ hj₀ hk₂ hy₂
  have ht₁ := htri {v} hvA _ (Or.inr hr₁) {w} hwA
  have ht₂ := htri _ (Or.inr hr₁) _ (Or.inr hr₀₁) {w} hwA
  have ht₃ := htri _ (Or.inr hr₀₁) _ (Or.inr hr₀₀) {w} hwA
  have ht₄ := htri _ (Or.inr hr₀₀) _ (Or.inr hr₀₂) {w} hwA
  have ht₅ := htri _ (Or.inr hr₀₂) _ (Or.inr hr₂) {w} hwA
  have hd_vw : d {v} {w} ≤ 8 * h + 2 := by omega
  refine ⟨hd_vw, ?_⟩
  unfold subsetTangleDist
  have hex : ∃ a ∈ Γ.drawing.A, ∃ b ∈ Γ.drawing.A,
      (a ∩ {v}).Nonempty ∧ (b ∩ {w}).Nonempty :=
    ⟨{v}, hvA, {w}, hwA, ⟨v, rfl, rfl⟩, ⟨w, rfl, rfl⟩⟩
  have hmem_sInf : d {v} {w} ∈ {k : ℕ | ∃ a ∈ Γ.drawing.A, ∃ b ∈ Γ.drawing.A,
      (a ∩ {v}).Nonempty ∧ (b ∩ {w}).Nonempty ∧ d a b = k} :=
    ⟨{v}, hvA, {w}, hwA, ⟨v, rfl, rfl⟩, ⟨w, rfl, rfl⟩, rfl⟩
  rw [ite_eq_left hex]
  exact (Nat.sInf_le hmem_sInf).trans hd_vw

/-! ## 2. Middle Vertex Tangle Distance Lower Bound (`hyp_xiv`) -/

/-- Every square `q ∈ squaresAbove (cellCode z)` has `q = (2 * x + 1, 2 * y + 1)` with
`(x : ℝ) ≤ z.1 ≤ (x : ℝ) + 1` and `(y : ℝ) ≤ z.2 ≤ (y : ℝ) + 1`. -/
theorem mem_squaresAbove_coord_bounds {z : ℝ × ℝ} {q : ℤ × ℤ}
    (hq : q ∈ squaresAbove (cellCode z)) :
    ∃ x y : ℤ, q = (2 * x + 1, 2 * y + 1) ∧
      (x : ℝ) ≤ z.1 ∧ z.1 ≤ (x : ℝ) + 1 ∧
      (y : ℝ) ≤ z.2 ∧ z.2 ≤ (y : ℝ) + 1 := by
  obtain ⟨x, y, hq_eq, hx1, hx2, hy1, hy2, -, -⟩ := exists_of_mem_squaresAbove hq
  change 2 * x ≤ cellCode1 z.1 at hx1
  change cellCode1 z.1 ≤ 2 * x + 2 at hx2
  change 2 * y ≤ cellCode1 z.2 at hy1
  change cellCode1 z.2 ≤ 2 * y + 2 at hy2
  refine ⟨x, y, hq_eq, ?_, ?_, ?_, ?_⟩
  · rcases cellCode1_cases z.1 with ⟨i, hc, hzi⟩ | ⟨i, hc, hzi1, hzi2⟩
    · have : x ≤ i := by omega
      have hcast : (x : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
      linarith
    · have : x ≤ i := by omega
      have hcast : (x : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
      linarith
  · rcases cellCode1_cases z.1 with ⟨i, hc, hzi⟩ | ⟨i, hc, hzi1, hzi2⟩
    · have : i ≤ x + 1 := by omega
      have hcast : (i : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast this
      linarith
    · have : i ≤ x := by omega
      have hcast : (i : ℝ) ≤ (x : ℝ) := by exact_mod_cast this
      linarith
  · rcases cellCode1_cases z.2 with ⟨i, hc, hzi⟩ | ⟨i, hc, hzi1, hzi2⟩
    · have : y ≤ i := by omega
      have hcast : (y : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
      linarith
    · have : y ≤ i := by omega
      have hcast : (y : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
      linarith
  · rcases cellCode1_cases z.2 with ⟨i, hc, hzi⟩ | ⟨i, hc, hzi1, hzi2⟩
    · have : i ≤ y + 1 := by omega
      have hcast : (i : ℝ) ≤ (y : ℝ) + 1 := by exact_mod_cast this
      linarith
    · have : i ≤ y := by omega
      have hcast : (i : ℝ) ≤ (y : ℝ) := by exact_mod_cast this
      linarith

/-- Lower bound on `planeWallDist` from a shifted middle coordinate `s` of `H'` (where
`H'.height = 2 * m'`) to any coordinate `t` outside the shifted open inner rectangle
`Ioo (i' + 1) (i' + 4 * m') ×ˢ Ioo j' (j' + 2 * m')`. -/
theorem le_planeWallDist_of_shifted_middle {W_h m' i' j' : ℕ}
    (hWh_even : Even W_h) (hm'2 : 2 ≤ m') (hm'_le : 2 * m' ≤ W_h)
    (hi' : i' ≤ 2 * W_h - 4 * m') (hj' : j' ≤ W_h - 2 * m')
    {s t : ℝ × ℝ}
    (hs1 : ((i' + 2 * m' : ℕ) : ℝ) ≤ s.1 ∧ s.1 ≤ ((i' + 2 * m' + 1 : ℕ) : ℝ))
    (hs2 : s.2 = ((j' + m' : ℕ) : ℝ))
    (ht : t.1 ≤ (i' : ℝ) + 1 ∨ (i' : ℝ) + 4 * (m' : ℝ) ≤ t.1 ∨
      t.2 ≤ (j' : ℝ) ∨ (j' : ℝ) + 2 * (m' : ℝ) ≤ t.2) :
    m' - 2 ≤ planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W_h))
      (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
  have hWh1 : 1 ≤ W_h := by omega
  -- First show `cellCode s ≠ cellCode t`
  have hst : cellCode s ≠ cellCode t := by
    intro heq
    have hq_s := cellUp_mem_squaresAbove (cellCode s)
    have hq_t : cellUp (cellCode s) ∈ squaresAbove (cellCode t) := heq ▸ hq_s
    obtain ⟨x_s, y_s, hq1, hxs1, hxs2, hys1, hys2⟩ := mem_squaresAbove_coord_bounds hq_s
    obtain ⟨x_t, y_t, hq2, hxt1, hxt2, hyt1, hyt2⟩ := mem_squaresAbove_coord_bounds hq_t
    have hxy_eq : x_s = x_t ∧ y_s = y_t := by
      have := hq1.symm.trans hq2
      simp only [Prod.mk.injEq] at this
      omega
    rcases hxy_eq with ⟨rfl, rfl⟩
    push_cast at hs1 hs2
    have hm'_r : (2 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hm'2
    rcases ht with ht1 | ht1 | ht2 | ht2 <;> linarith
  obtain ⟨q, hq, q', hq', hle⟩ := le_planeWallDist_fig1 hWh1 hWh_even hst
  obtain ⟨x_s, y_s, rfl, hxs1, hxs2, hys1, hys2⟩ := mem_squaresAbove_coord_bounds hq
  obtain ⟨x_t, y_t, rfl, hxt1, hxt2, hyt1, hyt2⟩ := mem_squaresAbove_coord_bounds hq'
  -- Bound `x_s, y_s` in `ℤ`
  have hxs_lo : (i' : ℤ) + 2 * (m' : ℤ) - 1 ≤ x_s := by
    have : ((i' : ℤ) + 2 * (m' : ℤ) - 1 : ℝ) < (x_s : ℝ) + 1 := by
      push_cast at hs1 ⊢; linarith [hs1.1]
    have hlt : (i' : ℤ) + 2 * (m' : ℤ) - 1 < x_s + 1 := by exact_mod_cast this
    omega
  have hxs_hi : x_s ≤ (i' : ℤ) + 2 * (m' : ℤ) + 1 := by
    have : (x_s : ℝ) < ((i' : ℤ) + 2 * (m' : ℤ) + 2 : ℝ) := by
      push_cast at hs1 ⊢; linarith [hs1.2]
    have hlt : x_s < (i' : ℤ) + 2 * (m' : ℤ) + 2 := by exact_mod_cast this
    omega
  have hys_lo : (j' : ℤ) + (m' : ℤ) - 1 ≤ y_s := by
    have : ((j' : ℤ) + (m' : ℤ) - 1 : ℝ) < (y_s : ℝ) + 1 := by
      push_cast at hs2 ⊢; linarith
    have hlt : (j' : ℤ) + (m' : ℤ) - 1 < y_s + 1 := by exact_mod_cast this
    omega
  have hys_hi : y_s ≤ (j' : ℤ) + (m' : ℤ) := by
    have : (y_s : ℝ) < ((j' : ℤ) + (m' : ℤ) + 1 : ℝ) := by
      push_cast at hs2 ⊢; linarith
    have hlt : y_s < (j' : ℤ) + (m' : ℤ) + 1 := by exact_mod_cast this
    omega
  -- Bound `x_t, y_t` in `ℤ`
  have hxt_yt : x_t ≤ (i' : ℤ) + 1 ∨ (i' : ℤ) + 4 * (m' : ℤ) - 1 ≤ x_t ∨
      y_t ≤ (j' : ℤ) ∨ (j' : ℤ) + 2 * (m' : ℤ) - 1 ≤ y_t := by
    rcases ht with ht1 | ht1 | ht2 | ht2
    · left
      have : (x_t : ℝ) < ((i' : ℤ) + 2 : ℝ) := by push_cast; linarith
      have hlt : x_t < (i' : ℤ) + 2 := by exact_mod_cast this
      omega
    · right; left
      have : ((i' : ℤ) + 4 * (m' : ℤ) - 1 : ℝ) < (x_t : ℝ) + 1 := by push_cast; linarith
      have hlt : (i' : ℤ) + 4 * (m' : ℤ) - 1 < x_t + 1 := by exact_mod_cast this
      omega
    · right; right; left
      have : (y_t : ℝ) < ((j' : ℤ) + 1 : ℝ) := by push_cast; linarith
      have hlt : y_t < (j' : ℤ) + 1 := by exact_mod_cast this
      omega
    · right; right; right
      have : ((j' : ℤ) + 2 * (m' : ℤ) - 1 : ℝ) < (y_t : ℝ) + 1 := by push_cast; linarith
      have hlt : (j' : ℤ) + 2 * (m' : ℤ) - 1 < y_t + 1 := by exact_mod_cast this
      omega
  set u_s : ℤ := x_s + (x_s + y_s) % 2
  set u_t : ℤ := x_t + (x_t + y_t) % 2
  have hu_s_lo : x_s ≤ u_s := by
    have : 0 ≤ (x_s + y_s) % 2 := Int.emod_nonneg _ (by decide)
    omega
  have hu_s_hi : u_s ≤ x_s + 1 := by
    have : (x_s + y_s) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    omega
  have hu_t_lo : x_t ≤ u_t := by
    have : 0 ≤ (x_t + y_t) % 2 := Int.emod_nonneg _ (by decide)
    omega
  have hu_t_hi : u_t ≤ x_t + 1 := by
    have : (x_t + y_t) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    omega
  have hb_s : 0 ≤ y_s ∧ y_s < (W_h : ℤ) ∧
      1 ≤ u_s ∧ u_s ≤ 2 * (W_h : ℤ) := by omega
  have hF_ne : (u_s, y_s) ≠ outFace := by
    simp only [outFace, ne_eq, Prod.mk.injEq, not_and]; omega
  have hout_s : (m' : ℤ) - 2 ≤ outDepth W_h (u_s, y_s) := by
    unfold outDepth
    dsimp only
    clear *- hm'2 hm'_le hi' hj' hxs_lo hxs_hi hys_lo hys_hi hu_s_lo hu_s_hi
    omega
  have hdir_st : (m' : ℤ) - 2 ≤ hexDist (u_s, y_s) (u_t, y_t) := by
    unfold hexDist
    dsimp only
    clear *- hm'2 hxs_lo hxs_hi hys_lo hys_hi hu_s_lo hu_s_hi hu_t_lo hu_t_hi hxt_yt
    omega
  have hface : m' - 2 ≤
      (faceDist W_h (wallFace W_h (2 * x_s + 1, 2 * y_s + 1))
        (wallFace W_h (2 * x_t + 1, 2 * y_t + 1))).toNat := by
    rw [wallFace_square, ite_eq_left hb_s, wallFace_square]
    split_ifs with hb_t
    · have hG_ne : (u_t, y_t) ≠ outFace := by
        simp only [outFace, ne_eq, Prod.mk.injEq, not_and]; omega
      rw [faceDist_of_ne hF_ne hG_ne]
      have hout_t : 0 ≤ outDepth W_h (u_t, y_t) := by
        unfold outDepth; dsimp only; clear *- hb_t; omega
      clear *- hout_s hdir_st hout_t
      omega
    · rw [faceDist_out_right hF_ne]
      clear *- hout_s
      omega
  clear *- hface hle
  omega

/-- Every region `r ∈ Γ.drawing.R` of the Fig. 1 sphere drawing `Γ` equals either
`brickReg φ x y` for some `IsFig1Brick W.height x y` or the outer region `r₀`, and in either case
contains a vertex `fig1Sph φ (pos u)` (`u ∈ V(W.graph)`) in its closure. -/
theorem exists_vertex_mem_closure_of_region {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.drawing.R) :
    ∃ u ∈ V(W.graph), fig1Sph φ (pos u) ∈ closure r := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hf : Topology.IsOpenEmbedding (fig1Sph φ) := isOpenEmbedding_fig1Sph φ
  have he : Even W.height := W.toWall.even_height
  have hh2 : 2 ≤ W.height := W.toWall.two_le_height
  obtain ⟨z, hzr⟩ := GM11.region_nonempty hr
  have hzU : z ∉ Γ.drawing.U := GM11.region_subset hr hzr
  by_cases hzE : z ∈ fig1Sph φ '' fig1EnclosedSet W.height
  · obtain ⟨p, hp, rfl⟩ := hzE
    obtain ⟨x, y, hb, hpB⟩ := exists_fig1Brick_of_mem_enclosed hp
    have hpOpen : p ∈ Ioo (x : ℝ) ((x : ℝ) + 2) ×ˢ Ioo (y : ℝ) ((y : ℝ) + 1) := by
      rw [← interior_Icc, ← interior_Icc, ← interior_prod_eq]
      by_contra hfr
      apply hzU
      rw [hΓU]
      exact mem_image_of_mem (fig1Sph φ)
        (frontier_brick_subset_fig1Set he hb.2.1 hb.2.2 hb.1 ⟨subset_closure hpB, hfr⟩)
    have hInt : fig1Sph φ p ∈ brickReg φ x y := by
      refine interior_maximal (image_mono ?_) (hf.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo))
        (mem_image_of_mem (fig1Sph φ) hpOpen)
      exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
    obtain ⟨hrB, hclB⟩ := brickReg_mem_R_and_closure hΓU hb
    have hr_eq : r = brickReg φ x y := GM11.region_eq_of_mem hr hrB hzr hInt
    let q : ℕ × ℕ := (x + 2, y)
    have hq : q ∈ elementaryWallVerts W.height := by
      have hx2 := hb.2.1
      have hy1 := hb.2.2
      dsimp [q, elementaryWallVerts]
      refine ⟨hx2, by omega, ?_, ?_⟩ <;>
        (simp only [Prod.mk.injEq, not_and]; omega)
    refine ⟨W.branchVertex q hq, W.toWall.branchVertex_mem_graph q hq, ?_⟩
    rw [hr_eq, hclB, hpos_branch q hq]
    refine ⟨GM16.latticePoint q, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change (x : ℝ) ≤ ((x + 2 : ℕ) : ℝ); push_cast; linarith
    · change ((x + 2 : ℕ) : ℝ) ≤ (x : ℝ) + 2; push_cast; linarith
    · change (y : ℝ) ≤ (y : ℝ); linarith
    · change (y : ℝ) ≤ (y : ℝ) + 1; linarith
  · let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
    have hC := isClosedDisc_image_fig1EnclosedSet hS hf.isEmbedding (by omega : 1 ≤ W.height)
    obtain ⟨hD, hBd, hCup, hMeet⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hSph hC
    have hDrawing : Γ.drawing.U ⊆ E₀ := by
      rw [hΓU]; exact image_mono (fig1Set_subset_enclosed he hh2)
    have hzD : z ∈ closure E₀ᶜ := (hCup.ge (mem_univ z)).resolve_left hzE
    have hzInt : z ∈ interior (closure E₀ᶜ) := by
      by_contra hn
      have hzFr : z ∈ frontier (closure E₀ᶜ) := ⟨subset_closure hzD, hn⟩
      have hzBd := GM11.IsClosedDisc.frontier_eq_discBd hS hD ▸ hzFr
      exact hzE (Surface.discBd_subset _ (hBd ▸ hzBd))
    have hBdU : discBd (closure E₀ᶜ) ⊆ Γ.drawing.U := by
      rw [hBd, hΓU]; exact discBd_image_enclosed_subset hS hf.isEmbedding he hh2
    have hEmpty : Disjoint (interior (closure E₀ᶜ)) Γ.drawing.U := by
      refine Set.disjoint_left.mpr fun w hwInt hwU => ?_
      have hwBd : w ∈ discBd E₀ := hMeet ▸ ⟨hDrawing hwU, interior_subset hwInt⟩
      have hwFr : w ∈ frontier (closure E₀ᶜ) :=
        (GM11.IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ (hBd.symm ▸ hwBd)
      exact hwFr.2 hwInt
    obtain ⟨hr₀, hcl_r₀⟩ := GM16.empty_disc_is_region hS hD hBdU hEmpty
    have hr_eq : r = interior (closure E₀ᶜ) := GM11.region_eq_of_mem hr hr₀ hzr hzInt
    let q : ℕ × ℕ := (1, 0)
    have hq : q ∈ elementaryWallVerts W.height := by
      dsimp [q, elementaryWallVerts]
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
        (simp only [Prod.mk.injEq, not_and]; omega)
    have hq_perim : q ∈ elementaryWallPerimeterVerts W.height := ⟨hq, Or.inl rfl⟩
    refine ⟨W.branchVertex q hq, W.toWall.branchVertex_mem_graph q hq, ?_⟩
    rw [hr_eq, hcl_r₀, closure_compl]
    change fig1Sph φ (pos (W.branchVertex q hq)) ∉ interior E₀
    rw [interior_image_eq_of_isOpenEmbedding hf, hpos_branch q hq]
    rintro ⟨w, hw_int, hweq⟩
    rw [hf.injective hweq] at hw_int
    obtain ⟨q', hq'_perim, hadj⟩ := exists_perimeter_adj_of_mem_perimeterVerts hh2 he hq_perim
    have hseg : GM16.latticePoint q ∈ fig1Segment q q' := by
      rcases hadj.2.2 with ⟨hy, hx⟩ | ⟨hx, hy⟩
      · unfold fig1Segment
        rw [ite_eq_left hy]
        refine ⟨⟨?_, ?_⟩, by simp [GM16.latticePoint, hy]⟩
        · change ((min q.1 q'.1 : ℕ) : ℝ) ≤ (q.1 : ℝ); exact_mod_cast Nat.min_le_left _ _
        · change (q.1 : ℝ) ≤ ((min q.1 q'.1 : ℕ) : ℝ) + 1
          have : q.1 ≤ min q.1 q'.1 + 1 := by rcases hx with h | h <;> omega
          exact_mod_cast this
      · unfold fig1Segment
        have hne : q.2 ≠ q'.2 := by rcases hy with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
        rw [ite_eq_right hne]
        refine ⟨by simp [GM16.latticePoint, hx], ?_, ?_⟩
        · change ((min q.2 q'.2 : ℕ) : ℝ) ≤ (q.2 : ℝ); exact_mod_cast Nat.min_le_left _ _
        · change (q.2 : ℝ) ≤ ((min q.2 q'.2 : ℕ) : ℝ) + 1
          have : q.2 ≤ min q.2 q'.2 + 1 := by rcases hy with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
          exact_mod_cast this
    exact not_mem_interior_fig1EnclosedSet_of_perimeter_segment hh2 he hq_perim hq'_perim hadj hseg hw_int

/-- For every atom `b ∈ Γ.drawing.A` meeting `D_disc`, there exists a vertex `u ∈ V(W.graph)` such
that `fig1Sph φ (pos u) ∈ D_disc` and `d {fig1Sph φ (pos u)} b ≤ 2`. -/
theorem exists_vertex_in_subwall_disc_near_atom {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    {b : Set (OnePoint EuclideanPlane)} (hb : b ∈ Γ.drawing.A)
    (hne : (b ∩ closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ).Nonempty) :
    let D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ
    ∃ u ∈ V(W.graph), fig1Sph φ (pos u) ∈ D_disc ∧ d {fig1Sph φ (pos u)} b ≤ 2 := by
  intro D_disc
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  let f : (ℝ × ℝ) → OnePoint EuclideanPlane := fig1Sph φ ∘ shiftHomeo i j
  have hf_open : Topology.IsOpenEmbedding f :=
    (isOpenEmbedding_fig1Sph φ).comp (shiftHomeo i j).isOpenEmbedding
  have hf_emb : Topology.IsEmbedding f := hf_open.isEmbedding
  have hh'2 := H'.two_le_height
  let E' := f '' fig1EnclosedSet H'.height
  have hC' : IsClosedDisc E' := isClosedDisc_image_fig1EnclosedSet hS hf_emb (by omega)
  obtain ⟨hD', hBd', _, _⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hSph hC'
  have hsubBd_D : subBd D_disc = discBd E' := by
    rw [subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hD', hBd']
  have hBd_sub_U : discBd E' ⊆ Γ.drawing.U := by
    rw [hΓU]
    refine (discBd_image_enclosed_subset hS hf_emb H'.even_height hh'2).trans ?_
    rw [image_comp]
    exact image_mono (shiftHomeo_image_fig1Set_subset hh' hi_even hj_even hi hj)
  obtain ⟨C', _, hC'_sub, hC'_U⟩ := GM11.exists_circuit_of_oArc hC'.isOArc_discBd hBd_sub_U
  have hcl_int_D : closure (interior D_disc) = D_disc :=
    Subset.antisymm (isClosed_closure.closure_subset_iff.mpr interior_subset)
      (closure_mono (interior_maximal subset_closure hC'.isCompact.isClosed.isOpen_compl))
  have hbd_cl : subBd (closure (interior D_disc)) = C'.U := by
    rw [hcl_int_D, hsubBd_D, hC'_U]
  have hdiff : closure (interior D_disc) \ C'.U = interior D_disc := by
    rw [hcl_int_D, hC'_U, ← hBd', ← GM11.IsClosedDisc.frontier_eq_discBd hS hD',
      frontier, closure_closure]
    ext x
    simp only [mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hx, h⟩ => h hx, fun hx => ⟨interior_subset hx, fun _ => hx⟩⟩
  have hcl_disc : IsClosedDisc (closure (interior D_disc)) := by
    rwa [hcl_int_D]
  have hne' : (b ∩ closure (interior D_disc)).Nonempty := by
    rwa [hcl_int_D]
  have hb_sub : b ⊆ D_disc := by
    have := GM14.atom_subset_closure_of_inter_nonempty hS hC'_sub hcl_disc hbd_cl hdiff hb hne'
    rwa [hcl_int_D] at this
  have hcl_b_sub : closure b ⊆ D_disc := closure_minimal hb_sub isClosed_closure
  have h91 := GM11.gm15_theorem_9_1 Γ.drawing W.height T d hS inferInstance hd
  have hrefl := h91.2.1
  have hv_reg := h91.2.2.2.2.2.1
  have hv_edge := h91.2.2.2.2.2.2
  have hE : Γ.drawing.E.Nonempty :=
    GM14.edgeSet_nonempty_of_isTangle hd.1.2.1 W.toWall.two_le_height
  rcases hb with (⟨v, hvV, rfl⟩ | he) | hr
  · obtain ⟨⟨u, huW⟩, hu_eq⟩ := Γ.iso.vertexEquiv.surjective ⟨v, hvV⟩
    have hv_eq : v = fig1Sph φ (pos u) :=
      (congrArg Subtype.val hu_eq).symm.trans (hΓv ⟨u, huW⟩)
    refine ⟨u, huW, hv_eq ▸ hb_sub (mem_singleton v), ?_⟩
    rw [← hv_eq, hrefl {v} (Or.inl (Or.inl ⟨v, hvV, rfl⟩))]
    omega
  · obtain ⟨v, w, hl⟩ := (Γ.drawing.toGraph.edge_mem_iff_exists_isLink b).mp he
    have hvV : v ∈ Γ.drawing.V := hl.left_mem
    have hv_cl : v ∈ closure b := by
      have : v ∈ closure b ∩ Γ.drawing.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact this.1
    obtain ⟨⟨u, huW⟩, hu_eq⟩ := Γ.iso.vertexEquiv.surjective ⟨v, hvV⟩
    have hv_eq : v = fig1Sph φ (pos u) :=
      (congrArg Subtype.val hu_eq).symm.trans (hΓv ⟨u, huW⟩)
    refine ⟨u, huW, hv_eq ▸ hcl_b_sub hv_cl, ?_⟩
    rw [← hv_eq]
    exact hv_edge v hvV b he hv_cl
  · obtain ⟨u, huW, hu_cl⟩ := exists_vertex_mem_closure_of_region hpos_branch hΓU hr
    have hvV : fig1Sph φ (pos u) ∈ Γ.drawing.V := by
      rw [← hΓv ⟨u, huW⟩]
      exact (Γ.iso.vertexEquiv _).2
    have hle1 := hv_reg hE _ hvV b hr hu_cl
    exact ⟨u, huW, hcl_b_sub hu_cl, by omega⟩

/-- **Middle vertex tangle distance lower bound (`hyp_xiv`)**:
When `2 * (4 * θ + 15) ≤ H'.height`, both middle vertices `u_star ∈ {H'.middleVertex₁, H'.middleVertex₂}`
of `H'` have `θ ≤ subsetTangleDist Γ.drawing W.height d {fig1Sph φ (pos u_star)} D_disc`. -/
theorem le_subsetTangleDist_middleVertex_subwall_disc {α : Type u} {β : Type v} [Nonempty β]
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos : ∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height)
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hdist : ∀ u ∈ V(W.graph), ∀ v ∈ V(W.graph), W.dist u v =
      planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
        (fig1PlaneEquiv (pos u)) (fig1PlaneEquiv (pos v)))
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    (hrow : ∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
      ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧ (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet)
    {H' : Wall α β} {i j θ : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    (hθ_height : 2 * (4 * θ + 15) ≤ H'.height)
    {u_star : α} (hu_star : u_star = H'.middleVertex₁ ∨ u_star = H'.middleVertex₂) :
    let D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ
    θ ≤ subsetTangleDist Γ.drawing W.height d {fig1Sph φ (pos u_star)} D_disc := by
  intro D_disc
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have h91 := GM11.gm15_theorem_9_1 Γ.drawing W.height T d hS inferInstance hd
  have hsymm := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hle_sub : H'.graph ≤ W.graph :=
    subwall_graph_le ⟨hh', i, j, hi_even, hj_even, hi, hj, hbranch, hpaths, hbase⟩
  have hu_star_W : u_star ∈ V(W.graph) := by
    rcases hu_star with rfl | rfl <;>
      exact hle_sub.vertexSet_mono (H'.branchVertex_mem_graph _ _)
  let v_star := fig1Sph φ (pos u_star)
  have hv_star_V : v_star ∈ Γ.drawing.V := by
    change fig1Sph φ (pos u_star) ∈ Γ.drawing.V
    rw [← hΓv ⟨u_star, hu_star_W⟩]
    exact (Γ.iso.vertexEquiv _).2
  have hv_star_A : ({v_star} : Set (OnePoint EuclideanPlane)) ∈ Γ.drawing.A :=
    Or.inl (Or.inl ⟨v_star, hv_star_V, rfl⟩)
  -- Coordinate of `u_star`
  let m' := H'.height / 2
  have hm'_eq : H'.height = 2 * m' := by
    obtain ⟨k, hk⟩ := H'.even_height
    dsimp [m']; omega
  have hm'2 : 2 ≤ m' := by omega
  have hs_coord : (((i + 2 * m' : ℕ) : ℝ) ≤ (pos u_star).1 ∧
      (pos u_star).1 ≤ ((i + 2 * m' + 1 : ℕ) : ℝ)) ∧
      (pos u_star).2 = ((j + m' : ℕ) : ℝ) := by
    have hh2 := H'.two_le_height
    rcases hu_star with rfl | rfl
    · have hp₁' : elementaryWallMiddle₁ H'.height ∈ elementaryWallVerts H'.height := by
        dsimp [elementaryWallMiddle₁, elementaryWallVerts]
        refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩ <;>
          (simp only [Prod.mk.injEq, not_and]; omega)
      have hp₁W := wallShift_mem_elementaryWallVerts hh' hi hj hp₁'
      have hm₁ : H'.middleVertex₁ = W.branchVertex (wallShift i j (elementaryWallMiddle₁ H'.height)) hp₁W :=
        hbranch _ hp₁' hp₁W
      rw [hm₁, hpos_branch _ hp₁W]
      dsimp [GM16.latticePoint, wallShift, elementaryWallMiddle₁]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast (show i + 2 * m' ≤ H'.height + i by omega)
      · exact_mod_cast (show H'.height + i ≤ i + 2 * m' + 1 by omega)
      · exact_mod_cast (show H'.height / 2 + j = j + m' by dsimp [m']; omega)
    · have hp₂' : elementaryWallMiddle₂ H'.height ∈ elementaryWallVerts H'.height := by
        dsimp [elementaryWallMiddle₂, elementaryWallVerts]
        refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩ <;>
          (simp only [Prod.mk.injEq, not_and]; omega)
      have hp₂W := wallShift_mem_elementaryWallVerts hh' hi hj hp₂'
      have hm₂ : H'.middleVertex₂ = W.branchVertex (wallShift i j (elementaryWallMiddle₂ H'.height)) hp₂W :=
        hbranch _ hp₂' hp₂W
      rw [hm₂, hpos_branch _ hp₂W]
      dsimp [GM16.latticePoint, wallShift, elementaryWallMiddle₂]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast (show i + 2 * m' ≤ H'.height + 1 + i by omega)
      · exact_mod_cast (show H'.height + 1 + i ≤ i + 2 * m' + 1 by omega)
      · exact_mod_cast (show H'.height / 2 + j = j + m' by dsimp [m']; omega)
  unfold subsetTangleDist
  split_ifs with hex
  · refine le_csInf ?_ ?_
    · obtain ⟨a, ha, b, hb, hne_a, hne_b⟩ := hex
      exact ⟨d a b, a, ha, b, hb, hne_a, hne_b, rfl⟩
    · rintro k ⟨a, ha, b, hb, hne_a, hne_b, rfl⟩
      -- Any atom `a ∈ Γ.drawing.A` meeting `{v_star}` must be `{v_star}`
      have ha_eq : a = {v_star} := by
        obtain ⟨x, hxa, hxv⟩ := hne_a
        rw [mem_singleton_iff] at hxv
        subst hxv
        rcases ha with (⟨v, _, hv_eq⟩ | he) | hr
        · subst hv_eq
          exact congrArg singleton (mem_singleton_iff.mp hxa).symm
        · exact ((he.2.1 hxa).2 hv_star_V).elim
        · exact (GM11.region_subset hr hxa (Γ.drawing.V_subset_U hv_star_V)).elim
      subst ha_eq
      obtain ⟨u, huW, hu_D, hd_ub⟩ := exists_vertex_in_subwall_disc_near_atom
        hpos_branch hΓU hΓv hd hh' hi_even hj_even hi hj hb hne_b
      have hpos_u_not_open : pos u ∉ shiftHomeo i j ''
          (Ioo (1 : ℝ) (2 * (H'.height : ℝ)) ×ˢ Ioo (0 : ℝ) (H'.height : ℝ)) := by
        intro hmem
        have hmem_int : pos u ∈ shiftHomeo i j '' interior (fig1EnclosedSet H'.height) :=
          image_mono (openInnerRect_subset_interior_fig1EnclosedSet (by omega)) hmem
        let f : (ℝ × ℝ) → OnePoint EuclideanPlane := fig1Sph φ ∘ shiftHomeo i j
        have hf_open : Topology.IsOpenEmbedding f :=
          (isOpenEmbedding_fig1Sph φ).comp (shiftHomeo i j).isOpenEmbedding
        have hcompl_D : univ \ D_disc = f '' interior (fig1EnclosedSet H'.height) := by
          change univ \ closure (f '' fig1EnclosedSet H'.height)ᶜ = _
          rw [← compl_eq_univ_sdiff, closure_compl, compl_compl]
          exact interior_image_eq_of_isOpenEmbedding hf_open (fig1EnclosedSet H'.height)
        have hnot_D : fig1Sph φ (pos u) ∈ univ \ D_disc := by
          rw [hcompl_D, image_comp]
          exact ⟨pos u, hmem_int, rfl⟩
        exact hnot_D.2 hu_D
      have ht_coord : (pos u).1 ≤ (i : ℝ) + 1 ∨ (i : ℝ) + 4 * (m' : ℝ) ≤ (pos u).1 ∨
          (pos u).2 ≤ (j : ℝ) ∨ (j : ℝ) + 2 * (m' : ℝ) ≤ (pos u).2 := by
        by_contra hnot
        push Not at hnot
        apply hpos_u_not_open
        refine ⟨(shiftHomeo i j).symm (pos u), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
          (shiftHomeo i j).apply_symm_apply (pos u)⟩
        · simp only [shiftHomeo_symm_apply]; linarith [hnot.1]
        · simp only [shiftHomeo_symm_apply, hm'_eq, Nat.cast_mul, Nat.cast_ofNat]; linarith [hnot.2.1]
        · simp only [shiftHomeo_symm_apply]; linarith [hnot.2.2.1]
        · simp only [shiftHomeo_symm_apply, hm'_eq, Nat.cast_mul, Nat.cast_ofNat]; linarith [hnot.2.2.2]
      have hdist_lower : m' - 2 ≤ W.dist u_star u := by
        rw [hdist u_star hu_star_W u huW]
        exact le_planeWallDist_of_shifted_middle W.toWall.even_height hm'2 (by omega)
          (by omega) (by omega) hs_coord.1 hs_coord.2 ht_coord
      -- If `d {v_star} b < θ`, then `d {v_star} {fig1Sph φ (pos u)} < θ + 2`
      by_contra hlt_θ
      push Not at hlt_θ
      have huV : fig1Sph φ (pos u) ∈ Γ.drawing.V := by
        rw [← hΓv ⟨u, huW⟩]
        exact (Γ.iso.vertexEquiv _).2
      have huA : ({fig1Sph φ (pos u)} : Set (OnePoint EuclideanPlane)) ∈ Γ.drawing.A :=
        Or.inl (Or.inl ⟨_, huV, rfl⟩)
      have hd_bu : d b {fig1Sph φ (pos u)} ≤ 2 := by
        rw [hsymm b hb _ huA]
        exact hd_ub
      have hd_vu_le := htri {v_star} hv_star_A b hb _ huA
      have hd_vu_lt : d {v_star} {fig1Sph φ (pos u)} < θ + 2 := by omega
      have hN_le : 2 * (θ + 2) + 2 ≤ W.height := by omega
      have hdist_upper := wallDist_le_of_tangleMetric_lt hpos hdist hΓU hΓv hΓe hrow hd
        hN_le hu_star_W huW hd_vu_lt
      omega
  · omega

end GM22
end GraphMinor
