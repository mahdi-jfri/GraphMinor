module

public import GraphMinor.Surface.DrawCarry
public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM07.Section7
public import GraphMinor.GM11.Section64b
public import GraphMinor.GM11.CitedResults
public import GraphMinor.GM12.Bridge
public import GraphMinor.GM12.Section1
public import GraphMinor.GM12.Section4Theorem45
public import GraphMinor.GM12.Section73MetricVisits
public import GraphMinor.GM12.Section78
public import GraphMinor.GM13.Section7
public import GraphMinor.GM13.Section7FourProof
public import GraphMinor.GM13.Section9a
public import GraphMinor.GM13.Section9Subwalls
public import GraphMinor.GM13.Section9Claim91Order
public import GraphMinor.GM13.Section9Claim91Cross
public import GraphMinor.GM16.EmptyDiscRegion
public import GraphMinor.GM16.GraphDrawingForwardMaps
public import GraphMinor.GM16.GraphDrawingSpanEmbedding
public import GraphMinor.GM16.GraphIsoImage
public import GraphMinor.GM16.Metric
public import GraphMinor.GM16.ModelInducedTangle
public import GraphMinor.GM16.Section3
public import GraphMinor.GM16.Section4WallTangle
public import GraphMinor.GM16.Section4WallRowImages
public import GraphMinor.GM16.InducedTangleEdgePatterns
public import GraphMinor.GM16.ControlFromInducedTangle
public import GraphMinor.GM16.HypergraphSupportedTangle
public import GraphMinor.GM16.Section6
public import GraphMinor.GM16.Section9Zones
public import GraphMinor.GM16.SphereComplementDisc
public import GraphMinor.GM16.SphereRespectful
public import GraphMinor.GM16.Theorem35Bridge

/-!
# Graph Minors XIII, (9.1): Crosses over Subwalls Yield a `K_p`-Minor

This file completes the proof of **Graph Minors XIII, (9.1)** (page 98) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110:

- Pigeonhole and planar routing helpers (`exists_disjoint_of_ncard_le`, `fig1VertStack`,
  `fig1LeftRay`, `fig1Collar`, `exists_collar_row_route`, `fig1EyeConnector`).
- The punctured sphere drawing `Γ' = clearedSubdrawing Γ.drawing Λ` obtained by deleting the open
  interiors of `t` subwalls `H'_1, …, H'_t`, its 2-cell property, eye regions `r_a`, boundary
  circuits `C_a`, and controlling tangle `(Tstar, T')` induced from an unpunctured bottom subwall
  `W_θ`.
- Verification that the 4 extended cross endpoints on each `C_a` form a free set (`IsFreeSet`) in
   cyclic order (`OccurInCircuitOrder`) and that distinct eye regions have tangle distance `≥ N₀`,
  followed by applying **Graph Minors XII, (4.5)** (`GM12.theorem_4_5_span`) to obtain a
  `K_p`-minor in `G`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical Topology
open Graph SimpleGraph Hypergraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM10
open GraphMinor.GM11
open GraphMinor.GM14
open GraphMinor.GM15
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## Pigeonhole Principle for Pairwise Disjoint Families -/

/-- If `X` is a finite set with `X.ncard ≤ M` and `S : ℕ → Set γ` is pairwise disjoint on
`Icc lo (lo + M)`, then some `k ∈ Icc lo (lo + M)` satisfies `Disjoint (S k) X`. -/
theorem exists_disjoint_of_ncard_le {γ : Type*} {X : Set γ} (hX : X.Finite) {M : ℕ}
    (hXM : X.ncard ≤ M) (lo : ℕ) {S : ℕ → Set γ}
    (hdisj : PairwiseDisjoint (Icc lo (lo + M)) S) :
    ∃ k ∈ Icc lo (lo + M), Disjoint (S k) X := by
  by_contra hno
  push Not at hno
  have hmem : ∀ k ∈ Icc lo (lo + M), ∃ x ∈ X, x ∈ S k := by
    intro k hk
    obtain ⟨x, hxS, hxX⟩ := not_disjoint_iff.mp (hno k hk)
    exact ⟨x, hxX, hxS⟩
  choose f hfX hfS using hmem
  let g : ℕ → γ := fun k => if hk : k ∈ Icc lo (lo + M) then f k hk else Classical.choice ⟨f lo (by simp)⟩
  have hg_maps : MapsTo g (Icc lo (lo + M)) X := by
    intro k hk
    rw [show g k = f k hk from dite_eq_left hk]
    exact hfX k hk
  have hg_inj : InjOn g (Icc lo (lo + M)) := by
    intro k₁ hk₁ k₂ hk₂ heq
    rw [show g k₁ = f k₁ hk₁ from dite_eq_left hk₁,
      show g k₂ = f k₂ hk₂ from dite_eq_left hk₂] at heq
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hk₁ hk₂ hne) (hfS k₁ hk₁) (heq ▸ hfS k₂ hk₂)
  have hle : (Icc lo (lo + M)).ncard ≤ X.ncard :=
    ncard_le_ncard_of_injOn g hg_maps hg_inj hX
  have hcard : (Icc lo (lo + M)).ncard = M + 1 := by
    rw [← Finset.coe_Icc, ncard_coe_finset, Nat.card_Icc]
    omega
  omega

/-! ## Vertical Brick Stacks and Horizontal Rays in Fig. 1 Coordinates -/

/-- Abscissa of the brick at row `y` in vertical stack `s`: `4s + 3` for even `y` and `4s + 2` for
odd `y`. -/
def fig1StackX (s y : ℕ) : ℕ :=
  if y % 2 = 0 then 4 * s + 3 else 4 * s + 2

/-- Every `(fig1StackX s y, y)` for `y < h` is a valid Fig. 1 brick when `4s + 5 ≤ 2h + 1`. -/
theorem isFig1Brick_fig1StackX {h s y : ℕ} (hs : 4 * s + 5 ≤ 2 * h + 1) (hy : y < h) :
    IsFig1Brick h (fig1StackX s y) y := by
  refine ⟨?_, ?_, hy⟩
  · rw [Nat.odd_iff]
    unfold fig1StackX
    split_ifs <;> omega
  · unfold fig1StackX
    split_ifs <;> omega

/-- Vertical stack `s` of brick frontiers spanning all rows `0 ≤ y < h`. -/
def fig1VertStack (h s : ℕ) : Set (ℝ × ℝ) :=
  ⋃ y ∈ Iic (h - 1), frontier (fig1Brick (fig1StackX s y) y)

/-- `fig1VertStack h s` is preconnected. -/
theorem isPreconnected_fig1VertStack (h s : ℕ) :
    IsPreconnected (fig1VertStack h s) := by
  refine IsPreconnected.biUnion_of_chain ordConnected_Iic
    (fun y _ => isPreconnected_frontier_fig1Brick _ _) ?_
  intro y _ hy1
  rw [Order.succ_eq_add_one]
  refine frontier_fig1Brick_inter_nonempty ?_
  unfold fig1StackX
  split_ifs <;> omega

/-- `fig1VertStack h s ⊆ fig1Set h` when `2 ≤ h`, `Even h`, and `4s + 5 ≤ 2h + 1`. -/
theorem fig1VertStack_subset_fig1Set {h s : ℕ} (hh : 2 ≤ h) (he : Even h)
    (hs : 4 * s + 5 ≤ 2 * h + 1) :
    fig1VertStack h s ⊆ fig1Set h := by
  refine iUnion₂_subset fun y hy => ?_
  have hy_lt : y < h := by
    have : y ≤ h - 1 := mem_Iic.mp hy
    omega
  obtain ⟨hodd, h1, h2⟩ := isFig1Brick_fig1StackX hs hy_lt
  exact frontier_brick_subset_fig1Set he h1 h2 hodd

/-- Every point of `fig1VertStack h s` has abscissa in `[4s + 2, 4s + 5]` and ordinate in `[0, h]`. -/
theorem fig1VertStack_subset_Icc (h s : ℕ) (hh : 1 ≤ h) :
    fig1VertStack h s ⊆
      Icc (4 * (s : ℝ) + 2) (4 * (s : ℝ) + 5) ×ˢ Icc (0 : ℝ) (h : ℝ) := by
  rintro ⟨x, y⟩ hz
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
  have hk_le : k ≤ h - 1 := mem_Iic.mp hk
  have hzB : (x, y) ∈ fig1Brick (fig1StackX s k) k :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset hzk
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hzB
  have hkx1 : 4 * s + 2 ≤ fig1StackX s k := by unfold fig1StackX; split_ifs <;> omega
  have hkx2 : fig1StackX s k + 2 ≤ 4 * s + 5 := by unfold fig1StackX; split_ifs <;> omega
  have hkx1_r : 4 * (s : ℝ) + 2 ≤ (fig1StackX s k : ℝ) := by exact_mod_cast hkx1
  have hkx2_r : (fig1StackX s k : ℝ) + 2 ≤ 4 * (s : ℝ) + 5 := by exact_mod_cast hkx2
  have hky_r : (k : ℝ) + 1 ≤ (h : ℝ) := by
    have : k + 1 ≤ h := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Vertical stacks for distinct indices `s₁ ≠ s₂` are disjoint. -/
theorem disjoint_fig1VertStack_of_ne (h : ℕ) (hh : 1 ≤ h) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂) :
    Disjoint (fig1VertStack h s₁) (fig1VertStack h s₂) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  obtain ⟨⟨hx1_lo, hx1_hi⟩, -⟩ := fig1VertStack_subset_Icc h s₁ hh hz1
  obtain ⟨⟨hx2_lo, hx2_hi⟩, -⟩ := fig1VertStack_subset_Icc h s₂ hh hz2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (s₁ : ℝ) + 1 ≤ (s₂ : ℝ) := by exact_mod_cast hlt
    linarith
  · have : (s₂ : ℝ) + 1 ≤ (s₁ : ℝ) := by exact_mod_cast hgt
    linarith

/-- For any `y < h`, the point `((fig1StackX s y : ℝ) + 1, (y : ℝ))` belongs to `fig1VertStack h s`. -/
theorem mem_fig1VertStack_of_lt {h s y : ℕ} (hy : y < h) :
    ((fig1StackX s y : ℝ) + 1, (y : ℝ)) ∈ fig1VertStack h s := by
  refine mem_biUnion (x := y) (mem_Iic.mpr (by omega)) ?_
  exact mem_frontier_rect_of_snd_eq (by linarith) (by linarith)
    ⟨by linarith, by linarith⟩ (Or.inl rfl)

/-- For any `j < h` and `s` with `4s + 5 ≤ 2h + 1`, `fig1VertStack h s` meets `fig1RowSeg h j`. -/
theorem fig1VertStack_inter_fig1RowSeg_nonempty {h s j : ℕ} (hs : 4 * s + 5 ≤ 2 * h + 1)
    (hj : j < h) :
    (fig1VertStack h s ∩ fig1RowSeg h j).Nonempty := by
  refine ⟨((fig1StackX s j : ℝ) + 1, (j : ℝ)), mem_fig1VertStack_of_lt hj, ?_⟩
  have h1 : 4 * s + 2 ≤ fig1StackX s j := by unfold fig1StackX; split_ifs <;> omega
  have h2 : fig1StackX s j + 1 ≤ 2 * h + 1 := by unfold fig1StackX; split_ifs <;> omega
  have h1_r : (1 : ℝ) ≤ (fig1StackX s j : ℝ) + 1 := by
    have : 1 ≤ fig1StackX s j + 1 := by omega
    exact_mod_cast this
  have h2_r : (fig1StackX s j : ℝ) + 1 ≤ 2 * (h : ℝ) + 1 := by exact_mod_cast h2
  exact ⟨⟨h1_r, h2_r⟩, rfl⟩

/-- Horizontal ray from `x = 1` to `x = i' + 1` at height `j' + 2k`. -/
def fig1LeftRay (i' j' k : ℕ) : Set (ℝ × ℝ) :=
  Icc (1 : ℝ) ((i' + 1 : ℕ) : ℝ) ×ˢ {((j' + 2 * k : ℕ) : ℝ)}

/-- `fig1LeftRay i' j' k` is preconnected. -/
theorem isPreconnected_fig1LeftRay (i' j' k : ℕ) :
    IsPreconnected (fig1LeftRay i' j' k) :=
  isPreconnected_Icc.prod isPreconnected_singleton

/-- `fig1LeftRay i' j' k ⊆ fig1RowSeg h (j' + 2k) ⊆ fig1Set h` when `i' ≤ 2h` and `j' + 2k < h`. -/
theorem fig1LeftRay_subset_fig1Set {h i' j' k : ℕ} (hi' : i' ≤ 2 * h) (hj' : j' + 2 * k < h) :
    fig1LeftRay i' j' k ⊆ fig1Set h := by
  refine Subset.trans ?_ (fig1RowSeg_subset_fig1Set hj')
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy⟩
  have hi'_r : ((i' + 1 : ℕ) : ℝ) ≤ 2 * (h : ℝ) + 1 := by
    have : i' + 1 ≤ 2 * h + 1 := by omega
    exact_mod_cast this
  exact ⟨⟨hx1, by linarith⟩, hy⟩

/-- Horizontal rays for distinct `k₁ ≠ k₂` are disjoint. -/
theorem disjoint_fig1LeftRay_of_ne (i' j' : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (fig1LeftRay i' j' k₁) (fig1LeftRay i' j' k₂) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨_, hy1⟩ ⟨_, hy2⟩
  simp only [mem_singleton_iff] at hy1 hy2
  have hcast : ((j' + 2 * k₁ : ℕ) : ℝ) = ((j' + 2 * k₂ : ℕ) : ℝ) := hy1.symm.trans hy2
  have := Nat.cast_injective hcast
  omega

/-- `fig1LeftRay i' j' k` is disjoint from `interior (wallShiftRealHomeomorph i' j' '' fig1EnclosedSet h')`. -/
theorem disjoint_fig1LeftRay_interior_shifted (i' j' h' k : ℕ) :
    Disjoint (fig1LeftRay i' j' k)
      (interior (wallShiftRealHomeomorph i' j' '' fig1EnclosedSet h')) := by
  rw [← (wallShiftRealHomeomorph i' j').image_interior, Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy⟩ ⟨⟨x₀, y₀⟩, hint, heq⟩
  simp only [mem_singleton_iff] at hy
  have hx_eq : x₀ + (i' : ℝ) = x := congrArg Prod.fst heq
  have hy_eq : y₀ + (j' : ℝ) = y := congrArg Prod.snd heq
  have hx₀_le : x₀ ≤ 1 := by
    push_cast at hx2
    linarith
  have hy₀_eq : y₀ = (2 * k : ℕ) := by
    rw [hy] at hy_eq
    push_cast at hy_eq ⊢
    linarith
  rw [hy₀_eq] at hint
  exact not_mem_interior_fig1EnclosedSet_of_even_le_one (even_two_mul k) hx₀_le hint

/-- The right endpoint `((i' + 1 : ℕ), (j' + 2k : ℕ))` lies in both `fig1LeftRay i' j' k` and
`frontier (wallShiftRealHomeomorph i' j' '' fig1EnclosedSet h')` when `1 ≤ h'` and `2k ≤ h'`. -/
theorem fig1LeftRay_inter_frontier_nonempty {i' j' h' k : ℕ} (hh' : 1 ≤ h') (hk : 2 * k ≤ h') :
    (fig1LeftRay i' j' k ∩
      frontier (wallShiftRealHomeomorph i' j' '' fig1EnclosedSet h')).Nonempty := by
  refine ⟨(((i' + 1 : ℕ) : ℝ), ((j' + 2 * k : ℕ) : ℝ)), ?_, ?_⟩
  · have hi'_0 : (0 : ℝ) ≤ (i' : ℝ) := Nat.cast_nonneg i'
    refine ⟨⟨by push_cast; linarith, by push_cast; linarith⟩, rfl⟩
  · rw [← (wallShiftRealHomeomorph i' j').image_frontier]
    refine ⟨(1, ((2 * k : ℕ) : ℝ)), ?_, ?_⟩
    · refine ⟨subset_closure ?_,
        not_mem_interior_fig1EnclosedSet_of_even_le_one (even_two_mul k) le_rfl⟩
      apply rect_subset_fig1EnclosedSet
      have hh'_r : (1 : ℝ) ≤ (h' : ℝ) := by exact_mod_cast hh'
      have hk_r : ((2 * k : ℕ) : ℝ) ≤ (h' : ℝ) := by exact_mod_cast hk
      exact ⟨⟨le_rfl, by linarith⟩, ⟨Nat.cast_nonneg _, hk_r⟩⟩
    · ext <;> dsimp <;> push_cast <;> ring

/-- `fig1LeftRay i' j' k` meets `fig1VertStack h s` when `4s + 4 ≤ i' + 1` and `j' + 2k < h`. -/
theorem fig1LeftRay_inter_fig1VertStack_nonempty {h s i' j' k : ℕ}
    (hs : 4 * s + 4 ≤ i' + 1) (hj' : j' + 2 * k < h) :
    (fig1LeftRay i' j' k ∩ fig1VertStack h s).Nonempty := by
  refine ⟨((fig1StackX s (j' + 2 * k) : ℝ) + 1, ((j' + 2 * k : ℕ) : ℝ)), ?_,
    mem_fig1VertStack_of_lt hj'⟩
  have h1 : (0 : ℝ) ≤ (fig1StackX s (j' + 2 * k) : ℝ) := Nat.cast_nonneg _
  have h2 : fig1StackX s (j' + 2 * k) ≤ i' := by unfold fig1StackX; split_ifs <;> omega
  have h2_r : (fig1StackX s (j' + 2 * k) : ℝ) ≤ (i' : ℝ) := by exact_mod_cast h2
  exact ⟨⟨by linarith, by push_cast; linarith⟩, rfl⟩

/-! ## Concentric Collars Around Subwall Enclosed Sets and Routing -/

/-- `frontier (fig1EnclosedSet h)` is preconnected for `1 ≤ h`. -/
theorem isPreconnected_frontier_fig1EnclosedSet {h : ℕ} (hh : 1 ≤ h) :
    IsPreconnected (frontier (fig1EnclosedSet h)) := by
  have hEmb := isOpenEmbedding_fig1Sph (Homeomorph.refl EuclideanPlane)
  have hDisc := isClosedDisc_image_fig1EnclosedSet GM09.isClosedSurface_sphere hEmb.isEmbedding hh
  have hO := hDisc.isOArc_discBd
  rw [← GM11.IsClosedDisc.frontier_eq_discBd GM09.isClosedSurface_sphere hDisc,
    frontier_image_fig1EnclosedSet GM09.isClosedSurface_sphere hEmb hh] at hO
  exact hEmb.isInducing.isPreconnected_image.mp hO.isPreconnected

/-- The `n`-th concentric collar around a subwall at `(i, j)` of height `h`:
the shifted enclosed set of height `h + 4n` at `(i - 4n, j - 2n)`. -/
def fig1Collar (i j h n : ℕ) : Set (ℝ × ℝ) :=
  wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n) '' fig1EnclosedSet (h + 4 * n)

@[simp]
theorem fig1Collar_zero (i j h : ℕ) :
    fig1Collar i j h 0 = wallShiftRealHomeomorph i j '' fig1EnclosedSet h := by
  simp [fig1Collar]

/-- `fig1Collar i j h n` is closed. -/
theorem isClosed_fig1Collar (i j h n : ℕ) : IsClosed (fig1Collar i j h n) :=
  (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).isClosedMap _
    (isClosed_fig1EnclosedSet (h + 4 * n))

/-- `frontier (fig1Collar i j h n)` is preconnected when `1 ≤ h`. -/
theorem isPreconnected_frontier_fig1Collar {i j h n : ℕ} (hh : 1 ≤ h) :
    IsPreconnected (frontier (fig1Collar i j h n)) := by
  unfold fig1Collar
  rw [← (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).image_frontier]
  exact (isPreconnected_frontier_fig1EnclosedSet (by omega)).image _
    (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).continuous.continuousOn

/-- `frontier (fig1EnclosedSet h) ⊆ fig1Set h` when `2 ≤ h` and `Even h`. -/
theorem frontier_fig1EnclosedSet_subset_fig1Set {h : ℕ} (hh : 2 ≤ h) (he : Even h) :
    frontier (fig1EnclosedSet h) ⊆ fig1Set h := by
  intro z hz
  have hEmb := isOpenEmbedding_fig1Sph (Homeomorph.refl EuclideanPlane)
  have hDisc := isClosedDisc_image_fig1EnclosedSet GM09.isClosedSurface_sphere
    hEmb.isEmbedding (h := h) (by omega)
  have hmem : fig1Sph (Homeomorph.refl EuclideanPlane) z ∈
      discBd (fig1Sph (Homeomorph.refl EuclideanPlane) '' fig1EnclosedSet h) := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd GM09.isClosedSurface_sphere hDisc,
      frontier_image_fig1EnclosedSet GM09.isClosedSurface_sphere hEmb (by omega)]
    exact ⟨z, hz, rfl⟩
  obtain ⟨w, hw, heq⟩ := discBd_image_enclosed_subset GM09.isClosedSurface_sphere
    hEmb.isEmbedding he hh hmem
  rwa [← hEmb.injective heq]

/-- Shifting `fig1Set h'` by `(i, j)` with `Even i`, `Even j`, `2 ≤ h'`, `h' ≤ h`,
`i + 2 * h' ≤ 2 * h`, and `j + h' ≤ h` lands inside `fig1Set h`. -/
theorem wallShiftRealHomeomorph_fig1Set_subset {h' h i j : ℕ}
    (h2 : 2 ≤ h') (hle : h' ≤ h) (hi : Even i) (hj : Even j)
    (hi_le : i + 2 * h' ≤ 2 * h) (hj_le : j + h' ≤ h) :
    wallShiftRealHomeomorph i j '' fig1Set h' ⊆ fig1Set h := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  simp only [fig1Set, mem_iUnion] at hxy ⊢
  obtain ⟨p, q, hadj', hseg⟩ := hxy
  have hadj : elementaryWallAdj h (wallShift i j p) (wallShift i j q) :=
    (elementaryWallAdj_wallShift_iff h2 hle hi hj (by omega) (by omega)
      hadj'.1 hadj'.2.1).mp hadj'
  refine ⟨wallShift i j p, wallShift i j q, hadj, ?_⟩
  unfold fig1Segment at hseg ⊢
  have hmin1 : min (p.1 + i) (q.1 + i) = min p.1 q.1 + i := Nat.add_min_add_right p.1 q.1 i
  have hmin2 : min (p.2 + j) (q.2 + j) = min p.2 q.2 + j := Nat.add_min_add_right p.2 q.2 j
  by_cases hpq2 : p.2 = q.2
  · have hpq2' : (wallShift i j p).2 = (wallShift i j q).2 := by dsimp [wallShift]; omega
    rw [ite_eq_left_iff.mpr fun h => (h hpq2).elim] at hseg
    rw [ite_eq_left_iff.mpr fun h => (h hpq2').elim]
    unfold GM16.horizontalLatticeLine at hseg ⊢
    rcases hseg with ⟨⟨hx1, hx2⟩, hy⟩
    rw [mem_singleton_iff] at hy
    dsimp at hx1 hx2 hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp [wallShift]; rw [hmin1, Nat.cast_add]; linarith
    · dsimp [wallShift]; rw [hmin1, Nat.cast_add]; linarith
    · dsimp [wallShift]; rw [mem_singleton_iff, hmin2, Nat.cast_add, hy]
  · have hpq2' : (wallShift i j p).2 ≠ (wallShift i j q).2 := by dsimp [wallShift]; omega
    rw [ite_eq_right_iff.mpr fun h => (hpq2 h).elim] at hseg
    rw [ite_eq_right_iff.mpr fun h => (hpq2' h).elim]
    unfold GM16.verticalLatticeLine at hseg ⊢
    rcases hseg with ⟨hx, ⟨hy1, hy2⟩⟩
    rw [mem_singleton_iff] at hx
    dsimp at hx hy1 hy2
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · dsimp [wallShift]; rw [mem_singleton_iff, hmin1, Nat.cast_add, hx]
    · dsimp [wallShift]; rw [hmin2, Nat.cast_add]; linarith
    · dsimp [wallShift]; rw [hmin2, Nat.cast_add]; linarith

/-- `frontier (fig1Collar i j h n) ⊆ fig1Set H_h` when the shifted subwall fits inside `H_h`. -/
theorem frontier_fig1Collar_subset_fig1Set {H_h i j h n : ℕ}
    (hh : 2 ≤ h) (he : Even h) (hi_even : Even i) (hj_even : Even j)
    (hi_lo : 4 * n ≤ i) (hj_lo : 2 * n ≤ j)
    (hi_hi : i + 2 * h + 4 * n ≤ 2 * H_h) (hj_hi : j + h + 2 * n ≤ H_h) :
    frontier (fig1Collar i j h n) ⊆ fig1Set H_h := by
  unfold fig1Collar
  rw [← (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).image_frontier]
  refine Subset.trans (image_mono (frontier_fig1EnclosedSet_subset_fig1Set (by omega) ?_)) ?_
  · exact he.add ⟨2 * n, by omega⟩
  · have hi' : Even (i - 4 * n) := by rcases hi_even with ⟨k, rfl⟩; exact ⟨k - 2 * n, by omega⟩
    have hj' : Even (j - 2 * n) := by rcases hj_even with ⟨k, rfl⟩; exact ⟨k - n, by omega⟩
    exact wallShiftRealHomeomorph_fig1Set_subset (by omega) (by omega) hi' hj' (by omega) (by omega)

/-- For `n₁ < n₂` and `4 * n₂ ≤ i`, `2 * n₂ ≤ j`, `fig1Collar i j h n₁` lies inside the interior of
`fig1Collar i j h n₂`. -/
theorem fig1Collar_subset_interior_of_lt {i j h n₁ n₂ : ℕ}
    (hlt : n₁ < n₂) (hi : 4 * n₂ ≤ i) (hj : 2 * n₂ ≤ j) :
    fig1Collar i j h n₁ ⊆ interior (fig1Collar i j h n₂) := by
  have hm : 1 ≤ n₂ - n₁ := by omega
  have hsub := fig1EnclosedSet_shift_subset_interior (i := i - 4 * n₁) (j := j - 2 * n₁)
    (h := h + 4 * n₁) (m := n₂ - n₁) hm (by omega) (by omega)
  have hi_eq : i - 4 * n₁ - 4 * (n₂ - n₁) = i - 4 * n₂ := by omega
  have hj_eq : j - 2 * n₁ - 2 * (n₂ - n₁) = j - 2 * n₂ := by omega
  have hh_eq : h + 4 * n₁ + 4 * (n₂ - n₁) = h + 4 * n₂ := by omega
  unfold fig1Collar
  rwa [hi_eq, hj_eq, hh_eq] at hsub

/-- Concentric collar frontiers for `n₁ ≠ n₂` (`n₁, n₂ ≤ M`, `4M ≤ i`, `2M ≤ j`) are disjoint. -/
theorem disjoint_frontier_fig1Collar_of_ne {i j h M n₁ n₂ : ℕ}
    (hi : 4 * M ≤ i) (hj : 2 * M ≤ j) (hn₁ : n₁ ≤ M) (hn₂ : n₂ ≤ M) (hne : n₁ ≠ n₂) :
    Disjoint (frontier (fig1Collar i j h n₁)) (frontier (fig1Collar i j h n₂)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [Set.disjoint_left]
    intro z hz1 hz2
    have hsub := fig1Collar_subset_interior_of_lt (i := i) (j := j) (h := h)
      hlt (by omega) (by omega)
    exact hz2.2 (hsub ((isClosed_fig1Collar i j h n₁).frontier_subset hz1))
  · rw [Set.disjoint_right]
    intro z hz2 hz1
    have hsub := fig1Collar_subset_interior_of_lt (i := i) (j := j) (h := h)
      hgt (by omega) (by omega)
    exact hz1.2 (hsub ((isClosed_fig1Collar i j h n₂).frontier_subset hz2))

/--Every point of `fig1Collar i j h n` lies in `[i - 4n, i + 2h + 4n + 1] × [j - 2n, j + h + 2n]`
when `4n ≤ i` and `2n ≤ j`. -/
theorem fig1Collar_subset_Icc {i j h n : ℕ} (hi : 4 * n ≤ i) (hj : 2 * n ≤ j) :
    fig1Collar i j h n ⊆
      Icc ((i - 4 * n : ℕ) : ℝ) ((i + 2 * h + 4 * n + 1 : ℕ) : ℝ) ×ˢ
        Icc ((j - 2 * n : ℕ) : ℝ) ((j + h + 2 * n : ℕ) : ℝ) := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := fig1EnclosedSet_subset_Icc (h + 4 * n) hxy
  have hi_eq : (i - 4 * n) + (2 * (h + 4 * n) + 1) = i + 2 * h + 4 * n + 1 := by omega
  have hj_eq : (j - 2 * n) + (h + 4 * n) = j + h + 2 * n := by omega
  have hi_r : ((i - 4 * n : ℕ) : ℝ) + (2 * ((h + 4 * n : ℕ) : ℝ) + 1) =
      ((i + 2 * h + 4 * n + 1 : ℕ) : ℝ) := by
    have : (((i - 4 * n) + (2 * (h + 4 * n) + 1) : ℕ) : ℝ) =
        ((i + 2 * h + 4 * n + 1 : ℕ) : ℝ) := by exact_mod_cast hi_eq
    push_cast at this ⊢
    linarith
  have hj_r : ((j - 2 * n : ℕ) : ℝ) + ((h + 4 * n : ℕ) : ℝ) = ((j + h + 2 * n : ℕ) : ℝ) := by
    have : (((j - 2 * n) + (h + 4 * n) : ℕ) : ℝ) = ((j + h + 2 * n : ℕ) : ℝ) := by
      exact_mod_cast hj_eq
    push_cast at this ⊢
    linarith
  exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, ⟨by dsimp; linarith, by dsimp; linarith⟩⟩

/-- Disjointness of `fig1VertStack H_h s` and `fig1Collar i j h n` when `4s + 6 ≤ i - 4n`. -/
theorem disjoint_fig1VertStack_fig1Collar {H_h s i j h n : ℕ}
    (hH : 1 ≤ H_h) (hi : 4 * n ≤ i) (hj : 2 * n ≤ j) (hs : 4 * s + 6 ≤ i - 4 * n) :
    Disjoint (fig1VertStack H_h s) (fig1Collar i j h n) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  obtain ⟨⟨hx1_lo, hx1_hi⟩, -⟩ := fig1VertStack_subset_Icc H_h s hH hz1
  obtain ⟨⟨hx2_lo, -⟩, -⟩ := fig1Collar_subset_Icc hi hj hz2
  have hs_r : 4 * (s : ℝ) + 6 ≤ ((i - 4 * n : ℕ) : ℝ) := by
    have : (4 * s + 6 : ℕ) ≤ i - 4 * n := hs
    exact_mod_cast this
  linarith

/-- Disjointness of `fig1RowSeg H_h j_row` and `fig1Collar i j h n` when `j_row < j - 2n`. -/
theorem disjoint_fig1RowSeg_fig1Collar {H_h j_row i j h n : ℕ}
    (hi : 4 * n ≤ i) (hj : 2 * n ≤ j) (hrow : j_row < j - 2 * n) :
    Disjoint (fig1RowSeg H_h j_row) (fig1Collar i j h n) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨_, hy1⟩ hz2
  simp only [mem_singleton_iff] at hy1
  obtain ⟨-, ⟨hy2_lo, -⟩⟩ := fig1Collar_subset_Icc hi hj hz2
  have hrow_r : (j_row : ℝ) + 1 ≤ ((j - 2 * n : ℕ) : ℝ) := by
    have : j_row + 1 ≤ j - 2 * n := hrow
    exact_mod_cast this
  dsimp at hy2_lo
  linarith

/-- **Unified collar-to-row routing lemma:**
Given `t` subwall positions `(i₀ c, j₀ c, h₀ c)` with margins `4M + 6 ≤ i₀ c - 4M` and
`M + 1 ≤ j₀ c - 2M` and pairwise disjointness of `fig1Collar (i₀ c₁) (j₀ c₁) (h₀ c₁) n₁` and
`fig1Collar (i₀ c₂) (j₀ c₂) (h₀ c₂) n₂` for `c₁ ≠ c₂` and `n₁, n₂ ≤ M`, for any `a : Fin t`,
any `M_sep` with `M_sep + 1 ≤ M`, any `n₀ ≤ M`, and any finite set `X ⊆ ℝ × ℝ` with
`X.ncard ≤ M_sep` and `Disjoint (frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀)) X`, there exist a
row index `j_row ≤ M_sep` and a preconnected set `Y_base ⊆ ℝ × ℝ` such that:
1. `frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀) ⊆ Y_base`,
2. `fig1RowSeg H_h j_row ⊆ Y_base`,
3. `Y_base ⊆ fig1Set H_h \ ⋃ c : Fin t, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0)`,
4. `Disjoint Y_base X`. -/
theorem exists_collar_row_route {t H_h M M_sep : ℕ}
    (hH_two : 2 ≤ H_h) (hH_even : Even H_h)
    (i₀ j₀ h₀ : Fin t → ℕ)
    (hh₀ : ∀ c, 6 ≤ h₀ c ∧ Even (h₀ c))
    (hi₀_even : ∀ c, Even (i₀ c))
    (hj₀_even : ∀ c, Even (j₀ c))
    (hi₀_lo : ∀ c, 4 * M + 6 ≤ i₀ c - 4 * M)
    (hj₀_lo : ∀ c, M + 1 ≤ j₀ c - 2 * M)
    (hi₀_hi : ∀ c, i₀ c + 2 * h₀ c + 4 * M ≤ 2 * H_h)
    (hj₀_hi : ∀ c, j₀ c + h₀ c + 2 * M ≤ H_h)
    (hsep : ∀ c₁ c₂, c₁ ≠ c₂ → ∀ n₁ ≤ M, ∀ n₂ ≤ M,
      Disjoint (fig1Collar (i₀ c₁) (j₀ c₁) (h₀ c₁) n₁)
        (fig1Collar (i₀ c₂) (j₀ c₂) (h₀ c₂) n₂))
    (hM_sep : M_sep + 1 ≤ M)
    (a : Fin t) {n₀ : ℕ} (hn₀ : n₀ ≤ M) (h2M : 2 * M_sep ≤ h₀ a + 4 * n₀)
    {X : Set (ℝ × ℝ)} (hX : X.Finite) (hXM : X.ncard ≤ M_sep)
    (hX_n₀ : Disjoint (frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀)) X) :
    ∃ (j_row : ℕ) (Y_base : Set (ℝ × ℝ)),
      j_row ≤ M_sep ∧
      IsPreconnected Y_base ∧
      frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀) ⊆ Y_base ∧
      fig1RowSeg H_h j_row ⊆ Y_base ∧
      Y_base ⊆ fig1Set H_h \ (⋃ c : Fin t, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0)) ∧
      Disjoint Y_base X := by
  let i' := i₀ a - 4 * n₀
  let j' := j₀ a - 2 * n₀
  let h' := h₀ a + 4 * n₀
  have h1_ray : PairwiseDisjoint (Icc 0 (0 + M_sep)) (fig1LeftRay i' j') :=
    fun k₁ _ k₂ _ hne => disjoint_fig1LeftRay_of_ne i' j' hne
  obtain ⟨k₀, hk₀_mem, hk₀_disj⟩ := exists_disjoint_of_ncard_le hX hXM 0 h1_ray
  have hk₀_le : k₀ ≤ M_sep := by have := (mem_Icc.mp hk₀_mem).2; omega
  have h2_stack : PairwiseDisjoint (Icc 0 (0 + M_sep)) (fig1VertStack H_h) :=
    fun s₁ _ s₂ _ hne => disjoint_fig1VertStack_of_ne H_h (by omega) hne
  obtain ⟨s₀, hs₀_mem, hs₀_disj⟩ := exists_disjoint_of_ncard_le hX hXM 0 h2_stack
  have hs₀_le : s₀ ≤ M_sep := by have := (mem_Icc.mp hs₀_mem).2; omega
  have h3_row : PairwiseDisjoint (Icc 0 (0 + M_sep)) (fig1RowSeg H_h) := by
    intro j₁ _ j₂ _ hne
    change Disjoint (fig1RowSeg H_h j₁) (fig1RowSeg H_h j₂)
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨_, hy1⟩ ⟨_, hy2⟩
    simp only [mem_singleton_iff] at hy1 hy2
    exact hne (Nat.cast_injective (hy1.symm.trans hy2))
  obtain ⟨j_row, hj_mem, hj_disj⟩ := exists_disjoint_of_ncard_le hX hXM 0 h3_row
  have hj_le : j_row ≤ M_sep := by have := (mem_Icc.mp hj_mem).2; omega
  have h4_collar : ∀ c : Fin t, ∃ n_c ∈ Icc 1 (1 + M_sep),
      Disjoint (frontier (fig1Collar (i₀ c) (j₀ c) (h₀ c) n_c)) X := by
    intro c
    refine exists_disjoint_of_ncard_le hX hXM 1 (fun n₁ hn₁ n₂ hn₂ hne => ?_)
    have := hi₀_lo c
    have := hj₀_lo c
    have := (mem_Icc.mp hn₁).2
    have := (mem_Icc.mp hn₂).2
    exact disjoint_frontier_fig1Collar_of_ne (M := M) (by omega) (by omega)
      (by omega) (by omega) hne
  choose n_c hn_c_mem hn_c_disj using h4_collar
  have hn_c_le : ∀ c, 1 ≤ n_c c ∧ n_c c ≤ M := fun c => by
    have := (mem_Icc.mp (hn_c_mem c))
    omega
  -- Build the initial preconnected trunk `Y₀ = B_collar a n₀ ∪ Ray k₀ ∪ Stack s₀ ∪ Row j_row`
  let B₀ := frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀)
  let R₀ := fig1LeftRay i' j' k₀
  let S₀ := fig1VertStack H_h s₀
  let L₀ := fig1RowSeg H_h j_row
  let Y₀ := B₀ ∪ R₀ ∪ S₀ ∪ L₀
  have hha := (hh₀ a).1
  have hia_lo := hi₀_lo a
  have hja_lo := hj₀_lo a
  have hia_hi := hi₀_hi a
  have hja_hi := hj₀_hi a
  have h2k₀_le : 2 * k₀ ≤ h' := by omega
  have hj'_2k₀_lt : j' + 2 * k₀ < H_h := by omega
  have hBR_meet : (R₀ ∩ B₀).Nonempty :=
    fig1LeftRay_inter_frontier_nonempty (by omega) h2k₀_le
  have hRS_meet : (R₀ ∩ S₀).Nonempty :=
    fig1LeftRay_inter_fig1VertStack_nonempty (by omega) hj'_2k₀_lt
  have hSL_meet : (S₀ ∩ L₀).Nonempty :=
    fig1VertStack_inter_fig1RowSeg_nonempty (by omega) (by omega)
  have hBR_pre : IsPreconnected (B₀ ∪ R₀) := by
    obtain ⟨p, hpR, hpB⟩ := hBR_meet
    exact IsPreconnected.union p hpB hpR
      (isPreconnected_frontier_fig1Collar (by omega))
      (isPreconnected_fig1LeftRay i' j' k₀)
  have hBRS_pre : IsPreconnected (B₀ ∪ R₀ ∪ S₀) := by
    obtain ⟨p, hpR, hpS⟩ := hRS_meet
    exact IsPreconnected.union p (Or.inr hpR) hpS hBR_pre
      (isPreconnected_fig1VertStack H_h s₀)
  have hY₀_pre : IsPreconnected Y₀ := by
    obtain ⟨p, hpS, hpL⟩ := hSL_meet
    exact IsPreconnected.union p (Or.inr hpS) hpL hBRS_pre
      (isPreconnected_fig1RowSeg H_h j_row)
  -- Route `Y₀` around `fig1Collar (i₀ c) (j₀ c) (h₀ c) (n_c c)` for `c ∈ Finset.univ.erase a`
  let S_fin : Finset (Fin t) := Finset.univ.erase a
  let D : Fin t → Set (ℝ × ℝ) := fun c => fig1Collar (i₀ c) (j₀ c) (h₀ c) (n_c c)
  obtain ⟨Y_base, hY_pre, hY_sub, hY_disj, hY_mem⟩ :=
    exists_preconnected_routeFinset S_fin D
      (fun c _ => isClosed_fig1Collar _ _ _ _)
      (fun c _ => isPreconnected_frontier_fig1Collar (by have := (hh₀ c).1; omega))
      (fun c₁ hc₁ c₂ hc₂ hne => hsep c₁ c₂ hne _ (hn_c_le c₁).2 _ (hn_c_le c₂).2)
      hY₀_pre
  refine ⟨j_row, Y_base, hj_le, hY_pre, ?_, ?_, ?_, ?_⟩
  · -- `B₀ ⊆ Y_base`
    intro p hp
    refine hY_mem p (Or.inl (Or.inl (Or.inl hp))) (fun c hc hint => ?_)
    have hne : a ≠ c := (Finset.mem_erase.mp hc).1.symm
    exact Set.disjoint_left.mp (hsep a c hne n₀ hn₀ (n_c c) (hn_c_le c).2)
      ((isClosed_fig1Collar _ _ _ _).frontier_subset hp) (interior_subset hint)
  · -- `L₀ ⊆ Y_base`
    intro p hp
    refine hY_mem p (Or.inr hp) (fun c _ hint => ?_)
    have := hi₀_lo c
    have := hj₀_lo c
    have := (hn_c_le c).2
    exact Set.disjoint_left.mp
      (disjoint_fig1RowSeg_fig1Collar (by omega) (by omega) (by omega))
      hp (interior_subset hint)
  · -- `Y_base ⊆ fig1Set H_h \ ⋃ c, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0)`
    have hY₀_fig1 : Y₀ ⊆ fig1Set H_h := by
      refine union_subset (union_subset (union_subset ?_ ?_) ?_) ?_
      · exact frontier_fig1Collar_subset_fig1Set (by omega) (hh₀ a).2 (hi₀_even a) (hj₀_even a)
          (by omega) (by omega) (by omega) (by omega)
      · exact fig1LeftRay_subset_fig1Set (by omega) hj'_2k₀_lt
      · exact fig1VertStack_subset_fig1Set hH_two hH_even (by omega)
      · exact fig1RowSeg_subset_fig1Set (by omega)
    intro p hp
    refine ⟨?_, ?_⟩
    · rcases hY_sub hp with hpY₀ | hpFr
      · exact hY₀_fig1 hpY₀
      · obtain ⟨c, _, hpc⟩ := mem_iUnion₂.mp hpFr
        have := (hh₀ c).1
        have := hi₀_lo c
        have := hj₀_lo c
        have := hi₀_hi c
        have := hj₀_hi c
        have := (hn_c_le c).2
        exact frontier_fig1Collar_subset_fig1Set (by omega) (hh₀ c).2 (hi₀_even c) (hj₀_even c)
          (by omega) (by omega) (by omega) (by omega) hpc
    · intro hpInt
      obtain ⟨c, hpc⟩ := mem_iUnion.mp hpInt
      by_cases hca : c = a
      · subst hca
        have hsub0 : interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0) ⊆
            interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) n₀) := by
          rcases Nat.eq_zero_or_pos n₀ with rfl | hpos
          · exact Subset.rfl
          · exact interior_subset.trans
              (fig1Collar_subset_interior_of_lt hpos (by omega) (by omega))
        have hp_n₀ : p ∈ interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) n₀) := hsub0 hpc
        rcases hY_sub hp with (((hpB | hpR) | hpS) | hpL) | hpFr
        · exact hpB.2 hp_n₀
        · exact Set.disjoint_left.mp (disjoint_fig1LeftRay_interior_shifted i' j' h' k₀) hpR hp_n₀
        · exact Set.disjoint_left.mp
            (disjoint_fig1VertStack_fig1Collar (by omega) (by omega) (by omega) (by omega))
            hpS (interior_subset hp_n₀)
        · exact Set.disjoint_left.mp
            (disjoint_fig1RowSeg_fig1Collar (by omega) (by omega) (by omega))
            hpL (interior_subset hp_n₀)
        · obtain ⟨c', hc', hpc'⟩ := mem_iUnion₂.mp hpFr
          have hne : c' ≠ c := (Finset.mem_erase.mp hc').1
          exact Set.disjoint_left.mp (hsep c' c hne (n_c c') (hn_c_le c').2 n₀ hn₀)
            ((isClosed_fig1Collar _ _ _ _).frontier_subset hpc') (interior_subset hp_n₀)
      · have hc_mem : c ∈ S_fin := Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩
        have hsub0 : interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0) ⊆
            interior (D c) := by
          have hpos : 0 < n_c c := (hn_c_le c).1
          have := hi₀_lo c
          have := hj₀_lo c
          have := (hn_c_le c).2
          exact interior_subset.trans
            (fig1Collar_subset_interior_of_lt hpos (by omega) (by omega))
        exact Set.disjoint_left.mp (hY_disj c hc_mem) hp (hsub0 hpc)
  · -- `Disjoint Y_base X`
    rw [Set.disjoint_left]
    intro p hp hpX
    rcases hY_sub hp with (((hpB | hpR) | hpS) | hpL) | hpFr
    · exact Set.disjoint_left.mp hX_n₀ hpB hpX
    · exact Set.disjoint_left.mp hk₀_disj hpR hpX
    · exact Set.disjoint_left.mp hs₀_disj hpS hpX
    · exact Set.disjoint_left.mp hj_disj hpL hpX
    · obtain ⟨c, _, hpc⟩ := mem_iUnion₂.mp hpFr
      exact Set.disjoint_left.mp (hn_c_disj c) hpc hpX

/-! ## Eye Points and Short Horizontal Connectors to Collar Frontiers -/

/-- The 4 eye vertex coordinates `(i + 1, j + 2)`, `(i + 2h, j + 2)`, `(i + 2h, j + h - 2)`,
`(i + 1, j + h - 2)` of a subwall at `(i, j)` of height `h`. -/
def fig1EyeCoord (i j h : ℕ) : Fin 4 → ℝ × ℝ
  | ⟨0, _⟩ => (((i + 1 : ℕ) : ℝ), ((j + 2 : ℕ) : ℝ))
  | ⟨1, _⟩ => (((i + 2 * h : ℕ) : ℝ), ((j + 2 : ℕ) : ℝ))
  | ⟨2, _⟩ => (((i + 2 * h : ℕ) : ℝ), ((j + h - 2 : ℕ) : ℝ))
  | ⟨3, _⟩ => (((i + 1 : ℕ) : ℝ), ((j + h - 2 : ℕ) : ℝ))

/-- The 4 short horizontal connectors from `fig1EyeCoord i j h idx` to `frontier (fig1Collar i j h n)`. -/
def fig1EyeConnector (i j h n : ℕ) : Fin 4 → Set (ℝ × ℝ)
  | ⟨0, _⟩ => Icc ((i - 4 * n + 1 : ℕ) : ℝ) ((i + 1 : ℕ) : ℝ) ×ˢ {((j + 2 : ℕ) : ℝ)}
  | ⟨1, _⟩ => Icc ((i + 2 * h : ℕ) : ℝ) ((i + 2 * h + 4 * n : ℕ) : ℝ) ×ˢ {((j + 2 : ℕ) : ℝ)}
  | ⟨2, _⟩ => Icc ((i + 2 * h : ℕ) : ℝ) ((i + 2 * h + 4 * n : ℕ) : ℝ) ×ˢ {((j + h - 2 : ℕ) : ℝ)}
  | ⟨3, _⟩ => Icc ((i - 4 * n + 1 : ℕ) : ℝ) ((i + 1 : ℕ) : ℝ) ×ˢ {((j + h - 2 : ℕ) : ℝ)}

/-- Each `fig1EyeConnector i j h n idx` is preconnected. -/
theorem isPreconnected_fig1EyeConnector (i j h n : ℕ) (idx : Fin 4) :
    IsPreconnected (fig1EyeConnector i j h n idx) := by
  fin_cases idx <;> exact isPreconnected_Icc.prod isPreconnected_singleton

/-- Each `fig1EyeCoord i j h idx` belongs to `fig1EyeConnector i j h n idx` when `4n ≤ i`. -/
theorem fig1EyeCoord_mem_fig1EyeConnector {i j h n : ℕ} (hi : 4 * n ≤ i) (idx : Fin 4) :
    fig1EyeCoord i j h idx ∈ fig1EyeConnector i j h n idx := by
  have h1 : ((i - 4 * n + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
    have : i - 4 * n + 1 ≤ i + 1 := by omega
    exact_mod_cast this
  have h2 : ((i + 2 * h : ℕ) : ℝ) ≤ ((i + 2 * h + 4 * n : ℕ) : ℝ) := by
    have : i + 2 * h ≤ i + 2 * h + 4 * n := by omega
    exact_mod_cast this
  fin_cases idx <;> exact ⟨⟨by first | exact h1 | exact le_rfl,
    by first | exact le_rfl | exact h2⟩, rfl⟩

/-- The 4 connectors `fig1EyeConnector i j h n idx` are pairwise disjoint when `6 ≤ h`. -/
theorem disjoint_fig1EyeConnector_of_ne {i j h n : ℕ} (hh : 6 ≤ h)
    {idx₁ idx₂ : Fin 4} (hne : idx₁ ≠ idx₂) :
    Disjoint (fig1EyeConnector i j h n idx₁) (fig1EyeConnector i j h n idx₂) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  have hx_lt : ((i + 1 : ℕ) : ℝ) < ((i + 2 * h : ℕ) : ℝ) := by
    have : i + 1 < i + 2 * h := by omega
    exact_mod_cast this
  have hy_lt : ((j + 2 : ℕ) : ℝ) < ((j + h - 2 : ℕ) : ℝ) := by
    have : j + 2 < j + h - 2 := by omega
    exact_mod_cast this
  fin_cases idx₁ <;> fin_cases idx₂ <;> try exact (hne rfl).elim
  all_goals
    dsimp [fig1EyeConnector] at h1 h2
    rcases h1 with ⟨⟨hx1_lo, hx1_hi⟩, hy1⟩
    rcases h2 with ⟨⟨hx2_lo, hx2_hi⟩, hy2⟩
    simp only [mem_singleton_iff] at hy1 hy2
    linarith

/-- Each `fig1EyeConnector i j h n idx` meets `frontier (fig1Collar i j h n)` when `6 ≤ h`, `Even h`,
`4n ≤ i`, and `2n ≤ j`. -/
theorem fig1EyeConnector_inter_frontier_nonempty {i j h n : ℕ}
    (hh : 6 ≤ h) (he : Even h) (hi : 4 * n ≤ i) (hj : 2 * n ≤ j) (idx : Fin 4) :
    (fig1EyeConnector i j h n idx ∩ frontier (fig1Collar i j h n)).Nonempty := by
  have h1 : ((i - 4 * n + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
    have : i - 4 * n + 1 ≤ i + 1 := by omega
    exact_mod_cast this
  have h2 : ((i + 2 * h : ℕ) : ℝ) ≤ ((i + 2 * h + 4 * n : ℕ) : ℝ) := by
    have : i + 2 * h ≤ i + 2 * h + 4 * n := by omega
    exact_mod_cast this
  have h_even_2 : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  have h_even_h2 : Even (2 * n + h - 2) := by
    rcases he with ⟨m, hm⟩
    refine ⟨n + m - 1, ?_⟩
    omega
  have h_odd_1 : ¬ Even (2 * n + 1) := by
    rw [Nat.even_iff]
    omega
  have h_odd_h3 : ¬ Even (2 * n + h - 3) := by
    rcases he with ⟨m, hm⟩
    rw [Nat.even_iff]
    omega
  have hh6_r : (6 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hn0_r : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hh2_sub : ((h - 2 : ℕ) : ℝ) = (h : ℝ) - 2 := by
    have : (h - 2) + 2 = h := by omega
    have h1 : (((h - 2) + 2 : ℕ) : ℝ) = (h : ℝ) := by exact_mod_cast this
    push_cast at h1; linarith
  have hh3_sub : ((2 * n + h - 3 : ℕ) : ℝ) = 2 * (n : ℝ) + (h : ℝ) - 3 := by
    have : (2 * n + h - 3) + 3 = 2 * n + h := by omega
    have h1 : (((2 * n + h - 3) + 3 : ℕ) : ℝ) = ((2 * n + h : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h1; linarith
  have hh2_n_sub : ((2 * n + h - 2 : ℕ) : ℝ) = 2 * (n : ℝ) + (h : ℝ) - 2 := by
    have : (2 * n + h - 2) + 2 = 2 * n + h := by omega
    have h1 : (((2 * n + h - 2) + 2 : ℕ) : ℝ) = ((2 * n + h : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h1; linarith
  fin_cases idx
  · refine ⟨(((i - 4 * n + 1 : ℕ) : ℝ), ((j + 2 : ℕ) : ℝ)), ⟨⟨le_rfl, h1⟩, rfl⟩, ?_⟩
    unfold fig1Collar
    rw [← (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).image_frontier]
    refine ⟨(1, ((2 * n + 2 : ℕ) : ℝ)), ⟨subset_closure ?_,
      not_mem_interior_fig1EnclosedSet_of_even_le_one h_even_2 le_rfl⟩, ?_⟩
    · apply rect_subset_fig1EnclosedSet
      exact ⟨⟨le_rfl, by push_cast; linarith⟩, ⟨Nat.cast_nonneg _, by push_cast; linarith⟩⟩
    · have hj_eq : (2 * n + 2) + (j - 2 * n) = j + 2 := by omega
      ext <;> dsimp
      · push_cast; ring
      · exact_mod_cast hj_eq
  · refine ⟨(((i + 2 * h + 4 * n : ℕ) : ℝ), ((j + 2 : ℕ) : ℝ)), ⟨⟨h2, le_rfl⟩, rfl⟩, ?_⟩
    unfold fig1Collar
    rw [← (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).image_frontier]
    refine ⟨(((2 * (h + 4 * n) : ℕ) : ℝ), ((2 * n + 1 : ℕ) : ℝ) + 1), ⟨subset_closure ?_,
      not_mem_interior_fig1EnclosedSet_of_odd_ge_two_mul h_odd_1 (by push_cast; linarith)⟩, ?_⟩
    · apply rect_subset_fig1EnclosedSet
      exact ⟨⟨by push_cast; linarith, by push_cast; linarith⟩,
        ⟨by positivity, by push_cast; linarith⟩⟩
    · have hi_eq : 2 * (h + 4 * n) + (i - 4 * n) = i + 2 * h + 4 * n := by omega
      have hj_eq : (2 * n + 1) + 1 + (j - 2 * n) = j + 2 := by omega
      ext <;> dsimp
      · exact_mod_cast hi_eq
      · exact_mod_cast hj_eq
  · refine ⟨(((i + 2 * h + 4 * n : ℕ) : ℝ), ((j + h - 2 : ℕ) : ℝ)), ⟨⟨h2, le_rfl⟩, rfl⟩, ?_⟩
    unfold fig1Collar
    rw [← (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).image_frontier]
    refine ⟨(((2 * (h + 4 * n) : ℕ) : ℝ), ((2 * n + h - 3 : ℕ) : ℝ) + 1), ⟨subset_closure ?_,
      not_mem_interior_fig1EnclosedSet_of_odd_ge_two_mul h_odd_h3 (by push_cast; linarith)⟩, ?_⟩
    · apply rect_subset_fig1EnclosedSet
      exact ⟨⟨by push_cast; linarith, by push_cast; linarith⟩,
        ⟨by positivity, by rw [hh3_sub]; push_cast; linarith⟩⟩
    · have hi_eq : 2 * (h + 4 * n) + (i - 4 * n) = i + 2 * h + 4 * n := by omega
      have hj_eq : (2 * n + h - 3) + 1 + (j - 2 * n) = j + h - 2 := by omega
      ext <;> dsimp
      · exact_mod_cast hi_eq
      · exact_mod_cast hj_eq
  · refine ⟨(((i - 4 * n + 1 : ℕ) : ℝ), ((j + h - 2 : ℕ) : ℝ)), ⟨⟨le_rfl, h1⟩, rfl⟩, ?_⟩
    unfold fig1Collar
    rw [← (wallShiftRealHomeomorph (i - 4 * n) (j - 2 * n)).image_frontier]
    refine ⟨(1, ((2 * n + h - 2 : ℕ) : ℝ)), ⟨subset_closure ?_,
      not_mem_interior_fig1EnclosedSet_of_even_le_one h_even_h2 le_rfl⟩, ?_⟩
    · apply rect_subset_fig1EnclosedSet
      exact ⟨⟨le_rfl, by push_cast; linarith⟩,
        ⟨Nat.cast_nonneg _, by rw [hh2_n_sub]; push_cast; linarith⟩⟩
    · have hj_eq : (2 * n + h - 2) + (j - 2 * n) = j + h - 2 := by omega
      ext <;> dsimp
      · push_cast; ring
      · exact_mod_cast hj_eq

/-- Each `fig1EyeConnector i j h n idx` is contained in `fig1Collar i j h n \ interior (fig1Collar i j h 0)`
and in `fig1Set H_h` when `6 ≤ h`, `Even h`, `4n ≤ i`, `2n ≤ j`, `i + 2h + 4n ≤ 2 * H_h`, and
`j + h ≤ H_h`. -/
theorem fig1EyeConnector_subset {H_h i j h n : ℕ}
    (hh : 6 ≤ h) (he : Even h) (hi : 4 * n ≤ i) (hj : 2 * n ≤ j)
    (hi_hi : i + 2 * h + 4 * n ≤ 2 * H_h) (hj_hi : j + h ≤ H_h) (idx : Fin 4) :
    fig1EyeConnector i j h n idx ⊆ fig1Collar i j h n ∧
    Disjoint (fig1EyeConnector i j h n idx) (interior (fig1Collar i j h 0)) ∧
    fig1EyeConnector i j h n idx ⊆ fig1Set H_h := by
  have h_even_2 : Even (2 : ℕ) := ⟨1, rfl⟩
  have h_even_h2 : Even (h - 2) := by
    rcases he with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    omega
  have h_odd_1 : ¬ Even (1 : ℕ) := by decide
  have h_odd_h3 : ¬ Even (h - 3) := by
    rcases he with ⟨m, hm⟩
    rw [Nat.even_iff]
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- Subset of `fig1Collar i j h n`
    rintro ⟨x, y⟩ hxy
    unfold fig1Collar
    refine ⟨(x - ((i - 4 * n : ℕ) : ℝ), y - ((j - 2 * n : ℕ) : ℝ)), ?_,
      by ext <;> dsimp <;> ring⟩
    apply rect_subset_fig1EnclosedSet
    have hi_sub : ((i - 4 * n + 1 : ℕ) : ℝ) - ((i - 4 * n : ℕ) : ℝ) = 1 := by push_cast; ring
    have hi_add : ((i + 1 : ℕ) : ℝ) - ((i - 4 * n : ℕ) : ℝ) ≤ 2 * ((h + 4 * n : ℕ) : ℝ) := by
      have : i + 1 ≤ (i - 4 * n) + 2 * (h + 4 * n) := by omega
      have hcast : ((i + 1 : ℕ) : ℝ) ≤ (((i - 4 * n) + 2 * (h + 4 * n) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at hcast ⊢
      linarith
    have hi_r_lo : 1 ≤ ((i + 2 * h : ℕ) : ℝ) - ((i - 4 * n : ℕ) : ℝ) := by
      have : (i - 4 * n) + 1 ≤ i + 2 * h := by omega
      have hcast : (((i - 4 * n) + 1 : ℕ) : ℝ) ≤ ((i + 2 * h : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_add, Nat.cast_one] at hcast
      linarith
    have hi_r_hi : ((i + 2 * h + 4 * n : ℕ) : ℝ) - ((i - 4 * n : ℕ) : ℝ) =
        2 * ((h + 4 * n : ℕ) : ℝ) := by
      have : i + 2 * h + 4 * n = (i - 4 * n) + 2 * (h + 4 * n) := by omega
      have hcast : ((i + 2 * h + 4 * n : ℕ) : ℝ) = (((i - 4 * n) + 2 * (h + 4 * n) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at hcast ⊢
      linarith
    have hj_2_lo : 0 ≤ ((j + 2 : ℕ) : ℝ) - ((j - 2 * n : ℕ) : ℝ) := by
      have : j - 2 * n ≤ j + 2 := by omega
      have hcast : ((j - 2 * n : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hj_2_hi : ((j + 2 : ℕ) : ℝ) - ((j - 2 * n : ℕ) : ℝ) ≤ ((h + 4 * n : ℕ) : ℝ) := by
      have : j + 2 ≤ (j - 2 * n) + (h + 4 * n) := by omega
      have hcast : ((j + 2 : ℕ) : ℝ) ≤ (((j - 2 * n) + (h + 4 * n) : ℕ) : ℝ) :=
        Nat.cast_le.mpr this
      rw [Nat.cast_add (j - 2 * n) (h + 4 * n)] at hcast
      linarith
    have hj_h2_lo : 0 ≤ ((j + h - 2 : ℕ) : ℝ) - ((j - 2 * n : ℕ) : ℝ) := by
      have : j - 2 * n ≤ j + h - 2 := by omega
      have hcast : ((j - 2 * n : ℕ) : ℝ) ≤ ((j + h - 2 : ℕ) : ℝ) := Nat.cast_le.mpr this
      linarith
    have hj_h2_hi : ((j + h - 2 : ℕ) : ℝ) - ((j - 2 * n : ℕ) : ℝ) ≤ ((h + 4 * n : ℕ) : ℝ) := by
      have : j + h - 2 ≤ (j - 2 * n) + (h + 4 * n) := by omega
      have hcast : ((j + h - 2 : ℕ) : ℝ) ≤ (((j - 2 * n) + (h + 4 * n) : ℕ) : ℝ) :=
        Nat.cast_le.mpr this
      rw [Nat.cast_add (j - 2 * n) (h + 4 * n)] at hcast
      linarith
    fin_cases idx <;>
    · dsimp [fig1EyeConnector] at hxy
      rcases hxy with ⟨⟨hx_lo, hx_hi⟩, hy⟩
      simp only [mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · -- Disjoint from `interior (fig1Collar i j h 0)`
    rw [fig1Collar_zero, ← (wallShiftRealHomeomorph i j).image_interior, Set.disjoint_left]
    rintro ⟨x, y⟩ hxy ⟨⟨x₀, y₀⟩, hint, heq⟩
    have hx_eq : x₀ + (i : ℝ) = x := congrArg Prod.fst heq
    have hy_eq : y₀ + (j : ℝ) = y := congrArg Prod.snd heq
    fin_cases idx
    · dsimp [fig1EyeConnector] at hxy
      rcases hxy with ⟨⟨_, hx_hi⟩, hy⟩
      simp only [mem_singleton_iff] at hy
      have hx₀_le : x₀ ≤ 1 := by push_cast at hx_hi; linarith
      have hy₀_eq : y₀ = ((2 : ℕ) : ℝ) := by rw [hy] at hy_eq; push_cast at hy_eq ⊢; linarith
      rw [hy₀_eq] at hint
      exact not_mem_interior_fig1EnclosedSet_of_even_le_one h_even_2 hx₀_le hint
    · dsimp [fig1EyeConnector] at hxy
      rcases hxy with ⟨⟨hx_lo, _⟩, hy⟩
      simp only [mem_singleton_iff] at hy
      have hx₀_ge : 2 * (h : ℝ) ≤ x₀ := by push_cast at hx_lo; linarith
      have hy₀_eq : y₀ = ((1 : ℕ) : ℝ) + 1 := by rw [hy] at hy_eq; push_cast at hy_eq ⊢; linarith
      rw [hy₀_eq] at hint
      exact not_mem_interior_fig1EnclosedSet_of_odd_ge_two_mul h_odd_1 hx₀_ge hint
    · dsimp [fig1EyeConnector] at hxy
      rcases hxy with ⟨⟨hx_lo, _⟩, hy⟩
      simp only [mem_singleton_iff] at hy
      have hx₀_ge : 2 * (h : ℝ) ≤ x₀ := by push_cast at hx_lo; linarith
      have hy₀_eq : y₀ = ((h - 3 : ℕ) : ℝ) + 1 := by
        have : j + h - 2 = j + (h - 3) + 1 := by omega
        rw [hy, this] at hy_eq
        push_cast at hy_eq ⊢
        linarith
      rw [hy₀_eq] at hint
      exact not_mem_interior_fig1EnclosedSet_of_odd_ge_two_mul h_odd_h3 hx₀_ge hint
    · dsimp [fig1EyeConnector] at hxy
      rcases hxy with ⟨⟨_, hx_hi⟩, hy⟩
      simp only [mem_singleton_iff] at hy
      have hx₀_le : x₀ ≤ 1 := by push_cast at hx_hi; linarith
      have hy₀_eq : y₀ = ((h - 2 : ℕ) : ℝ) := by
        have : j + h - 2 = j + (h - 2) := by omega
        rw [hy, this] at hy_eq
        push_cast at hy_eq ⊢
        linarith
      rw [hy₀_eq] at hint
      exact not_mem_interior_fig1EnclosedSet_of_even_le_one h_even_h2 hx₀_le hint
  · -- Subset of `fig1Set H_h`
    have hx_lo1 : (1 : ℝ) ≤ ((i - 4 * n + 1 : ℕ) : ℝ) := by
      have : 1 ≤ i - 4 * n + 1 := by omega
      exact_mod_cast this
    have hx_hi1 : ((i + 1 : ℕ) : ℝ) ≤ 2 * (H_h : ℝ) + 1 := by
      have : i + 1 ≤ 2 * H_h + 1 := by omega
      exact_mod_cast this
    have hx_lo2 : (1 : ℝ) ≤ ((i + 2 * h : ℕ) : ℝ) := by
      have : 1 ≤ i + 2 * h := by omega
      exact_mod_cast this
    have hx_hi2 : ((i + 2 * h + 4 * n : ℕ) : ℝ) ≤ 2 * (H_h : ℝ) + 1 := by
      have : i + 2 * h + 4 * n ≤ 2 * H_h + 1 := by omega
      exact_mod_cast this
    fin_cases idx
    · refine Subset.trans ?_ (fig1RowSeg_subset_fig1Set (j := j + 2) (by omega))
      rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, hy⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
    · refine Subset.trans ?_ (fig1RowSeg_subset_fig1Set (j := j + 2) (by omega))
      rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, hy⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
    · refine Subset.trans ?_ (fig1RowSeg_subset_fig1Set (j := j + h - 2) (by omega))
      rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, hy⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
    · refine Subset.trans ?_ (fig1RowSeg_subset_fig1Set (j := j + h - 2) (by omega))
      rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, hy⟩
      exact ⟨⟨by linarith, by linarith⟩, hy⟩

/-! ## Punctured Sphere Drawing of a Fig. 1 Wall and Controlling Bottom-Subwall Tangle -/

/-- `fig1Segment p q` is compact. -/
theorem isCompact_fig1Segment (p q : ℕ × ℕ) : IsCompact (fig1Segment p q) := by
  unfold fig1Segment GM16.horizontalLatticeLine GM16.verticalLatticeLine
  split_ifs
  · exact isCompact_Icc.prod isCompact_singleton
  · exact isCompact_singleton.prod isCompact_Icc

/-- Full coordinate representation of a Fig. 1 drawn wall `W`: in addition to `exists_fig1Coords`,
provides the plane coordinate drawing `Γ₀` (`IsFigure1CoordDrawing W.toWall Γ₀`), the branch-vertex
position identity `pos (W.toWall.branchVertex p hp) = (p.1, p.2)`, and the exact union identity
`⋃ f, closure (Γ.iso.edgeEquiv f.1).1 = fig1Sph φ '' fig1Segment p q` on each base edge. -/
theorem DrawnWall.IsFigure1.exists_fig1Coords_full {W : DrawnWall α β} (hW : W.IsFigure1) :
    ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ₀ : GraphDrawing W.graph EuclideanPlane)
      (pos : α → ℝ × ℝ) (Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)),
      IsFigure1CoordDrawing W.toWall Γ₀ ∧
      W.drawingU = φ '' Γ₀.drawing.U ∧
      (∀ (v : α) (hv : v ∈ V(W.graph)), W.vertexPoint v = φ (Γ₀.iso.vertexEquiv ⟨v, hv⟩).1) ∧
      (∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height) ∧
      InjOn pos V(W.graph) ∧
      (∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
        pos (W.toWall.branchVertex p hp) = ((p.1 : ℝ), (p.2 : ℝ))) ∧
      Γ.drawing.U = fig1Sph φ '' fig1Set W.height ∧
      (∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) ∧
      (∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
          (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q) ∧
      (∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
        (⋃ f : {f : E(W.graph) // f.1 ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj))},
          closure (Γ.iso.edgeEquiv f.1).1) = fig1Sph φ '' fig1Segment p q) ∧
      Γ.drawing.IsTwoCell := by
  classical
  obtain ⟨φ, Γ₀, hΓ₀, hU, hv⟩ := hW
  have hUc : IsCompact Γ₀.drawing.U := by
    rw [hΓ₀.drawing_U_eq]; exact isCompact_fig1WallSet _
  let F : EuclideanPlane → OnePoint EuclideanPlane := fun x =>
    ((φ x : EuclideanPlane) : OnePoint EuclideanPlane)
  have hF : Continuous F := OnePoint.continuous_coe.comp φ.continuous
  have hinj : InjOn F Γ₀.drawing.U := fun x _ y _ hxy =>
    φ.injective (OnePoint.coe_injective hxy)
  obtain ⟨Γ, hΓU, -, hΓv, -, hΓe, -⟩ := GM09.GraphDrawing.transportOn Γ₀ hUc hF.continuousOn hinj
  let pos : α → ℝ × ℝ := fun v => if hv : v ∈ V(W.graph) then
    fig1PlaneEquiv.symm (Γ₀.iso.vertexEquiv ⟨v, hv⟩).1 else 0
  have hpos : ∀ x : V(W.graph), fig1PlaneEquiv (pos x.1) = (Γ₀.iso.vertexEquiv x).1 := by
    intro x
    simp only [pos, dite_eq_left x.2, Homeomorph.apply_symm_apply]
  have hU0 : Γ₀.drawing.U = fig1PlaneEquiv '' fig1Set W.height := by
    rw [hΓ₀.drawing_U_eq, fig1WallSet_eq_image_fig1Set]
  have hΓe_sub : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β)
      (hf : f ∈ E(W.graph)),
      f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q := by
    intro p q hadj f hf hfP
    have h0 : GM09.graphDrawingEdgeSet Γ f = (Γ.iso.edgeEquiv ⟨f, hf⟩).1 := by
      ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
    have h0' : GM09.graphDrawingEdgeSet Γ₀ f = (Γ₀.iso.edgeEquiv ⟨f, hf⟩).1 := by
      ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
    have h1 := hΓe f
    rw [h0, h0'] at h1
    rw [h1]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ fig1PlaneEquiv '' fig1Segment p q := by
      rw [← hΓ₀.path_on_segment p q hadj]
      exact mem_iUnion₂.mpr ⟨⟨f, hf⟩, hfP, subset_closure hz⟩
    obtain ⟨w, hw, rfl⟩ := hz'
    exact ⟨w, hw, rfl⟩
  refine ⟨φ, Γ₀, pos, Γ, hΓ₀, hU, hv, ?_, ?_, ?_, ?_, ?_, hΓe_sub, ?_, ?_⟩
  · intro v hv_mem
    have h1 := Γ₀.drawing.V_subset_U (Γ₀.iso.vertexEquiv ⟨v, hv_mem⟩).2
    rw [← hpos ⟨v, hv_mem⟩, hU0] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    rwa [← fig1PlaneEquiv.injective hzeq]
  · intro u hu w hw huv
    have h1 : fig1PlaneEquiv (pos u) = fig1PlaneEquiv (pos w) := by rw [huv]
    rw [hpos ⟨u, hu⟩, hpos ⟨w, hw⟩] at h1
    have := Γ₀.iso.vertexEquiv.injective (Subtype.ext h1)
    exact congrArg Subtype.val this
  · intro p hp
    have hb_mem := W.toWall.branchVertex_mem_vertexSet p hp
    have h1 := hpos ⟨W.toWall.branchVertex p hp, hb_mem⟩
    rw [hΓ₀.branchVertex_point p hp hb_mem] at h1
    exact fig1PlaneEquiv.injective h1
  · rw [hΓU, hU0, image_image]
    rfl
  · intro x
    rw [hΓv x, ← hpos x]
    rfl
  · intro p q hadj
    apply Subset.antisymm
    · refine iUnion_subset fun f => ?_
      have hcl : IsClosed (fig1Sph φ '' fig1Segment p q) :=
        ((isCompact_fig1Segment p q).image (isOpenEmbedding_fig1Sph φ).continuous).isClosed
      exact closure_minimal (hΓe_sub p q hadj f.1.1 f.1.2 f.2) hcl
    · rintro _ ⟨w, hw, rfl⟩
      have hw0 : fig1PlaneEquiv w ∈ fig1PlaneEquiv '' fig1Segment p q := ⟨w, hw, rfl⟩
      rw [← hΓ₀.path_on_segment p q hadj] at hw0
      obtain ⟨f₀, hf₀P, hwf₀⟩ := mem_iUnion₂.mp hw0
      refine mem_iUnion.mpr ⟨⟨f₀, hf₀P⟩, ?_⟩
      have h0 : GM09.graphDrawingEdgeSet Γ f₀.1 = (Γ.iso.edgeEquiv f₀).1 := by
        ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨f₀.2, h⟩⟩
      have h0' : GM09.graphDrawingEdgeSet Γ₀ f₀.1 = (Γ₀.iso.edgeEquiv f₀).1 := by
        ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨f₀.2, h⟩⟩
      have h1 := hΓe f₀.1
      rw [h0, h0'] at h1
      rw [h1]
      exact image_closure_subset_closure_image hF ⟨fig1PlaneEquiv w, hwf₀, rfl⟩
  · have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
    refine fig1_isTwoCell GM09.isClosedSurface_sphere hsph (isOpenEmbedding_fig1Sph φ)
      W.toWall.even_height W.toWall.two_le_height ?_
    rw [hΓU, hU0, image_image]
    rfl

/-- For an interior base edge `(p, q)` of `(i₀, j₀, h₀)` (`hadj : elementaryWallAdj h p q`), every
point of `fig1Segment p q` other than its two endpoints `(p.1, p.2)` and `(q.1, q.2)` lies in
`interior (fig1Collar i₀ j₀ h₀ 0)`. -/
theorem interior_fig1Segment_subset_interior_fig1Collar {h i₀ j₀ h₀ : ℕ}
    {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q)
    (hint_edge : isInteriorBaseEdge i₀ j₀ h₀ p q) :
    fig1Segment p q \ {((p.1 : ℝ), (p.2 : ℝ)), ((q.1 : ℝ), (q.2 : ℝ))} ⊆
      interior (fig1Collar i₀ j₀ h₀ 0) := by
  rw [fig1Collar_zero, ← (wallShiftRealHomeomorph i₀ j₀).image_interior]
  rintro ⟨x, y⟩ ⟨hseg, hne⟩
  refine ⟨(x - (i₀ : ℝ), y - (j₀ : ℝ)),
    open_rect_subset_interior_fig1EnclosedSet h₀ ?_, by ext <;> dsimp <;> ring⟩
  have hnot_p : (x, y) ≠ ((p.1 : ℝ), (p.2 : ℝ)) := fun h => hne (Or.inl h)
  have hnot_q : (x, y) ≠ ((q.1 : ℝ), (q.2 : ℝ)) := fun h => hne (Or.inr h)
  rcases hint_edge with ⟨hpq2, hj_lo, hj_hi, hi_lo, hi_hi⟩ | ⟨hpq1, hj_lo, hj_hi, hi_lo, hi_hi⟩
  · -- Horizontal interior edge
    unfold fig1Segment at hseg
    rw [ite_eq_left_iff.mpr fun h => (h hpq2).elim] at hseg
    rcases hseg with ⟨⟨hx1, hx2⟩, hy⟩
    simp only [mem_singleton_iff] at hy
    have hp2_min : min p.2 q.2 = p.2 := by rw [hpq2, min_self]
    rw [hp2_min] at hy
    have hmax1 : max p.1 q.1 = min p.1 q.1 + 1 := by
      rcases hadj.2.2 with ⟨_, h1 | h1⟩ | ⟨h2, _⟩ <;> omega
    have hx_ne_min : x ≠ ((min p.1 q.1 : ℕ) : ℝ) := by
      intro heq
      rcases min_choice p.1 q.1 with hmin | hmin
      · exact hnot_p (Prod.ext (heq.trans (congrArg Nat.cast hmin)) hy)
      · exact hnot_q (Prod.ext (heq.trans (congrArg Nat.cast hmin))
          (hy.trans (congrArg Nat.cast hpq2)))
    have hx_ne_max : x ≠ ((min p.1 q.1 : ℕ) : ℝ) + 1 := by
      intro heq
      have hmax_cast : ((min p.1 q.1 : ℕ) : ℝ) + 1 = ((max p.1 q.1 : ℕ) : ℝ) := by
        have h1 := congrArg (Nat.cast (R := ℝ)) hmax1.symm
        rw [Nat.cast_add, Nat.cast_one] at h1
        exact h1
      rcases max_choice p.1 q.1 with hmax | hmax
      · exact hnot_p (Prod.ext (heq.trans (hmax_cast.trans (congrArg Nat.cast hmax))) hy)
      · exact hnot_q (Prod.ext (heq.trans (hmax_cast.trans (congrArg Nat.cast hmax)))
          (hy.trans (congrArg Nat.cast hpq2)))
    have hx_gt : ((min p.1 q.1 : ℕ) : ℝ) < x := lt_of_le_of_ne hx1 hx_ne_min.symm
    have hx_lt : x < ((min p.1 q.1 : ℕ) : ℝ) + 1 := lt_of_le_of_ne hx2 hx_ne_max
    have hi_lo_r : (i₀ : ℝ) + 1 ≤ ((min p.1 q.1 : ℕ) : ℝ) := by
      have h1 : (((i₀ + 1 : ℕ) : ℝ)) ≤ ((min p.1 q.1 : ℕ) : ℝ) := Nat.cast_le.mpr hi_lo
      rw [Nat.cast_add, Nat.cast_one] at h1; exact h1
    have hi_hi_r : ((min p.1 q.1 : ℕ) : ℝ) + 1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
      have : min p.1 q.1 + 1 ≤ i₀ + 2 * h₀ := by omega
      have h1 : (((min p.1 q.1 + 1 : ℕ) : ℝ)) ≤ (((i₀ + 2 * h₀ : ℕ) : ℝ)) := Nat.cast_le.mpr this
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h1; exact h1
    have hj_lo_r : (j₀ : ℝ) < (p.2 : ℝ) := by exact_mod_cast hj_lo
    have hj_hi_r : (p.2 : ℝ) < (j₀ : ℝ) + (h₀ : ℝ) := by exact_mod_cast hj_hi
    exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, ⟨by dsimp; linarith, by dsimp; linarith⟩⟩
  · -- Vertical interior edge
    have hpq2_ne : p.2 ≠ q.2 := by
      rcases hadj.2.2 with ⟨h1, _⟩ | ⟨_, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
    unfold fig1Segment at hseg
    rw [ite_eq_right_iff.mpr fun h => (hpq2_ne h).elim] at hseg
    rcases hseg with ⟨hx, ⟨hy1, hy2⟩⟩
    simp only [mem_singleton_iff] at hx
    have hp1_min : min p.1 q.1 = p.1 := by rw [hpq1, min_self]
    rw [hp1_min] at hx
    have hmax2 : max p.2 q.2 = min p.2 q.2 + 1 := by
      rcases hadj.2.2 with ⟨h1, _⟩ | ⟨_, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
    have hy_ne_min : y ≠ ((min p.2 q.2 : ℕ) : ℝ) := by
      intro heq
      rcases min_choice p.2 q.2 with hmin | hmin
      · exact hnot_p (Prod.ext hx (heq.trans (congrArg Nat.cast hmin)))
      · exact hnot_q (Prod.ext (hx.trans (congrArg Nat.cast hpq1))
          (heq.trans (congrArg Nat.cast hmin)))
    have hy_ne_max : y ≠ ((min p.2 q.2 : ℕ) : ℝ) + 1 := by
      intro heq
      have hmax_cast : ((min p.2 q.2 : ℕ) : ℝ) + 1 = ((max p.2 q.2 : ℕ) : ℝ) := by
        have h1 := congrArg (Nat.cast (R := ℝ)) hmax2.symm
        rw [Nat.cast_add, Nat.cast_one] at h1
        exact h1
      rcases max_choice p.2 q.2 with hmax | hmax
      · exact hnot_p (Prod.ext hx (heq.trans (hmax_cast.trans (congrArg Nat.cast hmax))))
      · exact hnot_q (Prod.ext (hx.trans (congrArg Nat.cast hpq1))
          (heq.trans (hmax_cast.trans (congrArg Nat.cast hmax))))
    have hy_gt : ((min p.2 q.2 : ℕ) : ℝ) < y := lt_of_le_of_ne hy1 hy_ne_min.symm
    have hy_lt : y < ((min p.2 q.2 : ℕ) : ℝ) + 1 := lt_of_le_of_ne hy2 hy_ne_max
    have hi_lo_r : (i₀ : ℝ) + 2 ≤ (p.1 : ℝ) := by exact_mod_cast hi_lo
    have hi_hi_r : (p.1 : ℝ) + 1 ≤ (i₀ : ℝ) + 2 * (h₀ : ℝ) := by
      have : p.1 + 1 ≤ i₀ + 2 * h₀ := by omega
      exact_mod_cast this
    have hj_lo_r : (j₀ : ℝ) ≤ ((min p.2 q.2 : ℕ) : ℝ) := Nat.cast_le.mpr hj_lo
    have hj_hi_r : ((min p.2 q.2 : ℕ) : ℝ) + 1 ≤ (j₀ : ℝ) + (h₀ : ℝ) := by
      have : min p.2 q.2 + 1 ≤ j₀ + h₀ := by omega
      have h1 : (((min p.2 q.2 + 1 : ℕ) : ℝ)) ≤ (((j₀ + h₀ : ℕ) : ℝ)) := Nat.cast_le.mpr this
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_add] at h1; exact h1
    exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, ⟨by dsimp; linarith, by dsimp; linarith⟩⟩

/-- Basic topological and drawing properties of the punctured sphere drawing
`Γ' := clearedSubdrawing Γ.drawing (⋃ a, interior (fig1Sph φ '' fig1Collar (i₀ a) (j₀ a) (h₀ a) 0))`. -/
theorem puncturedWallDrawing_props {W : DrawnWall α β} {t : ℕ}
    {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    (hΓe_cl : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      (⋃ f : {f : E(W.graph) // f.1 ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj))},
        closure (Γ.iso.edgeEquiv f.1).1) = fig1Sph φ '' fig1Segment p q)
    (i₀ j₀ h₀ : Fin t → ℕ)
    (hh₀ : ∀ a, 6 ≤ h₀ a ∧ Even (h₀ a))
    (hi₀_even : ∀ a, Even (i₀ a))
    (hj₀_even : ∀ a, Even (j₀ a))
    (hi₀_lo : ∀ a, 4 ≤ i₀ a)
    (hj₀_lo : ∀ a, 2 ≤ j₀ a)
    (hi₀_hi : ∀ a, i₀ a + 2 * h₀ a + 4 ≤ 2 * W.height)
    (hj₀_hi : ∀ a, j₀ a + h₀ a + 2 ≤ W.height)
    (hsep0 : ∀ a b, a ≠ b →
      Disjoint (fig1Collar (i₀ a) (j₀ a) (h₀ a) 0) (fig1Collar (i₀ b) (j₀ b) (h₀ b) 0)) :
    let K_a : Fin t → Set (ℝ × ℝ) := fun a => fig1Collar (i₀ a) (j₀ a) (h₀ a) 0
    let D_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => fig1Sph φ '' K_a a
    let Λ : Set (OnePoint EuclideanPlane) := ⋃ a : Fin t, interior (D_a a)
    let Γ' : Drawing (OnePoint EuclideanPlane) := clearedSubdrawing Γ.drawing Λ
    let r_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => interior (D_a a)
    let C_a : Fin t → Drawing (OnePoint EuclideanPlane) := fun a => Γ'.interSet (subBd (r_a a))
    (∀ a, IsClosedDisc (D_a a)) ∧
    (∀ a, interior (D_a a) = fig1Sph φ '' interior (K_a a)) ∧
    (∀ a, discBd (D_a a) = fig1Sph φ '' frontier (K_a a)) ∧
    Γ'.U = fig1Sph φ '' (fig1Set W.height \ ⋃ a : Fin t, interior (K_a a)) ∧
    (∀ a, r_a a ∈ Γ'.R ∧ subBd (r_a a) = fig1Sph φ '' frontier (K_a a)) ∧
    (∀ a, (C_a a).IsCircuit ∧ (C_a a).IsSubdrawing Γ' ∧ (C_a a).U = subBd (r_a a)) ∧
    Function.Injective r_a ∧
    Γ'.IsTwoCell := by
  intro K_a D_a Λ Γ' r_a C_a
  have hS := GM09.isClosedSurface_sphere
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hEmb := isOpenEmbedding_fig1Sph φ
  have hD_disc : ∀ a, IsClosedDisc (D_a a) := by
    intro a
    dsimp [D_a, K_a, fig1Collar]
    rw [← image_comp]
    have hf_a : Topology.IsOpenEmbedding (fig1Sph φ ∘ wallShiftRealHomeomorph (i₀ a) (j₀ a)) :=
      hEmb.comp (wallShiftRealHomeomorph (i₀ a) (j₀ a)).isOpenEmbedding
    have := (hh₀ a).1
    exact isClosedDisc_image_fig1EnclosedSet hS hf_a.isEmbedding (by omega)
  have hD_int : ∀ a, interior (D_a a) = fig1Sph φ '' interior (K_a a) := by
    intro a
    refine Subset.antisymm ?_ (interior_maximal (image_mono interior_subset)
      (hEmb.isOpenMap _ isOpen_interior))
    intro y hy
    obtain ⟨x, _, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    have hU : fig1Sph φ ⁻¹' interior (D_a a) ⊆ K_a a := by
      intro z hz
      obtain ⟨z', hz', hzz'⟩ := interior_subset hz
      rwa [← hEmb.injective hzz']
    exact interior_maximal hU (isOpen_interior.preimage hEmb.continuous) hy
  have hD_fr : ∀ a, frontier (D_a a) = fig1Sph φ '' frontier (K_a a) := by
    intro a
    have hcl : closure (D_a a) = fig1Sph φ '' closure (K_a a) := by
      rw [(hD_disc a).isClosed.closure_eq, (isClosed_fig1Collar _ _ _ _).closure_eq]
    rw [frontier, frontier, hcl, hD_int a, Set.image_sdiff hEmb.injective]
  have hD_bd : ∀ a, discBd (D_a a) = fig1Sph φ '' frontier (K_a a) := by
    intro a
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hS (hD_disc a), hD_fr a]
  have hΛ_eq : Λ = fig1Sph φ '' (⋃ a : Fin t, interior (K_a a)) := by
    dsimp [Λ]
    rw [image_iUnion]
    exact iUnion_congr hD_int
  have hclosed_compl : IsClosed (univ \ Λ) :=
    isClosed_univ.sdiff (isOpen_iUnion fun a => isOpen_interior)
  -- Non-interior base edges survive in `Γ'`
  have hSeg_in_Γ' : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      (∀ a, ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p q) →
      (∀ f (hf : f ∈ E(W.graph)),
        f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∈ Γ'.E) ∧
      fig1Sph φ '' fig1Segment p q ⊆ Γ'.U := by
    intro p q hadj hnot_int
    have hdisj_seg : ∀ a, Disjoint (fig1Segment p q) (interior (K_a a)) := by
      intro a
      exact disjoint_fig1Segment_interior_of_not_isInteriorBaseEdge
        (hi₀_even a) (hj₀_even a) hadj (hnot_int a)
    have hE_mem : ∀ f (hf : f ∈ E(W.graph)),
        f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∈ Γ'.E := by
      intro f hf hfP
      change (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∈ (Γ.drawing.interSet (univ \ Λ)).E
      rw [GM11.mem_interSet_E_iff]
      refine ⟨(Γ.iso.edgeEquiv ⟨f, hf⟩).2, fun x hx => ⟨mem_univ x, ?_⟩⟩
      rw [hΛ_eq]
      rintro ⟨z, hzInt, hxz⟩
      obtain ⟨w, hwSeg, hxw⟩ := hΓe p q hadj f hf hfP hx
      rw [← hEmb.injective (hxw.trans hxz.symm)] at hzInt
      obtain ⟨a, hza⟩ := mem_iUnion.mp hzInt
      exact Set.disjoint_left.mp (hdisj_seg a) hwSeg hza
    refine ⟨hE_mem, ?_⟩
    rw [← hΓe_cl p q hadj]
    exact iUnion_subset fun f => Γ'.closure_subset_U (hE_mem f.1.1 f.1.2 f.2)
  have hΓ'U : Γ'.U = fig1Sph φ '' (fig1Set W.height \ ⋃ a : Fin t, interior (K_a a)) := by
    apply Subset.antisymm
    · intro x hx
      have hxH : x ∈ Γ.drawing.U := interSet_isSub.U_subset hx
      have hxOut : x ∉ Λ := (interSet_U_subset hclosed_compl hx).2
      rw [hΓU] at hxH
      obtain ⟨z, hz, rfl⟩ := hxH
      refine ⟨z, ⟨hz, fun hzInt => hxOut ?_⟩, rfl⟩
      rw [hΛ_eq]
      exact ⟨z, hzInt, rfl⟩
    · rintro _ ⟨z, ⟨hz_set, hz_not_int⟩, rfl⟩
      have hnot_int : ∀ a, z ∉ interior (K_a a) := fun a hza =>
        hz_not_int (mem_iUnion.mpr ⟨a, hza⟩)
      -- Choose a non-interior base edge containing `z`
      have hz_set' := hz_set
      simp only [fig1Set, mem_iUnion] at hz_set'
      obtain ⟨p₀, q₀, hadj₀, hz_seg₀⟩ := hz_set'
      by_cases hall : ∀ a, ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p₀ q₀
      · exact (hSeg_in_Γ' p₀ q₀ hadj₀ hall).2 ⟨z, hz_seg₀, rfl⟩
      · push Not at hall
        obtain ⟨a, hint_a⟩ := hall
        have ha_bounds := (hh₀ a).1
        have := hi₀_lo a
        have := hj₀_lo a
        have := hi₀_hi a
        have := hj₀_hi a
        obtain ⟨p, q, hadj, hnot_a, hseg_sub, hz_seg⟩ :=
          exists_nonInterior_baseEdge_of_not_mem_interior
            (by omega) (by omega) (by omega) (hh₀ a).2 (by omega) (by omega)
            hadj₀ hint_a hz_seg₀ (hnot_int a)
        have hall' : ∀ b, ¬ isInteriorBaseEdge (i₀ b) (j₀ b) (h₀ b) p q := by
          intro b hb_int
          by_cases hba : b = a
          · exact hnot_a (hba ▸ hb_int)
          · -- The midpoint of `fig1Segment p q` lies in `K_a a` and `interior (K_b b)`
            let mid : ℝ × ℝ := (((p.1 : ℝ) + (q.1 : ℝ)) / 2, ((p.2 : ℝ) + (q.2 : ℝ)) / 2)
            have hmid_seg : mid ∈ fig1Segment p q := by
              unfold fig1Segment
              split_ifs with hpq2
              · unfold GM16.horizontalLatticeLine
                have hp2_min : min p.2 q.2 = p.2 := by rw [hpq2, min_self]
                have hmax1 : max p.1 q.1 = min p.1 q.1 + 1 := by
                  rcases hadj.2.2 with ⟨_, h1 | h1⟩ | ⟨h2, _⟩ <;> omega
                have hsum1 : (p.1 : ℝ) + (q.1 : ℝ) = 2 * ((min p.1 q.1 : ℕ) : ℝ) + 1 := by
                  have : p.1 + q.1 = 2 * min p.1 q.1 + 1 := by omega
                  exact_mod_cast this
                refine ⟨⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩, ?_⟩
                simp only [mem_singleton_iff, mid, hp2_min]
                rw [hpq2]
                ring
              · unfold GM16.verticalLatticeLine
                have hp1_eq : p.1 = q.1 := by
                  rcases hadj.2.2 with ⟨h1, _⟩ | ⟨h2, _⟩
                  · exact (hpq2 h1).elim
                  · exact h2
                have hp1_min : min p.1 q.1 = p.1 := by rw [hp1_eq, min_self]
                have hmax2 : max p.2 q.2 = min p.2 q.2 + 1 := by
                  rcases hadj.2.2 with ⟨h1, _⟩ | ⟨_, ⟨h2, _⟩ | ⟨h2, _⟩⟩ <;> omega
                have hsum2 : (p.2 : ℝ) + (q.2 : ℝ) = 2 * ((min p.2 q.2 : ℕ) : ℝ) + 1 := by
                  have : p.2 + q.2 = 2 * min p.2 q.2 + 1 := by omega
                  exact_mod_cast this
                refine ⟨?_, ⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩⟩
                simp only [mem_singleton_iff, mid, hp1_min]
                rw [hp1_eq]
                ring
            have hmid_ne : mid ∉ ({((p.1 : ℝ), (p.2 : ℝ)), ((q.1 : ℝ), (q.2 : ℝ))} : Set (ℝ × ℝ)) := by
              rintro (h1 | h2)
              · have hx : (p.1 : ℝ) = (q.1 : ℝ) := by
                  have := congrArg Prod.fst h1; dsimp [mid] at this; linarith
                have hy : (p.2 : ℝ) = (q.2 : ℝ) := by
                  have := congrArg Prod.snd h1; dsimp [mid] at this; linarith
                have hpq : p = q := Prod.ext (Nat.cast_injective hx) (Nat.cast_injective hy)
                rcases hadj.2.2 with ⟨_, h | h⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩ <;>
                  (rw [hpq] at h; omega)
              · have hx : (p.1 : ℝ) = (q.1 : ℝ) := by
                  have := congrArg Prod.fst h2; dsimp [mid] at this; linarith
                have hy : (p.2 : ℝ) = (q.2 : ℝ) := by
                  have := congrArg Prod.snd h2; dsimp [mid] at this; linarith
                have hpq : p = q := Prod.ext (Nat.cast_injective hx) (Nat.cast_injective hy)
                rcases hadj.2.2 with ⟨_, h | h⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩ <;>
                  (rw [hpq] at h; omega)
            have hmid_b : mid ∈ interior (K_a b) :=
              interior_fig1Segment_subset_interior_fig1Collar hadj hb_int ⟨hmid_seg, hmid_ne⟩
            exact Set.disjoint_left.mp (hsep0 a b (Ne.symm hba)) (hseg_sub hmid_seg)
              (interior_subset hmid_b)
        exact (hSeg_in_Γ' p q hadj hall').2 ⟨z, hz_seg, rfl⟩
  have hFr_sub_U : ∀ a, discBd (D_a a) ⊆ Γ'.U := by
    intro a
    rw [hD_bd a, hΓ'U]
    apply image_mono
    intro z hz
    have := (hh₀ a).1
    have := hi₀_lo a
    have := hj₀_lo a
    have := hi₀_hi a
    have := hj₀_hi a
    refine ⟨frontier_fig1Collar_subset_fig1Set (n := 0) (by omega) (hh₀ a).2 (hi₀_even a)
      (hj₀_even a) (by omega) (by omega) (by omega) (by omega) hz, ?_⟩
    intro hzInt
    obtain ⟨b, hzb⟩ := mem_iUnion.mp hzInt
    by_cases hba : b = a
    · exact hz.2 (hba ▸ hzb)
    · exact Set.disjoint_left.mp (hsep0 a b (Ne.symm hba))
        ((isClosed_fig1Collar _ _ _ _).frontier_subset hz) (interior_subset hzb)
  have hInt_disj_U : ∀ a, Disjoint (interior (D_a a)) Γ'.U := by
    intro a
    rw [hD_int a, hΓ'U, Set.disjoint_left]
    rintro _ ⟨z, hzInt, rfl⟩ ⟨z', hz', heq⟩
    rw [hEmb.injective heq] at hz'
    exact hz'.2 (mem_iUnion.mpr ⟨a, hzInt⟩)
  have hr_a : ∀ a, r_a a ∈ Γ'.R ∧ subBd (r_a a) = fig1Sph φ '' frontier (K_a a) := by
    intro a
    obtain ⟨hmemR, hclR⟩ := GM16.empty_disc_is_region hS (hD_disc a) (hFr_sub_U a) (hInt_disj_U a)
    refine ⟨hmemR, ?_⟩
    dsimp [r_a]
    rw [subBd_eq_frontier, ← hD_fr a]
    change closure (interior (D_a a)) \ interior (interior (D_a a)) =
      closure (D_a a) \ interior (D_a a)
    rw [hclR, (isOpen_interior : IsOpen (interior (D_a a))).interior_eq,
      (hD_disc a).isClosed.closure_eq]
  have hC_a : ∀ a, (C_a a).IsCircuit ∧ (C_a a).IsSubdrawing Γ' ∧ (C_a a).U = subBd (r_a a) := by
    intro a
    have hbd_eq : subBd (r_a a) = discBd (D_a a) := by rw [(hr_a a).2, hD_bd a]
    refine ⟨?_, GM11.interSet_isSub, GM16.interSet_subBd_U hS (hr_a a).1⟩
    dsimp [C_a]
    rw [hbd_eq]
    exact GM16.interSet_isCircuit_of_oArc (hD_disc a).isOArc_discBd (hFr_sub_U a)
  have hr_inj : Function.Injective r_a := by
    intro a b hab
    by_contra hne
    have hne_int : (r_a a).Nonempty := by
      dsimp [r_a]
      rw [← GM16.discInt_eq_interior_of_closedSurface hS (hD_disc a)]
      exact (hD_disc a).nonempty_discInt
    obtain ⟨x, hxa⟩ := hne_int
    have hxb : x ∈ r_a b := hab ▸ hxa
    dsimp [r_a] at hxa hxb
    rw [hD_int a] at hxa
    rw [hD_int b] at hxb
    obtain ⟨za, hza, rfl⟩ := hxa
    obtain ⟨zb, hzb, heq⟩ := hxb
    rw [hEmb.injective heq] at hzb
    exact Set.disjoint_left.mp (hsep0 a b hne) (interior_subset hza) (interior_subset hzb)
  -- `Γ'.IsTwoCell`
  refine ⟨hD_disc, hD_int, hD_bd, hΓ'U, hr_a, hC_a, hr_inj, ⟨inferInstance, fun r hr => ?_⟩⟩
  obtain ⟨z, hzr⟩ := GM11.region_nonempty hr
  have hzU : z ∉ Γ'.U := GM11.region_subset hr hzr
  by_cases hzD : ∃ a, z ∈ D_a a
  · obtain ⟨a, hza⟩ := hzD
    have hzr_a : z ∈ r_a a := by
      by_contra hnot
      have hzFr : z ∈ frontier (D_a a) := ⟨subset_closure hza, hnot⟩
      rw [hD_fr a, ← hD_bd a] at hzFr
      exact hzU (hFr_sub_U a hzFr)
    have hreg_eq := GM11.region_eq_of_mem hr (hr_a a).1 hzr hzr_a
    rw [hreg_eq]
    dsimp [r_a]
    rw [GM11.interior_eq_sdiff_discBd hS (hD_disc a)]
    exact GM11.isOpenDisc_interior hS (hD_disc a)
  · push Not at hzD
    by_cases hzE : z ∈ fig1Sph φ '' fig1EnclosedSet W.height
    · obtain ⟨p, hp, rfl⟩ := hzE
      obtain ⟨x, y, hb, hpB⟩ := exists_fig1Brick_of_mem_enclosed hp
      obtain ⟨hB, hBd_B⟩ := discBd_image_fig1Brick hEmb.isEmbedding x y
      have hp_not_K : ∀ a, p ∉ K_a a := fun a hpK => hzD a ⟨p, hpK, rfl⟩
      have hpOpen : p ∈ Ioo (x : ℝ) ((x : ℝ) + 2) ×ˢ Ioo (y : ℝ) ((y : ℝ) + 1) := by
        rw [← interior_Icc, ← interior_Icc, ← interior_prod_eq]
        by_contra hfr
        apply hzU
        rw [hΓ'U]
        refine ⟨p, ⟨frontier_brick_subset_fig1Set W.toWall.even_height hb.2.1 hb.2.2 hb.1
          ⟨subset_closure hpB, hfr⟩, ?_⟩, rfl⟩
        intro hpInt
        obtain ⟨a, hpa⟩ := mem_iUnion.mp hpInt
        exact hp_not_K a (interior_subset hpa)
      have hInt : fig1Sph φ p ∈ interior (fig1Sph φ '' fig1Brick x y) := by
        refine interior_maximal (image_mono ?_) (hEmb.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo))
          (mem_image_of_mem _ hpOpen)
        exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
      -- Show `fig1Brick x y` is disjoint from `interior (K_a a)` for all `a`
      have hBrick_disj : ∀ a, Disjoint (fig1Brick x y) (interior (K_a a)) := by
        intro a
        let U_B := Ioo (x : ℝ) ((x : ℝ) + 2) ×ˢ Ioo (y : ℝ) ((y : ℝ) + 1)
        have hUB_pre : IsPreconnected U_B := isPreconnected_Ioo.prod isPreconnected_Ioo
        have hUB_disj_fr : Disjoint U_B (frontier (K_a a)) := by
          have := (hh₀ a).1
          have := hi₀_lo a
          have := hj₀_lo a
          have := hi₀_hi a
          have := hj₀_hi a
          have hFr_fig1 := frontier_fig1Collar_subset_fig1Set (H_h := W.height) (n := 0) (by omega)
            (hh₀ a).2 (hi₀_even a) (hj₀_even a) (by omega) (by omega) (by omega) (by omega)
          exact (disjoint_open_brick_fig1Set (h := W.height) hb.1).mono_right hFr_fig1
        have hUB_disj_K : Disjoint U_B (K_a a) := by
          rcases GM11.subset_or_disjoint_of_frontier (isClosed_fig1Collar _ _ _ _) hUB_pre
            hUB_disj_fr with hsub | hdisj
          · exact (hp_not_K a (hsub hpOpen)).elim
          · exact hdisj
        have hcl_UB : fig1Brick x y ⊆ closure U_B := by
          dsimp [fig1Brick, U_B]
          rw [closure_prod_eq, closure_Ioo (by linarith), closure_Ioo (by linarith)]
        exact (hUB_disj_K.mono_right interior_subset).closure_left isOpen_interior |>.mono_left hcl_UB
      have hBd_B_sub : discBd (fig1Sph φ '' fig1Brick x y) ⊆ Γ'.U := by
        rw [hBd_B, hΓ'U]
        apply image_mono
        intro w hw
        refine ⟨frontier_brick_subset_fig1Set W.toWall.even_height hb.2.1 hb.2.2 hb.1 hw, ?_⟩
        intro hwInt
        obtain ⟨a, hwa⟩ := mem_iUnion.mp hwInt
        exact Set.disjoint_left.mp (hBrick_disj a)
          ((isClosed_Icc.prod isClosed_Icc).frontier_subset hw) hwa
      have hEmpty_B : Disjoint (interior (fig1Sph φ '' fig1Brick x y)) Γ'.U := by
        rw [hΓ'U, Set.disjoint_left]
        intro w hw hwU
        obtain ⟨u, hu, rfl⟩ := GM16.interior_image_rectangle_subset hEmb.isEmbedding _ _ _ _ hw
        obtain ⟨u', hu', huu'⟩ := hwU
        rw [hEmb.injective huu'] at hu'
        exact Set.disjoint_left.mp (disjoint_open_brick_fig1Set (h := W.height) hb.1) hu hu'.1
      have hReg_B := (GM16.empty_disc_is_region hS hB hBd_B_sub hEmpty_B).1
      rw [GM11.region_eq_of_mem hr hReg_B hzr hInt, GM11.interior_eq_sdiff_discBd hS hB]
      exact GM11.isOpenDisc_interior hS hB
    · -- Outer region case
      have h2 := W.toWall.two_le_height
      have he := W.toWall.even_height
      have hC := isClosedDisc_image_fig1EnclosedSet hS hEmb.isEmbedding (by omega : 1 ≤ W.height)
      obtain ⟨hD, hBd, hCup, hMeet⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hsph hC
      have hDrawing : Γ'.U ⊆ fig1Sph φ '' fig1EnclosedSet W.height := by
        rw [hΓ'U]
        exact image_mono (sdiff_subset.trans (fig1Set_subset_enclosed he h2))
      have hzD_compl : z ∈ closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ :=
        (hCup.ge (mem_univ z)).resolve_left hzE
      have hzInt : z ∈ interior (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ) := by
        by_contra hn
        have hzFr : z ∈ frontier (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ) :=
          ⟨subset_closure hzD_compl, hn⟩
        have hzBd := GM11.IsClosedDisc.frontier_eq_discBd hS hD ▸ hzFr
        exact hzE (Surface.discBd_subset _ (hBd ▸ hzBd))
      have hBdU : discBd (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ) ⊆ Γ'.U := by
        rw [hBd, ← GM11.IsClosedDisc.frontier_eq_discBd hS hC,
          frontier_image_fig1EnclosedSet hS hEmb (by omega), hΓ'U]
        apply image_mono
        intro w hw
        refine ⟨frontier_fig1EnclosedSet_subset_fig1Set h2 he hw, ?_⟩
        intro hwInt
        obtain ⟨a, hwa⟩ := mem_iUnion.mp hwInt
        -- `K_a a` is strictly inside `interior (fig1EnclosedSet W.height)`
        have hKa_sub : K_a a ⊆ interior (fig1EnclosedSet W.height) := by
          dsimp [K_a, fig1Collar]
          rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
          obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := fig1EnclosedSet_subset_Icc (h₀ a) hxy
          have := (hh₀ a).1
          have hia_lo : (4 : ℝ) ≤ (i₀ a : ℝ) := by exact_mod_cast hi₀_lo a
          have hja_lo : (2 : ℝ) ≤ (j₀ a : ℝ) := by exact_mod_cast hj₀_lo a
          have hia_hi : (i₀ a : ℝ) + 2 * (h₀ a : ℝ) + 4 ≤ 2 * (W.height : ℝ) := by
            exact_mod_cast hi₀_hi a
          have hja_hi : (j₀ a : ℝ) + (h₀ a : ℝ) + 2 ≤ (W.height : ℝ) := by
            exact_mod_cast hj₀_hi a
          apply open_rect_subset_interior_fig1EnclosedSet W.height
          exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, ⟨by dsimp; linarith, by dsimp; linarith⟩⟩
        exact hw.2 (hKa_sub (interior_subset hwa))
      have hEmpty : Disjoint (interior (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ)) Γ'.U := by
        refine Set.disjoint_left.mpr fun w hwInt hwU => ?_
        have hwBd : w ∈ discBd (fig1Sph φ '' fig1EnclosedSet W.height) :=
          hMeet ▸ ⟨hDrawing hwU, interior_subset hwInt⟩
        have hwFr : w ∈ frontier (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ) :=
          (GM11.IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ (hBd.symm ▸ hwBd)
        exact hwFr.2 hwInt
      have hReg := (GM16.empty_disc_is_region hS hD hBdU hEmpty).1
      rw [GM11.region_eq_of_mem hr hReg hzr hzInt, GM11.interior_eq_sdiff_discBd hS hD]
      exact GM11.isOpenDisc_interior hS hD

/-- **Controlling tangle on the punctured sphere drawing `Γ'` from an unpunctured bottom subwall `W_θ`:**
Given `θ` (`2 ≤ θ`, `Even θ`, `θ ≤ W.height`) with `θ + 2 ≤ j₀ a` for all `a : Fin t`, the bottom
subwall `W_θ := W.toWall.subwallAt 0 0 θ ...` lies wholly inside `η'.imageGraph` (where
`η' := GM16.restrictCleared η₀ Λ`), and induces a controlling tangle `(Tstar, T')` of order `θ`
for `(G₀, Γ', η')` such that no small side `(A, B) ∈ T'` contains all edges of `Γ'` on any row
`j < θ`. Moreover, `η'.imageGraph` satisfies the vertex and edge conditions of
`exists_extended_cross_hPaths` for every `a : Fin t`. -/
theorem exists_punctured_controlled_tangle [Nonempty α] [Nonempty β]
    {W : DrawnWall α β} {G₀ : Graph α β} (hWG₀ : W.graph ≤ G₀)
    (hV₀ : V(G₀).Finite) (hE₀ : E(G₀).Finite) {t : ℕ}
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hbranch_pos : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.toWall.branchVertex p hp) = ((p.1 : ℝ), (p.2 : ℝ)))
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    (i₀ j₀ h₀ : Fin t → ℕ)
    (hh₀ : ∀ a, 6 ≤ h₀ a ∧ Even (h₀ a))
    (hi₀_even : ∀ a, Even (i₀ a))
    (hj₀_even : ∀ a, Even (j₀ a))
    (hi₀_lo : ∀ a, 4 ≤ i₀ a)
    (hi₀_hi : ∀ a, i₀ a + 2 * h₀ a + 4 ≤ 2 * W.height)
    (hj₀_hi : ∀ a, j₀ a + h₀ a + 2 ≤ W.height)
    (hD_int : ∀ a, interior (fig1Sph φ '' fig1Collar (i₀ a) (j₀ a) (h₀ a) 0) =
      fig1Sph φ '' interior (fig1Collar (i₀ a) (j₀ a) (h₀ a) 0))
    {θ : ℕ} (hθ_two : 2 ≤ θ) (hθ_even : Even θ) (hθ_le : θ ≤ W.height)
    (hj₀_θ : ∀ a, θ + 2 ≤ j₀ a) :
    let K_a : Fin t → Set (ℝ × ℝ) := fun a => fig1Collar (i₀ a) (j₀ a) (h₀ a) 0
    let D_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => fig1Sph φ '' K_a a
    let Λ : Set (OnePoint EuclideanPlane) := ⋃ a : Fin t, interior (D_a a)
    let Γ' : Drawing (OnePoint EuclideanPlane) := clearedSubdrawing Γ.drawing Λ
    ∃ (η' : SpanEmbedding Γ' G₀)
      (Tstar : Set (Hypergraph α β × Hypergraph α β))
      (T' : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
        Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))),
      η'.imageGraph ≤ W.graph ∧
      (∀ z ∈ V(W.graph), pos z ∉ (⋃ a : Fin t, interior (K_a a)) →
        z ∈ V(η'.imageGraph) ∧ fig1Sph φ (pos z) ∈ Γ'.V ∧ η'.vMap (fig1Sph φ (pos z)) = z) ∧
      (∀ a, ∀ z ∈ V(η'.imageGraph), ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
        ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p q ∧
          z ∈ V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj))) ∧
      (∀ a, ∀ e ∈ E(η'.imageGraph), ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
        ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p q ∧
          e ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj))) ∧
      IsControllingTangle G₀ Γ' η' θ θ Tstar T' ∧
      (∀ A B, (A, B) ∈ T' → ∀ j < θ,
        ∃ e ∈ Γ'.E, e ⊆ fig1Sph φ '' fig1RowSeg W.height j ∧ e ∉ A.edgeSet) := by
  intro K_a D_a Λ Γ'
  have hEmb := isOpenEmbedding_fig1Sph φ
  have hΛ_eq : Λ = fig1Sph φ '' (⋃ a : Fin t, interior (K_a a)) := by
    dsimp [Λ]
    rw [image_iUnion]
    exact iUnion_congr hD_int
  have hclosed_compl : IsClosed (univ \ Λ) :=
    isClosed_univ.sdiff (isOpen_iUnion fun a => isOpen_interior)
  obtain ⟨η₀, hη₀Image, hη₀V, hη₀E⟩ := GM16.exists_spanEmbedding_of_graphDrawing hWG₀ Γ
  obtain ⟨f, g, hf, hg, hfInj, hgInj⟩ := GM16.exists_graphDrawing_forward_maps Γ
  let η' : SpanEmbedding Γ' G₀ := GM16.restrictCleared η₀ Λ
  let N : Graph α β := η'.imageGraph
  have hNW : N ≤ W.graph := hη₀Image ▸ GM16.restrictCleared_imageGraph_le η₀ Λ
  have hNG₀ : N ≤ G₀ := η'.imageGraph_le
  have hVN : V(N).Finite := W.toWall.vertexSet_finite.subset hNW.vertexSet_mono
  have hEN : E(N).Finite := W.toWall.edgeSet_finite.subset hNW.edgeSet_mono
  have hη₀v_inv : ∀ z (hz : z ∈ V(W.graph)), η₀.vMap (fig1Sph φ (pos z)) = z := by
    intro z hz
    have h2 : η₀.vMap (Γ.iso.vertexEquiv ⟨z, hz⟩).1 = z := by
      rw [hη₀V ⟨(Γ.iso.vertexEquiv ⟨z, hz⟩).1, (Γ.iso.vertexEquiv ⟨z, hz⟩).2⟩]
      exact congrArg Subtype.val (Γ.iso.vertexEquiv.symm_apply_apply ⟨z, hz⟩)
    rwa [hΓv ⟨z, hz⟩] at h2
  -- Vertex characterization in `N` and `Γ'`
  have hVert_N : ∀ z ∈ V(W.graph), pos z ∉ (⋃ a : Fin t, interior (K_a a)) →
      z ∈ V(N) ∧ fig1Sph φ (pos z) ∈ Γ'.V ∧ η'.vMap (fig1Sph φ (pos z)) = z := by
    intro z hz hnot
    have hvΓ : fig1Sph φ (pos z) ∈ Γ.drawing.V := by
      rw [← hΓv ⟨z, hz⟩]
      exact (Γ.iso.vertexEquiv ⟨z, hz⟩).2
    have hnotΛ : fig1Sph φ (pos z) ∉ Λ := by
      rw [hΛ_eq]
      rintro ⟨w, hw, heq⟩
      rw [hEmb.injective heq] at hw
      exact hnot hw
    have hvΓ' : fig1Sph φ (pos z) ∈ Γ'.V := GM16.mem_clearedSubdrawing_V hvΓ hnotΛ
    have hv_map : η'.vMap (fig1Sph φ (pos z)) = z := hη₀v_inv z hz
    have hzN : z ∈ V(N) := hv_map ▸ η'.bijOn_v.mapsTo hvΓ'
    exact ⟨hzN, hvΓ', hv_map⟩
  -- Non-interior base edge subdivision paths lie in `N`
  have hPath_le_N : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      (∀ a, ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p q) →
      (∀ f (hf : f ∈ E(W.graph)),
        f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∈ Γ'.E) ∧
      W.toWall.subdivisionPaths (W.toWall.baseEdge hadj) ≤ N := by
    intro p q hadj hnot_int
    have hdisj_seg : ∀ a, Disjoint (fig1Segment p q) (interior (K_a a)) := by
      intro a
      exact disjoint_fig1Segment_interior_of_not_isInteriorBaseEdge
        (hi₀_even a) (hj₀_even a) hadj (hnot_int a)
    have hE_mem : ∀ f (hf : f ∈ E(W.graph)),
        f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∈ Γ'.E := by
      intro f hf hfP
      change (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∈ (Γ.drawing.interSet (univ \ Λ)).E
      rw [GM11.mem_interSet_E_iff]
      refine ⟨(Γ.iso.edgeEquiv ⟨f, hf⟩).2, fun x hx => ⟨mem_univ x, ?_⟩⟩
      rw [hΛ_eq]
      rintro ⟨z, hzInt, hxz⟩
      obtain ⟨w, hwSeg, hxw⟩ := hΓe p q hadj f hf hfP hx
      rw [← hEmb.injective (hxw.trans hxz.symm)] at hzInt
      obtain ⟨a, hza⟩ := mem_iUnion.mp hzInt
      exact Set.disjoint_left.mp (hdisj_seg a) hwSeg hza
    refine ⟨hE_mem, ?_⟩
    have hpathW : W.toWall.subdivisionPaths (W.toWall.baseEdge hadj) ≤ W.graph :=
      (W.toWall.isGraphPathWithEnds_baseEdge hadj).le
    have hV_sub : V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) ⊆ V(N) := by
      intro z hzP
      have hzW : z ∈ V(W.graph) := hpathW.vertexSet_mono hzP
      have hpq_ne : W.toWall.branchVertex p hadj.1 ≠ W.toWall.branchVertex q hadj.2.1 := by
        intro h
        have hpq_eq := W.toWall.branchVertex_injective hadj.1 hadj.2.1 h
        rw [← hpq_eq] at hadj
        exact elementaryWallAdj_irrefl p hadj
      obtain ⟨f₀, hf₀P, y₀, hlinkP⟩ :=
        IsGraphPathWithEnds.exists_inc (W.toWall.isGraphPathWithEnds_baseEdge hadj) hpq_ne hzP
      have hf₀W : f₀ ∈ E(W.graph) := hpathW.edgeSet_mono hf₀P
      have he_draw : (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 ∈ Γ'.E := hE_mem f₀ hf₀W hf₀P
      have hincW : W.graph.Inc f₀ z := ⟨y₀, hpathW.isLink_mono hlinkP⟩
      have he_map : η₀.eMap (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 = f₀ := by
        rw [hη₀E (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩)]
        exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨f₀, hf₀W⟩)
      have hz_cl : fig1Sph φ (pos z) ∈ closure (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 := by
        have hv_draw : fig1Sph φ (pos z) ∈ Γ.drawing.V := by
          rw [← hΓv ⟨z, hzW⟩]; exact (Γ.iso.vertexEquiv ⟨z, hzW⟩).2
        apply (η₀.inc_iff _ (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).2 _ hv_draw).mp
        rwa [hη₀Image, he_map, hη₀v_inv z hzW]
      have hz_seg : pos z ∈ fig1Segment p q := by
        have hcl : IsClosed (fig1Sph φ '' fig1Segment p q) :=
          ((isCompact_fig1Segment p q).image hEmb.continuous).isClosed
        have hsub := closure_minimal (hΓe p q hadj f₀ hf₀W hf₀P) hcl hz_cl
        obtain ⟨w, hw, heq⟩ := hsub
        rwa [← hEmb.injective heq]
      refine (hVert_N z hzW ?_).1
      intro hzInt
      obtain ⟨a, hza⟩ := mem_iUnion.mp hzInt
      exact Set.disjoint_left.mp (hdisj_seg a) hz_seg hza
    refine ⟨hV_sub, fun f₀ x y hlinkP => ?_⟩
    have hf₀P : f₀ ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) := hlinkP.edge_mem
    have hf₀W : f₀ ∈ E(W.graph) := hpathW.edgeSet_mono hf₀P
    have he_draw : (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 ∈ Γ'.E := hE_mem f₀ hf₀W hf₀P
    have he_map : η'.eMap (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 = f₀ := by
      change η₀.eMap (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 = f₀
      rw [hη₀E (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩)]
      exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨f₀, hf₀W⟩)
    have hf₀N : f₀ ∈ E(N) := he_map ▸ η'.bijOn_e.mapsTo he_draw
    exact (hNW.isLink_iff' (y := y)).mpr ⟨hpathW.isLink_mono hlinkP, hf₀N⟩
  -- Every edge of `N` lies on a non-interior base edge for each `a`
  have hEdges_N : ∀ a, ∀ e ∈ E(N), ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p q ∧
        e ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) := by
    intro a e heN
    have heW : e ∈ E(W.graph) := hNW.edgeSet_mono heN
    obtain ⟨e_draw, he_draw, rfl⟩ := (η'.bijOn_e.image_eq ▸ heN : e ∈ η'.eMap '' Γ'.E)
    have he_draw' : e_draw ∈ (Γ.drawing.interSet (univ \ Λ)).E := he_draw
    have he_draw_Γ : e_draw ∈ Γ.drawing.E := (GM11.mem_interSet_E_iff.mp he_draw').1
    have he_draw_out : e_draw ⊆ univ \ Λ := (GM11.mem_interSet_E_iff.mp he_draw').2
    have he_eq : (Γ.iso.edgeEquiv ⟨η'.eMap e_draw, heW⟩).1 = e_draw := by
      have heW₀ : η₀.eMap e_draw ∈ E(W.graph) := heW
      change (Γ.iso.edgeEquiv ⟨η₀.eMap e_draw, heW₀⟩).1 = e_draw
      have h1 := hη₀E ⟨e_draw, he_draw_Γ⟩
      have h2 : (⟨η₀.eMap e_draw, heW₀⟩ : E(W.graph)) = Γ.iso.edgeEquiv.symm ⟨e_draw, he_draw_Γ⟩ :=
        Subtype.ext h1
      rw [h2, Equiv.apply_symm_apply]
    have hW_edge : η'.eMap e_draw ∈ E(W.graph) := heW
    rw [W.toWall.edgeSet_eq] at hW_edge
    obtain ⟨b, hb, heb⟩ := mem_iUnion₂.mp hW_edge
    obtain ⟨p, q, hadj, rfl⟩ := W.toWall.exists_baseEdge_eq hb
    refine ⟨p, q, hadj, ?_, heb⟩
    intro hint
    obtain ⟨w, hw⟩ := he_draw_Γ.2.2.1.nonempty
    have hw_not_V : w ∉ Γ.drawing.V := GM11.edge_notMem_V he_draw_Γ hw
    have hw_seg : w ∈ fig1Sph φ '' fig1Segment p q := by
      apply hΓe p q hadj (η'.eMap e_draw) heW heb
      rwa [he_eq]
    obtain ⟨z, hz_seg, rfl⟩ := hw_seg
    have hz_ne : z ∉ ({((p.1 : ℝ), (p.2 : ℝ)), ((q.1 : ℝ), (q.2 : ℝ))} : Set (ℝ × ℝ)) := by
      rintro (h1 | h2)
      · have hbp_mem := W.toWall.branchVertex_mem_vertexSet p hadj.1
        have hbp_V : fig1Sph φ (pos (W.toWall.branchVertex p hadj.1)) ∈ Γ.drawing.V := by
          rw [← hΓv ⟨_, hbp_mem⟩]; exact (Γ.iso.vertexEquiv ⟨_, hbp_mem⟩).2
        rw [hbranch_pos p hadj.1, ← h1] at hbp_V
        exact hw_not_V hbp_V
      · have hbq_mem := W.toWall.branchVertex_mem_vertexSet q hadj.2.1
        have hbq_V : fig1Sph φ (pos (W.toWall.branchVertex q hadj.2.1)) ∈ Γ.drawing.V := by
          rw [← hΓv ⟨_, hbq_mem⟩]; exact (Γ.iso.vertexEquiv ⟨_, hbq_mem⟩).2
        rw [hbranch_pos q hadj.2.1, ← h2] at hbq_V
        exact hw_not_V hbq_V
    have hz_int : z ∈ interior (K_a a) :=
      interior_fig1Segment_subset_interior_fig1Collar hadj hint ⟨hz_seg, hz_ne⟩
    have hw_Λ : fig1Sph φ z ∈ Λ := by
      rw [hΛ_eq]
      exact ⟨z, mem_iUnion.mpr ⟨a, hz_int⟩, rfl⟩
    exact (he_draw_out hw).2 hw_Λ
  -- Every vertex of `N` lies on a non-interior base edge for each `a`
  have hVerts_N : ∀ a, ∀ z ∈ V(N), ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p q ∧
        z ∈ V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) := by
    intro a z hzN
    have hzW : z ∈ V(W.graph) := hNW.vertexSet_mono hzN
    obtain ⟨v_draw, hv_draw, rfl⟩ := (η'.bijOn_v.image_eq ▸ hzN : z ∈ η'.vMap '' Γ'.V)
    have hv_draw_Γ : v_draw ∈ Γ.drawing.V := Γ.drawing.spanV_subset _ _ hv_draw
    have hv_draw_out : v_draw ∉ Λ := by
      have hcl : IsClosed (univ \ Λ) := hclosed_compl
      have hv_draw' : v_draw ∈ (Γ.drawing.interSet (univ \ Λ)).V := hv_draw
      exact ((GM11.mem_interSet_V_iff hcl).mp hv_draw').2.2
    have hzW₀ : η₀.vMap v_draw ∈ V(W.graph) := hzW
    have hv_eq : fig1Sph φ (pos (η'.vMap v_draw)) = v_draw := by
      change fig1Sph φ (pos (η₀.vMap v_draw)) = v_draw
      rw [← hΓv ⟨η₀.vMap v_draw, hzW₀⟩]
      have h1 : (⟨η₀.vMap v_draw, hzW₀⟩ : V(W.graph)) = Γ.iso.vertexEquiv.symm ⟨v_draw, hv_draw_Γ⟩ :=
        Subtype.ext (hη₀V ⟨v_draw, hv_draw_Γ⟩)
      rw [h1, Equiv.apply_symm_apply]
    have hpos_not_int : pos (η'.vMap v_draw) ∉ interior (K_a a) := by
      intro hint
      apply hv_draw_out
      rw [← hv_eq, hΛ_eq]
      exact ⟨_, mem_iUnion.mpr ⟨a, hint⟩, rfl⟩
    obtain ⟨p₀, q₀, hadj₀, f₀, hf₀P, y₀, hlinkP⟩ := W.toWall.exists_inc_baseEdge hzW
    have hzP₀ : η'.vMap v_draw ∈ V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj₀)) :=
      hlinkP.left_mem
    by_cases hnot₀ : ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) p₀ q₀
    · exact ⟨p₀, q₀, hadj₀, hnot₀, hzP₀⟩
    · push Not at hnot₀
      -- Since `η'.vMap v_draw ∈ V(W.subdivisionPaths (W.baseEdge hadj₀))` and `pos ∉ interior`,
      -- `pos` must be one of the endpoints `p₀` or `q₀`.
      have hpathW : W.toWall.subdivisionPaths (W.toWall.baseEdge hadj₀) ≤ W.graph :=
        (W.toWall.isGraphPathWithEnds_baseEdge hadj₀).le
      have hf₀W : f₀ ∈ E(W.graph) := hpathW.edgeSet_mono hf₀P
      have he_map : η₀.eMap (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 = f₀ := by
        rw [hη₀E (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩)]
        exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨f₀, hf₀W⟩)
      have hz_cl : v_draw ∈ closure (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).1 := by
        apply (η₀.inc_iff _ (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩).2 _ hv_draw_Γ).mp
        rw [hη₀Image, he_map]
        exact ⟨y₀, hpathW.isLink_mono hlinkP⟩
      have hz_seg : pos (η'.vMap v_draw) ∈ fig1Segment p₀ q₀ := by
        have hcl : IsClosed (fig1Sph φ '' fig1Segment p₀ q₀) :=
          ((isCompact_fig1Segment p₀ q₀).image hEmb.continuous).isClosed
        have hsub := closure_minimal (hΓe p₀ q₀ hadj₀ f₀ hf₀W hf₀P) hcl (hv_eq.symm ▸ hz_cl)
        obtain ⟨w, hw, heq⟩ := hsub
        rwa [← hEmb.injective heq]
      have hz_end : pos (η'.vMap v_draw) ∈
          ({((p₀.1 : ℝ), (p₀.2 : ℝ)), ((q₀.1 : ℝ), (q₀.2 : ℝ))} : Set (ℝ × ℝ)) := by
        by_contra hne_end
        exact hpos_not_int
          (interior_fig1Segment_subset_interior_fig1Collar hadj₀ hnot₀ ⟨hz_seg, hne_end⟩)
      -- Auxiliary: for a branch vertex `r` of an interior base edge whose position is not in
      -- `interior (K_a a)`, there is a non-interior base edge incident to `r`.
      have hex_branch : ∀ (r s : ℕ × ℕ) (hadj_rs : elementaryWallAdj W.height r s),
          isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) r s →
          ((r.1 : ℝ), (r.2 : ℝ)) ∉ interior (K_a a) →
          ∃ (q' : ℕ × ℕ) (hadj' : elementaryWallAdj W.height r q'),
            ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) r q' := by
        intro r s hadj_rs hint_rs hr_not_int
        have := (hh₀ a).1
        have := hi₀_lo a
        have := hi₀_hi a
        have := hj₀_hi a
        have := hj₀_θ a
        have hr_not_box : ¬ (i₀ a + 1 < r.1 ∧ r.1 < i₀ a + 2 * h₀ a ∧
            j₀ a < r.2 ∧ r.2 < j₀ a + h₀ a) := by
          rintro ⟨h1, h2, h3, h4⟩
          apply hr_not_int
          dsimp [K_a]
          rw [fig1Collar_zero, ← (wallShiftRealHomeomorph (i₀ a) (j₀ a)).image_interior]
          refine ⟨((r.1 : ℝ) - (i₀ a : ℝ), (r.2 : ℝ) - (j₀ a : ℝ)),
            open_rect_subset_interior_fig1EnclosedSet (h₀ a) ?_, by ext <;> dsimp <;> ring⟩
          have h1_r : (i₀ a : ℝ) + 1 < (r.1 : ℝ) := by exact_mod_cast h1
          have h2_r : (r.1 : ℝ) < (i₀ a : ℝ) + 2 * (h₀ a : ℝ) := by exact_mod_cast h2
          have h3_r : (j₀ a : ℝ) < (r.2 : ℝ) := by exact_mod_cast h3
          have h4_r : (r.2 : ℝ) < (j₀ a : ℝ) + (h₀ a : ℝ) := by exact_mod_cast h4
          exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, ⟨by dsimp; linarith, by dsimp; linarith⟩⟩
        rcases hint_rs with ⟨hrs2, hj_lo, hj_hi, hi_lo, hi_hi⟩ | ⟨hrs1, hj_lo, hj_hi, hi_lo, hi_hi⟩
        · have hr1_end : r.1 = i₀ a + 1 ∨ r.1 = i₀ a + 2 * h₀ a := by omega
          rcases hr1_end with hr1_eq | hr1_eq
          · refine ⟨(i₀ a, r.2), ?_, ?_⟩
            · rw [show r = (i₀ a + 1, r.2) from Prod.ext hr1_eq rfl]
              exact elementaryWallAdj_symm
                (elementaryWallAdj_horiz_of_row_interior (by omega) (by omega) (by omega))
            · rintro (⟨_, _, _, hmin, _⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
          · refine ⟨(i₀ a + 2 * h₀ a + 1, r.2), ?_, ?_⟩
            · rw [show r = (i₀ a + 2 * h₀ a, r.2) from Prod.ext hr1_eq rfl]
              exact elementaryWallAdj_horiz_of_row_interior (by omega) (by omega) (by omega)
            · rintro (⟨_, _, _, _, hmax⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
        · have hr2_end : r.2 = j₀ a ∨ r.2 = j₀ a + h₀ a := by omega
          refine ⟨(r.1 + 1, r.2), ?_, ?_⟩
          · rw [show r = (r.1, r.2) from rfl]
            exact elementaryWallAdj_horiz_of_row_interior (by omega) (by omega) (by omega)
          · rintro (⟨_, hj1, hj2, _, _⟩ | ⟨heq1, _⟩) <;> dsimp at * <;> omega
      rcases hz_end with hpos_p | hpos_q
      · have hz_eq : η'.vMap v_draw = W.toWall.branchVertex p₀ hadj₀.1 :=
          hinj hzW (W.toWall.branchVertex_mem_vertexSet p₀ hadj₀.1)
            (hpos_p.trans (hbranch_pos p₀ hadj₀.1).symm)
        rw [hpos_p] at hpos_not_int
        obtain ⟨q', hadj', hnot'⟩ := hex_branch p₀ q₀ hadj₀ hnot₀ hpos_not_int
        refine ⟨p₀, q', hadj', hnot', ?_⟩
        rw [hz_eq]
        exact (W.toWall.isGraphPathWithEnds_baseEdge hadj').left_mem
      · have hz_eq : η'.vMap v_draw = W.toWall.branchVertex q₀ hadj₀.2.1 :=
          hinj hzW (W.toWall.branchVertex_mem_vertexSet q₀ hadj₀.2.1)
            (hpos_q.trans (hbranch_pos q₀ hadj₀.2.1).symm)
        rw [hpos_q] at hpos_not_int
        obtain ⟨q', hadj', hnot'⟩ := hex_branch q₀ p₀
          (elementaryWallAdj_symm hadj₀)
          ((isInteriorBaseEdge_symm _ _ _ _ _).mp hnot₀) hpos_not_int
        refine ⟨q₀, q', hadj', hnot', ?_⟩
        rw [hz_eq]
        exact (W.toWall.isGraphPathWithEnds_baseEdge hadj').left_mem
  -- Construct the bottom subwall `W_θ` and show `W_θ.graph ≤ N`
  have heven_zero : Even 0 := ⟨0, rfl⟩
  let W_θ : Wall α β :=
    W.toWall.subwallAt 0 0 θ hθ_two hθ_even hθ_le heven_zero heven_zero (by omega) (by omega)
  have hWθ_le_N : W_θ.graph ≤ N := by
    have hbase_not_int : ∀ (p q : ℕ × ℕ) (hadj' : elementaryWallAdj θ p q) (a : Fin t),
        ¬ isInteriorBaseEdge (i₀ a) (j₀ a) (h₀ a) (wallShift 0 0 p) (wallShift 0 0 q) := by
      intro p q hadj' a hint
      have hp2 : p.2 ≤ θ := hadj'.1.2.1
      have hq2 : q.2 ≤ θ := hadj'.2.1.2.1
      have := hj₀_θ a
      rcases hint with ⟨_, hj_lo, _⟩ | ⟨_, hj_lo, _⟩ <;> dsimp [wallShift] at * <;> omega
    have hV_sub : V(W_θ.graph) ⊆ V(N) := by
      intro z hz
      obtain ⟨p, q, hadj', f₀, hf₀, y₀, hlink⟩ := W_θ.exists_inc_baseEdge hz
      have hadjW : elementaryWallAdj W.height (wallShift 0 0 p) (wallShift 0 0 q) :=
        (elementaryWallAdj_wallShift_iff hθ_two hθ_le heven_zero heven_zero (by omega) (by omega)
          hadj'.1 hadj'.2.1).mp hadj'
      have hbase_eq : W_θ.baseEdge hadj' = W.toWall.baseEdge hadjW := rfl
      have hzP : z ∈ V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadjW)) := by
        rw [← hbase_eq]
        exact hlink.left_mem
      exact (hPath_le_N _ _ hadjW (hbase_not_int p q hadj')).2.vertexSet_mono hzP
    refine ⟨hV_sub, fun f₀ x y hlink => ?_⟩
    have hf₀_mem : f₀ ∈ E(W_θ.graph) := hlink.edge_mem
    rw [W_θ.edgeSet_eq] at hf₀_mem
    obtain ⟨b, hb, hf₀P⟩ := mem_iUnion₂.mp hf₀_mem
    obtain ⟨p, q, hadj', rfl⟩ := W_θ.exists_baseEdge_eq hb
    have hadjW : elementaryWallAdj W.height (wallShift 0 0 p) (wallShift 0 0 q) :=
      (elementaryWallAdj_wallShift_iff hθ_two hθ_le heven_zero heven_zero (by omega) (by omega)
        hadj'.1 hadj'.2.1).mp hadj'
    have hbase_eq : W_θ.baseEdge hadj' = W.toWall.baseEdge hadjW := rfl
    have hf₀PW : f₀ ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadjW)) := hbase_eq ▸ hf₀P
    have hsubN := (hPath_le_N _ _ hadjW (hbase_not_int p q hadj')).2
    have hWθ_le_W : W_θ.graph ≤ W.graph :=
      (W.toWall.subwallAt_isSubwallOf 0 0 θ hθ_two hθ_even hθ_le heven_zero heven_zero
        (by omega) (by omega)).graph_le'
    have hf₀N : f₀ ∈ E(N) := hsubN.edgeSet_mono hf₀PW
    exact (hNW.isLink_iff' (y := y)).mpr ⟨hWθ_le_W.isLink_mono hlink, hf₀N⟩
  -- Induce the sphere wall tangle of order `θ` from `W_θ` to `N` and `G₀`
  have hex_model : ∃ (ηv : Fin (2 * θ + 1) × Fin θ → Set α)
      (ηe : Sym2 (Fin (2 * θ + 1) × Fin θ) → β),
      IsMinorModel (GM16.sphereWallGraph θ) W_θ.graph ηv ηe ∧
      ∀ e ∈ (GM16.sphereWallSimpleGraph θ).edgeSet,
        ηe e ∈ E(W_θ.subdivisionPaths (W_θ.sphereEdge e)) :=
    W_θ.exists_sphereWall_model
  obtain ⟨ηv, ηe, hmodel_Wθ, hηe⟩ := hex_model
  have hmodel_N : IsMinorModel (GM16.sphereWallGraph θ) N ηv ηe := hmodel_Wθ.mono hWθ_le_N
  have hmodel_G₀ : IsMinorModel (GM16.sphereWallGraph θ) G₀ ηv ηe := hmodel_N.mono hNG₀
  obtain ⟨K_N, hVKN, hEKN, -, hImageN, -, hTN⟩ := GM16.exists_model_induced_tangle
    (Set.toFinite _) (Set.toFinite _) hVN hEN hmodel_N hθ_two (GM16.theorem_4_2_claim_1 hθ_two)
  obtain ⟨K_G₀, hVKG₀, hEKG₀, -, hImageG₀, -, hTstar⟩ := GM16.exists_model_induced_tangle
    (Set.toFinite _) (Set.toFinite _) hV₀ hE₀ hmodel_G₀ hθ_two (GM16.theorem_4_2_claim_1 hθ_two)
  let Wsph := Hypergraph.ofGraph (GM16.sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _)
  let TN := inducedTangle (Hypergraph.ofGraph N hVN hEN) (Hypergraph.ofGraph K_N hVKN hEKN)
    (GM16.imageHypergraphTangle ηv ηe (GM16.sphereWallTangle θ)) θ
  let Tstar := inducedTangle (Hypergraph.ofGraph G₀ hV₀ hE₀) (Hypergraph.ofGraph K_G₀ hVKG₀ hEKG₀)
    (GM16.imageHypergraphTangle ηv ηe (GM16.sphereWallTangle θ)) θ
  have hTstarG : GM15.IsGraphTangle G₀ θ Tstar := ⟨hV₀, hE₀, hTstar⟩
  have hChosen : ηe '' Wsph.edgeSet ⊆ (Hypergraph.ofGraph N hVN hEN).edgeSet := by
    rintro e ⟨e₀, he₀, rfl⟩
    exact hmodel_N.edge_mem e₀ he₀
  have hConformal : inducedTangle (Hypergraph.ofGraph G₀ hTstarG.finite_V hTstarG.finite_E)
      (Hypergraph.ofGraph N hVN hEN) TN θ ⊆ Tstar := by
    have hSub := GM16.inducedTangle_subset_of_same_edge_pattern Wsph
      (Hypergraph.ofGraph G₀ hV₀ hE₀) (Hypergraph.ofGraph N hVN hEN)
      ηv ηv ηe (GM16.sphereWallTangle θ) θ hChosen
    simpa only [TN, Tstar, hImageN, hImageG₀] using hSub
  -- Transport `TN` along `f, g` to `Γ'.toHypergraph`
  have hfInj_N : InjOn f V(N) := hfInj.mono hNW.vertexSet_mono
  have hgInj_N : InjOn g E(N) := hgInj.mono hNW.edgeSet_mono
  have hf_inv_η' : ∀ x ∈ Γ'.V, f (η'.vMap x) = x := by
    intro x hx
    have hxW : η'.vMap x ∈ V(W.graph) := hNW.vertexSet_mono (η'.bijOn_v.mapsTo hx)
    have hxW₀ : η₀.vMap x ∈ V(W.graph) := hxW
    have hxΓ : x ∈ Γ.drawing.V := Γ.drawing.spanV_subset _ _ hx
    rw [hf ⟨η'.vMap x, hxW⟩]
    change (Γ.iso.vertexEquiv ⟨η₀.vMap x, hxW₀⟩).1 = x
    have h1 := hη₀V ⟨x, hxΓ⟩
    have h2 : (⟨η₀.vMap x, hxW₀⟩ : V(W.graph)) = Γ.iso.vertexEquiv.symm ⟨x, hxΓ⟩ := Subtype.ext h1
    rw [h2, Equiv.apply_symm_apply]
  have hg_inv_η' : ∀ e ∈ Γ'.E, g (η'.eMap e) = e := by
    intro e he
    have heW : η'.eMap e ∈ E(W.graph) := hNW.edgeSet_mono (η'.bijOn_e.mapsTo he)
    have heW₀ : η₀.eMap e ∈ E(W.graph) := heW
    have heΓ : e ∈ Γ.drawing.E := (mem_interSet_E_iff.mp he).1
    rw [hg ⟨η'.eMap e, heW⟩]
    change (Γ.iso.edgeEquiv ⟨η₀.eMap e, heW₀⟩).1 = e
    have h1 := hη₀E ⟨e, heΓ⟩
    have h2 : (⟨η₀.eMap e, heW₀⟩ : E(W.graph)) = Γ.iso.edgeEquiv.symm ⟨e, heΓ⟩ := Subtype.ext h1
    rw [h2, Equiv.apply_symm_apply]
  have hHyp' : GM16.imageHypergraph f g (Hypergraph.ofGraph N hVN hEN) = Γ'.toHypergraph := by
    apply Hypergraph.ext
    · ext x
      constructor
      · rintro ⟨v, hvN, rfl⟩
        obtain ⟨x', hx', rfl⟩ := (η'.bijOn_v.image_eq ▸ hvN : v ∈ η'.vMap '' Γ'.V)
        rwa [hf_inv_η' x' hx']
      · intro hx'
        exact ⟨η'.vMap x, η'.bijOn_v.mapsTo hx', hf_inv_η' x hx'⟩
    · ext e
      constructor
      · rintro ⟨f₀, hf₀N, rfl⟩
        obtain ⟨e', he', rfl⟩ := (η'.bijOn_e.image_eq ▸ hf₀N : f₀ ∈ η'.eMap '' Γ'.E)
        rwa [hg_inv_η' e' he']
      · intro he'
        exact ⟨η'.eMap e, η'.bijOn_e.mapsTo he', hg_inv_η' e he'⟩
    · funext e x
      apply propext
      constructor
      · rintro ⟨f₀, v₀, hinc, rfl, rfl⟩
        have hf₀N : f₀ ∈ E(N) := by obtain ⟨w₀, hlink⟩ := hinc; exact hlink.edge_mem
        have hv₀N : v₀ ∈ V(N) := by obtain ⟨w₀, hlink⟩ := hinc; exact hlink.left_mem
        obtain ⟨e', he', rfl⟩ := (η'.bijOn_e.image_eq ▸ hf₀N : f₀ ∈ η'.eMap '' Γ'.E)
        obtain ⟨x', hx', rfl⟩ := (η'.bijOn_v.image_eq ▸ hv₀N : v₀ ∈ η'.vMap '' Γ'.V)
        rw [hg_inv_η' e' he', hf_inv_η' x' hx']
        exact ⟨he', hx', (η'.inc_iff e' he' x' hx').mp hinc⟩
      · rintro ⟨he', hx', hxcl⟩
        refine ⟨η'.eMap e, η'.vMap x, (η'.inc_iff e he' x hx').mpr hxcl,
          hg_inv_η' e he', hf_inv_η' x hx'⟩
  have hTD' : IsTangle Γ'.toHypergraph θ (GM16.imageHypergraphTangle f g TN) := by
    rw [← hHyp']
    exact GM16.isTangle_imageHypergraphTangle_on f g hfInj_N hgInj_N hTN
  have hInv' : LeftInvOn η'.eMap g E(N) := by
    intro f₀ hf₀N
    have hf₀W : f₀ ∈ E(W.graph) := hNW.edgeSet_mono hf₀N
    change η₀.eMap (g f₀) = f₀
    rw [hg ⟨f₀, hf₀W⟩, hη₀E (Γ.iso.edgeEquiv ⟨f₀, hf₀W⟩)]
    exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨f₀, hf₀W⟩)
  have hCtrl' := GM16.controllingTangle_of_induced_subset η' rfl hTstarG le_rfl hVN hEN TN hTN
    f g hInv' hTD' hConformal
  refine ⟨η', Tstar, GM16.imageHypergraphTangle f g TN, hNW, hVert_N, hVerts_N, hEdges_N, hCtrl', ?_⟩
  -- Row property on `Γ'`
  rintro A B ⟨⟨A', B'⟩, hA'B', hpair⟩ j hj
  have hA : A = GM16.imageHypergraph f g A' := (congrArg Prod.fst hpair).symm
  obtain ⟨hSep', -, p', hp', hp'E⟩ := hA'B'
  obtain ⟨⟨A₀, B₀⟩, h₀_sep, hp'eq⟩ := hp'
  have hA₀E : ηe '' A₀.edgeSet = A'.edgeSet ∩ E(K_N) := by
    rw [← hp'eq] at hp'E
    exact hp'E
  by_contra hall
  push Not at hall
  apply sphereWallTangle_no_small_row hθ_two h₀_sep ⟨j, hj⟩
  intro e he
  have heW : e ∈ (GM16.sphereWallSimpleGraph θ).edgeSet :=
    (GM16.sphereWallRow_le θ ⟨j, hj⟩).edgeSet_mono he
  have hfN : ηe e ∈ E(N) := hmodel_N.edge_mem e heW
  have hfW : ηe e ∈ E(W.graph) := hNW.edgeSet_mono hfN
  have hgE : g (ηe e) ∈ Γ'.E := by
    have hmem : g (ηe e) ∈ (GM16.imageHypergraph f g (Hypergraph.ofGraph N hVN hEN)).edgeSet :=
      ⟨ηe e, hfN, rfl⟩
    rwa [hHyp'] at hmem
  have hg_sub : g (ηe e) ⊆ fig1Sph φ '' fig1RowSeg W.height j := by
    have hfP₀ : ηe e ∈ E(W_θ.subdivisionPaths (W_θ.sphereEdge e)) := hηe e heW
    obtain ⟨a₁, b₁, ⟨rfl, hadjE⟩, ha₁, hb₁⟩ := he
    have hadj : (GM16.sphereWallSimpleGraph θ).Adj a₁ b₁ := hadjE
    have hadj' : elementaryWallAdj θ (sphereToWall a₁) (sphereToWall b₁) := sphereToWall_adj hadj
    have hfP : ηe s(a₁, b₁) ∈ E(W_θ.subdivisionPaths (W_θ.baseEdge hadj')) := by
      have h2 : W_θ.sphereEdge s(a₁, b₁) = W_θ.baseEdge hadj' := W_θ.sphereEdge_mk hadj'
      exact h2 ▸ hfP₀
    have hadjW : elementaryWallAdj W.height (wallShift 0 0 (sphereToWall a₁))
        (wallShift 0 0 (sphereToWall b₁)) :=
      (elementaryWallAdj_wallShift_iff hθ_two hθ_le heven_zero heven_zero (by omega) (by omega)
        hadj'.1 hadj'.2.1).mp hadj'
    have hbase_eq : W_θ.baseEdge hadj' = W.toWall.baseEdge hadjW := rfl
    have hfPW : ηe s(a₁, b₁) ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadjW)) :=
      hbase_eq ▸ hfP
    rw [hg ⟨ηe s(a₁, b₁), hfW⟩]
    refine (hΓe _ _ hadjW (ηe s(a₁, b₁)) hfW hfPW).trans (image_mono ?_)
    have ha₁j : a₁.2.val = j := congrArg Fin.val ha₁
    have hb₁j : b₁.2.val = j := congrArg Fin.val hb₁
    have hstep : b₁.1.val = a₁.1.val + 1 ∨ a₁.1.val = b₁.1.val + 1 := by
      have h12 : a₁.2 = b₁.2 := ha₁.trans hb₁.symm
      rcases hadj with ⟨-, h | h⟩ | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
      · rw [h12] at h; omega
      · rw [h12] at h; omega
    have hpa : wallShift 0 0 (sphereToWall a₁) = (a₁.1.val + 1, j) := by
      simp [wallShift, sphereToWall, ha₁j]
    have hpb : wallShift 0 0 (sphereToWall b₁) = (b₁.1.val + 1, j) := by
      simp [wallShift, sphereToWall, hb₁j]
    rw [hpa, hpb]
    have := a₁.1.isLt
    have := b₁.1.isLt
    exact fig1Segment_subset_fig1RowSeg (by omega) (by omega) (by omega) (by omega) (by omega)
  have hgA : g (ηe e) ∈ A.edgeSet := hall (g (ηe e)) hgE hg_sub
  rw [hA] at hgA
  obtain ⟨f', hf', hgf'⟩ := hgA
  have hf'N : f' ∈ E(N) := hSep'.left_le.edgeSet_subset hf'
  have hf'eq : f' = ηe e := hgInj_N hf'N hfN hgf'
  have hKE : E(K_N) = ηe '' Wsph.edgeSet := congrArg Hypergraph.edgeSet hImageN
  have hmem : ηe e ∈ A'.edgeSet ∩ E(K_N) := ⟨hf'eq ▸ hf', hKE ▸ ⟨e, heW, rfl⟩⟩
  rw [← hA₀E] at hmem
  obtain ⟨e₀, he₀, he₀eq⟩ := hmem
  have he₀W : e₀ ∈ Wsph.edgeSet := (GM10.IsTangle.isSeparation
    (GM16.theorem_4_2_claim_1 hθ_two) h₀_sep).left_le.edgeSet_subset he₀
  rw [← hmodel_N.edge_injOn he₀W heW he₀eq]
  exact he₀

/-! ## 4. Free Eye Sets, Tangle Distance Between Eye Regions, and Proof of (9.1) -/

/-- If `(A, B)` is a separation of `Γ'.toHypergraph` and `Row ⊆ Z` contains an edge `e ∈ Γ'.E` with
`e ∉ A.edgeSet`, then no preconnected subset `Z ⊆ Γ'.U \ (A.vertexSet ∩ B.vertexSet)` containing
`Row` can also contain a vertex `p₀ ∈ A.vertexSet \ B.vertexSet`. -/
theorem no_preconnected_to_row_of_tangle_sep
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ' : Drawing S} {A B : Hypergraph S (Set S)}
    (hsep : Γ'.toHypergraph.IsSeparation A B)
    {Row : Set S}
    (hrow : ∃ e ∈ Γ'.E, e ⊆ Row ∧ e ∉ A.edgeSet)
    {Z : Set S} (hZ_pre : IsPreconnected Z)
    (hZ_sub : Z ⊆ Γ'.U \ (A.vertexSet ∩ B.vertexSet))
    (hRow_sub : Row ⊆ Z)
    (hp₀ : ∃ p₀ ∈ Z, p₀ ∈ A.vertexSet \ B.vertexSet) :
    False := by
  have hcl : ∀ e ∈ (PaintingOrDrawing.drawing Γ').E,
      closure e \ (PaintingOrDrawing.drawing Γ').V ⊆ e :=
    fun e he => (Γ'.closure_diff_V he).subset
  have hAc : IsClosed (PaintingOrDrawing.underlying A) :=
    GM11.isClosed_underlying (Γ := PaintingOrDrawing.drawing Γ') hcl hsep.left_le
  have hBc : IsClosed (PaintingOrDrawing.underlying B) :=
    GM11.isClosed_underlying (Γ := PaintingOrDrawing.drawing Γ') hcl hsep.right_le
  have hcov : Γ'.U ⊆ PaintingOrDrawing.underlying A ∪ PaintingOrDrawing.underlying B :=
    GM11.U_subset_underlying (Γ := PaintingOrDrawing.drawing Γ')
      (fun x hx hxV => Γ'.exists_edge_of_mem hx hxV) hsep
  have hint : PaintingOrDrawing.underlying A ∩ PaintingOrDrawing.underlying B ⊆
      (A ∩ B).vertexSet :=
    GM11.underlying_inter (Γ := PaintingOrDrawing.drawing Γ')
      (fun e he f hf x hxe hxf => Γ'.edge_eq_of_mem he hf hxe hxf)
      (fun e he x hx => GM11.edge_notMem_V he hx) hsep
  have hZ_cov : Z ⊆ PaintingOrDrawing.underlying A ∪ PaintingOrDrawing.underlying B :=
    fun x hx => hcov (hZ_sub hx).1
  obtain ⟨p₀, hp₀Z, hp₀A, hp₀_notB⟩ := hp₀
  obtain ⟨e, heE, heRow, he_notA⟩ := hrow
  obtain ⟨z, hz⟩ := heE.1
  have hzZ : z ∈ Z := hRow_sub (heRow hz)
  have hz_notV : z ∉ Γ'.V := GM11.edge_notMem_V heE hz
  have hz_notA : z ∉ PaintingOrDrawing.underlying A := by
    rintro (hzAV | ⟨f, hfA, hzf⟩)
    · exact hz_notV (hsep.left_le.vertexSet_subset hzAV)
    · have hfE : f ∈ Γ'.E := hsep.left_le.edgeSet_subset hfA
      have hef : e = f := Γ'.edge_eq_of_mem heE hfE hz hzf
      exact he_notA (hef ▸ hfA)
  have hzB : z ∈ PaintingOrDrawing.underlying B := (hZ_cov hzZ).resolve_left hz_notA
  obtain ⟨w, hwZ, hwA, hwB⟩ := isPreconnected_closed_iff.mp hZ_pre
    (PaintingOrDrawing.underlying A) (PaintingOrDrawing.underlying B) hAc hBc hZ_cov
    ⟨p₀, hp₀Z, Or.inl hp₀A⟩ ⟨z, hzZ, hzB⟩
  exact (hZ_sub hwZ).2 (hint ⟨hwA, hwB⟩)

/-- Every eye coordinate `fig1EyeCoord i j h idx` belongs to `frontier (fig1Collar i j h 0)` when
`6 ≤ h` and `Even h`. -/
theorem fig1EyeCoord_mem_frontier_zero {i j h : ℕ} (hh : 6 ≤ h) (he : Even h) (idx : Fin 4) :
    fig1EyeCoord i j h idx ∈ frontier (fig1Collar i j h 0) := by
  rw [fig1Collar_zero, ← (wallShiftRealHomeomorph i j).image_frontier]
  have hcross := pairsCrossOn_frontier_fig1EnclosedSet hh he
  have hsub : ((j + h - 2 : ℕ) : ℝ) = ((h : ℝ) - 2) + (j : ℝ) := by
    have : (j + h - 2) + 2 = j + h := Nat.sub_add_cancel (by omega)
    have h1 : (((j + h - 2) + 2 : ℕ) : ℝ) = ((j + h : ℕ) : ℝ) := Nat.cast_inj.mpr this
    push_cast at h1
    linarith
  fin_cases idx
  · refine ⟨((1 : ℝ), (2 : ℝ)), hcross.1, ?_⟩
    ext <;> dsimp [fig1EyeCoord] <;> push_cast <;> ring
  · refine ⟨(2 * (h : ℝ), (2 : ℝ)), hcross.2.2.2.1, ?_⟩
    ext <;> dsimp [fig1EyeCoord] <;> push_cast <;> ring
  · refine ⟨(2 * (h : ℝ), (h : ℝ) - 2), hcross.2.2.1, ?_⟩
    ext <;> dsimp [fig1EyeCoord]
    · push_cast; ring
    · rw [hsub]
  · refine ⟨((1 : ℝ), (h : ℝ) - 2), hcross.2.1, ?_⟩
    ext <;> dsimp [fig1EyeCoord]
    · push_cast; ring
    · rw [hsub]

/-- For each `a : Fin t`, the 4 eye vertices `fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx)`
(`idx : Fin 4`) form a free set (`GM10.IsFreeSet`) of `Γ'.toHypergraph` with respect to `T'` of
order `θ`. -/
theorem eye_four_points_isFreeSet {t H_h M θ : ℕ}
    (hH_two : 2 ≤ H_h) (hH_even : Even H_h)
    (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    (i₀ j₀ h₀ : Fin t → ℕ)
    (hh₀ : ∀ c, 6 ≤ h₀ c ∧ Even (h₀ c))
    (hi₀_even : ∀ c, Even (i₀ c))
    (hj₀_even : ∀ c, Even (j₀ c))
    (hi₀_lo : ∀ c, 4 * M + 6 ≤ i₀ c - 4 * M)
    (hj₀_lo : ∀ c, M + 1 ≤ j₀ c - 2 * M)
    (hi₀_hi : ∀ c, i₀ c + 2 * h₀ c + 4 * M ≤ 2 * H_h)
    (hj₀_hi : ∀ c, j₀ c + h₀ c + 2 * M ≤ H_h)
    (hsep : ∀ c₁ c₂, c₁ ≠ c₂ → ∀ n₁ ≤ M, ∀ n₂ ≤ M,
      Disjoint (fig1Collar (i₀ c₁) (j₀ c₁) (h₀ c₁) n₁)
        (fig1Collar (i₀ c₂) (j₀ c₂) (h₀ c₂) n₂))
    (hM : 31 ≤ M) (hθ : 4 ≤ θ)
    {Γ' : Drawing (OnePoint EuclideanPlane)}
    (hΓ'U : Γ'.U = fig1Sph φ '' (fig1Set H_h \ ⋃ c : Fin t, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0)))
    {T' : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    (hT' : IsTangle Γ'.toHypergraph θ T')
    (hrow : ∀ A B, (A, B) ∈ T' → ∀ j < θ,
      ∃ e ∈ Γ'.E, e ⊆ fig1Sph φ '' fig1RowSeg H_h j ∧ e ∉ A.edgeSet)
    (a : Fin t)
    (hpt_V : ∀ idx : Fin 4, fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx) ∈ Γ'.V) :
    let pt : Fin 4 → OnePoint EuclideanPlane :=
      fun idx => fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx)
    GM10.IsFreeSet Γ'.toHypergraph T' θ {pt 0, pt 1, pt 2, pt 3} := by
  intro pt
  have hEmb := isOpenEmbedding_fig1Sph φ
  let X : Set (OnePoint EuclideanPlane) := {pt 0, pt 1, pt 2, pt 3}
  have hX_V : X ⊆ Γ'.toHypergraph.vertexSet := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact hpt_V 0
    · exact hpt_V 1
    · exact hpt_V 2
    · exact hpt_V 3
  have hX_card : X.ncard ≤ 4 :=
    (ncard_insert_le _ _).trans (Nat.add_le_add_right
      ((ncard_insert_le _ _).trans (Nat.add_le_add_right
        ((ncard_insert_le _ _).trans (by simp)) 1)) 1)
  refine ⟨hX_V, hX_card.trans hθ, fun A B hAB hXA => ?_⟩
  refine hX_card.trans ?_
  by_contra hlt
  push Not at hlt
  have hsep_AB : Γ'.toHypergraph.IsSeparation A B := hT'.isSeparation hAB
  let S_sep : Set (ℝ × ℝ) := fig1Sph φ ⁻¹' (A.vertexSet ∩ B.vertexSet)
  have hAB_fin : (A.vertexSet ∩ B.vertexSet).Finite := (A ∩ B).vertexSet_finite
  have hS_fin : S_sep.Finite := hAB_fin.preimage hEmb.injective.injOn
  have hS_card : S_sep.ncard ≤ 3 := by
    rw [← Set.ncard_image_of_injective S_sep hEmb.injective]
    have hle : (fig1Sph φ '' S_sep).ncard ≤ separationOrder A B :=
      ncard_le_ncard (image_preimage_subset _ _) hAB_fin
    omega
  -- Choose `n₀ ∈ Icc 4 7` with `frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀)` disjoint from `S_sep`
  have h_collar_disj : PairwiseDisjoint (Icc 4 (4 + 3))
      (fun n => frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n)) := by
    intro n₁ hn₁ n₂ hn₂ hne
    have := hi₀_lo a
    have := hj₀_lo a
    have := (mem_Icc.mp hn₁).2
    have := (mem_Icc.mp hn₂).2
    exact disjoint_frontier_fig1Collar_of_ne (M := M) (by omega) (by omega)
      (by omega) (by omega) hne
  obtain ⟨n₀, hn₀_mem, hn₀_disj⟩ := exists_disjoint_of_ncard_le hS_fin hS_card 4 h_collar_disj
  have hn₀_bounds : 4 ≤ n₀ ∧ n₀ ≤ 7 := mem_Icc.mp hn₀_mem
  -- Choose `idx₀ : Fin 4` with `fig1EyeConnector (i₀ a) (j₀ a) (h₀ a) n₀ idx₀` disjoint from `S_sep`
  let connFam : ℕ → Set (ℝ × ℝ) := fun k =>
    if hk : k < 4 then fig1EyeConnector (i₀ a) (j₀ a) (h₀ a) n₀ ⟨k, hk⟩ else ∅
  have h_conn_disj : PairwiseDisjoint (Icc 0 (0 + 3)) connFam := by
    intro k₁ hk₁ k₂ hk₂ hne
    have hk₁_lt : k₁ < 4 := by have := (mem_Icc.mp hk₁).2; omega
    have hk₂_lt : k₂ < 4 := by have := (mem_Icc.mp hk₂).2; omega
    change Disjoint (connFam k₁) (connFam k₂)
    dsimp [connFam]
    rw [dite_eq_left hk₁_lt, dite_eq_left hk₂_lt]
    exact disjoint_fig1EyeConnector_of_ne (hh₀ a).1 (fun h => hne (congrArg Fin.val h))
  obtain ⟨k₀, hk₀_mem, hk₀_disj⟩ := exists_disjoint_of_ncard_le hS_fin hS_card 0 h_conn_disj
  have hk₀_lt : k₀ < 4 := by have := (mem_Icc.mp hk₀_mem).2; omega
  let idx₀ : Fin 4 := ⟨k₀, hk₀_lt⟩
  have hidx₀_disj : Disjoint (fig1EyeConnector (i₀ a) (j₀ a) (h₀ a) n₀ idx₀) S_sep := by
    dsimp [connFam] at hk₀_disj
    rwa [dite_eq_left hk₀_lt] at hk₀_disj
  -- Route from `frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₀)` to a row `j_row ≤ 3 < θ`
  have h_h₀ := (hh₀ a).1
  obtain ⟨j_row, Y_base, hj_le, hY_pre, hY_fr, hY_row, hY_sub, hY_disj⟩ :=
    exists_collar_row_route hH_two hH_even i₀ j₀ h₀ hh₀ hi₀_even hj₀_even
      hi₀_lo hj₀_lo hi₀_hi hj₀_hi hsep (M_sep := 3) (by omega) a (n₀ := n₀)
      (by omega) (by omega) hS_fin hS_card hn₀_disj
  let E₀ := fig1EyeConnector (i₀ a) (j₀ a) (h₀ a) n₀ idx₀
  let Z_base := E₀ ∪ Y_base
  let Z := fig1Sph φ '' Z_base
  have h_i₀_lo_a := hi₀_lo a
  have h_j₀_lo_a := hj₀_lo a
  have h_i₀_hi_a := hi₀_hi a
  have h_j₀_hi_a := hj₀_hi a
  have hE₀_meet : (E₀ ∩ Y_base).Nonempty :=
    (fig1EyeConnector_inter_frontier_nonempty (i := i₀ a) (j := j₀ a) (h := h₀ a) (n := n₀)
      (hh₀ a).1 (hh₀ a).2 (by omega) (by omega) idx₀).mono
      (inter_subset_inter_right _ hY_fr)
  have hZ_pre : IsPreconnected Z :=
    ((isPreconnected_fig1EyeConnector (i₀ a) (j₀ a) (h₀ a) n₀ idx₀).union' hE₀_meet hY_pre).image
      _ hEmb.continuous.continuousOn
  have hE₀_sub := fig1EyeConnector_subset (H_h := H_h) (i := i₀ a) (j := j₀ a) (h := h₀ a) (n := n₀)
    (hh₀ a).1 (hh₀ a).2 (by omega) (by omega) (by omega) (by omega) idx₀
  have hE₀_Γ' : E₀ ⊆ fig1Set H_h \ ⋃ c : Fin t, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0) := by
    intro p hp
    refine ⟨hE₀_sub.2.2 hp, ?_⟩
    intro hpInt
    obtain ⟨c, hpc⟩ := mem_iUnion.mp hpInt
    by_cases hca : c = a
    · subst hca
      exact Set.disjoint_left.mp hE₀_sub.2.1 hp hpc
    · exact Set.disjoint_left.mp (hsep a c (Ne.symm hca) n₀ (by omega) 0 (by omega))
        (hE₀_sub.1 hp) (interior_subset hpc)
  have hZ_sub : Z ⊆ Γ'.U \ (A.vertexSet ∩ B.vertexSet) := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hΓ'U]
      rcases hp with hpE | hpY
      · exact ⟨p, hE₀_Γ' hpE, rfl⟩
      · exact ⟨p, hY_sub hpY, rfl⟩
    · intro hpAB
      have hpS : p ∈ S_sep := hpAB
      rcases hp with hpE | hpY
      · exact Set.disjoint_left.mp hidx₀_disj hpE hpS
      · exact Set.disjoint_left.mp hY_disj hpY hpS
  have hRow_sub : fig1Sph φ '' fig1RowSeg H_h j_row ⊆ Z :=
    image_mono (hY_row.trans subset_union_right)
  have hpt_Z : pt idx₀ ∈ Z :=
    ⟨fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx₀,
      Or.inl (fig1EyeCoord_mem_fig1EyeConnector (by omega) idx₀), rfl⟩
  have hpt_A : pt idx₀ ∈ A.vertexSet := by
    apply hXA
    have hk₀_cases : k₀ = 0 ∨ k₀ = 1 ∨ k₀ = 2 ∨ k₀ = 3 := by omega
    rcases hk₀_cases with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hpt_notB : pt idx₀ ∉ B.vertexSet :=
    fun hB => (hZ_sub hpt_Z).2 ⟨hpt_A, hB⟩
  exact no_preconnected_to_row_of_tangle_sep hsep_AB (hrow A B hAB j_row (by omega))
    hZ_pre hZ_sub hRow_sub ⟨pt idx₀, hpt_Z, hpt_A, hpt_notB⟩

/-- For distinct subwall indices `a ≠ b`, the eye regions `r_a a` and `r_a b` have tangle distance
at least `N₀` (`N₀ ≤ d (r_a a) (r_a b)`). -/
theorem eye_region_dist_ge {t H_h M θ N₀ : ℕ}
    (hH_two : 2 ≤ H_h) (hH_even : Even H_h)
    (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    (i₀ j₀ h₀ : Fin t → ℕ)
    (hh₀ : ∀ c, 6 ≤ h₀ c ∧ Even (h₀ c))
    (hi₀_even : ∀ c, Even (i₀ c))
    (hj₀_even : ∀ c, Even (j₀ c))
    (hi₀_lo : ∀ c, 4 * M + 6 ≤ i₀ c - 4 * M)
    (hj₀_lo : ∀ c, M + 1 ≤ j₀ c - 2 * M)
    (hi₀_hi : ∀ c, i₀ c + 2 * h₀ c + 4 * M ≤ 2 * H_h)
    (hj₀_hi : ∀ c, j₀ c + h₀ c + 2 * M ≤ H_h)
    (hsep : ∀ c₁ c₂, c₁ ≠ c₂ → ∀ n₁ ≤ M, ∀ n₂ ≤ M,
      Disjoint (fig1Collar (i₀ c₁) (j₀ c₁) (h₀ c₁) n₁)
        (fig1Collar (i₀ c₂) (j₀ c₂) (h₀ c₂) n₂))
    (hN₀_pos : 1 ≤ N₀) (hθ : N₀ + 3 ≤ θ) (hM : 3 * N₀ + 5 ≤ M)
    {Γ' : Drawing (OnePoint EuclideanPlane)}
    (hΓ'U : Γ'.U = fig1Sph φ '' (fig1Set H_h \ ⋃ c : Fin t, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0)))
    (hE_ne : Γ'.E.Nonempty)
    {T' : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    (hrow : ∀ A B, (A, B) ∈ T' → ∀ j < θ,
      ∃ e ∈ Γ'.E, e ⊆ fig1Sph φ '' fig1RowSeg H_h j ∧ e ∉ A.edgeSet)
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ' θ T' d)
    {r_a : Fin t → Set (OnePoint EuclideanPlane)}
    (hr_a : ∀ c, r_a c ∈ Γ'.R ∧ subBd (r_a c) = fig1Sph φ '' frontier (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0))
    (hu_V : ∀ c, fig1Sph φ (fig1EyeCoord (i₀ c) (j₀ c) (h₀ c) 0) ∈ Γ'.V)
    {a b : Fin t} (hab : a ≠ b) :
    N₀ ≤ d (r_a a) (r_a b) := by
  by_contra hlt
  push Not at hlt
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hEmb := isOpenEmbedding_fig1Sph φ
  obtain ⟨hResp, K, ins, hK, hder, hdeq⟩ := hd
  have hsl : GM11.IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γ') hS
      ⟨hResp.2.1.one_le, hResp.2.1.isSeparation, hResp.2.1.order_lt, hResp.2.1.axiom1,
        hResp.2.1.axiom2⟩ hK.2.1.1 hder
  let u_c : Fin t → OnePoint EuclideanPlane :=
    fun c => fig1Sph φ (fig1EyeCoord (i₀ c) (j₀ c) (h₀ c) 0)
  have hu_A : ∀ c, ({u_c c} : Set (OnePoint EuclideanPlane)) ∈ Γ'.A :=
    fun c => Or.inl (Or.inl ⟨u_c c, hu_V c, rfl⟩)
  have hr_A : ∀ c, r_a c ∈ Γ'.A := fun c => Or.inr (hr_a c).1
  have hu_cl : ∀ c, u_c c ∈ closure (r_a c) := by
    intro c
    have hmem_fr : fig1EyeCoord (i₀ c) (j₀ c) (h₀ c) 0 ∈
        frontier (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0) :=
      fig1EyeCoord_mem_frontier_zero (hh₀ c).1 (hh₀ c).2 0
    have hmem_bd : u_c c ∈ subBd (r_a c) := by
      rw [(hr_a c).2]
      exact ⟨_, hmem_fr, rfl⟩
    exact hmem_bd.1
  have hd_u : ∀ c, tangleMetric Γ' K ins θ {u_c c} (r_a c) ≤ 1 :=
    fun c => GM11.tangleMetric_le_one hS hK hE_ne (hu_V c) (hr_a c).1 (hu_cl c)
  rw [hdeq (r_a a) (hr_A a) (r_a b) (hr_A b)] at hlt
  have htri1 := GM11.tangleMetric_triangle hS hK.2.1 hsl {u_c a} (r_a a) {u_c b}
  have htri2 := GM11.tangleMetric_triangle hS hK.2.1 hsl (r_a a) (r_a b) {u_c b}
  have hcomm := GM11.tangleMetric_comm Γ' K ins θ (r_a b) {u_c b}
  have hd_ua := hd_u a
  have hd_ub := hd_u b
  have hd_uab_le : tangleMetric Γ' K ins θ {u_c a} {u_c b} ≤ N₀ + 1 := by omega
  have hu_ab_ne : ({u_c a} : Set (OnePoint EuclideanPlane)) ≠ {u_c b} := by
    intro heq
    have h1 : fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0 = fig1EyeCoord (i₀ b) (j₀ b) (h₀ b) 0 :=
      hEmb.injective (singleton_injective heq)
    have hmem_a : fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0 ∈ fig1Collar (i₀ a) (j₀ a) (h₀ a) 0 :=
      (isClosed_fig1Collar _ _ _ _).frontier_subset (fig1EyeCoord_mem_frontier_zero (hh₀ a).1 (hh₀ a).2 0)
    have hmem_b : fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0 ∈ fig1Collar (i₀ b) (j₀ b) (h₀ b) 0 := by
      rw [h1]
      exact (isClosed_fig1Collar _ _ _ _).frontier_subset
        (fig1EyeCoord_mem_frontier_zero (hh₀ b).1 (hh₀ b).2 0)
    exact Set.disjoint_left.mp (hsep a b hab 0 (Nat.zero_le _) 0 (Nat.zero_le _)) hmem_a hmem_b
  obtain ⟨p, W_rad, a', b', ha', hb', hW_len, -, haW, hbW, -⟩ :=
    GM12.exists_tangleMetric_walk_with_two_visit_bound hS hK hsl hu_ab_ne (by omega)
  rw [correspondingAtom_singleton (hu_V a) ha'] at haW
  rw [correspondingAtom_singleton (hu_V b) hb'] at hbW
  let M_sep := N₀ + 1
  -- Step 1: `W_rad` must visit `fig1Sph φ '' fig1Collar (i₀ c) (j₀ c) (h₀ c) M_sep` for both `c = a` and `c = b`
  have hmeet : ∀ c : Fin t, u_c c ∈ GM11.insWalk ins K W_rad →
      ∃ w_c ∈ W_rad.support, w_c ∈ fig1Sph φ '' fig1Collar (i₀ c) (j₀ c) (h₀ c) M_sep := by
    intro c huc_ins
    by_contra hno
    push Not at hno
    have huc_collar : u_c c ∈ fig1Sph φ '' fig1Collar (i₀ c) (j₀ c) (h₀ c) M_sep := by
      have h_i₀_lo_c := hi₀_lo c
      have h_j₀_lo_c := hj₀_lo c
      have h0 : fig1EyeCoord (i₀ c) (j₀ c) (h₀ c) 0 ∈ fig1Collar (i₀ c) (j₀ c) (h₀ c) 0 :=
        (isClosed_fig1Collar _ _ _ _).frontier_subset
          (fig1EyeCoord_mem_frontier_zero (hh₀ c).1 (hh₀ c).2 0)
      have hsub : fig1Collar (i₀ c) (j₀ c) (h₀ c) 0 ⊆ fig1Collar (i₀ c) (j₀ c) (h₀ c) M_sep :=
        (fig1Collar_subset_interior_of_lt (n₁ := 0) (n₂ := M_sep) (by omega) (by omega) (by omega)).trans
          interior_subset
      exact ⟨_, hsub h0, rfl⟩
    rcases huc_ins with huc_U | huc_C
    · rcases GM11.walk_U_cases huc_U with hmem_supp | ⟨e, he, huce⟩
      · exact hno (u_c c) hmem_supp huc_collar
      · have heK : e ∈ K.E :=
          (GM11.walkDrawing_isSubdrawing K W_rad).2 (by rw [GM11.walkDrawing_E]; exact he)
        exact GM11.edge_notMem_V heK huce (hK.2.1.2.1 (hu_V c))
    · obtain ⟨C, ⟨hC, hCW⟩, huc_C⟩ := mem_iUnion₂.mp huc_C
      have hCK : C.IsSubdrawing K := hCW.trans (GM11.walkDrawing_isSubdrawing K W_rad)
      have hClen : C.length ≤ W_rad.length := by
        apply (ncard_le_ncard (fun e he => ?_) W_rad.edges.finite_toSet).trans
          (GM11.ncard_mem_list_le W_rad.edges)
        have hem := hCW.2 he
        rwa [GM11.walkDrawing_E] at hem
      have hClt : C.length < 2 * θ := by omega
      obtain ⟨hdisc, hbd, hT⟩ := hder C hC hCK hClt
      obtain ⟨hcount, _⟩ := GM12.circuit_length_eq_two_mul_ncard hK.2.1 hC hCK
      have hCfin : (C.V ∩ Γ'.V).Finite := Γ'.finite_V.subset inter_subset_right
      have hCsupp : C.V ∩ Γ'.V ⊆ {w | w ∈ W_rad.support} := by
        intro w hw
        have := hCW.1 hw.1
        rwa [GM11.walkDrawing_V] at this
      let X_C : Set (ℝ × ℝ) := fig1Sph φ ⁻¹' (C.V ∩ Γ'.V)
      have hXC_fin : X_C.Finite := hCfin.preimage hEmb.injective.injOn
      have hXC_card : X_C.ncard ≤ M_sep := by
        rw [← Set.ncard_image_of_injective X_C hEmb.injective]
        have hle : (fig1Sph φ '' X_C).ncard ≤ (C.V ∩ Γ'.V).ncard :=
          ncard_le_ncard (image_preimage_subset _ _) hCfin
        omega
      have hXC_disj_collar : Disjoint (fig1Collar (i₀ c) (j₀ c) (h₀ c) M_sep) X_C := by
        rw [Set.disjoint_left]
        intro z hz_col hz_XC
        exact hno (fig1Sph φ z) (hCsupp hz_XC) ⟨z, hz_col, rfl⟩
      have hXC_disj_fr : Disjoint (frontier (fig1Collar (i₀ c) (j₀ c) (h₀ c) M_sep)) X_C :=
        hXC_disj_collar.mono_left (isClosed_fig1Collar _ _ _ _).frontier_subset
      obtain ⟨j_row, Y_base, hj_le, hY_pre, hY_fr, hY_row, hY_sub, hY_disj⟩ :=
        exists_collar_row_route hH_two hH_even i₀ j₀ h₀ hh₀ hi₀_even hj₀_even
          hi₀_lo hj₀_lo hi₀_hi hj₀_hi hsep (M_sep := M_sep) (by omega) c (n₀ := M_sep)
          (by omega) (by omega) hXC_fin hXC_card hXC_disj_fr
      let E₀ := fig1EyeConnector (i₀ c) (j₀ c) (h₀ c) M_sep 0
      let Z_base := E₀ ∪ Y_base
      have h_i₀_lo_c := hi₀_lo c
      have h_j₀_lo_c := hj₀_lo c
      have h_i₀_hi_c := hi₀_hi c
      have h_j₀_hi_c := hj₀_hi c
      have hE₀_meet : (E₀ ∩ Y_base).Nonempty :=
        (fig1EyeConnector_inter_frontier_nonempty (i := i₀ c) (j := j₀ c) (h := h₀ c) (n := M_sep)
          (hh₀ c).1 (hh₀ c).2 (by omega) (by omega) 0).mono
          (inter_subset_inter_right _ hY_fr)
      have hZ_pre : IsPreconnected Z_base :=
        (isPreconnected_fig1EyeConnector (i₀ c) (j₀ c) (h₀ c) M_sep 0).union' hE₀_meet hY_pre
      have hE₀_sub := fig1EyeConnector_subset (H_h := H_h) (i := i₀ c) (j := j₀ c) (h := h₀ c)
        (n := M_sep) (hh₀ c).1 (hh₀ c).2 (by omega) (by omega) (by omega) (by omega) 0
      have hZ_Γ' : Z_base ⊆ fig1Set H_h \ ⋃ c' : Fin t, interior (fig1Collar (i₀ c') (j₀ c') (h₀ c') 0) := by
        intro z hz
        rcases hz with hzE | hzY
        · refine ⟨hE₀_sub.2.2 hzE, ?_⟩
          intro hzInt
          obtain ⟨c', hzc'⟩ := mem_iUnion.mp hzInt
          by_cases hcc' : c' = c
          · subst hcc'
            exact Set.disjoint_left.mp hE₀_sub.2.1 hzE hzc'
          · exact Set.disjoint_left.mp (hsep c c' (Ne.symm hcc') M_sep (by omega) 0 (by omega))
              (hE₀_sub.1 hzE) (interior_subset hzc')
        · exact hY_sub hzY
      have hZ_disj_XC : Disjoint Z_base X_C :=
        (hXC_disj_collar.mono_left hE₀_sub.1).union_left hY_disj
      have hZC : Disjoint (fig1Sph φ '' Z_base) (frontier (ins C)) := by
        rw [← GM11.subBd_eq_frontier, hbd]
        refine disjoint_left.mpr ?_
        rintro _ ⟨z, hzZ, rfl⟩ hzC
        have hzU : fig1Sph φ z ∈ Γ'.U := by
          rw [hΓ'U]
          exact ⟨z, hZ_Γ' hzZ, rfl⟩
        have hzK : fig1Sph φ z ∈ K.U := hCK.U_subset hzC
        have hzV : fig1Sph φ z ∈ Γ'.V := by
          have hm : fig1Sph φ z ∈ (PaintingOrDrawing.drawing Γ').U ∩ K.U := ⟨hzU, hzK⟩
          rwa [hK.2.1.1] at hm
        have hzCV : fig1Sph φ z ∈ C.V := by
          rw [C.U_eq] at hzC
          rcases hzC with hzC | hzC
          · exact hzC
          · obtain ⟨e, heC, hze⟩ := mem_iUnion₂.mp hzC
            have : fig1Sph φ z ∈ closure e ∩ C.V := by
              rw [hCK.closure_inter_V heC]
              exact ⟨hze, hK.2.1.2.1 hzV⟩
            exact this.2
        exact Set.disjoint_left.mp hZ_disj_XC hzZ ⟨hzCV, hzV⟩
      have huc_Z : u_c c ∈ fig1Sph φ '' Z_base :=
        ⟨fig1EyeCoord (i₀ c) (j₀ c) (h₀ c) 0,
          Or.inl (fig1EyeCoord_mem_fig1EyeConnector (by omega) 0), rfl⟩
      have hZ_sub_ins : fig1Sph φ '' Z_base ⊆ ins C :=
        GM12.subset_of_disjoint_frontier
          (hZ_pre.image _ hEmb.continuous.continuousOn) hdisc.isClosed hZC huc_Z huc_C
      obtain ⟨e, heE, heRow, he_notA⟩ := hrow _ _ hT j_row (by omega)
      apply he_notA
      have he_ins : e ⊆ ins C :=
        heRow.trans ((image_mono (hY_row.trans subset_union_right)).trans hZ_sub_ins)
      exact ⟨heE, he_ins⟩
  -- Step 2: Connect `w_a` and `w_b` by a simple walk `W'` of `K` and trap `L = (walkDrawing K W').U`
  -- inside a collar `fig1Collar (i₀ a) (j₀ a) (h₀ a) n₁`
  obtain ⟨w_a, hwa_supp, hwa_col⟩ := hmeet a (haW (mem_singleton (u_c a)))
  obtain ⟨w_b, hwb_supp, hwb_col⟩ := hmeet b (hbW (mem_singleton (u_c b)))
  have hw_ne : w_a ≠ w_b := by
    rintro rfl
    obtain ⟨za, hza, hza_eq⟩ := hwa_col
    obtain ⟨zb, hzb, hzb_eq⟩ := hwb_col
    rw [← hEmb.injective (hza_eq.trans hzb_eq.symm)] at hzb
    exact Set.disjoint_left.mp (hsep a b hab M_sep (by omega) M_sep (by omega)) hza hzb
  obtain ⟨W₁, W₂, rfl⟩ := W_rad.exists_append_of_mem hwa_supp
  let Rot := W₂.append W₁
  have hRot_len : Rot.length ≤ 2 * (N₀ + 1) := by
    rw [GraphWalk.length_append] at hW_len ⊢
    omega
  have hwb_Rot : w_b ∈ Rot.support := by
    rw [_root_.GraphMinor.Surface.GraphWalk.mem_support_append] at hwb_supp ⊢
    exact hwb_supp.symm
  obtain ⟨P₁, P₂, hRot_eq⟩ := Rot.exists_append_of_mem hwb_Rot
  have hP₁_len : P₁.length ≤ 2 * (N₀ + 1) := by
    have : P₁.length + P₂.length = Rot.length := by
      rw [← GraphWalk.length_append, ← hRot_eq]
    omega
  obtain ⟨W', hW'_sim, hW'_len, _⟩ := GM12.exists_simple_subwalk P₁
  let L := (GM11.walkDrawing K W').U
  have hP_path : (GM11.walkDrawing K W').IsPathBetween w_a w_b :=
    GM11.walkDrawing_isPathBetween K hW'_sim
  obtain ⟨f_line, -⟩ := GM11.isLine_of_isPathBetween hP_path hw_ne
  have hL_pre : IsPreconnected L := by
    have heq : L = range fun t : unitInterval => (f_line t).1 := by
      ext x
      exact ⟨fun hx => ⟨f_line.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (f_line t).2⟩
    rw [heq]
    exact isPreconnected_range (continuous_subtype_val.comp f_line.continuous)
  have hSubK : (GM11.walkDrawing K W').IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W'
  have hwa_L : w_a ∈ L :=
    (GM11.walkDrawing K W').V_subset_U (by rw [GM11.walkDrawing_V]; exact W'.start_mem_support)
  have hwb_L : w_b ∈ L :=
    (GM11.walkDrawing K W').V_subset_U (by rw [GM11.walkDrawing_V]; exact W'.end_mem_support)
  let M_walk := 2 * N₀ + 3
  have hL_inter_sub : L ∩ Γ'.V ⊆ (W'.support.toFinset : Set (OnePoint EuclideanPlane)) := by
    intro x ⟨hxL, hxV⟩
    have hxWV : x ∈ (GM11.walkDrawing K W').V :=
      GM12.subdrawing_vertex_of_mem_U hSubK hxL (hK.2.1.2.1 hxV)
    rw [GM11.walkDrawing_V] at hxWV
    simpa using hxWV
  have hL_card : (L ∩ Γ'.V).ncard ≤ M_walk := by
    calc (L ∩ Γ'.V).ncard
      _ ≤ (W'.support.toFinset : Set (OnePoint EuclideanPlane)).ncard :=
          ncard_le_ncard hL_inter_sub (Finset.finite_toSet _)
      _ = W'.support.length := by
          rw [ncard_coe_finset, List.toFinset_card_of_nodup hW'_sim]
      _ = W'.length + 1 := GM11.length_support W'
      _ ≤ M_walk := by omega
  let X_L : Set (ℝ × ℝ) := fig1Sph φ ⁻¹' (L ∩ Γ'.V)
  have hL_fin : (L ∩ Γ'.V).Finite := Γ'.finite_V.subset inter_subset_right
  have hXL_fin : X_L.Finite := hL_fin.preimage hEmb.injective.injOn
  have hXL_card : X_L.ncard ≤ M_walk := by
    rw [← Set.ncard_image_of_injective X_L hEmb.injective]
    exact (ncard_le_ncard (image_preimage_subset _ _) hL_fin).trans hL_card
  have h_collar_disj : PairwiseDisjoint (Icc (M_sep + 1) ((M_sep + 1) + M_walk))
      (fun n => frontier (fig1Collar (i₀ a) (j₀ a) (h₀ a) n)) := by
    intro n₁ hn₁ n₂ hn₂ hne
    have := hi₀_lo a
    have := hj₀_lo a
    have := (mem_Icc.mp hn₁).2
    have := (mem_Icc.mp hn₂).2
    exact disjoint_frontier_fig1Collar_of_ne (M := M) (by omega) (by omega)
      (by omega) (by omega) hne
  obtain ⟨n₁, hn₁_mem, hn₁_disj⟩ :=
    exists_disjoint_of_ncard_le hXL_fin hXL_card (M_sep + 1) h_collar_disj
  have hn₁_bounds : M_sep + 1 ≤ n₁ ∧ n₁ ≤ M_sep + 1 + M_walk := mem_Icc.mp hn₁_mem
  let K₁ := fig1Collar (i₀ a) (j₀ a) (h₀ a) n₁
  let Δ₁ := fig1Sph φ '' K₁
  have h_i₀_lo_a := hi₀_lo a
  have h_j₀_lo_a := hj₀_lo a
  have h_i₀_hi_a := hi₀_hi a
  have h_j₀_hi_a := hj₀_hi a
  have h_h₀_a := (hh₀ a).1
  have hΔ₁_disc : IsClosedDisc Δ₁ := by
    dsimp [Δ₁, K₁, fig1Collar]
    rw [← image_comp]
    have hf_a : Topology.IsOpenEmbedding
        (fig1Sph φ ∘ wallShiftRealHomeomorph (i₀ a - 4 * n₁) (j₀ a - 2 * n₁)) :=
      hEmb.comp (wallShiftRealHomeomorph (i₀ a - 4 * n₁) (j₀ a - 2 * n₁)).isOpenEmbedding
    exact isClosedDisc_image_fig1EnclosedSet hS hf_a.isEmbedding (by omega)
  have hΔ₁_int : interior Δ₁ = fig1Sph φ '' interior K₁ := by
    refine Subset.antisymm ?_ (interior_maximal (image_mono interior_subset)
      (hEmb.isOpenMap _ isOpen_interior))
    intro y hy
    obtain ⟨x, _, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    have hU : fig1Sph φ ⁻¹' interior Δ₁ ⊆ K₁ := by
      intro z hz
      obtain ⟨z', hz', hzz'⟩ := interior_subset hz
      rwa [← hEmb.injective hzz']
    exact interior_maximal hU (isOpen_interior.preimage hEmb.continuous) hy
  have hΔ₁_fr : frontier Δ₁ = fig1Sph φ '' frontier K₁ := by
    have hcl : closure Δ₁ = fig1Sph φ '' closure K₁ := by
      rw [hΔ₁_disc.isClosed.closure_eq, (isClosed_fig1Collar _ _ _ _).closure_eq]
    rw [frontier, frontier, hcl, hΔ₁_int, Set.image_sdiff hEmb.injective]
  have hL_disj_fr : Disjoint L (frontier Δ₁) := by
    rw [hΔ₁_fr]
    refine disjoint_left.mpr ?_
    rintro _ hxL ⟨z, hzFr, rfl⟩
    have hz_set : z ∈ fig1Set H_h :=
      frontier_fig1Collar_subset_fig1Set (by omega) (hh₀ a).2 (hi₀_even a) (hj₀_even a)
        (by omega) (by omega) (by omega) (by omega) hzFr
    have hz_not_int : z ∉ ⋃ c : Fin t, interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0) := by
      intro hzInt
      obtain ⟨c, hzc⟩ := mem_iUnion.mp hzInt
      by_cases hca : c = a
      · subst hca
        have hsub0 : interior (fig1Collar (i₀ c) (j₀ c) (h₀ c) 0) ⊆ interior K₁ :=
          interior_subset.trans (fig1Collar_subset_interior_of_lt (by omega) (by omega) (by omega))
        exact hzFr.2 (hsub0 hzc)
      · exact Set.disjoint_left.mp (hsep a c (Ne.symm hca) n₁ (by omega) 0 (by omega))
          ((isClosed_fig1Collar _ _ _ _).frontier_subset hzFr) (interior_subset hzc)
    have hzU : fig1Sph φ z ∈ Γ'.U := by
      rw [hΓ'U]
      exact ⟨z, ⟨hz_set, hz_not_int⟩, rfl⟩
    have hzK : fig1Sph φ z ∈ K.U := hSubK.U_subset hxL
    have hzV : fig1Sph φ z ∈ Γ'.V := by
      have hm : fig1Sph φ z ∈ (PaintingOrDrawing.drawing Γ').U ∩ K.U := ⟨hzU, hzK⟩
      rwa [hK.2.1.1] at hm
    exact Set.disjoint_left.mp hn₁_disj hzFr ⟨hxL, hzV⟩
  have hwa_Δ₁ : w_a ∈ Δ₁ := by
    obtain ⟨za, hza, rfl⟩ := hwa_col
    have hsub : fig1Collar (i₀ a) (j₀ a) (h₀ a) M_sep ⊆ K₁ :=
      (fig1Collar_subset_interior_of_lt (by omega) (by omega) (by omega)).trans interior_subset
    exact ⟨za, hsub hza, rfl⟩
  have hL_sub_Δ₁ : L ⊆ Δ₁ :=
    GM12.subset_of_disjoint_frontier hL_pre hΔ₁_disc.isClosed hL_disj_fr hwa_L hwa_Δ₁
  obtain ⟨za, hza, hza_eq⟩ := hL_sub_Δ₁ hwb_L
  obtain ⟨zb, hzb, hzb_eq⟩ := hwb_col
  rw [← hEmb.injective (hza_eq.trans hzb_eq.symm)] at hzb
  exact Set.disjoint_left.mp (hsep a b hab n₁ (by omega) M_sep (by omega)) hza hzb

/-- Every subwall `W₀.IsSubwallOf W` has the same `graph` and `corner`s as `W.subwallAt i j W₀.height ...`
for some even shift `(i, j)`. -/
lemma Wall.IsSubwallOf.exists_subwallAt_eq {W₀ W : Wall α β} (h : W₀.IsSubwallOf W) :
    ∃ (i j : ℕ) (hi_even : Even i) (hj_even : Even j)
      (hi_le : i ≤ 2 * W.height - 2 * W₀.height) (hj_le : j ≤ W.height - W₀.height),
      let W₀' := W.subwallAt i j W₀.height W₀.two_le_height W₀.even_height h.height_le
        hi_even hj_even hi_le hj_le
      W₀.graph = W₀'.graph ∧
      ∀ {G P Q : Graph α β}, IsCrossOverWall G W₀ P Q → IsCrossOverWall G W₀' P Q := by
  obtain ⟨i, j, hi_even, hj_even, hi_le, hj_le, hbv, hpaths, hbase⟩ := h.exists_shift
  obtain ⟨_, hgraph_eq, hbv_eq, _, _, _⟩ :=
    h.eq_subwallAt_of_shift hi_even hj_even hi_le hj_le hbv hpaths hbase
  refine ⟨i, j, hi_even, hj_even, hi_le, hj_le, hgraph_eq, ?_⟩
  intro G P Q ⟨hdisj, hP, hQ⟩
  have hcorner : ∀ k : Fin 4, W₀.corner k =
      (W.subwallAt i j W₀.height W₀.two_le_height W₀.even_height h.height_le
        hi_even hj_even hi_le hj_le).corner k := by
    intro k
    have hp : elementaryWallCorner W₀.height k ∈ elementaryWallVerts W₀.height := by
      have h2 := W₀.two_le_height
      fin_cases k <;> simp [elementaryWallCorner, elementaryWallVerts] <;> omega
    exact hbv_eq (elementaryWallCorner W₀.height k) hp
  rw [hcorner 0, hcorner 2] at hP
  rw [hcorner 1, hcorner 3] at hQ
  exact ⟨hdisj, hP, hQ⟩

/-- The four eye points `fig1Sph φ (fig1EyeCoord i j h idx)` (`idx = 0, 3, 2, 1`) are pairwise
distinct and occur in cyclic order around any circuit `C` with
`C.U = fig1Sph φ '' frontier (fig1Collar i j h 0)`. -/
theorem pairsCrossOn_eye_circuit {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {i j h : ℕ} (hh : 6 ≤ h) (he : Even h)
    {C : Drawing (OnePoint EuclideanPlane)}
    (hCU : C.U = fig1Sph φ '' frontier (fig1Collar i j h 0)) :
    let pt : Fin 4 → OnePoint EuclideanPlane := fun idx => fig1Sph φ (fig1EyeCoord i j h idx)
    ([pt 0, pt 3, pt 2, pt 1]).Nodup ∧
      OccurInCircuitOrder C (pt 0) (pt 3) (pt 2) (pt 1) := by
  intro pt
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hEmb := isOpenEmbedding_fig1Sph φ
  have hf : Topology.IsOpenEmbedding (fig1Sph φ ∘ wallShiftRealHomeomorph i j) :=
    hEmb.comp (wallShiftRealHomeomorph i j).isOpenEmbedding
  have hDisc : IsClosedDisc (fig1Sph φ '' fig1Collar i j h 0) := by
    dsimp [fig1Collar]
    rw [← image_comp]
    exact isClosedDisc_image_fig1EnclosedSet hS hf.isEmbedding (by omega)
  have hInt : interior (fig1Sph φ '' fig1Collar i j h 0) =
      fig1Sph φ '' interior (fig1Collar i j h 0) := by
    refine Subset.antisymm ?_ (interior_maximal (image_mono interior_subset)
      (hEmb.isOpenMap _ isOpen_interior))
    intro y hy
    obtain ⟨x, _, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    have hU : fig1Sph φ ⁻¹' interior (fig1Sph φ '' fig1Collar i j h 0) ⊆ fig1Collar i j h 0 := by
      intro z hz
      obtain ⟨z', hz', hzz'⟩ := interior_subset hz
      rwa [← hEmb.injective hzz']
    exact interior_maximal hU (isOpen_interior.preimage hEmb.continuous) hy
  have hFr : frontier (fig1Sph φ '' fig1Collar i j h 0) =
      fig1Sph φ '' frontier (fig1Collar i j h 0) := by
    have hcl : closure (fig1Sph φ '' fig1Collar i j h 0) =
        fig1Sph φ '' closure (fig1Collar i j h 0) := by
      rw [hDisc.isClosed.closure_eq, (isClosed_fig1Collar _ _ _ _).closure_eq]
    rw [frontier, frontier, hcl, hInt, Set.image_sdiff hEmb.injective]
  have hOArc : IsOArc C.U := by
    rw [hCU, ← hFr, GM11.IsClosedDisc.frontier_eq_discBd hS hDisc]
    exact hDisc.isOArc_discBd
  apply occurInCircuitOrder_of_pairsCrossOn hOArc
  have hCU' : C.U = (fig1Sph φ ∘ wallShiftRealHomeomorph i j) '' frontier (fig1EnclosedSet h) := by
    rw [hCU, fig1Collar_zero, ← (wallShiftRealHomeomorph i j).image_frontier, ← image_comp]
  have hsub : ((j + h - 2 : ℕ) : ℝ) = ((h : ℝ) - 2) + (j : ℝ) := by
    have : (j + h - 2) + 2 = j + h := Nat.sub_add_cancel (by omega)
    have h1 : (((j + h - 2) + 2 : ℕ) : ℝ) = ((j + h : ℕ) : ℝ) := Nat.cast_inj.mpr this
    push_cast at h1
    linarith
  have hpt0 : (fig1Sph φ ∘ wallShiftRealHomeomorph i j) (1, 2) = pt 0 := by
    dsimp [pt, fig1EyeCoord]; congr 1; ext <;> dsimp <;> push_cast <;> ring
  have hpt2 : (fig1Sph φ ∘ wallShiftRealHomeomorph i j) (2 * (h : ℝ), (h : ℝ) - 2) = pt 2 := by
    dsimp [pt, fig1EyeCoord]; congr 1; ext
    · dsimp; push_cast; ring
    · dsimp; rw [hsub]
  have hpt3 : (fig1Sph φ ∘ wallShiftRealHomeomorph i j) (1, (h : ℝ) - 2) = pt 3 := by
    dsimp [pt, fig1EyeCoord]; congr 1; ext
    · dsimp; push_cast; ring
    · dsimp; rw [hsub]
  have hpt1 : (fig1Sph φ ∘ wallShiftRealHomeomorph i j) (2 * (h : ℝ), 2) = pt 1 := by
    dsimp [pt, fig1EyeCoord]; congr 1; ext <;> dsimp <;> push_cast <;> ring
  rw [hCU', ← hpt0, ← hpt2, ← hpt3, ← hpt1]
  exact PairsCrossOn.image_of_isEmbedding hf.isEmbedding
    (pairsCrossOn_frontier_fig1EnclosedSet hh he)

/-- Core sphere-tangle / independent-eyes step of **Graph Minors XIII, (9.1)** (page 98):
given `k₀, N₀` (`1 ≤ N₀`) from XII (4.5) (`GM12.theorem_4_5_span`) on the sphere, let
`t := max k₀ 1`, `θ := 4 * N₀ + 32`, `M := θ`, and `r := 12 * M + 26`. If `W` is a Fig. 1 drawn wall
in `G` and `H' : Fin t → Wall α β` are `t` subwalls of `W` at pairwise `wallSubgraphDist ≥ r` such
that every vertex of every `H' a` is at `planeDist ≥ r / 2` from the outer point
`φ (fig1PlaneEquiv (-1, -1))`, and `(P' a, Q' a)` are crosses over `H' a` satisfying (i) and (ii)
of (9.1), then `G` has a `K_p`-minor (`HasGraphModel (GM16.completeGraph p) G`). -/
theorem lemma_9_1_tangle_eyes_step (p : ℕ) {k₀ N₀ : ℕ} (hN₀_pos : 1 ≤ N₀)
    (h45 : ∀ (G : Graph α β) (θstar θ : ℕ)
      (Tstar : Set (Hypergraph α β × Hypergraph α β)) (Γ : Drawing (OnePoint EuclideanPlane))
      (η : SpanEmbedding Γ G)
      (T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
        Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))))
      (d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ)
      (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N₀ ≤ θ →
      ∀ (r : Fin k₀ → Set (OnePoint EuclideanPlane)) (P Q : Fin k₀ → Graph α β),
      Function.Injective r → (∀ i, GM15.IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i)) →
      (∀ i j, i ≠ j → N₀ ≤ d (r i) (r j)) →
      (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
        ((P j).vertexSet ∪ (Q j).vertexSet)) →
      GM12.ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p)) :
    let t := max k₀ 1
    let θ := 4 * N₀ + 32
    let M := θ
    let r := 12 * M + 26
    ∀ {G : Graph α β} {W : DrawnWall α β}
      {φ : EuclideanPlane ≃ₜ EuclideanPlane}
      {Γ₀ : GraphDrawing W.graph EuclideanPlane}
      {pos : α → ℝ × ℝ}
      {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)},
      IsFigure1CoordDrawing W.toWall Γ₀ →
      W.drawingU = φ '' Γ₀.drawing.U →
      (∀ (v : α) (hv : v ∈ V(W.graph)), W.vertexPoint v = φ (Γ₀.iso.vertexEquiv ⟨v, hv⟩).1) →
      InjOn pos V(W.graph) →
      (∀ (q : ℕ × ℕ) (hq : q ∈ elementaryWallVerts W.height),
        pos (W.toWall.branchVertex q hq) = ((q.1 : ℝ), (q.2 : ℝ))) →
      Γ.drawing.U = fig1Sph φ '' fig1Set W.height →
      (∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) →
      (∀ (p' q' : ℕ × ℕ) (hadj : elementaryWallAdj W.height p' q') (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj)) →
          (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p' q') →
      (∀ (p' q' : ℕ × ℕ) (hadj : elementaryWallAdj W.height p' q'),
        (⋃ f : {f : E(W.graph) // f.1 ∈ E(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj))},
          closure (Γ.iso.edgeEquiv f.1).1) = fig1Sph φ '' fig1Segment p' q') →
      W.graph ≤ G →
      ∀ (H' : Fin t → Wall α β) (P' Q' : Fin t → Graph α β),
        (∀ a : Fin t, (H' a).IsSubwallOf W.toWall) →
        (∀ a : Fin t, ∀ x ∈ V((H' a).graph),
          r / 2 ≤ W.planeDist (φ (fig1PlaneEquiv (-1, -1))) (W.vertexPoint x)) →
        (∀ a b : Fin t, a ≠ b → r ≤ wallSubgraphDist W (H' a).graph (H' b).graph) →
        (∀ a : Fin t, IsCrossOverWall G (H' a) (P' a) (Q' a)) →
        (∀ a : Fin t, (V(P' a) ∪ V(Q' a)) ∩ V(W.graph) ⊆ V((H' a).graph)) →
        Pairwise (fun a b : Fin t => Disjoint (V(P' a) ∪ V(Q' a)) (V(P' b) ∪ V(Q' b))) →
        HasGraphModel (GM16.completeGraph p) G := by
  intro t θ M r G W φ Γ₀ pos Γ hΓ₀ hW_U hW_v hpos_inj hpos_bv hΓU hΓv hΓe hΓe_cl hWG H' P' Q'
    hsub hfar_out hdist hcross hinter hdisj
  have hαβ := W.toWall.nonempty_types
  have := hαβ.1
  have := hαβ.2
  have ht_pos : 1 ≤ t := le_max_right k₀ 1
  have hk₀_le : k₀ ≤ t := le_max_left k₀ 1
  have hθ_two : 2 ≤ θ := by omega
  have hθ_four : 4 ≤ θ := by omega
  have hθ_even : Even θ := ⟨2 * N₀ + 16, by omega⟩
  have hM_31 : 31 ≤ M := by omega
  have hM_3N₀ : 3 * N₀ + 5 ≤ M := by omega
  have hθ_M : θ ≤ M := le_rfl
  -- Step 1: Finite subgraph `G₀ ≤ G` containing `W.graph` and all `P' a, Q' a`
  let fam : Option (Fin t ⊕ Fin t) → Graph α β
    | none => W.graph
    | some (Sum.inl a) => P' a
    | some (Sum.inr a) => Q' a
  obtain ⟨G₀, hG₀G, hVG₀, hEG₀, hfam⟩ :=
    exists_finite_le (G := G) fam
      (by rintro (_ | a | a); exacts [hWG, (hcross a).2.1.1, (hcross a).2.2.1])
      (by rintro (_ | a | a)
          · exact W.toWall.vertexSet_finite
          · exact IsGraphPathWithEnds.vertexSet_finite (hcross a).2.1
          · exact IsGraphPathWithEnds.vertexSet_finite (hcross a).2.2)
      (by rintro (_ | a | a)
          · exact W.toWall.edgeSet_finite
          · exact IsGraphPathWithEnds.edgeSet_finite (hcross a).2.1
          · exact IsGraphPathWithEnds.edgeSet_finite (hcross a).2.2)
  have hWG₀ : W.graph ≤ G₀ := hfam none
  have hP'_G₀ : ∀ a, P' a ≤ G₀ := fun a => hfam (some (Sum.inl a))
  have hQ'_G₀ : ∀ a, Q' a ≤ G₀ := fun a => hfam (some (Sum.inr a))
  have hcross_G₀ : ∀ a : Fin t, IsCrossOverWall G₀ (H' a) (P' a) (Q' a) := by
    intro a
    exact ⟨(hcross a).1,
      (hcross a).2.1.of_le (hP'_G₀ a),
      (hcross a).2.2.of_le (hQ'_G₀ a)⟩
  -- Step 2: Shift coordinates `(i_orig a, j_orig a)` and enlarged collars `(i₀ a, j₀ a, h₀ a)`
  have hex_shift : ∀ a : Fin t, ∃ (i j : ℕ) (hi_even : Even i) (hj_even : Even j)
      (hi_le : i ≤ 2 * W.height - 2 * (H' a).height) (hj_le : j ≤ W.height - (H' a).height),
      let W₀' := W.toWall.subwallAt i j (H' a).height (H' a).two_le_height (H' a).even_height
        (hsub a).height_le hi_even hj_even hi_le hj_le
      (H' a).graph = W₀'.graph ∧ IsCrossOverWall G₀ W₀' (P' a) (Q' a) := by
    intro a
    obtain ⟨i, j, hi_even, hj_even, hi_le, hj_le, hgraph_eq, hcross_imp⟩ :=
      (hsub a).exists_subwallAt_eq
    exact ⟨i, j, hi_even, hj_even, hi_le, hj_le, hgraph_eq, hcross_imp (hcross_G₀ a)⟩
  choose i_orig j_orig hi_orig_even hj_orig_even hi_orig_le hj_orig_le hH'_eq hcross_sub using hex_shift
  have hmargin : ∀ a : Fin t,
      4 * M + 8 ≤ j_orig a ∧
      j_orig a + (H' a).height + (4 * M + 8) ≤ W.height ∧
      2 * (4 * M + 8) ≤ i_orig a ∧
      i_orig a + 2 * (H' a).height + 2 * (4 * M + 8) ≤ 2 * W.height := by
    intro a
    refine hΓ₀.subwallAt_shift_margin hW_U hW_v
      (H' a).two_le_height (H' a).even_height (hsub a).height_le
      (hi_orig_even a) (hj_orig_even a) (hi_orig_le a) (hj_orig_le a) (m := 4 * M + 8) ?_
    intro x hx
    rw [← hH'_eq a] at hx
    have := hfar_out a x hx
    omega
  have hbox_sep : ∀ a b : Fin t, a ≠ b →
      i_orig a + 2 * (H' a).height + 2 * (4 * M + 6) < i_orig b ∨
      i_orig b + 2 * (H' b).height + 2 * (4 * M + 6) < i_orig a ∨
      j_orig a + (H' a).height + (4 * M + 6) < j_orig b ∨
      j_orig b + (H' b).height + (4 * M + 6) < j_orig a := by
    intro a b hab
    refine hΓ₀.subwallAt_shift_sep hW_U hW_v
      (H' a).two_le_height (H' a).even_height (hsub a).height_le
      (hi_orig_even a) (hj_orig_even a) (hi_orig_le a) (hj_orig_le a)
      (H' b).two_le_height (H' b).even_height (hsub b).height_le
      (hi_orig_even b) (hj_orig_even b) (hi_orig_le b) (hj_orig_le b)
      (δ := 4 * M + 6) ?_
    rw [← hH'_eq a, ← hH'_eq b]
    have := hdist a b hab
    omega
  let i₀ : Fin t → ℕ := fun a => i_orig a - 4
  let j₀ : Fin t → ℕ := fun a => j_orig a - 2
  let h₀ : Fin t → ℕ := fun a => (H' a).height + 4
  have hi₀_add : ∀ a, i₀ a + 4 = i_orig a := fun a => by
    have := (hmargin a).2.2.1; dsimp [i₀]; omega
  have hj₀_add : ∀ a, j₀ a + 2 = j_orig a := fun a => by
    have := (hmargin a).1; dsimp [j₀]; omega
  have hh₀ : ∀ a, 6 ≤ h₀ a ∧ Even (h₀ a) := fun a => by
    have h2 := (H' a).two_le_height
    exact ⟨by dsimp [h₀]; omega, (H' a).even_height.add (by decide)⟩
  have hi₀_even : ∀ a, Even (i₀ a) := fun a => by
    rcases hi_orig_even a with ⟨k, hk⟩
    have := (hmargin a).2.2.1
    exact ⟨k - 2, by dsimp [i₀]; omega⟩
  have hj₀_even : ∀ a, Even (j₀ a) := fun a => by
    rcases hj_orig_even a with ⟨k, hk⟩
    have := (hmargin a).1
    exact ⟨k - 1, by dsimp [j₀]; omega⟩
  have hi₀_lo : ∀ a, 4 * M + 6 ≤ i₀ a - 4 * M := fun a => by
    have := (hmargin a).2.2.1; dsimp [i₀]; omega
  have hj₀_lo : ∀ a, M + 1 ≤ j₀ a - 2 * M := fun a => by
    have := (hmargin a).1; dsimp [j₀]; omega
  have hi₀_hi : ∀ a, i₀ a + 2 * h₀ a + 4 * M ≤ 2 * W.height := fun a => by
    have := (hmargin a).2.2.1
    have := (hmargin a).2.2.2
    dsimp [i₀, h₀]; omega
  have hj₀_hi : ∀ a, j₀ a + h₀ a + 2 * M ≤ W.height := fun a => by
    have := (hmargin a).1
    have := (hmargin a).2.1
    dsimp [j₀, h₀]; omega
  have hθ_le : θ ≤ W.height := by
    let a₀ : Fin t := ⟨0, ht_pos⟩
    have := hj₀_lo a₀
    have := hj₀_hi a₀
    omega
  have hj₀_θ : ∀ a, θ + 2 ≤ j₀ a := fun a => by
    have := hj₀_lo a; omega
  have hsep : ∀ a b : Fin t, a ≠ b → ∀ n₁ ≤ M, ∀ n₂ ≤ M,
      Disjoint (fig1Collar (i₀ a) (j₀ a) (h₀ a) n₁)
        (fig1Collar (i₀ b) (j₀ b) (h₀ b) n₂) := by
    intro a b hab n₁ hn₁ n₂ hn₂
    apply disjoint_wallShiftRealHomeomorph_fig1EnclosedSet
    have := (hmargin a).1
    have := (hmargin a).2.2.1
    have := (hmargin b).1
    have := (hmargin b).2.2.1
    rcases hbox_sep a b hab with h | h | h | h
    · exact Or.inl (by dsimp [i₀, h₀]; omega)
    · exact Or.inr (Or.inl (by dsimp [i₀, h₀]; omega))
    · exact Or.inr (Or.inr (Or.inl (by dsimp [j₀, h₀]; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp [j₀, h₀]; omega)))
  have hsep0 : ∀ a b : Fin t, a ≠ b →
      Disjoint (fig1Collar (i₀ a) (j₀ a) (h₀ a) 0) (fig1Collar (i₀ b) (j₀ b) (h₀ b) 0) :=
    fun a b hab => hsep a b hab 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  -- Step 3: Punctured sphere drawing `Γ'`, controlling tangle `T'`, and metric `d`
  let K_a : Fin t → Set (ℝ × ℝ) := fun a => fig1Collar (i₀ a) (j₀ a) (h₀ a) 0
  let D_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => fig1Sph φ '' K_a a
  let Λ : Set (OnePoint EuclideanPlane) := ⋃ a : Fin t, interior (D_a a)
  let Γ' : Drawing (OnePoint EuclideanPlane) := clearedSubdrawing Γ.drawing Λ
  let r_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => interior (D_a a)
  let C_a : Fin t → Drawing (OnePoint EuclideanPlane) := fun a => Γ'.interSet (subBd (r_a a))
  obtain ⟨hD_disc, hD_int, hD_bd, hΓ'U, hr_a, hC_a, hr_inj, hΓ'_2cell⟩ :=
    puncturedWallDrawing_props hΓU hΓe hΓe_cl i₀ j₀ h₀ hh₀ hi₀_even hj₀_even
      (fun a => by have := hi₀_lo a; omega)
      (fun a => by have := hj₀_lo a; omega)
      (fun a => by have := hi₀_hi a; omega)
      (fun a => by have := hj₀_hi a; omega)
      hsep0
  obtain ⟨η', Tstar, T', hNW, hVert_N, hVerts_N, hEdges_N, hCtrl', hrow⟩ :=
    exists_punctured_controlled_tangle hWG₀ hVG₀ hEG₀ hpos_inj hpos_bv hΓv hΓe
      i₀ j₀ h₀ hh₀ hi₀_even hj₀_even
      (fun a => by have := hi₀_lo a; omega)
      (fun a => by have := hi₀_hi a; omega)
      (fun a => by have := hj₀_hi a; omega)
      hD_int hθ_two hθ_even hθ_le hj₀_θ
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSphere : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hresp := GM16.drawing_tangle_isRespectful_of_isSphere hS hSphere Γ' hCtrl'.isTangle_H
  obtain ⟨d, hd⟩ := GM16.exists_tangleMetric hS ⟨hΓ'_2cell, hCtrl'.isTangle_H, hresp⟩
  have hE_ne : Γ'.E.Nonempty := by
    obtain ⟨u, W_c, _, hlen, _, hCE⟩ := (hC_a ⟨0, ht_pos⟩).1
    cases W_c with
    | nil _ => simp at hlen
    | @cons _ _ _ e _ _ =>
      exact ⟨e, (hC_a ⟨0, ht_pos⟩).2.1.2 (hCE.symm ▸ List.mem_cons_self)⟩
  -- Step 4: Eye vertices `pt a idx` and extended crosses `(P_hat a, Q_hat a)`
  have hEye_not_int : ∀ a : Fin t, ∀ idx : Fin 4,
      fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx ∉ ⋃ c : Fin t, interior (K_a c) := by
    intro a idx hpInt
    obtain ⟨c, hpc⟩ := mem_iUnion.mp hpInt
    have hfr := fig1EyeCoord_mem_frontier_zero (i := i₀ a) (j := j₀ a) (h := h₀ a)
      (hh₀ a).1 (hh₀ a).2 idx
    by_cases hca : c = a
    · subst hca
      exact hfr.2 hpc
    · exact Set.disjoint_left.mp (hsep0 a c (Ne.symm hca))
        ((isClosed_fig1Collar _ _ _ _).frontier_subset hfr) (interior_subset hpc)
  have hpa_vert : ∀ a : Fin t, (i₀ a + 1, j₀ a + 2) ∈ elementaryWallVerts W.height :=
    fun a => mem_elementaryWallVerts_of_row_interior
      (by have := hj₀_lo a; omega)
      (by have := hj₀_hi a; have := (hh₀ a).1; omega)
      (by have := hi₀_hi a; have := (hh₀ a).1; omega)
  have hpb_vert : ∀ a : Fin t, (i₀ a + 1, j₀ a + 2 + (H' a).height) ∈ elementaryWallVerts W.height :=
    fun a => mem_elementaryWallVerts_of_row_interior
      (by have := hj₀_lo a; omega)
      (by have := hj₀_hi a; dsimp [h₀] at this; omega)
      (by have := hi₀_hi a; have := (hh₀ a).1; omega)
  have hpc_vert : ∀ a : Fin t, (i₀ a + 2 * h₀ a, j₀ a + 2 + (H' a).height) ∈ elementaryWallVerts W.height :=
    fun a => mem_elementaryWallVerts_of_row_interior
      (by have := hj₀_lo a; omega)
      (by have := hj₀_hi a; dsimp [h₀] at this; omega)
      (by have := hi₀_hi a; omega)
  have hpd_vert : ∀ a : Fin t, (i₀ a + 2 * h₀ a, j₀ a + 2) ∈ elementaryWallVerts W.height :=
    fun a => mem_elementaryWallVerts_of_row_interior
      (by have := hj₀_lo a; omega)
      (by have := hj₀_hi a; have := (hh₀ a).1; omega)
      (by have := hi₀_hi a; omega)
  let v_a : Fin t → α := fun a => W.toWall.branchVertex (i₀ a + 1, j₀ a + 2) (hpa_vert a)
  let v_b : Fin t → α := fun a => W.toWall.branchVertex (i₀ a + 1, j₀ a + 2 + (H' a).height) (hpb_vert a)
  let v_c : Fin t → α := fun a => W.toWall.branchVertex (i₀ a + 2 * h₀ a, j₀ a + 2 + (H' a).height) (hpc_vert a)
  let v_d : Fin t → α := fun a => W.toWall.branchVertex (i₀ a + 2 * h₀ a, j₀ a + 2) (hpd_vert a)
  have hpos_va : ∀ a, pos (v_a a) = fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0 := by
    intro a
    rw [hpos_bv _ (hpa_vert a)]
    rfl
  have hpos_vb : ∀ a, pos (v_b a) = fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 3 := by
    intro a
    rw [hpos_bv _ (hpb_vert a)]
    have hj_eq : j₀ a + 2 + (H' a).height = j₀ a + h₀ a - 2 := by dsimp [h₀]; omega
    rw [hj_eq]
    rfl
  have hpos_vc : ∀ a, pos (v_c a) = fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 2 := by
    intro a
    rw [hpos_bv _ (hpc_vert a)]
    have hj_eq : j₀ a + 2 + (H' a).height = j₀ a + h₀ a - 2 := by dsimp [h₀]; omega
    rw [hj_eq]
    rfl
  have hpos_vd : ∀ a, pos (v_d a) = fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 1 := by
    intro a
    rw [hpos_bv _ (hpd_vert a)]
    rfl
  have hva_N : ∀ a, v_a a ∈ V(η'.imageGraph) ∧
      fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0) ∈ Γ'.V ∧
      η'.vMap (fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0)) = v_a a := by
    intro a
    have h := hVert_N (v_a a) (W.toWall.branchVertex_mem_vertexSet _ (hpa_vert a))
      (by rw [hpos_va a]; exact hEye_not_int a 0)
    rwa [hpos_va a] at h
  have hvb_N : ∀ a, v_b a ∈ V(η'.imageGraph) ∧
      fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 3) ∈ Γ'.V ∧
      η'.vMap (fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 3)) = v_b a := by
    intro a
    have h := hVert_N (v_b a) (W.toWall.branchVertex_mem_vertexSet _ (hpb_vert a))
      (by rw [hpos_vb a]; exact hEye_not_int a 3)
    rwa [hpos_vb a] at h
  have hvc_N : ∀ a, v_c a ∈ V(η'.imageGraph) ∧
      fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 2) ∈ Γ'.V ∧
      η'.vMap (fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 2)) = v_c a := by
    intro a
    have h := hVert_N (v_c a) (W.toWall.branchVertex_mem_vertexSet _ (hpc_vert a))
      (by rw [hpos_vc a]; exact hEye_not_int a 2)
    rwa [hpos_vc a] at h
  have hvd_N : ∀ a, v_d a ∈ V(η'.imageGraph) ∧
      fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 1) ∈ Γ'.V ∧
      η'.vMap (fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 1)) = v_d a := by
    intro a
    have h := hVert_N (v_d a) (W.toWall.branchVertex_mem_vertexSet _ (hpd_vert a))
      (by rw [hpos_vd a]; exact hEye_not_int a 1)
    rwa [hpos_vd a] at h
  have hpt_V : ∀ a : Fin t, ∀ idx : Fin 4,
      fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx) ∈ Γ'.V := by
    intro a idx
    fin_cases idx
    · exact (hva_N a).2.1
    · exact (hvd_N a).2.1
    · exact (hvc_N a).2.1
    · exact (hvb_N a).2.1
  have hex_ext : ∀ a : Fin t, ∃ P_hat Q_hat : Graph α β,
      IsHPathWithEnds G₀ η'.imageGraph P_hat (v_a a) (v_c a) ∧
      IsHPathWithEnds G₀ η'.imageGraph Q_hat (v_b a) (v_d a) ∧
      Disjoint V(P_hat) V(Q_hat) ∧
      (V(P_hat) ∪ V(Q_hat)) \ V(W.graph) ⊆ V(P' a) ∪ V(Q' a) ∧
      (V(P_hat) ∪ V(Q_hat)) ∩ V(W.graph) ⊆
        subwallRegionVerts W.toWall
          {p : ℕ × ℕ | i₀ a + 1 ≤ p.1 ∧ p.1 ≤ i₀ a + 2 * h₀ a ∧
            j₀ a + 2 ≤ p.2 ∧ p.2 ≤ j₀ a + 2 + (H' a).height} := by
    intro a
    have hhi_i : i₀ a + 2 * ((H' a).height + 4) + 1 ≤ 2 * W.height + 1 := by
      have := hi₀_hi a; dsimp [h₀] at this; omega
    have hhi_j : j₀ a + ((H' a).height + 4) < W.height := by
      have := hj₀_hi a; dsimp [h₀] at this; omega
    have hsub_eq : W.toWall.subwallAt (i₀ a + 4) (j₀ a + 2) (H' a).height
        (H' a).two_le_height (H' a).even_height (by omega)
        ((hi₀_even a).add (by decide)) ((hj₀_even a).add (by decide))
        (by omega) (by omega) =
      W.toWall.subwallAt (i_orig a) (j_orig a) (H' a).height
        (H' a).two_le_height (H' a).even_height (hsub a).height_le
        (hi_orig_even a) (hj_orig_even a) (hi_orig_le a) (hj_orig_le a) := by
      congr 1
      · exact hi₀_add a
      · exact hj₀_add a
    have hH'_eq_a : (H' a).graph =
        (W.toWall.subwallAt (i₀ a + 4) (j₀ a + 2) (H' a).height
          (H' a).two_le_height (H' a).even_height (by omega)
          ((hi₀_even a).add (by decide)) ((hj₀_even a).add (by decide))
          (by omega) (by omega)).graph := by
      rw [hsub_eq, hH'_eq a]
    have hcross_a : IsCrossOverWall G₀
        (W.toWall.subwallAt (i₀ a + 4) (j₀ a + 2) (H' a).height
          (H' a).two_le_height (H' a).even_height (by omega)
          ((hi₀_even a).add (by decide)) ((hj₀_even a).add (by decide))
          (by omega) (by omega))
        (P' a) (Q' a) := by
      rw [hsub_eq]
      exact hcross_sub a
    exact exists_extended_cross_hPaths hWG₀ hNW
      (H' a).two_le_height (H' a).even_height (hi₀_even a) (hj₀_even a)
      (by have := hi₀_lo a; omega) (by have := hj₀_lo a; omega)
      hhi_i hhi_j hH'_eq_a hcross_a (hinter a)
      (hva_N a).1 (hvb_N a).1 (hvc_N a).1 (hvd_N a).1
      (hVerts_N a) (hEdges_N a)
  choose P_hat Q_hat hP_hat hQ_hat hPQ_hat_disj hPQ_hat_out hPQ_hat_in using hex_ext
  -- Step 5: Pairwise disjointness of `V(P_hat a) ∪ V(Q_hat a)` for `a ≠ b`
  have hPQ_ext_disj : ∀ a b : Fin t, a ≠ b →
      Disjoint (V(P_hat a) ∪ V(Q_hat a)) (V(P_hat b) ∪ V(Q_hat b)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro z hza hzb
    by_cases hzW : z ∈ V(W.graph)
    · have hza_box := hPQ_hat_in a ⟨hza, hzW⟩
      have hzb_box := hPQ_hat_in b ⟨hzb, hzW⟩
      let Box : Fin t → Set (ℕ × ℕ) := fun c =>
        {p : ℕ × ℕ | i₀ c + 1 ≤ p.1 ∧ p.1 ≤ i₀ c + 2 * h₀ c ∧
          j₀ c + 2 ≤ p.2 ∧ p.2 ≤ j₀ c + 2 + (H' c).height}
      have hBox_disj : Box a ∩ Box b = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro p hp
        have ha1 := hp.1.1
        have ha2 := hp.1.2.1
        have ha3 := hp.1.2.2.1
        have ha4 := hp.1.2.2.2
        have hb1 := hp.2.1
        have hb2 := hp.2.2.1
        have hb3 := hp.2.2.2.1
        have hb4 := hp.2.2.2.2
        have := (hmargin a).1
        have := (hmargin a).2.2.1
        have := (hmargin b).1
        have := (hmargin b).2.2.1
        rcases hbox_sep a b hab with h | h | h | h <;>
        · dsimp [i₀, j₀, h₀] at *; omega
      have h_inter := subwallRegionVerts_inter_subset (W := W.toWall) (S₁ := Box a) (S₂ := Box b)
        (fun p q _ ⟨hp, _⟩ => by rw [hBox_disj] at hp; exact hp) ⟨hza_box, hzb_box⟩
      obtain ⟨p, hp, -, -⟩ := h_inter
      rw [hBox_disj] at hp
      exact hp
    · exact Set.disjoint_left.mp (hdisj hab) (hPQ_hat_out a ⟨hza, hzW⟩) (hPQ_hat_out b ⟨hzb, hzW⟩)
  -- Step 6: `IsEyeWithPaths G₀ Γ' η' θ T' (r_a a) (P_hat a) (Q_hat a)` for all `a : Fin t`
  have hEye : ∀ a : Fin t, GM15.IsEyeWithPaths G₀ Γ' η' θ T' (r_a a) (P_hat a) (Q_hat a) := by
    intro a
    let pt : Fin 4 → OnePoint EuclideanPlane :=
      fun idx => fig1Sph φ (fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx)
    have hpt_C : ∀ idx : Fin 4, pt idx ∈ (C_a a).V := by
      intro idx
      refine GM11.mem_interSet_V (hpt_V a idx) ?_
      rw [(hr_a a).2]
      exact ⟨_, fig1EyeCoord_mem_frontier_zero (i := i₀ a) (j := j₀ a) (h := h₀ a)
        (hh₀ a).1 (hh₀ a).2 idx, rfl⟩
    have hOrd := pairsCrossOn_eye_circuit (hh₀ a).1 (hh₀ a).2 ((hC_a a).2.2.trans (hr_a a).2)
    have hFree0 := eye_four_points_isFreeSet W.toWall.two_le_height W.toWall.even_height
      φ i₀ j₀ h₀ hh₀ hi₀_even hj₀_even hi₀_lo hj₀_lo hi₀_hi hj₀_hi hsep
      hM_31 hθ_four hΓ'U hCtrl'.isTangle_H hrow (a := a) (hpt_V a)
    have hSet_eq : ({pt 0, pt 3, pt 2, pt 1} : Set (OnePoint EuclideanPlane)) =
        {pt 0, pt 1, pt 2, pt 3} := by
      ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    have hFree : GM10.IsFreeSet Γ'.toHypergraph T' θ {pt 0, pt 3, pt 2, pt 1} := by
      rwa [hSet_eq]
    refine ⟨(hr_a a).1, C_a a, pt 0, pt 3, pt 2, pt 1,
      (hC_a a).1, (hC_a a).2.1, (hC_a a).2.2,
      hpt_C 0, hpt_C 3, hpt_C 2, hpt_C 1,
      hOrd.1, hOrd.2, hFree, hPQ_hat_disj a, ?_, ?_⟩
    · rw [(hva_N a).2.2, (hvc_N a).2.2]
      exact hP_hat a
    · rw [(hvb_N a).2.2, (hvd_N a).2.2]
      exact hQ_hat a
  -- Step 7: Apply `h45` (XII (4.5)) to the first `k₀` eyes
  let emb₀ : Fin k₀ ↪ Fin t := Fin.castLEEmb hk₀_le
  have hcm := h45 G₀ θ θ Tstar Γ' η' T' d hCtrl' hd (by omega)
    (fun i => r_a (emb₀ i)) (fun i => P_hat (emb₀ i)) (fun i => Q_hat (emb₀ i))
    (hr_inj.comp emb₀.injective)
    (fun i => hEye (emb₀ i))
    (fun i j hij => eye_region_dist_ge W.toWall.two_le_height W.toWall.even_height
      φ i₀ j₀ h₀ hh₀ hi₀_even hj₀_even hi₀_lo hj₀_lo hi₀_hi hj₀_hi hsep
      hN₀_pos (by omega) hM_3N₀ hΓ'U hE_ne hrow hd hr_a
      (fun c => hpt_V c 0) (emb₀.injective.ne hij))
    (fun i j hij => hPQ_ext_disj (emb₀ i) (emb₀ j) (emb₀.injective.ne hij))
  exact (hasGraphModel_of_controlsMinor (GM16.controlsMinor_of_gm12 hcm)).mono hG₀G

end GraphMinor.GM13






