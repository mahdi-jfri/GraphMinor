module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM17.Bridge
public import GraphMinor.GM17.Section6
import GraphMinor.GM17.Section8Proved
import GraphMinor.Surface.DiscArcs
import GraphMinor.GM17.PasteCuff
import GraphMinor.GM17.ArcDisc
import GraphMinor.GM17.MarkCross
import GraphMinor.GM17.ReplaceDisc
import GraphMinor.GM17.RegionDisc
import GraphMinor.GM17.CutArcPaint
import GraphMinor.GM17.PushNode
import GraphMinor.GM17.RegionBoundary
import GraphMinor.GM17.IndentMain

import GraphMinor.GM17.Section6Proved

import GraphMinor.GM17.Section9bProved

/-!
# Graph Minors XXI, Section 9: Portrait Definitions and Bridge from True Portrayals

This file defines the Section 9 portrait structures of Robertson and Seymour,
*Graph Minors. XXI. Graphs with unique linkages*, J. Combin. Theory Ser. B 99 (2009), 583–616
(pages 37–38 of the preprint), and proves that every true redundant portrayal of
Graph Minors XVII yields a Section 9 portrait (`exists_portrait_of_true_portrayal`).
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Topology Metric Classical
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.GM17
open GraphMinor.Hypergraph

universe u v

local notation "𝕀" => unitInterval

/-! ## 1. Disc Drawability and Portrait Definitions (Section 9, pages 37–38 of the preprint) -/

/-- A hypergraph `H` is an indexed path between `x` and `y` if its vertex set is the range of an
injective sequence `v₀, v₁, ..., vₘ` (`m ≥ 1`) with `v₀ = x`, `vₘ = y`, and two vertices are
adjacent in `H.skeleton` if and only if they are consecutive in the sequence. -/
def IsIndexedPath {α : Type u} {β : Type v} (H : Hypergraph α β) (x y : α) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (v : Fin (m + 1) → α),
    Function.Injective v ∧
    v 0 = x ∧
    v ⟨m, Nat.lt_succ_self m⟩ = y ∧
    H.vertexSet = Set.range v ∧
    ∀ i j : Fin (m + 1), H.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

/-- Reversing an `IsIndexedPath H x₁ x₂` gives `IsIndexedPath H x₂ x₁`. -/
theorem IsIndexedPath.symm {α : Type u} {β : Type v} {H : Hypergraph α β} {x₁ x₂ : α}
    (h : IsIndexedPath H x₁ x₂) : IsIndexedPath H x₂ x₁ := by
  rcases h with ⟨m, hm, v, hv_inj, hv0, hvm, hV, hadj⟩
  let rev : Fin (m + 1) → Fin (m + 1) := fun i => ⟨m - i.1, by omega⟩
  have hrev_inv : ∀ i : Fin (m + 1), rev (rev i) = i := fun i => Fin.ext (by dsimp [rev]; omega)
  have hrev_inj : Function.Injective rev := Function.LeftInverse.injective hrev_inv
  refine ⟨m, hm, v ∘ rev, hv_inj.comp hrev_inj, ?_, ?_, ?_, ?_⟩
  · simpa [rev] using hvm
  · have h0 : rev ⟨m, Nat.lt_succ_self m⟩ = 0 := Fin.ext (by dsimp [rev]; omega)
    simpa [Function.comp, h0] using hv0
  · rw [hV]
    ext w
    simp only [mem_range, Function.comp_apply]
    exact ⟨fun ⟨i, hi⟩ => ⟨rev i, by rwa [hrev_inv]⟩, fun ⟨i, hi⟩ => ⟨rev i, hi⟩⟩
  · intro i j
    simp only [Function.comp_apply, hadj (rev i) (rev j), rev]
    omega

/-- Graph Minors XXI, Section 9, (R9) and (9.1) (page 38 of the preprint):
A cell subgraph `H = α(c)` can be drawn in the closed disc `closure c` with `X = ιN '' tilde c`
in the boundary of the disc. As established in the proof of (9.1) (page 38 of the preprint:
"If $V(\alpha(c)) = \tilde{c}$ this is clear ... Hence either $\alpha(c)$ is a path with both ends
in $\tilde{c}$, or $\alpha(c) \setminus v$ is a path with both ends in $\tilde{c}$, for some
$v \in \tilde{c}$. In either case $\alpha(c)$ can be drawn in a disc with all the members of
$\tilde{c}$ drawn in the boundary"), this holds when either `V(H) = X`, `H` is an indexed path
between two distinct vertices of `X`, or `H \ {v}` is an indexed path between two distinct vertices
of `X \ {v}` for some `v ∈ X`. -/
def CanBeDrawnInDisc21 {α : Type u} {β : Type v}
    (H : Hypergraph α β) (X : Set α) : Prop :=
  H.vertexSet = X ∨
  (X ⊆ H.vertexSet ∧ ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ x₂ ∧ IsIndexedPath H x₁ x₂) ∨
  (X ⊆ H.vertexSet ∧ ∃ v ∈ X, ∃ x₁ ∈ X \ {v}, ∃ x₂ ∈ X \ {v},
    x₁ ≠ x₂ ∧ IsIndexedPath (H.deleteVertices {v}) x₁ x₂)

/-- Graph Minors XXI, Section 9 (pages 37–38 of the preprint):
Portrait `(Γ, α)` of `G` in a surface `S`, with `CanBeDrawnInDisc21` in (R9). -/
structure IsPortrait21 {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : GM17.Painting S) (ιN : S → α)
    (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β)
    (q_cuff : Set S → ℕ) : Prop where
  is_surface : IsSurface S
  is_connected_surface : ConnectedSpace S
  -- (R1)
  r1_painting : IsPainting21 Γ
  r1_injOn : InjOn ιN Γ.N
  r1_subset : ιN '' Γ.N ⊆ G.vertexSet
  -- (R2)
  r2_cell_le : ∀ c ∈ Γ.C, α_cell c ≤ G
  r2_cell_inter : ∀ c ∈ Γ.C, (α_cell c).vertexSet ∩ (ιN '' Γ.N) = ιN '' (tilde c)
  -- (R3)
  r3_union_V : G.vertexSet = ⋃ c ∈ Γ.C, (α_cell c).vertexSet
  r3_union_E : G.edgeSet = ⋃ c ∈ Γ.C, (α_cell c).edgeSet
  r3_edge_disjoint : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ →
    Disjoint (α_cell c₁).edgeSet (α_cell c₂).edgeSet
  -- (R4)
  r4_vert : ∀ v ∈ Γ.N ∩ bd S,
    α_vert v ≤ G ∧
    (α_vert v).edgeSet = ∅ ∧
    (α_vert v).vertexSet ∩ (ιN '' Γ.N) = {ιN v}
  -- (R5)
  r5_cuff_pos : ∀ C ∈ cuffs S, 1 ≤ q_cuff C
  r5_cuff_card : ∀ C ∈ cuffs S, ∀ v ∈ Γ.N ∩ C, (α_vert v).vertexSet.ncard = q_cuff C
  -- (R6)
  r6_border : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty →
    ∀ u v : S, u ≠ v → tilde c = {u, v} →
      α_vert u ≤ α_cell c ∧
      α_vert v ≤ α_cell c ∧
      (HasDisjointPaths (α_cell c).skeleton (α_vert u).vertexSet (α_vert v).vertexSet
          (α_vert u).vertexSet.ncard ∨
       ∃ c' ∈ Γ.C, (tilde c').ncard = 3 ∧ u ∈ tilde c' ∧ v ∈ tilde c')
  -- (R7)
  r7_inter : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ →
    (∀ C ∈ cuffs S, ¬ ((c₁ ∩ C).Nonempty ∧ (c₂ ∩ C).Nonempty)) →
    (α_cell c₁ ∩ α_cell c₂).vertexSet = ιN '' (tilde c₁ ∩ tilde c₂)
  -- (R8)
  r8_order : ∀ C ∈ cuffs S, ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C,
    (c₁ ∩ C).Nonempty → (c₂ ∩ C).Nonempty →
    ∀ u₁ ∈ Γ.N ∩ C, ∀ u₂ ∈ Γ.N ∩ C,
      InCuffOrder C c₁ u₁ c₂ u₂ →
      α_cell c₁ ∩ α_cell c₂ ≤ α_vert u₁ ∪ α_vert u₂
  -- (R9)
  r9_three : ∀ c ∈ Γ.C, (tilde c).ncard = 3 →
    ¬ CanBeDrawnInDisc21 (α_cell c) (ιN '' (tilde c))
  -- (R10)
  r10_null : ∀ C ∈ cuffs S, (⋂ u ∈ Γ.N ∩ C, (α_vert u).vertexSet) = ∅

/-- A portrait has depth `≤ q` if `q_cuff C ≤ q` for every cuff `C ∈ cuffs S`. -/
def PortraitHasDepthLe21 {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : GM17.Painting S) (ιN : S → α)
    (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β) (q : ℕ) : Prop :=
  ∃ q_cuff : Set S → ℕ,
    IsPortrait21 G Γ ιN α_cell α_vert q_cuff ∧
    ∀ C ∈ cuffs S, q_cuff C ≤ q

/-- A portrait surrounds a tangle `𝒯` if `α_cell c` is small for each `c ∈ Γ.C`. -/
def PortraitSurroundsTangle21 {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (Γ : GM17.Painting S) (α_cell : Set S → Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ c ∈ Γ.C, IsSmallSubgraph 𝒯 (α_cell c)

/-! ## 2. Disc-Splitting Infrastructure for 3-Ended Internal Cells -/

private theorem norm_convex_combo_eq {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (u : ℝ) :
    ‖(1 - (u : ℂ)) * z + (u : ℂ) * w‖ ^ 2 + u * (1 - u) * ‖z - w‖ ^ 2 = 1 := by
  have h1 : ∀ a : ℂ, ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := fun a => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by rw [← h1 z, hz, one_pow]
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by rw [← h1 w, hw, one_pow]
  rw [h1, h1]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (1 - u) * hz2 + u * hw2

theorem exists_chord_in_closedDisc {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {s t : S} (hs : s ∈ discBd D) (ht : t ∈ discBd D)
    (hst : s ≠ t) :
    ∃ F : Set S, F ⊆ D ∧ IsLineWithEnds F s t ∧ F ∩ discBd D = {s, t} ∧
      IsConnected (F \ {t}) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hs_D : s ∈ D := discBd_subset D hs
  have ht_D : t ∈ D := discBd_subset D ht
  have hzs : h s ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h hs
  have hzt : h t ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h ht
  have hzs_norm : ‖h s‖ = 1 := mem_sphere_zero_iff_norm.mp hzs
  have hzt_norm : ‖h t‖ = 1 := mem_sphere_zero_iff_norm.mp hzt
  have hz_ne : h s ≠ h t := fun hEq => hst (c.gh.injOn hs_D ht_D hEq)
  let ℓ : 𝕀 → ℂ := fun u => (1 - (u : ℝ) : ℂ) * h s + (u : ℝ) * h t
  have hℓ_cont : Continuous ℓ :=
    ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)).mul
      continuous_const).add
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
  have hℓ_ball : ∀ u : 𝕀, ℓ u ∈ closedBall (0 : ℂ) 1 := fun u => by
    rw [mem_closedBall_zero_iff]
    have hid := norm_convex_combo_eq hzs_norm hzt_norm (u : ℝ)
    have hnonneg : 0 ≤ (u : ℝ) * (1 - (u : ℝ)) * ‖h s - h t‖ ^ 2 :=
      mul_nonneg (mul_nonneg u.2.1 (sub_nonneg.mpr u.2.2)) (sq_nonneg _)
    have hsq : ‖ℓ u‖ ^ 2 ≤ 1 ^ 2 := by dsimp [ℓ]; linarith
    exact (abs_le_of_sq_le_sq' hsq zero_le_one).2
  have hℓ_sphere : ∀ u : 𝕀, ℓ u ∈ sphere (0 : ℂ) 1 → u = 0 ∨ u = 1 := fun u hu => by
    have hn : ‖ℓ u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hid := norm_convex_combo_eq hzs_norm hzt_norm (u : ℝ)
    change ‖ℓ u‖ ^ 2 + (u : ℝ) * (1 - (u : ℝ)) * ‖h s - h t‖ ^ 2 = 1 at hid
    rw [hn, one_pow] at hid
    have hdiff_ne : ‖h s - h t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz_ne)
    have hmul : (u : ℝ) * (1 - (u : ℝ)) = 0 := by
      have h0 : (u : ℝ) * (1 - (u : ℝ)) * ‖h s - h t‖ ^ 2 = 0 := by linarith
      exact (mul_eq_zero.mp h0).resolve_right (pow_ne_zero 2 hdiff_ne)
    rcases mul_eq_zero.mp hmul with hu0 | hu1
    · exact Or.inl (Subtype.ext hu0)
    · have h1 : (u : ℝ) = 1 := by linarith
      exact Or.inr (Subtype.ext h1)
  have hℓ_inj : Function.Injective ℓ := fun u₁ u₂ hEq => by
    have hsub : ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) * (h t - h s) = 0 := by
      calc ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) * (h t - h s)
        _ = ℓ u₁ - ℓ u₂ := by dsimp [ℓ]; ring
        _ = 0 := sub_eq_zero.mpr hEq
    have hdiff : h t - h s ≠ 0 := sub_ne_zero.mpr hz_ne.symm
    have hu : ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) = 0 := (mul_eq_zero.mp hsub).resolve_right hdiff
    have hu' : (u₁ : ℝ) - (u₂ : ℝ) = 0 := Complex.ofReal_eq_zero.mp (by simpa using hu)
    exact Subtype.ext (sub_eq_zero.mp hu')
  let φ : 𝕀 → S := fun u => g (ℓ u)
  have hφ_cont : Continuous φ := c.gc.comp_continuous hℓ_cont hℓ_ball
  have hφ_inj : Function.Injective φ := fun u₁ u₂ hEq =>
    hℓ_inj (c.injOn (hℓ_ball u₁) (hℓ_ball u₂) hEq)
  have hφ0 : φ 0 = s := by
    show g (ℓ 0) = s
    simp only [ℓ, Icc.coe_zero, Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact c.gh hs_D
  have hφ1 : φ 1 = t := by
    show g (ℓ 1) = t
    simp only [ℓ, Icc.coe_one, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add]
    exact c.gh ht_D
  set F := range φ
  have hF_sub : F ⊆ D := by
    rintro _ ⟨u, rfl⟩
    exact c.gm (hℓ_ball u)
  let ev : 𝕀 ≃ₜ F :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective φ hφ_inj)
      hφ_cont.rangeFactorization
  have hF_line : IsLineWithEnds F s t := ⟨ev, hφ0, hφ1⟩
  have hF_bd : F ∩ discBd D = {s, t} := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨u, rfl⟩, hbd⟩
      have hlu_sphere : ℓ u ∈ sphere (0 : ℂ) 1 := by
        rw [← c.bd, ← c.hg (hℓ_ball u)]
        exact mem_image_of_mem h hbd
      rcases hℓ_sphere u hlu_sphere with rfl | rfl
      · exact Or.inl hφ0
      · exact Or.inr hφ1
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, hφ0⟩, hs⟩
      · exact ⟨⟨1, hφ1⟩, ht⟩
  have hF_conn : IsConnected (F \ {t}) := by
    have hEq : F \ {t} = φ '' {u : 𝕀 | (u : ℝ) < 1} := by
      ext x
      simp only [F, mem_sdiff, mem_range, mem_singleton_iff, mem_image, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨u, rfl⟩, hne⟩
        have hu1 : u ≠ 1 := fun h => hne (h ▸ hφ1)
        exact ⟨u, lt_of_le_of_ne u.2.2 (Subtype.ext_iff.not.mp hu1), rfl⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨u, rfl⟩, fun hEq => ?_⟩
        have hu1 : u = 1 := hφ_inj (hEq.trans hφ1.symm)
        exact hu.ne (congrArg Subtype.val hu1)
    rw [hEq]
    have hpre : IsConnected {u : 𝕀 | (u : ℝ) < 1} := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      exact isPreconnected_iff_preconnectedSpace.mpr (Subtype.preconnectedSpace (by
        have hconv : Convex ℝ (Ico (0 : ℝ) 1) := convex_Ico 0 1
        have hEq2 : {u : 𝕀 | (u : ℝ) < 1} = Subtype.val ⁻¹' Ico (0 : ℝ) 1 := by
          ext u; simp [u.2.1]
        rw [hEq2]
        exact (IsInducing.subtypeVal.isPreconnected_image.mp (by
          rw [Subtype.image_preimage_coe]
          have hinter : (Icc (0 : ℝ) 1) ∩ Ico 0 1 = Ico 0 1 :=
            inter_eq_right.mpr Ico_subset_Icc_self
          rw [hinter]
          exact hconv.isPreconnected))))
    exact hpre.image φ hφ_cont.continuousOn
  exact ⟨F, hF_sub, hF_line, hF_bd, hF_conn⟩

private theorem exists_two_discs_touching_at_point {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {n₁ n₂ n₃ : S}
    (hn₁ : n₁ ∈ discBd D) (hn₂ : n₂ ∈ discBd D) (hn₃ : n₃ ∈ discBd D)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ D ∧ Δ₂ ⊆ D ∧
      n₁ ∈ Δ₁ ∧ n₃ ∈ Δ₁ ∧ n₂ ∉ Δ₁ ∧
      n₂ ∈ Δ₂ ∧ n₃ ∈ Δ₂ ∧ n₁ ∉ Δ₂ ∧
      Δ₁ ∩ Δ₂ = {n₃} := by
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, hF₁_conn⟩ :=
    exists_chord_in_closedDisc hD hn₁ hn₃ h13
  obtain ⟨A₁, A₂, E₁, E₂, -, -, hE₁_disc, hE₂_disc, hE_union, hE_inter, hE₁_bd, hE₂_bd, -⟩ :=
    disc_iArc D F₁ n₁ n₃ hD hF₁_sub h13 hF₁_line hF₁_bd
  have hn₁_F₁ : n₁ ∈ F₁ := by
    have : n₁ ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₁ : n₃ ∈ F₁ := by
    have : n₃ ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hn₂_not_F₁ : n₂ ∉ F₁ := by
    intro hmem
    have : n₂ ∈ F₁ ∩ discBd D := ⟨hmem, hn₂⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact h12 hEq.symm
    · exact h23 hEq
  have hn₂_D : n₂ ∈ E₁ ∪ E₂ := hE_union.symm ▸ discBd_subset D hn₂
  have hhalf : ∃ Δ₁ D' : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc D' ∧
      Δ₁ ⊆ D ∧ D' ⊆ D ∧ Δ₁ ∩ D' = F₁ ∧ F₁ ⊆ Δ₁ ∧ F₁ ⊆ discBd D' ∧
      n₂ ∉ Δ₁ ∧ n₂ ∈ discBd D' := by
    rcases hn₂_D with hn₂_E₁ | hn₂_E₂
    · have hn₂_not_E₂ : n₂ ∉ E₂ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨hn₂_E₁, h⟩)
      have hE₁_sub : E₁ ⊆ D := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ D := hE_union ▸ subset_union_right
      refine ⟨E₂, E₁, hE₂_disc, hE₁_disc, hE₂_sub, hE₁_sub, ?_, ?_, ?_, hn₂_not_E₂, ?_⟩
      · rw [Set.inter_comm, hE_inter]
      · rw [← hE_inter]; exact inter_subset_right
      · rw [hE₁_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₁_disc hE₁_sub ⟨hn₂_E₁, hn₂⟩
    · have hn₂_not_E₁ : n₂ ∉ E₁ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨h, hn₂_E₂⟩)
      have hE₁_sub : E₁ ⊆ D := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ D := hE_union ▸ subset_union_right
      refine ⟨E₁, E₂, hE₁_disc, hE₂_disc, hE₁_sub, hE₂_sub, hE_inter, ?_, ?_, hn₂_not_E₁, ?_⟩
      · rw [← hE_inter]; exact inter_subset_left
      · rw [hE₂_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₂_disc hE₂_sub ⟨hn₂_E₂, hn₂⟩
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub, hΔ₁D'_inter, hF₁_Δ₁,
    hF₁_bdD', hn₂_not_Δ₁, hn₂_bdD'⟩ := hhalf
  have hn₃_bdD' : n₃ ∈ discBd D' := hF₁_bdD' hn₃_F₁
  obtain ⟨F₂, hF₂_sub, hF₂_line, hF₂_bd, -⟩ :=
    exists_chord_in_closedDisc hD'_disc hn₂_bdD' hn₃_bdD' h23
  obtain ⟨B₁, B₂, G₁, G₂, hB_ne, hB_comp, hG₁_disc, hG₂_disc, hG_union, hG_inter,
    hG₁_bd, hG₂_bd, -⟩ :=
    disc_iArc D' F₂ n₂ n₃ hD'_disc hF₂_sub h23 hF₂_line hF₂_bd
  have hn₂_F₂ : n₂ ∈ F₂ := by
    have : n₂ ∈ F₂ ∩ discBd D' := by rw [hF₂_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₂ : n₃ ∈ F₂ := by
    have : n₃ ∈ F₂ ∩ discBd D' := by rw [hF₂_bd]; exact Or.inr rfl
    exact this.1
  have hF₁_sub_bdD' : F₁ \ {n₃} ⊆ discBd D' \ {n₂, n₃} := by
    rintro x ⟨hxF₁, hxn₃⟩
    refine ⟨hF₁_bdD' hxF₁, ?_⟩
    rintro (rfl | rfl)
    · exact hn₂_not_F₁ hxF₁
    · exact hxn₃ rfl
  have hn₁_mem_diff : n₁ ∈ discBd D' \ {n₂, n₃} := hF₁_sub_bdD' ⟨hn₁_F₁, h13⟩
  have hcomp_mem : connectedComponentIn (discBd D' \ {n₂, n₃}) n₁ ∈ ({B₁, B₂} : Set (Set S)) := by
    rw [← hB_comp]
    exact ⟨n₁, hn₁_mem_diff, rfl⟩
  have hF₁_in_comp : F₁ \ {n₃} ⊆ connectedComponentIn (discBd D' \ {n₂, n₃}) n₁ :=
    hF₁_conn.isPreconnected.subset_connectedComponentIn ⟨hn₁_F₁, h13⟩ hF₁_sub_bdD'
  have hB₁_mem : B₁ ∈ componentsIn (discBd D' \ {n₂, n₃}) := by rw [hB_comp]; exact Or.inl rfl
  have hB₂_mem : B₂ ∈ componentsIn (discBd D' \ {n₂, n₃}) := by rw [hB_comp]; exact Or.inr rfl
  have hB_disj : Disjoint B₁ B₂ := by
    rcases hB₁_mem with ⟨x₁, hx₁, rfl⟩
    rcases hB₂_mem with ⟨x₂, hx₂, rfl⟩
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hB_ne ?_
    rw [connectedComponentIn_eq hz₁, connectedComponentIn_eq hz₂]
  have hchoose_G : ∃ B Δ₂ : Set S, IsClosedDisc Δ₂ ∧ Δ₂ ⊆ D' ∧ F₂ ⊆ Δ₂ ∧
      discBd Δ₂ = B ∪ F₂ ∧ Disjoint B (F₁ \ {n₃}) := by
    rcases hcomp_mem with hEq | hEq
    · refine ⟨B₂, G₂, hG₂_disc, hG_union ▸ subset_union_right, ?_, hG₂_bd, ?_⟩
      · rw [← hG_inter]; exact inter_subset_right
      · exact hB_disj.symm.mono_right (hEq ▸ hF₁_in_comp)
    · have hEq' : connectedComponentIn (discBd D' \ {n₂, n₃}) n₁ = B₂ := hEq
      refine ⟨B₁, G₁, hG₁_disc, hG_union ▸ subset_union_left, ?_, hG₁_bd, ?_⟩
      · rw [← hG_inter]; exact inter_subset_left
      · exact hB_disj.mono_right (hEq' ▸ hF₁_in_comp)
  obtain ⟨B, Δ₂, hΔ₂_disc, hΔ₂_sub', hF₂_Δ₂, hΔ₂_bd, hB_disj_F₁⟩ := hchoose_G
  have hΔ₂_sub : Δ₂ ⊆ D := hΔ₂_sub'.trans hD'_sub
  have hinter : Δ₁ ∩ Δ₂ = {n₃} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₁, hx₂⟩
      have hxF₁ : x ∈ F₁ := by
        rw [← hΔ₁D'_inter]
        exact ⟨hx₁, hΔ₂_sub' hx₂⟩
      by_cases hxn₃ : x = n₃
      · exact hxn₃
      · exfalso
        have hx_bdΔ₂ : x ∈ discBd Δ₂ :=
          disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hx₂, hF₁_bdD' hxF₁⟩
        rw [hΔ₂_bd] at hx_bdΔ₂
        rcases hx_bdΔ₂ with hxB | hxF₂
        · exact Set.disjoint_left.mp hB_disj_F₁ hxB ⟨hxF₁, hxn₃⟩
        · have hx_bd : x ∈ F₂ ∩ discBd D' := ⟨hxF₂, hF₁_bdD' hxF₁⟩
          rw [hF₂_bd] at hx_bd
          rcases hx_bd with rfl | rfl
          · exact hn₂_not_F₁ hxF₁
          · exact hxn₃ rfl
    · rintro x rfl
      exact ⟨hF₁_Δ₁ hn₃_F₁, hF₂_Δ₂ hn₃_F₂⟩
  have hn₁_not_Δ₂ : n₁ ∉ Δ₂ := by
    intro h
    have : n₁ ∈ Δ₁ ∩ Δ₂ := ⟨hF₁_Δ₁ hn₁_F₁, h⟩
    rw [hinter] at this
    exact h13 this
  exact ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
    hF₁_Δ₁ hn₁_F₁, hF₁_Δ₁ hn₃_F₁, hn₂_not_Δ₁,
    hF₂_Δ₂ hn₂_F₂, hF₂_Δ₂ hn₃_F₂, hn₁_not_Δ₂, hinter⟩

private theorem exists_subdisc_inter_discBd_eq_pair {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {s t : S}
    (hs : s ∈ discBd D) (ht : t ∈ discBd D) (hst : s ≠ t) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ D ∧ s ∈ Δ ∧ t ∈ Δ ∧ Δ ∩ discBd D = {s, t} := by
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, _⟩ :=
    exists_chord_in_closedDisc hD hs ht hst
  obtain ⟨B₁, B₂, G₁, G₂, _, hB_comp, hG₁_disc, _, hG_union, hG_inter, hG₁_bd, _, _⟩ :=
    disc_iArc D F₁ s t hD hF₁_sub hst hF₁_line hF₁_bd
  have hG₁_sub : G₁ ⊆ D := hG_union ▸ subset_union_left
  have hF₁_G₁ : F₁ ⊆ G₁ := hG_inter ▸ inter_subset_left
  have hs_F₁ : s ∈ F₁ := by
    have : s ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have ht_F₁ : t ∈ F₁ := by
    have : t ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hs_bdG₁ : s ∈ discBd G₁ := hG₁_bd ▸ Or.inr hs_F₁
  have ht_bdG₁ : t ∈ discBd G₁ := hG₁_bd ▸ Or.inr ht_F₁
  have hB₁_mem : B₁ ∈ componentsIn (discBd D \ {s, t}) := by rw [hB_comp]; exact Or.inl rfl
  rcases hB₁_mem with ⟨x₁, hx₁_diff, hB₁_eq⟩
  have hB₁_sub_diff : B₁ ⊆ discBd G₁ \ {s, t} := by
    intro x hxB₁
    have hx_bdD : x ∈ discBd D \ {s, t} := by
      rw [← hB₁_eq] at hxB₁
      exact connectedComponentIn_subset (discBd D \ {s, t}) x₁ hxB₁
    exact ⟨hG₁_bd ▸ Or.inl hxB₁, hx_bdD.2⟩
  have hx₁_B₁ : x₁ ∈ B₁ := hB₁_eq ▸ mem_connectedComponentIn hx₁_diff
  have hB₁_preconn : IsPreconnected B₁ := hB₁_eq ▸ isPreconnected_connectedComponentIn
  obtain ⟨F₂, hF₂_sub, hF₂_line, hF₂_bd, _⟩ :=
    exists_chord_in_closedDisc hG₁_disc hs_bdG₁ ht_bdG₁ hst
  obtain ⟨C₁, C₂, H₁, H₂, hC_ne, hC_comp, hH₁_disc, hH₂_disc, hH_union, hH_inter,
    hH₁_bd, hH₂_bd, _⟩ :=
    disc_iArc G₁ F₂ s t hG₁_disc hF₂_sub hst hF₂_line hF₂_bd
  have hs_F₂ : s ∈ F₂ := by
    have : s ∈ F₂ ∩ discBd G₁ := by rw [hF₂_bd]; exact Or.inl rfl
    exact this.1
  have ht_F₂ : t ∈ F₂ := by
    have : t ∈ F₂ ∩ discBd G₁ := by rw [hF₂_bd]; exact Or.inr rfl
    exact this.1
  have hx₁_diffG₁ : x₁ ∈ discBd G₁ \ {s, t} := hB₁_sub_diff hx₁_B₁
  have hcomp_mem : connectedComponentIn (discBd G₁ \ {s, t}) x₁ ∈ ({C₁, C₂} : Set (Set S)) := by
    rw [← hC_comp]
    exact ⟨x₁, hx₁_diffG₁, rfl⟩
  have hB₁_in_comp : B₁ ⊆ connectedComponentIn (discBd G₁ \ {s, t}) x₁ :=
    hB₁_preconn.subset_connectedComponentIn hx₁_B₁ hB₁_sub_diff
  have hC₁_mem : C₁ ∈ componentsIn (discBd G₁ \ {s, t}) := by rw [hC_comp]; exact Or.inl rfl
  have hC₂_mem : C₂ ∈ componentsIn (discBd G₁ \ {s, t}) := by rw [hC_comp]; exact Or.inr rfl
  have hC_disj : Disjoint C₁ C₂ := by
    rcases hC₁_mem with ⟨y₁, hy₁, rfl⟩
    rcases hC₂_mem with ⟨y₂, hy₂, rfl⟩
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hC_ne ?_
    rw [connectedComponentIn_eq hz₁, connectedComponentIn_eq hz₂]
  have hchoose_H : ∃ C Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ G₁ ∧ F₂ ⊆ Δ ∧
      discBd Δ = C ∪ F₂ ∧ Disjoint C B₁ := by
    rcases hcomp_mem with hEq | hEq
    · refine ⟨C₂, H₂, hH₂_disc, hH_union ▸ subset_union_right, ?_, hH₂_bd, ?_⟩
      · rw [← hH_inter]; exact inter_subset_right
      · exact hC_disj.symm.mono_right (hEq ▸ hB₁_in_comp)
    · have hEq' : connectedComponentIn (discBd G₁ \ {s, t}) x₁ = C₂ := hEq
      refine ⟨C₁, H₁, hH₁_disc, hH_union ▸ subset_union_left, ?_, hH₁_bd, ?_⟩
      · rw [← hH_inter]; exact inter_subset_left
      · exact hC_disj.mono_right (hEq' ▸ hB₁_in_comp)
  obtain ⟨C, Δ, hΔ_disc, hΔ_sub_G₁, hF₂_Δ, hΔ_bd, hC_disj_B₁⟩ := hchoose_H
  have hΔ_sub : Δ ⊆ D := hΔ_sub_G₁.trans hG₁_sub
  refine ⟨Δ, hΔ_disc, hΔ_sub, hF₂_Δ hs_F₂, hF₂_Δ ht_F₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxΔ, hx_bdD⟩
    have hx_bdG₁ : x ∈ discBd G₁ :=
      disc_inter_discBd_subset_discBd hD hG₁_disc hG₁_sub ⟨hΔ_sub_G₁ hxΔ, hx_bdD⟩
    have hx_bdΔ : x ∈ discBd Δ :=
      disc_inter_discBd_subset_discBd hD hΔ_disc hΔ_sub ⟨hxΔ, hx_bdD⟩
    rw [hΔ_bd] at hx_bdΔ
    rcases hx_bdΔ with hxC | hxF₂
    · have hxF₁ : x ∈ F₁ := by
        rw [hG₁_bd] at hx_bdG₁
        exact hx_bdG₁.resolve_left (Set.disjoint_left.mp hC_disj_B₁ hxC)
      have : x ∈ F₁ ∩ discBd D := ⟨hxF₁, hx_bdD⟩
      rwa [hF₁_bd] at this
    · have : x ∈ F₂ ∩ discBd G₁ := ⟨hxF₂, hx_bdG₁⟩
      rwa [hF₂_bd] at this
  · rintro x (rfl | rfl)
    · exact ⟨hF₂_Δ hs_F₂, hs⟩
    · exact ⟨hF₂_Δ ht_F₂, ht⟩

private noncomputable def splitInternalCell {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : GM17.Painting S) {c₀ Δ₁ Δ₂ N' : Set S} (hc₀ : c₀ ∈ Γ.C) (hint₀ : ¬ (c₀ ∩ bd S).Nonempty)
    (hΔ₁_disc : IsClosedDisc Δ₁) (hΔ₂_disc : IsClosedDisc Δ₂)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀) (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hN_sub : Γ.N ⊆ N') (hN'_fin : N'.Finite) (hN'_diff : N' \ Γ.N ⊆ Δ₁ ∩ Δ₂)
    (hΔ_inter : Δ₁ ∩ Δ₂ ⊆ N')
    (hΔ₁_bd : Δ₁ ∩ N' ⊆ discBd Δ₁) (hΔ₂_bd : Δ₂ ∩ N' ⊆ discBd Δ₂)
    (hΔ₁_card : (Δ₁ ∩ N').ncard ≤ 3) (hΔ₂_card : (Δ₂ ∩ N').ncard ≤ 3) :
    GM17.Painting S := by
  classical
  let c₁ : Set S := Δ₁ \ N'
  let c₂ : Set S := Δ₂ \ N'
  let U' : Set S := (Γ.U \ c₀) ∪ Δ₁ ∪ Δ₂
  let I₀ : Set (Set S) := Γ.C \ {c₀}
  let I : Set (Set S) := insert c₁ (insert c₂ I₀)
  have hI₀_fin : I₀.Finite := Γ.finite_cells.subset sdiff_subset
  have hI_fin : I.Finite := (hI₀_fin.insert c₂).insert c₁
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₁, hxN'⟩ => ⟨hΔ₁_sub hx₁, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₂, hxN'⟩ => ⟨hΔ₂_sub hx₂, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₁_diff_fin : (Δ₁ \ c₁).Finite :=
    hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩
  have hc₂_diff_fin : (Δ₂ \ c₂).Finite :=
    hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩
  have hc₁_pc : IsPathConnected c₁ :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset hc₁_diff_fin
  have hc₂_pc : IsPathConnected c₂ :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset hc₂_diff_fin
  have hcl_c₁ : closure c₁ = Δ₁ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset hc₁_diff_fin
  have hcl_c₂ : closure c₂ = Δ₂ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset hc₂_diff_fin
  have htc₁ : tilde c₁ = Δ₁ ∩ N' :=
    tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin
  have htc₂ : tilde c₂ = Δ₂ ∩ N' :=
    tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin
  have hc₁_disj_c₂ : Disjoint c₁ c₂ := by
    refine Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter ⟨hx₁, hx₂⟩)
  have hcell_disj_N' : ∀ c ∈ I₀, ∀ x ∈ c, x ∉ N' := by
    rintro c ⟨hc, hne⟩ x hxc hxN'
    by_cases hxN : x ∈ Γ.N
    · exact (Γ.cell_subset_diff hc hxc).2 hxN
    · have hx_c₀ : x ∈ c₀ := by
        rw [← Γ.closure_cell_diff_N hc₀]
        exact ⟨hΔ₁_sub (hN'_diff ⟨hxN', hxN⟩).1, hxN⟩
      exact Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc hx_c₀
  have hcl_sub_I₀ : ∀ c ∈ I₀, closure c ⊆ Γ.U \ c₀ := by
    rintro c ⟨hc, hne⟩ x hxcl
    refine ⟨Γ.closure_cell_subset_U hc hxcl, fun hxc₀ => ?_⟩
    by_cases hxc : x ∈ c
    · exact Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc hxc₀
    · exact (Γ.cell_subset_diff hc₀ hxc₀).2 (Γ.tilde_subset_N hc ⟨hxcl, hxc⟩)
  have hU₀_eq : Γ.U \ c₀ = Γ.N ∪ ⋃ c ∈ I₀, closure c := by
    ext x
    simp only [I₀, mem_sdiff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hxU, hx_not_c₀⟩
      rw [Γ.U_eq_N_union_biUnion_closure] at hxU
      rcases hxU with hxN | hcl
      · exact Or.inl hxN
      · rw [mem_iUnion₂] at hcl
        rcases hcl with ⟨c, hc, hxcl⟩
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          exact Or.inl (Γ.tilde_subset_N hc₀ ⟨hxcl, hx_not_c₀⟩)
        · exact Or.inr ⟨c, ⟨hc, hcc₀⟩, hxcl⟩
    · rintro (hxN | ⟨c, hcI, hxcl⟩)
      · exact ⟨Γ.N_subset hxN, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩
      · exact hcl_sub_I₀ c hcI hxcl
  have hU'_closed : IsClosed U' := by
    have hU₀_cl : IsClosed (Γ.U \ c₀) := by
      rw [hU₀_eq]
      exact Γ.finite_N.isClosed.union (hI₀_fin.isClosed_biUnion fun _ _ => isClosed_closure)
    exact (hU₀_cl.union (isClosed_of_isClosedDisc hΔ₁_disc)).union (isClosed_of_isClosedDisc hΔ₂_disc)
  have hcov : ⋃₀ I = U' \ N' := by
    ext x
    simp only [I, U', sUnion_insert, mem_union, mem_sUnion, mem_sdiff]
    constructor
    · rintro (hxc₁ | hxc₂ | ⟨c, ⟨hc, hne⟩, hxc⟩)
      · exact ⟨Or.inl (Or.inr hxc₁.1), hxc₁.2⟩
      · exact ⟨Or.inr hxc₂.1, hxc₂.2⟩
      · exact ⟨Or.inl (Or.inl ⟨Γ.cell_subset_U hc hxc,
          Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc⟩),
          hcell_disj_N' c ⟨hc, hne⟩ x hxc⟩
    · rintro ⟨((⟨hxU, hx_not_c₀⟩ | hxΔ₁) | hxΔ₂), hx_not_N'⟩
      · have hx_not_N : x ∉ Γ.N := fun hxN => hx_not_N' (hN_sub hxN)
        have hx_cells : x ∈ ⋃₀ Γ.C := Γ.sUnion_cells.symm ▸ ⟨hxU, hx_not_N⟩
        rcases hx_cells with ⟨c, hc, hxc⟩
        have hne : c ≠ c₀ := fun h => hx_not_c₀ (h ▸ hxc)
        exact Or.inr (Or.inr ⟨c, ⟨hc, hne⟩, hxc⟩)
      · exact Or.inl ⟨hxΔ₁, hx_not_N'⟩
      · exact Or.inr (Or.inl ⟨hxΔ₂, hx_not_N'⟩)
  have hC'_eq : arcComponentsIn (U' \ N') = I := by
    apply arcComponentsIn_eq_of_finite_cover hI_fin hcov
    · rintro c (rfl | rfl | hcI)
      · exact hc₁_pc.nonempty
      · exact hc₂_pc.nonempty
      · exact Γ.cell_nonempty hcI.1
    · rintro c (rfl | rfl | hcI)
      · exact hc₁_pc
      · exact hc₂_pc
      · exact Γ.cell_isPathConnected hcI.1
    · rintro c (rfl | rfl | hcI) c' (rfl | rfl | hc'I) hne
      · exact (hne rfl).elim
      · exact hc₁_disj_c₂
      · exact (Γ.cell_disjoint hc'I.1 hc₀ hc'I.2).symm.mono_left hc₁_sub_c₀
      · exact hc₁_disj_c₂.symm
      · exact (hne rfl).elim
      · exact (Γ.cell_disjoint hc'I.1 hc₀ hc'I.2).symm.mono_left hc₂_sub_c₀
      · exact (Γ.cell_disjoint hcI.1 hc₀ hcI.2).mono_right hc₁_sub_c₀
      · exact (Γ.cell_disjoint hcI.1 hc₀ hcI.2).mono_right hc₂_sub_c₀
      · exact Γ.cell_disjoint hcI.1 hc'I.1 hne
    · intro c hcI_all
      refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc, hcov ▸ ⟨c, hcI_all, hxc⟩⟩)
      rintro x ⟨hxcl, hxUN⟩
      rcases hcI_all with rfl | rfl | hcI
      · rw [hcl_c₁] at hxcl
        exact ⟨hxcl, hxUN.2⟩
      · rw [hcl_c₂] at hxcl
        exact ⟨hxcl, hxUN.2⟩
      · rw [← Γ.closure_cell_diff_N hcI.1]
        exact ⟨hxcl, fun hxN => hxUN.2 (hN_sub hxN)⟩
  refine
    { U := U'
      N := N'
      isClosed_U := hU'_closed
      finite_N := hN'_fin
      N_subset := fun x hxN' => by
        by_cases hxN : x ∈ Γ.N
        · exact Or.inl (Or.inl ⟨Γ.N_subset hxN,
            fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩)
        · exact Or.inl (Or.inr (hN'_diff ⟨hxN', hxN⟩).1)
      finite_cells := hC'_eq ▸ hI_fin
      cell_disc := ?_
      bd_subset := fun x hxbd => Or.inl (Or.inl ⟨Γ.bd_subset hxbd,
        fun hxc₀ => hint₀ ⟨x, hxc₀, hxbd⟩⟩)
      border_cell := ?_ }
  · intro c hc
    rw [hC'_eq] at hc
    rcases hc with rfl | rfl | hcI
    · rw [hcl_c₁, htc₁]
      exact ⟨hΔ₁_disc, hΔ₁_bd, hN'_fin.inter_of_right Δ₁, hΔ₁_card⟩
    · rw [hcl_c₂, htc₂]
      exact ⟨hΔ₂_disc, hΔ₂_bd, hN'_fin.inter_of_right Δ₂, hΔ₂_card⟩
    · exact Γ.cell_disc c hcI.1
  · intro c hc hbd
    rw [hC'_eq] at hc
    rcases hc with rfl | rfl | hcI
    · exact False.elim (hint₀ (hbd.mono (inter_subset_inter_left _ hc₁_sub_c₀)))
    · exact False.elim (hint₀ (hbd.mono (inter_subset_inter_left _ hc₂_sub_c₀)))
    · exact Γ.border_cell c hcI.1 hbd

private theorem splitInternalCell_C {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : GM17.Painting S) {c₀ Δ₁ Δ₂ N' : Set S} (hc₀ : c₀ ∈ Γ.C) (hint₀ : ¬ (c₀ ∩ bd S).Nonempty)
    (hΔ₁_disc : IsClosedDisc Δ₁) (hΔ₂_disc : IsClosedDisc Δ₂)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀) (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hN_sub : Γ.N ⊆ N') (hN'_fin : N'.Finite) (hN'_diff : N' \ Γ.N ⊆ Δ₁ ∩ Δ₂)
    (hΔ_inter : Δ₁ ∩ Δ₂ ⊆ N')
    (hΔ₁_bd : Δ₁ ∩ N' ⊆ discBd Δ₁) (hΔ₂_bd : Δ₂ ∩ N' ⊆ discBd Δ₂)
    (hΔ₁_card : (Δ₁ ∩ N').ncard ≤ 3) (hΔ₂_card : (Δ₂ ∩ N').ncard ≤ 3) :
    (splitInternalCell Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card).C =
      insert (Δ₁ \ N') (insert (Δ₂ \ N') (Γ.C \ {c₀})) := by
  classical
  let c₁ : Set S := Δ₁ \ N'
  let c₂ : Set S := Δ₂ \ N'
  let U' : Set S := (Γ.U \ c₀) ∪ Δ₁ ∪ Δ₂
  let I₀ : Set (Set S) := Γ.C \ {c₀}
  let I : Set (Set S) := insert c₁ (insert c₂ I₀)
  have hI₀_fin : I₀.Finite := Γ.finite_cells.subset sdiff_subset
  have hI_fin : I.Finite := (hI₀_fin.insert c₂).insert c₁
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₁, hxN'⟩ => ⟨hΔ₁_sub hx₁, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₂, hxN'⟩ => ⟨hΔ₂_sub hx₂, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₁_diff_fin : (Δ₁ \ c₁).Finite :=
    hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩
  have hc₂_diff_fin : (Δ₂ \ c₂).Finite :=
    hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩
  have hc₁_pc : IsPathConnected c₁ :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset hc₁_diff_fin
  have hc₂_pc : IsPathConnected c₂ :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset hc₂_diff_fin
  have hcl_c₁ : closure c₁ = Δ₁ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset hc₁_diff_fin
  have hcl_c₂ : closure c₂ = Δ₂ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset hc₂_diff_fin
  have hc₁_disj_c₂ : Disjoint c₁ c₂ := by
    refine Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter ⟨hx₁, hx₂⟩)
  have hcell_disj_N' : ∀ c ∈ I₀, ∀ x ∈ c, x ∉ N' := by
    rintro c ⟨hc, hne⟩ x hxc hxN'
    by_cases hxN : x ∈ Γ.N
    · exact (Γ.cell_subset_diff hc hxc).2 hxN
    · have hx_c₀ : x ∈ c₀ := by
        rw [← Γ.closure_cell_diff_N hc₀]
        exact ⟨hΔ₁_sub (hN'_diff ⟨hxN', hxN⟩).1, hxN⟩
      exact Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc hx_c₀
  have hcov : ⋃₀ I = U' \ N' := by
    ext x
    simp only [I, U', sUnion_insert, mem_union, mem_sUnion, mem_sdiff]
    constructor
    · rintro (hxc₁ | hxc₂ | ⟨c, ⟨hc, hne⟩, hxc⟩)
      · exact ⟨Or.inl (Or.inr hxc₁.1), hxc₁.2⟩
      · exact ⟨Or.inr hxc₂.1, hxc₂.2⟩
      · exact ⟨Or.inl (Or.inl ⟨Γ.cell_subset_U hc hxc,
          Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc⟩),
          hcell_disj_N' c ⟨hc, hne⟩ x hxc⟩
    · rintro ⟨((⟨hxU, hx_not_c₀⟩ | hxΔ₁) | hxΔ₂), hx_not_N'⟩
      · have hx_not_N : x ∉ Γ.N := fun hxN => hx_not_N' (hN_sub hxN)
        have hx_cells : x ∈ ⋃₀ Γ.C := Γ.sUnion_cells.symm ▸ ⟨hxU, hx_not_N⟩
        rcases hx_cells with ⟨c, hc, hxc⟩
        have hne : c ≠ c₀ := fun h => hx_not_c₀ (h ▸ hxc)
        exact Or.inr (Or.inr ⟨c, ⟨hc, hne⟩, hxc⟩)
      · exact Or.inl ⟨hxΔ₁, hx_not_N'⟩
      · exact Or.inr (Or.inl ⟨hxΔ₂, hx_not_N'⟩)
  apply arcComponentsIn_eq_of_finite_cover hI_fin hcov
  · rintro c (rfl | rfl | hcI)
    · exact hc₁_pc.nonempty
    · exact hc₂_pc.nonempty
    · exact Γ.cell_nonempty hcI.1
  · rintro c (rfl | rfl | hcI)
    · exact hc₁_pc
    · exact hc₂_pc
    · exact Γ.cell_isPathConnected hcI.1
  · rintro c (rfl | rfl | hcI) c' (rfl | rfl | hc'I) hne
    · exact (hne rfl).elim
    · exact hc₁_disj_c₂
    · exact (Γ.cell_disjoint hc'I.1 hc₀ hc'I.2).symm.mono_left hc₁_sub_c₀
    · exact hc₁_disj_c₂.symm
    · exact (hne rfl).elim
    · exact (Γ.cell_disjoint hc'I.1 hc₀ hc'I.2).symm.mono_left hc₂_sub_c₀
    · exact (Γ.cell_disjoint hcI.1 hc₀ hcI.2).mono_right hc₁_sub_c₀
    · exact (Γ.cell_disjoint hcI.1 hc₀ hcI.2).mono_right hc₂_sub_c₀
    · exact Γ.cell_disjoint hcI.1 hc'I.1 hne
  · intro c hcI_all
    refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc, hcov ▸ ⟨c, hcI_all, hxc⟩⟩)
    rintro x ⟨hxcl, hxUN⟩
    rcases hcI_all with rfl | rfl | hcI
    · rw [hcl_c₁] at hxcl
      exact ⟨hxcl, hxUN.2⟩
    · rw [hcl_c₂] at hxcl
      exact ⟨hxcl, hxUN.2⟩
    · rw [← Γ.closure_cell_diff_N hcI.1]
      exact ⟨hxcl, fun hxN => hxUN.2 (hN_sub hxN)⟩

/-- Disc configuration for peeling off a 2-ended cell `{n₁, n₃}` from a 3-ended internal cell
`{n₁, n₂, n₃}` without adding any new nodes. -/
private theorem exists_discs_for_peel {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : GM17.Painting S) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.C)
    {n₁ n₂ n₃ : S} (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃) :
    ∃ Δ₁ Δ₂ : Set S,
      IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ closure c₀ ∧ Δ₂ ⊆ closure c₀ ∧
      Δ₁ ∩ Δ₂ = {n₁, n₃} ∧
      Δ₁ ∩ Γ.N = {n₁, n₂, n₃} ∧
      Δ₂ ∩ Γ.N = {n₁, n₃} ∧
      Δ₁ ∩ Γ.N ⊆ discBd Δ₁ ∧
      Δ₂ ∩ Γ.N ⊆ discBd Δ₂ := by
  have hD : IsClosedDisc (closure c₀) := Γ.isClosedDisc_closure_cell hc₀
  have htc₀_bd : tilde c₀ ⊆ discBd (closure c₀) := (Γ.cell_disc c₀ hc₀).2.1
  have hn₁_tc : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc : n₃ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inr rfl)
  have hn₁_bd : n₁ ∈ discBd (closure c₀) := htc₀_bd hn₁_tc
  have hn₂_bd : n₂ ∈ discBd (closure c₀) := htc₀_bd hn₂_tc
  have hn₃_bd : n₃ ∈ discBd (closure c₀) := htc₀_bd hn₃_tc
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, _⟩ :=
    exists_chord_in_closedDisc hD hn₁_bd hn₃_bd h13
  obtain ⟨A₁, A₂, E₁, E₂, _, _, hE₁_disc, hE₂_disc, hE_union, hE_inter, hE₁_bd, hE₂_bd, _⟩ :=
    disc_iArc (closure c₀) F₁ n₁ n₃ hD hF₁_sub h13 hF₁_line hF₁_bd
  have hn₁_F₁ : n₁ ∈ F₁ := by
    have : n₁ ∈ F₁ ∩ discBd (closure c₀) := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₁ : n₃ ∈ F₁ := by
    have : n₃ ∈ F₁ ∩ discBd (closure c₀) := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hn₂_not_F₁ : n₂ ∉ F₁ := by
    intro hmem
    have : n₂ ∈ F₁ ∩ discBd (closure c₀) := ⟨hmem, hn₂_bd⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact h12 hEq.symm
    · exact h23 hEq
  have hn₂_D : n₂ ∈ E₁ ∪ E₂ := hE_union.symm ▸ discBd_subset (closure c₀) hn₂_bd
  have hhalf : ∃ Δ₁ D' : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc D' ∧
      Δ₁ ⊆ closure c₀ ∧ D' ⊆ closure c₀ ∧ Δ₁ ∩ D' = F₁ ∧
      F₁ ⊆ discBd Δ₁ ∧ F₁ ⊆ discBd D' ∧
      n₂ ∈ discBd Δ₁ ∧ n₂ ∉ D' := by
    rcases hn₂_D with hn₂_E₁ | hn₂_E₂
    · have hn₂_not_E₂ : n₂ ∉ E₂ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨hn₂_E₁, h⟩)
      have hE₁_sub : E₁ ⊆ closure c₀ := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ closure c₀ := hE_union ▸ subset_union_right
      refine ⟨E₁, E₂, hE₁_disc, hE₂_disc, hE₁_sub, hE₂_sub, hE_inter, ?_, ?_, ?_, hn₂_not_E₂⟩
      · rw [hE₁_bd]; exact subset_union_right
      · rw [hE₂_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₁_disc hE₁_sub ⟨hn₂_E₁, hn₂_bd⟩
    · have hn₂_not_E₁ : n₂ ∉ E₁ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨h, hn₂_E₂⟩)
      have hE₁_sub : E₁ ⊆ closure c₀ := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ closure c₀ := hE_union ▸ subset_union_right
      refine ⟨E₂, E₁, hE₂_disc, hE₁_disc, hE₂_sub, hE₁_sub, ?_, ?_, ?_, ?_, hn₂_not_E₁⟩
      · rw [Set.inter_comm, hE_inter]
      · rw [hE₂_bd]; exact subset_union_right
      · rw [hE₁_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₂_disc hE₂_sub ⟨hn₂_E₂, hn₂_bd⟩
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub, hΔ₁D'_inter, hF₁_bdΔ₁,
    hF₁_bdD', hn₂_bdΔ₁, hn₂_not_D'⟩ := hhalf
  have hF₁_Δ₁ : F₁ ⊆ Δ₁ := hF₁_bdΔ₁.trans (discBd_subset Δ₁)
  obtain ⟨Δ₂, hΔ₂_disc, hΔ₂_sub', hn₁_Δ₂, hn₃_Δ₂, hΔ₂_bdD'_inter⟩ :=
    exists_subdisc_inter_discBd_eq_pair hD'_disc (hF₁_bdD' hn₁_F₁) (hF₁_bdD' hn₃_F₁) h13
  have hΔ₂_sub : Δ₂ ⊆ closure c₀ := hΔ₂_sub'.trans hD'_sub
  have hinter : Δ₁ ∩ Δ₂ = {n₁, n₃} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₁, hx₂⟩
      have hxF₁ : x ∈ F₁ := hΔ₁D'_inter ▸ ⟨hx₁, hΔ₂_sub' hx₂⟩
      exact hΔ₂_bdD'_inter ▸ ⟨hx₂, hF₁_bdD' hxF₁⟩
    · rintro x (rfl | rfl)
      · exact ⟨hF₁_Δ₁ hn₁_F₁, hn₁_Δ₂⟩
      · exact ⟨hF₁_Δ₁ hn₃_F₁, hn₃_Δ₂⟩
  have hcl_inter_N : closure c₀ ∩ Γ.N = {n₁, n₂, n₃} := by
    rw [← htc₀]
    ext x
    simp only [mem_inter_iff, tilde, mem_sdiff]
    exact ⟨fun ⟨hxcl, hxN⟩ => ⟨hxcl, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩,
      fun hxtc₀ => ⟨hxtc₀.1, Γ.tilde_subset_N hc₀ hxtc₀⟩⟩
  have hΔ₁_N : Δ₁ ∩ Γ.N = {n₁, n₂, n₃} := by
    refine Subset.antisymm (fun x ⟨hx₁, hxN⟩ => hcl_inter_N ▸ ⟨hΔ₁_sub hx₁, hxN⟩) ?_
    rintro x (rfl | rfl | rfl)
    · exact ⟨hF₁_Δ₁ hn₁_F₁, Γ.tilde_subset_N hc₀ hn₁_tc⟩
    · exact ⟨discBd_subset Δ₁ hn₂_bdΔ₁, Γ.tilde_subset_N hc₀ hn₂_tc⟩
    · exact ⟨hF₁_Δ₁ hn₃_F₁, Γ.tilde_subset_N hc₀ hn₃_tc⟩
  have hΔ₂_N : Δ₂ ∩ Γ.N = {n₁, n₃} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₂, hxN⟩
      have hx3 : x ∈ ({n₁, n₂, n₃} : Set S) := hcl_inter_N ▸ ⟨hΔ₂_sub hx₂, hxN⟩
      rcases hx3 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hn₂_not_D' (hΔ₂_sub' hx₂)).elim
      · exact Or.inr rfl
    · rintro x (rfl | rfl)
      · exact ⟨hn₁_Δ₂, Γ.tilde_subset_N hc₀ hn₁_tc⟩
      · exact ⟨hn₃_Δ₂, Γ.tilde_subset_N hc₀ hn₃_tc⟩
  have hΔ₁_bdN : Δ₁ ∩ Γ.N ⊆ discBd Δ₁ := by
    rw [hΔ₁_N]
    rintro x (rfl | rfl | rfl)
    · exact hF₁_bdΔ₁ hn₁_F₁
    · exact hn₂_bdΔ₁
    · exact hF₁_bdΔ₁ hn₃_F₁
  have hΔ₂_bdN : Δ₂ ∩ Γ.N ⊆ discBd Δ₂ := by
    rw [hΔ₂_N]
    rintro x (rfl | rfl)
    · exact disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hn₁_Δ₂, hF₁_bdD' hn₁_F₁⟩
    · exact disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hn₃_Δ₂, hF₁_bdD' hn₃_F₁⟩
  exact ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hinter, hΔ₁_N, hΔ₂_N, hΔ₁_bdN, hΔ₂_bdN⟩

private theorem exists_discs_for_9_2 {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : GM17.Painting S) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.C)
    {n₁ n₂ n₃ : S} (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃) :
    ∃ n₀ ∈ c₀, ∃ Δ₁ Δ₂ : Set S,
      IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ closure c₀ ∧ Δ₂ ⊆ closure c₀ ∧
      Δ₁ ∩ Δ₂ = {n₀} ∧
      Δ₁ ∩ insert n₀ Γ.N = {n₀, n₁, n₃} ∧
      Δ₂ ∩ insert n₀ Γ.N = {n₀, n₂} ∧
      Δ₁ ∩ insert n₀ Γ.N ⊆ discBd Δ₁ ∧
      Δ₂ ∩ insert n₀ Γ.N ⊆ discBd Δ₂ := by
  have hD : IsClosedDisc (closure c₀) := Γ.isClosedDisc_closure_cell hc₀
  have htc₀_bd : tilde c₀ ⊆ discBd (closure c₀) := (Γ.cell_disc c₀ hc₀).2.1
  have hn₁_tc : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc : n₃ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inr rfl)
  have hn₁_bd : n₁ ∈ discBd (closure c₀) := htc₀_bd hn₁_tc
  have hn₂_bd : n₂ ∈ discBd (closure c₀) := htc₀_bd hn₂_tc
  have hn₃_bd : n₃ ∈ discBd (closure c₀) := htc₀_bd hn₃_tc
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, _⟩ :=
    exists_chord_in_closedDisc hD hn₁_bd hn₃_bd h13
  obtain ⟨ev, hev0, hev1⟩ := hF₁_line
  let u₀ : 𝕀 := ⟨1 / 2, by constructor <;> norm_num⟩
  let n₀ : S := (ev u₀).1
  have hn₀_F₁ : n₀ ∈ F₁ := (ev u₀).2
  have hn₀_ne_n₁ : n₀ ≠ n₁ := fun h => by
    have hEq : ev u₀ = ev 0 := Subtype.ext (h.trans hev0.symm)
    have hval := congrArg Subtype.val (ev.injective hEq)
    norm_num [u₀] at hval
  have hn₀_ne_n₃ : n₀ ≠ n₃ := fun h => by
    have hEq : ev u₀ = ev 1 := Subtype.ext (h.trans hev1.symm)
    have hval := congrArg Subtype.val (ev.injective hEq)
    norm_num [u₀] at hval
  have hn₀_not_bd : n₀ ∉ discBd (closure c₀) := by
    intro hbd
    have : n₀ ∈ F₁ ∩ discBd (closure c₀) := ⟨hn₀_F₁, hbd⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact hn₀_ne_n₁ hEq
    · exact hn₀_ne_n₃ hEq
  have hn₀_c₀ : n₀ ∈ c₀ := by
    have hcl : n₀ ∈ closure c₀ := hF₁_sub hn₀_F₁
    by_contra hnot
    exact hn₀_not_bd (htc₀_bd ⟨hcl, hnot⟩)
  obtain ⟨A₁, A₂, E₁, E₂, _, _, hE₁_disc, hE₂_disc, hE_union, hE_inter, hE₁_bd, hE₂_bd, _⟩ :=
    disc_iArc (closure c₀) F₁ n₁ n₃ hD hF₁_sub h13 ⟨ev, hev0, hev1⟩ hF₁_bd
  have hn₁_F₁ : n₁ ∈ F₁ := by
    have : n₁ ∈ F₁ ∩ discBd (closure c₀) := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₁ : n₃ ∈ F₁ := by
    have : n₃ ∈ F₁ ∩ discBd (closure c₀) := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hn₂_not_F₁ : n₂ ∉ F₁ := by
    intro hmem
    have : n₂ ∈ F₁ ∩ discBd (closure c₀) := ⟨hmem, hn₂_bd⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact h12 hEq.symm
    · exact h23 hEq
  have hn₂_D : n₂ ∈ E₁ ∪ E₂ := hE_union.symm ▸ discBd_subset (closure c₀) hn₂_bd
  have hhalf : ∃ Δ₁ D' : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc D' ∧
      Δ₁ ⊆ closure c₀ ∧ D' ⊆ closure c₀ ∧ Δ₁ ∩ D' = F₁ ∧
      F₁ ⊆ discBd Δ₁ ∧ F₁ ⊆ discBd D' ∧
      n₂ ∉ Δ₁ ∧ n₂ ∈ discBd D' := by
    rcases hn₂_D with hn₂_E₁ | hn₂_E₂
    · have hn₂_not_E₂ : n₂ ∉ E₂ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨hn₂_E₁, h⟩)
      have hE₁_sub : E₁ ⊆ closure c₀ := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ closure c₀ := hE_union ▸ subset_union_right
      refine ⟨E₂, E₁, hE₂_disc, hE₁_disc, hE₂_sub, hE₁_sub, ?_, ?_, ?_, hn₂_not_E₂, ?_⟩
      · rw [Set.inter_comm, hE_inter]
      · rw [hE₂_bd]; exact subset_union_right
      · rw [hE₁_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₁_disc hE₁_sub ⟨hn₂_E₁, hn₂_bd⟩
    · have hn₂_not_E₁ : n₂ ∉ E₁ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨h, hn₂_E₂⟩)
      have hE₁_sub : E₁ ⊆ closure c₀ := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ closure c₀ := hE_union ▸ subset_union_right
      refine ⟨E₁, E₂, hE₁_disc, hE₂_disc, hE₁_sub, hE₂_sub, hE_inter, ?_, ?_, hn₂_not_E₁, ?_⟩
      · rw [hE₁_bd]; exact subset_union_right
      · rw [hE₂_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₂_disc hE₂_sub ⟨hn₂_E₂, hn₂_bd⟩
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub, hΔ₁D'_inter, hF₁_bdΔ₁,
    hF₁_bdD', hn₂_not_Δ₁, hn₂_bdD'⟩ := hhalf
  have hF₁_Δ₁ : F₁ ⊆ Δ₁ := hF₁_bdΔ₁.trans (discBd_subset Δ₁)
  have hn₀_bdD' : n₀ ∈ discBd D' := hF₁_bdD' hn₀_F₁
  have h20 : n₂ ≠ n₀ := fun h => hn₀_not_bd (h ▸ hn₂_bd)
  obtain ⟨Δ₂, hΔ₂_disc, hΔ₂_sub', hn₂_Δ₂, hn₀_Δ₂, hΔ₂_bdD'_inter⟩ :=
    exists_subdisc_inter_discBd_eq_pair hD'_disc hn₂_bdD' hn₀_bdD' h20
  have hΔ₂_sub : Δ₂ ⊆ closure c₀ := hΔ₂_sub'.trans hD'_sub
  have hinter : Δ₁ ∩ Δ₂ = {n₀} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₁, hx₂⟩
      have hxF₁ : x ∈ F₁ := hΔ₁D'_inter ▸ ⟨hx₁, hΔ₂_sub' hx₂⟩
      have hx_pair : x ∈ ({n₂, n₀} : Set S) := hΔ₂_bdD'_inter ▸ ⟨hx₂, hF₁_bdD' hxF₁⟩
      rcases hx_pair with rfl | rfl
      · exact (hn₂_not_Δ₁ hx₁).elim
      · rfl
    · rintro x rfl
      exact ⟨hF₁_Δ₁ hn₀_F₁, hn₀_Δ₂⟩
  have hcl_inter_N : closure c₀ ∩ Γ.N = {n₁, n₂, n₃} := by
    rw [← htc₀]
    ext x
    simp only [mem_inter_iff, tilde, mem_sdiff]
    exact ⟨fun ⟨hxcl, hxN⟩ => ⟨hxcl, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩,
      fun hxtc₀ => ⟨hxtc₀.1, Γ.tilde_subset_N hc₀ hxtc₀⟩⟩
  have hΔ₁_N' : Δ₁ ∩ insert n₀ Γ.N = {n₀, n₁, n₃} := by
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, rfl | hxN⟩
      · exact Or.inl rfl
      · have hx3 : x ∈ ({n₁, n₂, n₃} : Set S) := hcl_inter_N ▸ ⟨hΔ₁_sub hx₁, hxN⟩
        rcases hx3 with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact (hn₂_not_Δ₁ hx₁).elim
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨hF₁_Δ₁ hn₀_F₁, Or.inl rfl⟩
      · exact ⟨hF₁_Δ₁ hn₁_F₁, Or.inr (Γ.tilde_subset_N hc₀ hn₁_tc)⟩
      · exact ⟨hF₁_Δ₁ hn₃_F₁, Or.inr (Γ.tilde_subset_N hc₀ hn₃_tc)⟩
  have hΔ₂_N' : Δ₂ ∩ insert n₀ Γ.N = {n₀, n₂} := by
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx₂, hxn₀ | hxN⟩
      · exact Or.inl hxn₀
      · have hx3 : x ∈ ({n₁, n₂, n₃} : Set S) := hcl_inter_N ▸ ⟨hΔ₂_sub hx₂, hxN⟩
        rcases hx3 with hEq | hEq | hEq
        · have : n₁ ∈ Δ₁ ∩ Δ₂ := ⟨hF₁_Δ₁ hn₁_F₁, hEq ▸ hx₂⟩
          rw [hinter] at this
          exact (hn₀_ne_n₁ this.symm).elim
        · exact Or.inr hEq
        · have : n₃ ∈ Δ₁ ∩ Δ₂ := ⟨hF₁_Δ₁ hn₃_F₁, hEq ▸ hx₂⟩
          rw [hinter] at this
          exact (hn₀_ne_n₃ this.symm).elim
    · rintro (rfl | rfl)
      · exact ⟨hn₀_Δ₂, Or.inl rfl⟩
      · exact ⟨hn₂_Δ₂, Or.inr (Γ.tilde_subset_N hc₀ hn₂_tc)⟩
  have hΔ₁_bdN' : Δ₁ ∩ insert n₀ Γ.N ⊆ discBd Δ₁ := by
    rw [hΔ₁_N']
    rintro x (rfl | rfl | rfl)
    · exact hF₁_bdΔ₁ hn₀_F₁
    · exact hF₁_bdΔ₁ hn₁_F₁
    · exact hF₁_bdΔ₁ hn₃_F₁
  have hΔ₂_bdN' : Δ₂ ∩ insert n₀ Γ.N ⊆ discBd Δ₂ := by
    rw [hΔ₂_N']
    rintro x (rfl | rfl)
    · exact disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hn₀_Δ₂, hn₀_bdD'⟩
    · exact disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hn₂_Δ₂, hn₂_bdD'⟩
  exact ⟨n₀, hn₀_c₀, Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hinter,
    hΔ₁_N', hΔ₂_N', hΔ₁_bdN', hΔ₂_bdN'⟩

private theorem exists_third_point_in_discBd {S : Type*} [TopologicalSpace S]
    {D : Set S} (hD : IsClosedDisc D) (n₁ n₂ : S) :
    ∃ n₃ ∈ discBd D, n₁ ≠ n₃ ∧ n₂ ≠ n₃ := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have h1_sp : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hm1_sp : (-1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hI_sp : Complex.I ∈ sphere (0 : ℂ) 1 := by simp
  have h1_ball : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall h1_sp
  have hm1_ball : (-1 : ℂ) ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hm1_sp
  have hI_ball : Complex.I ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hI_sp
  have hg_bd : ∀ z ∈ sphere (0 : ℂ) 1, g z ∈ discBd D := by
    intro z hz
    have hzD : g z ∈ D := c.gm (sphere_subset_closedBall hz)
    have hhz : h (g z) ∈ h '' discBd D := by
      rw [c.bd, c.hg (sphere_subset_closedBall hz)]
      exact hz
    rcases hhz with ⟨x, hx_bd, hEq⟩
    rwa [c.gh.injOn hzD (discBd_subset D hx_bd) hEq.symm]
  have hne_1_m1 : g 1 ≠ g (-1) := fun hEq => by
    have : (1 : ℂ) = -1 := c.injOn h1_ball hm1_ball hEq
    norm_num at this
  have hne_1_I : g 1 ≠ g Complex.I := fun hEq => by
    have : (1 : ℂ) = Complex.I := c.injOn h1_ball hI_ball hEq
    have := congrArg Complex.im this
    norm_num at this
  have hne_m1_I : g (-1) ≠ g Complex.I := fun hEq => by
    have : (-1 : ℂ) = Complex.I := c.injOn hm1_ball hI_ball hEq
    have := congrArg Complex.im this
    norm_num at this
  by_cases h1 : n₁ ≠ g 1 ∧ n₂ ≠ g 1
  · exact ⟨g 1, hg_bd 1 h1_sp, h1.1, h1.2⟩
  by_cases hm1 : n₁ ≠ g (-1) ∧ n₂ ≠ g (-1)
  · exact ⟨g (-1), hg_bd (-1) hm1_sp, hm1.1, hm1.2⟩
  refine ⟨g Complex.I, hg_bd Complex.I hI_sp, ?_, ?_⟩
  · intro hEq1
    rcases not_and_or.mp h1 with h1' | h1' <;> rcases not_and_or.mp hm1 with hm1' | hm1'
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')
    · push Not at h1'; exact hne_1_I (h1'.symm.trans hEq1)
    · push Not at hm1'; exact hne_m1_I (hm1'.symm.trans hEq1)
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')
  · intro hEq2
    rcases not_and_or.mp h1 with h1' | h1' <;> rcases not_and_or.mp hm1 with hm1' | hm1'
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')
    · push Not at hm1'; exact hne_m1_I (hm1'.symm.trans hEq2)
    · push Not at h1'; exact hne_1_I (h1'.symm.trans hEq2)
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')

private theorem exists_two_disjoint_discs {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {n₁ n₂ : S}
    (hn₁ : n₁ ∈ discBd D) (hn₂ : n₂ ∈ discBd D) (h12 : n₁ ≠ n₂) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ D ∧ Δ₂ ⊆ D ∧
      n₁ ∈ Δ₁ ∧ n₂ ∉ Δ₁ ∧
      n₂ ∈ Δ₂ ∧ n₁ ∉ Δ₂ ∧
      Δ₁ ∩ Δ₂ = ∅ := by
  obtain ⟨p₃, hp₃, h13, h23⟩ := exists_third_point_in_discBd hD n₁ n₂
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub,
    hn₁_Δ₁, _, hn₂_not_Δ₁, hn₂_D', hp₃_D', hn₁_not_D', hinter1⟩ :=
    exists_two_discs_touching_at_point hD hn₁ hn₂ hp₃ h12 h13 h23
  have hn₂_bdD' : n₂ ∈ discBd D' :=
    disc_inter_discBd_subset_discBd hD hD'_disc hD'_sub ⟨hn₂_D', hn₂⟩
  have hp₃_bdD' : p₃ ∈ discBd D' :=
    disc_inter_discBd_subset_discBd hD hD'_disc hD'_sub ⟨hp₃_D', hp₃⟩
  obtain ⟨p₄, hp₄, h24, h34⟩ := exists_third_point_in_discBd hD'_disc n₂ p₃
  obtain ⟨Δ₂, _, hΔ₂_disc, _, hΔ₂_sub', _,
    hn₂_Δ₂, _, hp₃_not_Δ₂, _, _, _, _⟩ :=
    exists_two_discs_touching_at_point hD'_disc hn₂_bdD' hp₃_bdD' hp₄ h23 h24 h34
  have hΔ₂_sub : Δ₂ ⊆ D := hΔ₂_sub'.trans hD'_sub
  have hn₁_not_Δ₂ : n₁ ∉ Δ₂ := fun h => hn₁_not_D' (hΔ₂_sub' h)
  have hinter : Δ₁ ∩ Δ₂ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx₁, hx₂⟩
    have hxp₃ : x ∈ Δ₁ ∩ D' := ⟨hx₁, hΔ₂_sub' hx₂⟩
    rw [hinter1] at hxp₃
    exact hp₃_not_Δ₂ (hxp₃ ▸ hx₂)
  exact ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
    hn₁_Δ₁, hn₂_not_Δ₁, hn₂_Δ₂, hn₁_not_Δ₂, hinter⟩

private theorem exists_discs_for_splitInternalCell {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : GM17.Painting S) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.C)
    (htc₀_ge2 : 2 ≤ (tilde c₀).ncard)
    {n₁ n₂ : S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ closure c₀ ∧ Δ₂ ⊆ closure c₀ ∧
      Δ₁ ∩ Δ₂ = tilde c₀ \ {n₁, n₂} ∧
      tilde (Δ₁ \ Γ.N) = tilde c₀ \ {n₂} ∧
      tilde (Δ₂ \ Γ.N) = tilde c₀ \ {n₁} := by
  have hD : IsClosedDisc (closure c₀) := Γ.isClosedDisc_closure_cell hc₀
  have htc₀_bd : tilde c₀ ⊆ discBd (closure c₀) := (Γ.cell_disc c₀ hc₀).2.1
  have htc₀_fin : (tilde c₀).Finite := Γ.finite_tilde_cell hc₀
  have htc₀_le3 : (tilde c₀).ncard ≤ 3 := Γ.ncard_tilde_cell_le hc₀
  have htc_diff : ∀ Δ : Set S, IsClosedDisc Δ → Δ ⊆ closure c₀ → tilde (Δ \ Γ.N) = Δ ∩ tilde c₀ := by
    intro Δ hΔ hΔ_sub
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ Γ.finite_N]
    ext x
    simp only [mem_inter_iff, tilde, mem_sdiff]
    exact ⟨fun ⟨hxΔ, hxN⟩ => ⟨hxΔ, hΔ_sub hxΔ, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩,
      fun ⟨hxΔ, hxtc₀⟩ => ⟨hxΔ, Γ.tilde_subset_N hc₀ hxtc₀⟩⟩
  by_cases hex₃ : (tilde c₀ \ {n₁, n₂}).Nonempty
  · obtain ⟨n₃, hn₃_tc, hn₃_not_pair⟩ := hex₃
    have h13 : n₁ ≠ n₃ := fun h => hn₃_not_pair (Or.inl h.symm)
    have h23 : n₂ ≠ n₃ := fun h => hn₃_not_pair (Or.inr h.symm)
    have hsub3 : ({n₁, n₂, n₃} : Set S) ⊆ tilde c₀ := by
      rintro x (rfl | rfl | rfl) <;> assumption
    have hcard3 : ({n₁, n₂, n₃} : Set S).ncard = 3 := by
      rw [ncard_insert_of_notMem, ncard_pair h23]
      rintro (rfl | rfl)
      · exact hne rfl
      · exact h13 rfl
    have htc₀_eq : tilde c₀ = {n₁, n₂, n₃} :=
      (eq_of_subset_of_ncard_le hsub3 (by omega) htc₀_fin).symm
    obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
      hn₁_Δ₁, hn₃_Δ₁, hn₂_not_Δ₁, hn₂_Δ₂, hn₃_Δ₂, hn₁_not_Δ₂, hinter⟩ :=
      exists_two_discs_touching_at_point hD (htc₀_bd hn₁) (htc₀_bd hn₂) (htc₀_bd hn₃_tc) hne h13 h23
    refine ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, ?_, ?_, ?_⟩
    · rw [hinter, htc₀_eq]
      ext x
      simp only [mem_singleton_iff, mem_sdiff, mem_insert_iff]
      constructor
      · rintro rfl
        exact ⟨Or.inr (Or.inr rfl), fun h => by rcases h with rfl | rfl; exact h13 rfl; exact h23 rfl⟩
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact (hnot (Or.inl rfl)).elim
        · exact (hnot (Or.inr rfl)).elim
        · rfl
    · rw [htc_diff Δ₁ hΔ₁_disc hΔ₁_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₁, rfl | rfl | rfl⟩
        · exact ⟨Or.inl rfl, hne⟩
        · exact (hn₂_not_Δ₁ hxΔ₁).elim
        · exact ⟨Or.inr (Or.inr rfl), h23.symm⟩
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact ⟨hn₁_Δ₁, Or.inl rfl⟩
        · exact (hnot rfl).elim
        · exact ⟨hn₃_Δ₁, Or.inr (Or.inr rfl)⟩
    · rw [htc_diff Δ₂ hΔ₂_disc hΔ₂_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₂, rfl | rfl | rfl⟩
        · exact (hn₁_not_Δ₂ hxΔ₂).elim
        · exact ⟨Or.inr (Or.inl rfl), hne.symm⟩
        · exact ⟨Or.inr (Or.inr rfl), h13.symm⟩
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact (hnot rfl).elim
        · exact ⟨hn₂_Δ₂, Or.inr (Or.inl rfl)⟩
        · exact ⟨hn₃_Δ₂, Or.inr (Or.inr rfl)⟩
  · have htc₀_diff_empty : tilde c₀ \ {n₁, n₂} = ∅ := not_nonempty_iff_eq_empty.mp hex₃
    have htc₀_eq : tilde c₀ = {n₁, n₂} := by
      refine Subset.antisymm (sdiff_eq_empty.mp htc₀_diff_empty) ?_
      rintro x (rfl | rfl) <;> assumption
    obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
      hn₁_Δ₁, hn₂_not_Δ₁, hn₂_Δ₂, hn₁_not_Δ₂, hinter⟩ :=
      exists_two_disjoint_discs hD (htc₀_bd hn₁) (htc₀_bd hn₂) hne
    refine ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, ?_, ?_, ?_⟩
    · rw [hinter, htc₀_diff_empty]
    · rw [htc_diff Δ₁ hΔ₁_disc hΔ₁_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₁, rfl | rfl⟩
        · exact ⟨Or.inl rfl, hne⟩
        · exact (hn₂_not_Δ₁ hxΔ₁).elim
      · rintro ⟨rfl | rfl, hnot⟩
        · exact ⟨hn₁_Δ₁, Or.inl rfl⟩
        · exact (hnot rfl).elim
    · rw [htc_diff Δ₂ hΔ₂_disc hΔ₂_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₂, rfl | rfl⟩
        · exact (hn₁_not_Δ₂ hxΔ₂).elim
        · exact ⟨Or.inr rfl, hne.symm⟩
      · rintro ⟨rfl | rfl, hnot⟩
        · exact (hnot rfl).elim
        · exact ⟨hn₂_Δ₂, Or.inr rfl⟩

private theorem exists_truer_of_splitInternalCell
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hdom : π.domγ = π.Γ.N)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    (htc₀_ge2 : 2 ≤ (tilde c₀).ncard)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂)
    {A₁ A₂ : Hypergraph α β} (hA₁_le : A₁ ≤ π.cellGraph c₀) (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hA_union_V : A₁.vertexSet ∪ A₂.vertexSet = (π.cellGraph c₀).vertexSet)
    (hA_union_E : A₁.edgeSet ∪ A₂.edgeSet = (π.cellGraph c₀).edgeSet)
    (hA_disj_E : Disjoint A₁.edgeSet A₂.edgeSet)
    (hA₁_tc : ∀ n ∈ tilde c₀ \ {n₂}, π.nodeVertex n ∈ A₁.vertexSet)
    (hA₂_tc : ∀ n ∈ tilde c₀ \ {n₁}, π.nodeVertex n ∈ A₂.vertexSet)
    (hA₁_not_n₂ : π.nodeVertex n₂ ∉ A₁.vertexSet)
    (hA₂_not_n₁ : π.nodeVertex n₁ ∉ A₂.vertexSet)
    (hA_inter_V : A₁.vertexSet ∩ A₂.vertexSet ⊆ π.nodeVertex '' (tilde c₀ \ {n₁, n₂})) :
    ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ π'.Resembles π ∧ π'.IsTruer π ∧
      ((tilde c₀).ncard = 3 → π'.truth 0 < π.truth 0 ∧
        ∀ w : Set π.S → ℕ, (∀ Θ ∈ cuffs π.S, π.warpAt Θ = w Θ) →
          ∃ ψ : π'.S ≃ₜ π.S, (∀ Θ ∈ cuffs π'.S, ψ '' Θ ∈ cuffs π.S) ∧
            ∀ Θ ∈ cuffs π'.S, π'.warpAt Θ = w (ψ '' Θ)) := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hΔ_inter, htc₁, htc₂⟩ :=
    exists_discs_for_splitInternalCell π.Γ hc₀ htc₀_ge2 hn₁ hn₂ hne
  have hΔ_inter_N : Δ₁ ∩ Δ₂ ⊆ π.Γ.N := by
    rw [hΔ_inter]
    exact sdiff_subset.trans (π.Γ.tilde_subset_N hc₀)
  let c₁ : Set π.S := Δ₁ \ π.Γ.N
  let c₂ : Set π.S := Δ₂ \ π.Γ.N
  have hΔ₁_N_eq : Δ₁ ∩ π.Γ.N = tilde c₀ \ {n₂} := by
    rw [← tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc π.Γ.finite_N, htc₁]
  have hΔ₂_N_eq : Δ₂ ∩ π.Γ.N = tilde c₀ \ {n₁} := by
    rw [← tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc π.Γ.finite_N, htc₂]
  have hΔ₁_bd : Δ₁ ∩ π.Γ.N ⊆ discBd Δ₁ := by
    intro x hx
    have hxtc₀ : x ∈ tilde c₀ := (hΔ₁_N_eq ▸ hx).1
    exact disc_inter_discBd_subset_discBd (π.Γ.isClosedDisc_closure_cell hc₀) hΔ₁_disc hΔ₁_sub
      ⟨hx.1, (π.Γ.cell_disc c₀ hc₀).2.1 hxtc₀⟩
  have hΔ₂_bd : Δ₂ ∩ π.Γ.N ⊆ discBd Δ₂ := by
    intro x hx
    have hxtc₀ : x ∈ tilde c₀ := (hΔ₂_N_eq ▸ hx).1
    exact disc_inter_discBd_subset_discBd (π.Γ.isClosedDisc_closure_cell hc₀) hΔ₂_disc hΔ₂_sub
      ⟨hx.1, (π.Γ.cell_disc c₀ hc₀).2.1 hxtc₀⟩
  have hΔ₁_card : (Δ₁ ∩ π.Γ.N).ncard ≤ 3 := by
    rw [hΔ₁_N_eq]
    exact (ncard_le_ncard sdiff_subset (π.Γ.finite_tilde_cell hc₀)).trans (π.Γ.ncard_tilde_cell_le hc₀)
  have hΔ₂_card : (Δ₂ ∩ π.Γ.N).ncard ≤ 3 := by
    rw [hΔ₂_N_eq]
    exact (ncard_le_ncard sdiff_subset (π.Γ.finite_tilde_cell hc₀)).trans (π.Γ.ncard_tilde_cell_le hc₀)
  let Γ' : GM17.Painting π.S :=
    splitInternalCell π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      Subset.rfl π.Γ.finite_N (by simp) hΔ_inter_N hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card
  have hC' : Γ'.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})) :=
    splitInternalCell_C π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      Subset.rfl π.Γ.finite_N (by simp) hΔ_inter_N hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact sdiff_le_sdiff_right hΔ₁_sub
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact sdiff_le_sdiff_right hΔ₂_sub
  have hc₁_ne : c₁.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset
      (π.Γ.finite_N.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₂_ne : c₂.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset
      (π.Γ.finite_N.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₁_disj_c₂ : Disjoint c₁ c₂ :=
    Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter_N ⟨hx₁, hx₂⟩)
  have hc₁_ne_c₂ : c₁ ≠ c₂ := by
    rcases hc₁_ne with ⟨x, hx⟩
    exact fun h => Set.disjoint_left.mp hc₁_disj_c₂ hx (h ▸ hx)
  have hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₁_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₁_sub_c₀ hx)
  have hc₂_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₂ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₂_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₂_sub_c₀ hx)
  have hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₁_sub_c₀))
  have hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₂_sub_c₀))
  have hc₁_C' : c₁ ∈ Γ'.C := hC'.symm ▸ Or.inl rfl
  have hc₂_C' : c₂ ∈ Γ'.C := hC'.symm ▸ Or.inr (Or.inl rfl)
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c₁ then A₁ else if c = c₂ then A₂ else π.cellGraph c
  have hcellG_c₁ : cellG c₁ = A₁ := by simp [cellG]
  have hcellG_c₂ : cellG c₂ = A₂ := by simp [cellG, hc₁_ne_c₂.symm]
  have hcellG_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG d = π.cellGraph d := fun d hd => by
    simp [cellG, hc₁_not_I₀ d hd, hc₂_not_I₀ d hd]
  have hcellG_le : ∀ c ∈ Γ'.C, cellG c ≤ G := by
    intro c hc
    rw [hC'] at hc
    rcases hc with rfl | rfl | hd
    · rw [hcellG_c₁]; exact hA₁_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG_c₂]; exact hA₂_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG_other c hd]; exact π.cellGraph_le c hd.1
  have hp5_aux : ∀ c ∈ Γ'.C, ¬ (c ∩ bd π.S).Nonempty → ∀ v ∈ (cellG c).vertexSet,
      (∃ d ∈ Γ'.C, d ≠ c ∧ v ∈ (cellG d).vertexSet) → v ∈ π.nodeVertex '' (tilde c ∩ π.domγ) := by
    intro c hc hint v hvc ⟨d, hd, hne_dc, hvd⟩
    rw [hC'] at hc hd
    rcases hc with rfl | rfl | hcI
    · rw [hcellG_c₁] at hvc
      change v ∈ π.nodeVertex '' (tilde c₁ ∩ π.domγ)
      rw [htc₁, hdom, inter_eq_left.mpr (sdiff_subset.trans (π.Γ.tilde_subset_N hc₀))]
      rcases hd with rfl | rfl | hdI
      · exact (hne_dc rfl).elim
      · rw [hcellG_c₂] at hvd
        obtain ⟨n, ⟨hn_tc, hn_not_pair⟩, rfl⟩ := hA_inter_V ⟨hvc, hvd⟩
        exact ⟨n, ⟨hn_tc, fun h => hn_not_pair (Or.inr h)⟩, rfl⟩
      · rw [hcellG_other d hdI] at hvd
        obtain ⟨n, ⟨hn_tc, _⟩, rfl⟩ :=
          π.p5 c₀ hc₀ hint₀ v (hA₁_le.1 hvc) ⟨d, hdI.1, hdI.2, hvd⟩
        have hnn₂ : n ≠ n₂ := fun h => hA₁_not_n₂ (h ▸ hvc)
        exact ⟨n, ⟨hn_tc, hnn₂⟩, rfl⟩
    · rw [hcellG_c₂] at hvc
      change v ∈ π.nodeVertex '' (tilde c₂ ∩ π.domγ)
      rw [htc₂, hdom, inter_eq_left.mpr (sdiff_subset.trans (π.Γ.tilde_subset_N hc₀))]
      rcases hd with rfl | rfl | hdI
      · rw [hcellG_c₁] at hvd
        obtain ⟨n, ⟨hn_tc, hn_not_pair⟩, rfl⟩ := hA_inter_V ⟨hvd, hvc⟩
        exact ⟨n, ⟨hn_tc, fun h => hn_not_pair (Or.inl h)⟩, rfl⟩
      · exact (hne_dc rfl).elim
      · rw [hcellG_other d hdI] at hvd
        obtain ⟨n, ⟨hn_tc, _⟩, rfl⟩ :=
          π.p5 c₀ hc₀ hint₀ v (hA₂_le.1 hvc) ⟨d, hdI.1, hdI.2, hvd⟩
        have hnn₁ : n ≠ n₁ := fun h => hA₂_not_n₁ (h ▸ hvc)
        exact ⟨n, ⟨hn_tc, hnn₁⟩, rfl⟩
    · rw [hcellG_other c hcI] at hvc
      rcases hd with rfl | rfl | hdI
      · rw [hcellG_c₁] at hvd
        exact π.p5 c hcI.1 hint v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₁_le.1 hvd⟩
      · rw [hcellG_c₂] at hvd
        exact π.p5 c hcI.1 hint v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₂_le.1 hvd⟩
      · rw [hcellG_other d hdI] at hvd
        exact π.p5 c hcI.1 hint v hvc ⟨d, hdI.1, hne_dc, hvd⟩
  let π' : Portrayal G :=
    { S := π.S
      top := π.top
      isSurface := π.isSurface
      connected := π.connected
      Γ := Γ'
      cellGraph := cellG
      borderSet := π.borderSet
      domγ := π.domγ
      nodeVertex := π.nodeVertex
      cellGraph_le := hcellG_le
      borderSet_subset := π.borderSet_subset
      domγ_subset := π.domγ_subset
      nodeVertex_mem := π.nodeVertex_mem
      nodeVertex_injOn := π.nodeVertex_injOn
      p1_vertex := fun v hv => by
        obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          rw [← hA_union_V] at hvc
          rcases hvc with hv₁ | hv₂
          · exact ⟨c₁, hc₁_C', hcellG_c₁.symm ▸ hv₁⟩
          · exact ⟨c₂, hc₂_C', hcellG_c₂.symm ▸ hv₂⟩
        · exact ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
            (hcellG_other c ⟨hc, hcc₀⟩).symm ▸ hvc⟩
      p1_edge := fun e he => by
        obtain ⟨c, hc, hec⟩ := π.p1_edge e he
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          rw [← hA_union_E] at hec
          rcases hec with he₁ | he₂
          · exact ⟨c₁, hc₁_C', hcellG_c₁.symm ▸ he₁⟩
          · exact ⟨c₂, hc₂_C', hcellG_c₂.symm ▸ he₂⟩
        · exact ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
            (hcellG_other c ⟨hc, hcc₀⟩).symm ▸ hec⟩
      p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne => by
        rw [hC'] at hd₁ hd₂
        rcases hd₁ with rfl | rfl | hd₁I <;> rcases hd₂ with rfl | rfl | hd₂I
        · exact (hne rfl).elim
        · rw [hcellG_c₁, hcellG_c₂]; exact hA_disj_E
        · rw [hcellG_c₁, hcellG_other d₂ hd₂I]
          exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hA₁_le.2
        · rw [hcellG_c₂, hcellG_c₁]; exact hA_disj_E.symm
        · exact (hne rfl).elim
        · rw [hcellG_c₂, hcellG_other d₂ hd₂I]
          exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hA₂_le.2
        · rw [hcellG_other d₁ hd₁I, hcellG_c₁]
          exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hA₁_le.2
        · rw [hcellG_other d₁ hd₁I, hcellG_c₂]
          exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hA₂_le.2
        · rw [hcellG_other d₁ hd₁I, hcellG_other d₂ hd₂I]
          exact π.p1_disjoint d₁ hd₁I.1 d₂ hd₂I.1 hne
      p2 := fun c hc n hn => by
        rw [hC'] at hc
        rcases hc with rfl | rfl | hcI
        · rw [hcellG_c₁]
          exact hA₁_tc n (htc₁ ▸ hn.1)
        · rw [hcellG_c₂]
          exact hA₂_tc n (htc₂ ▸ hn.1)
        · rw [hcellG_other c hcI]
          exact π.p2 c hcI.1 n hn
      p3_notMem := π.p3_notMem
      p3_subset := fun c hc hbd n hn => by
        rw [hC'] at hc
        rcases hc with rfl | rfl | hcI
        · exact (hint₁ hbd).elim
        · exact (hint₂ hbd).elim
        · rw [hcellG_other c hcI]
          exact π.p3_subset c hcI.1 hbd n hn
      p4_disjoint := π.p4_disjoint
      p4_notMem := π.p4_notMem
      p5 := hp5_aux
      p6 := fun c hc hbd v hvc ⟨d, hd, hne_dc, hvd⟩ => by
        rw [hC'] at hc hd
        rcases hc with rfl | rfl | hcI
        · exact (hint₁ hbd).elim
        · exact (hint₂ hbd).elim
        · rw [hcellG_other c hcI] at hvc
          rcases hd with rfl | rfl | hdI
          · rw [hcellG_c₁] at hvd
            exact π.p6 c hcI.1 hbd v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₁_le.1 hvd⟩
          · rw [hcellG_c₂] at hvd
            exact π.p6 c hcI.1 hbd v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₂_le.1 hvd⟩
          · rw [hcellG_other d hdI] at hvd
            exact π.p6 c hcI.1 hbd v hvc ⟨d, hdI.1, hne_dc, hvd⟩
      p7 := π.p7 }
  have hπ'_central : π'.IsCentral 𝒯 := by
    intro c hc
    change IsSmallWrt 𝒯 (cellG c)
    have hcases : c ∈ insert c₁ (insert c₂ (π.Γ.C \ {c₀})) := hC' ▸ hc
    rcases hcases with rfl | rfl | hcI
    · have hatt_sub : attachments G (cellG c₁) ⊆ π.nodeVertex '' (tilde c₁ ∩ π.domγ) := by
        rintro v ⟨hvc₁, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd, hed⟩ := π'.p1_edge e heG
        have hd_ne : d ≠ c₁ := fun h => he_not (h ▸ hed)
        have hvd : v ∈ (cellG d).vertexSet := by
          have hends := (π'.cellGraph_le d hd).3 e hed
          exact (cellG d).vertex_mem_of_inc (by change v ∈ (cellG d).ends e; rw [← hends]; exact hinc)
        exact hp5_aux c₁ hc₁_C' hint₁ v hvc₁ ⟨d, hd, hd_ne, hvd⟩
      have hfin_tc₁ : (tilde c₁).Finite := Γ'.finite_tilde_cell hc₁_C'
      have hfin_dom : (tilde c₁ ∩ π.domγ).Finite := hfin_tc₁.inter_of_left _
      have hatt_lt : (attachments G (cellG c₁)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub (hfin_dom.image π.nodeVertex)
        have h2 := ncard_image_le (f := π.nodeVertex) hfin_dom
        have h3 := ncard_le_ncard (inter_subset_left : tilde c₁ ∩ π.domγ ⊆ tilde c₁) hfin_tc₁
        have h4 := Γ'.ncard_tilde_cell_le hc₁_C'
        omega
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG_c₁ ▸ hA₁_le) hatt_lt
    · have hatt_sub : attachments G (cellG c₂) ⊆ π.nodeVertex '' (tilde c₂ ∩ π.domγ) := by
        rintro v ⟨hvc₂, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd, hed⟩ := π'.p1_edge e heG
        have hd_ne : d ≠ c₂ := fun h => he_not (h ▸ hed)
        have hvd : v ∈ (cellG d).vertexSet := by
          have hends := (π'.cellGraph_le d hd).3 e hed
          exact (cellG d).vertex_mem_of_inc (by change v ∈ (cellG d).ends e; rw [← hends]; exact hinc)
        exact hp5_aux c₂ hc₂_C' hint₂ v hvc₂ ⟨d, hd, hd_ne, hvd⟩
      have hfin_tc₂ : (tilde c₂).Finite := Γ'.finite_tilde_cell hc₂_C'
      have hfin_dom : (tilde c₂ ∩ π.domγ).Finite := hfin_tc₂.inter_of_left _
      have hatt_lt : (attachments G (cellG c₂)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub (hfin_dom.image π.nodeVertex)
        have h2 := ncard_image_le (f := π.nodeVertex) hfin_dom
        have h3 := ncard_le_ncard (inter_subset_left : tilde c₂ ∩ π.domγ ⊆ tilde c₂) hfin_tc₂
        have h4 := Γ'.ncard_tilde_cell_le hc₂_C'
        omega
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG_c₂ ▸ hA₂_le) hatt_lt
    · rw [hcellG_other c hcI]
      exact hcentral c hcI.1
  have hπ'_warpAt : ∀ Θ ∈ cuffs π.S, π'.warpAt Θ = π.warpAt Θ := by
    intro Θ hΘ
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases hΘ with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hcw_eq : ∀ c ∈ π.Γ.C \ {c₀}, (c ∩ Θ).Nonempty → π'.cellWarp c = π.cellWarp c := by
      intro c hcI _
      change sInf {q | π'.CellWarpLE c q} = sInf {q | π.CellWarpLE c q}
      congr 1; ext q
      change (∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
          (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
          ((π.borderPlus n₁).ncard = q + 1 → (π.borderPlus n₂).ncard = q + 1 →
            Portrayal.LinkagePairs (cellG c).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
              (q + 1) (π.nodeVertex n₁) (π.nodeVertex n₂))) ↔ _
      rw [hcellG_other c hcI]
      rfl
    change sSup {p | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
      sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
    congr 1; ext q
    constructor
    · rintro ⟨c, hc', hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
      rw [hC'] at hc'
      rcases hc' with rfl | rfl | hcI
      · exact (hint₁ hbd_c).elim
      · exact (hint₂ hbd_c).elim
      · exact ⟨c, hcI.1, hcΘ, hcw_eq c hcI hcΘ⟩
    · rintro ⟨c, hc_C, hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
      have hcc₀ : c ≠ c₀ := fun h => hint₀ (h ▸ hbd_c)
      exact ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc_C, hcc₀⟩), hcΘ, (hcw_eq c ⟨hc_C, hcc₀⟩ hcΘ).symm⟩
  have hπ'_res : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
    rw [Homeomorph.refl_apply, image_id]
    exact hπ'_warpAt Θ hΘ
  have htc₀_le3 : (tilde c₀).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc₀
  let k₀ : Fin 6 := ⟨3 - (tilde c₀).ncard, by omega⟩
  have hk₀_lt : π'.truth k₀ < π.truth k₀ := by
    have htc₁_card : (tilde c₁).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₁ = tilde c₀ \ {n₂} from htc₁, ncard_sdiff_singleton_of_mem hn₂]
    have htc₂_card : (tilde c₂).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₂ = tilde c₀ \ {n₁} from htc₂, ncard_sdiff_singleton_of_mem hn₁]
    have hk₀_lt4 : k₀.1 < 4 := by dsimp [k₀]; omega
    simp only [Portrayal.truth, π', hk₀_lt4, ↓reduceIte]
    have hm_eq : 3 - k₀.1 = (tilde c₀).ncard := by dsimp [k₀]; omega
    have hset_eq :
        {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} =
        {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} := by
      rw [hC']
      ext d
      simp only [mem_sep_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
        · omega
        · omega
        · exact ⟨hdI, hint_d, hcard_d⟩
      · rintro ⟨hdI, hint_d, hcard_d⟩
        exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
    rw [hset_eq]
    have hssub : {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} ⊂
        {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} := by
      refine ⟨fun d hd => ⟨hd.1.1, hd.2⟩, fun h => ?_⟩
      have hc₀_mem : c₀ ∈ {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} :=
        ⟨hc₀, hint₀, hm_eq.symm⟩
      exact (h hc₀_mem).1.2 rfl
    exact ncard_lt_ncard hssub (π.Γ.finite_cells.subset fun _ hd => hd.1)
  have hπ'_truer : π'.IsTruer π := by
    have htc₁_card : (tilde c₁).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₁ = tilde c₀ \ {n₂} from htc₁, ncard_sdiff_singleton_of_mem hn₂]
    have htc₂_card : (tilde c₂).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₂ = tilde c₀ \ {n₁} from htc₂, ncard_sdiff_singleton_of_mem hn₁]
    have hset_eq : ∀ m : ℕ, (tilde c₀).ncard ≤ m →
        {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = m} =
        {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = m} := by
      intro m hm
      rw [hC']
      ext d
      simp only [mem_sep_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
        · omega
        · omega
        · exact ⟨hdI, hint_d, hcard_d⟩
      · rintro ⟨hdI, hint_d, hcard_d⟩
        exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
    refine ⟨k₀, fun i hi => ?_, hk₀_lt⟩
    have hi_lt : i.1 < 3 - (tilde c₀).ncard := hi
    have hi4 : i.1 < 4 := by omega
    simp only [Portrayal.truth, π', hi4, ↓reduceIte]
    rw [hset_eq (3 - i.1) (by omega)]
    congr 1; ext d
    simp only [mem_sep_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hd, _⟩, h⟩ => ⟨hd, h⟩,
      fun ⟨hd, hint_d, hcard_d⟩ => ⟨⟨hd, fun hEq => by subst hEq; omega⟩, hint_d, hcard_d⟩⟩
  refine ⟨π', hπ'_central, hπ'_res, hπ'_truer, fun h3 => ⟨?_, fun w hw => ?_⟩⟩
  · have hk0 : k₀ = 0 := by ext; simp [k₀, h3]
    exact hk0 ▸ hk₀_lt
  · refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_, fun Θ hΘ => ?_⟩
    · rwa [Homeomorph.refl_apply, image_id]
    · rw [Homeomorph.refl_apply, image_id, hπ'_warpAt Θ hΘ, hw Θ hΘ]

/-- Strengthened resemblance of portrayals that preserves cuff membership under the homeomorphism,
so that it is manifestly transitive. -/
def ResemblesRefl {α : Type u} {β : Type v} {G : Hypergraph α β} (π₁ π₂ : Portrayal G) : Prop :=
  ∃ ψ : π₁.S ≃ₜ π₂.S, (∀ Θ ∈ cuffs π₁.S, ψ '' Θ ∈ cuffs π₂.S) ∧
    ∀ Θ ∈ cuffs π₁.S, π₁.warpAt Θ = π₂.warpAt (ψ '' Θ)

lemma ResemblesRefl.refl {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G) :
    ResemblesRefl π π := by
  refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_, fun Θ _ => ?_⟩
  · rwa [Homeomorph.refl_apply, image_id]
  · rw [Homeomorph.refl_apply, image_id]

lemma ResemblesRefl.trans {α : Type u} {β : Type v} {G : Hypergraph α β} {π₁ π₂ π₃ : Portrayal G}
    (h12 : ResemblesRefl π₁ π₂) (h23 : ResemblesRefl π₂ π₃) : ResemblesRefl π₁ π₃ := by
  rcases h12 with ⟨ψ₁, hΘ₁, hw₁⟩
  rcases h23 with ⟨ψ₂, hΘ₂, hw₂⟩
  have h_img : ∀ Θ : Set π₁.S, ⇑(ψ₁.trans ψ₂) '' Θ = ⇑ψ₂ '' (⇑ψ₁ '' Θ) := by
    intro Θ; ext x; simp
  refine ⟨ψ₁.trans ψ₂, fun Θ hΘ => ?_, fun Θ hΘ => ?_⟩
  · rw [h_img Θ]
    exact hΘ₂ (ψ₁ '' Θ) (hΘ₁ Θ hΘ)
  · rw [h_img Θ, hw₁ Θ hΘ, hw₂ (ψ₁ '' Θ) (hΘ₁ Θ hΘ)]

lemma ResemblesRefl.to_resembles {α : Type u} {β : Type v} {G : Hypergraph α β} {π₁ π₂ : Portrayal G}
    (h : ResemblesRefl π₁ π₂) : π₁.Resembles π₂ :=
  let ⟨ψ, _, hw⟩ := h; ⟨ψ, hw⟩

/-- Peeling off all edges of a 3-ended internal cell `c₀` whose ends lie in `{x₁, x₃}` into a
2-ended internal cell `{n₁, n₃}`, preserving `IsCentral`, `truth 0`, and `ResemblesRefl`. -/
lemma exists_peel_portrayal {α : Type u} {β : Type v}
    {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hdom : π.domγ = π.Γ.N)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ n₃ : π.S} (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃) :
    ∃ (π₁ : Portrayal G) (c₁ : Set π₁.S) (n₁' n₂' n₃' : π₁.S),
      π₁.IsCentral 𝒯 ∧ π₁.domγ = π₁.Γ.N ∧
      ((∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d) → (∀ n ∈ π₁.Γ.N, ∃ d ∈ π₁.Γ.C, n ∈ tilde d)) ∧
      ResemblesRefl π₁ π ∧ π₁.truth 0 = π.truth 0 ∧
      c₁ ∈ π₁.Γ.C ∧ ¬ (c₁ ∩ bd π₁.S).Nonempty ∧
      tilde c₁ = {n₁', n₂', n₃'} ∧ n₁' ≠ n₂' ∧ n₁' ≠ n₃' ∧ n₂' ≠ n₃' ∧
      π₁.nodeVertex n₁' = π.nodeVertex n₁ ∧
      π₁.nodeVertex n₂' = π.nodeVertex n₂ ∧
      π₁.nodeVertex n₃' = π.nodeVertex n₃ ∧
      π₁.cellGraph c₁ ≤ π.cellGraph c₀ ∧
      (π₁.cellGraph c₁).vertexSet = (π.cellGraph c₀).vertexSet ∧
      ∀ e ∈ (π₁.cellGraph c₁).edgeSet,
        ¬ (π₁.cellGraph c₁).ends e ⊆ {π₁.nodeVertex n₁', π₁.nodeVertex n₃'} := by
  have : T2Space π.S := π.isSurface.2.1
  have hn₁_tc : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc : n₃ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inr rfl)
  have hn₁_N : n₁ ∈ π.Γ.N := π.Γ.tilde_subset_N hc₀ hn₁_tc
  have hn₂_N : n₂ ∈ π.Γ.N := π.Γ.tilde_subset_N hc₀ hn₂_tc
  have hn₃_N : n₃ ∈ π.Γ.N := π.Γ.tilde_subset_N hc₀ hn₃_tc
  have hx₁_mem : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet :=
    π.p2 c₀ hc₀ n₁ ⟨hn₁_tc, hdom ▸ hn₁_N⟩
  have hx₃_mem : π.nodeVertex n₃ ∈ (π.cellGraph c₀).vertexSet :=
    π.p2 c₀ hc₀ n₃ ⟨hn₃_tc, hdom ▸ hn₃_N⟩
  have hcard3 : (tilde c₀).ncard = 3 := by
    rw [htc₀, ncard_insert_of_notMem, ncard_pair h23]
    rintro (rfl | rfl)
    · exact h12 rfl
    · exact h13 rfl
  let B₁ : Hypergraph α β :=
    { vertexSet := (π.cellGraph c₀).vertexSet
      edgeSet := {e ∈ (π.cellGraph c₀).edgeSet |
        ¬ (π.cellGraph c₀).ends e ⊆ {π.nodeVertex n₁, π.nodeVertex n₃}}
      Inc := fun e v => e ∈ (π.cellGraph c₀).edgeSet ∧
        ¬ (π.cellGraph c₀).ends e ⊆ {π.nodeVertex n₁, π.nodeVertex n₃} ∧ (π.cellGraph c₀).Inc e v
      vertex_mem_of_inc := fun _ _ h => (π.cellGraph c₀).vertex_mem_of_inc h.2.2
      edge_mem_of_inc := fun _ _ h => ⟨h.1, h.2.1⟩
      vertexSet_finite := (π.cellGraph c₀).vertexSet_finite
      edgeSet_finite := (π.cellGraph c₀).edgeSet_finite.subset fun _ h => h.1 }
  let B₂ : Hypergraph α β :=
    { vertexSet := {π.nodeVertex n₁, π.nodeVertex n₃}
      edgeSet := {e ∈ (π.cellGraph c₀).edgeSet |
        (π.cellGraph c₀).ends e ⊆ {π.nodeVertex n₁, π.nodeVertex n₃}}
      Inc := fun e v => e ∈ (π.cellGraph c₀).edgeSet ∧
        (π.cellGraph c₀).ends e ⊆ {π.nodeVertex n₁, π.nodeVertex n₃} ∧ (π.cellGraph c₀).Inc e v
      vertex_mem_of_inc := fun _ _ h => h.2.1 h.2.2
      edge_mem_of_inc := fun _ _ h => ⟨h.1, h.2.1⟩
      vertexSet_finite := (finite_singleton _).insert _
      edgeSet_finite := (π.cellGraph c₀).edgeSet_finite.subset fun _ h => h.1 }
  have hB₁_le : B₁ ≤ π.cellGraph c₀ := by
    refine ⟨Subset.rfl, fun e he => he.1, fun e he => ?_⟩
    ext v; exact ⟨fun h => ⟨he.1, he.2, h⟩, fun h => h.2.2⟩
  have hB₂_le : B₂ ≤ π.cellGraph c₀ := by
    refine ⟨?_, fun e he => he.1, fun e he => ?_⟩
    · rintro v (rfl | rfl)
      · exact hx₁_mem
      · exact hx₃_mem
    · ext v; exact ⟨fun h => ⟨he.1, he.2, h⟩, fun h => h.2.2⟩
  have hB_disj : Disjoint B₁.edgeSet B₂.edgeSet :=
    Set.disjoint_left.mpr fun _ he₁ he₂ => he₁.2 he₂.2
  obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hΔ_inter,
    hΔ₁_N, hΔ₂_N, hΔ₁_bdN, hΔ₂_bdN⟩ :=
    exists_discs_for_peel π.Γ hc₀ htc₀ h12 h13 h23
  have hN_sub : π.Γ.N ⊆ π.Γ.N := Subset.rfl
  have hN'_fin : π.Γ.N.Finite := π.Γ.finite_N
  have hN'_diff : π.Γ.N \ π.Γ.N ⊆ Δ₁ ∩ Δ₂ := by simp
  have hΔ_inter_N : Δ₁ ∩ Δ₂ ⊆ π.Γ.N := by
    rw [hΔ_inter]
    rintro x (rfl | rfl)
    · exact hn₁_N
    · exact hn₃_N
  have hΔ₁_card : (Δ₁ ∩ π.Γ.N).ncard = 3 := by
    rw [hΔ₁_N, ← htc₀, hcard3]
  have hΔ₂_card : (Δ₂ ∩ π.Γ.N).ncard = 2 := by
    rw [hΔ₂_N, ncard_pair h13]
  let c₁ : Set π.S := Δ₁ \ π.Γ.N
  let c₂ : Set π.S := Δ₂ \ π.Γ.N
  let Γ₁ : GM17.Painting π.S :=
    splitInternalCell π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter_N hΔ₁_bdN hΔ₂_bdN hΔ₁_card.le (by omega)
  have hC₁ : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})) :=
    splitInternalCell_C π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter_N hΔ₁_bdN hΔ₂_bdN hΔ₁_card.le (by omega)
  have htc₁ : tilde c₁ = {n₁, n₂, n₃} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin, hΔ₁_N]
  have htc₂ : tilde c₂ = {n₁, n₃} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin, hΔ₂_N]
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₁, hxN⟩ => ⟨hΔ₁_sub hx₁, hxN⟩
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₂, hxN⟩ => ⟨hΔ₂_sub hx₂, hxN⟩
  have hc₁_ne : c₁.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset
      (hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₂_ne : c₂.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset
      (hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₁_disj_c₂ : Disjoint c₁ c₂ :=
    Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter_N ⟨hx₁, hx₂⟩)
  have hc₁_ne_c₂ : c₁ ≠ c₂ := by
    rcases hc₁_ne with ⟨x, hx⟩
    exact fun h => Set.disjoint_left.mp hc₁_disj_c₂ hx (h ▸ hx)
  have hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₁_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₁_sub_c₀ hx)
  have hc₂_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₂ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₂_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₂_sub_c₀ hx)
  have hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₁_sub_c₀))
  have hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₂_sub_c₀))
  have hc₁_C₁ : c₁ ∈ Γ₁.C := hC₁.symm ▸ Or.inl rfl
  have hc₂_C₁ : c₂ ∈ Γ₁.C := hC₁.symm ▸ Or.inr (Or.inl rfl)
  let cellG₁ : Set π.S → Hypergraph α β := fun c =>
    if c = c₁ then B₁ else if c = c₂ then B₂ else π.cellGraph c
  have hcellG₁_c₁ : cellG₁ c₁ = B₁ := by simp [cellG₁]
  have hcellG₁_c₂ : cellG₁ c₂ = B₂ := by simp [cellG₁, hc₁_ne_c₂.symm]
  have hcellG₁_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG₁ d = π.cellGraph d := fun d hd => by
    simp [cellG₁, hc₁_not_I₀ d hd, hc₂_not_I₀ d hd]
  have hcellG₁_le : ∀ c ∈ Γ₁.C, cellG₁ c ≤ G := by
    intro c hc
    rw [hC₁] at hc
    rcases hc with rfl | rfl | hd
    · rw [hcellG₁_c₁]; exact hB₁_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG₁_c₂]; exact hB₂_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG₁_other c hd]; exact π.cellGraph_le c hd.1
  have hp5_aux₁ : ∀ c ∈ Γ₁.C, ¬ (c ∩ bd π.S).Nonempty → ∀ w ∈ (cellG₁ c).vertexSet,
      (∃ d ∈ Γ₁.C, d ≠ c ∧ w ∈ (cellG₁ d).vertexSet) → w ∈ π.nodeVertex '' (tilde c ∩ π.Γ.N) := by
    intro c hc hint w hwc ⟨d, hd, hne_dc, hwd⟩
    rw [hC₁] at hc hd
    rcases hc with rfl | rfl | hcI
    · rw [hcellG₁_c₁] at hwc
      rw [htc₁]
      rcases hd with rfl | rfl | hdI
      · exact (hne_dc rfl).elim
      · rw [hcellG₁_c₂] at hwd
        rcases hwd with rfl | rfl
        · exact ⟨n₁, ⟨Or.inl rfl, hn₁_N⟩, rfl⟩
        · exact ⟨n₃, ⟨Or.inr (Or.inr rfl), hn₃_N⟩, rfl⟩
      · rw [hcellG₁_other d hdI] at hwd
        obtain ⟨n, ⟨hn_tc₀, hn_dom⟩, hnw⟩ :=
          π.p5 c₀ hc₀ hint₀ w hwc ⟨d, hdI.1, hdI.2, hwd⟩
        exact ⟨n, ⟨htc₀ ▸ hn_tc₀, hdom ▸ hn_dom⟩, hnw⟩
    · rw [hcellG₁_c₂] at hwc
      rw [htc₂]
      rcases hwc with rfl | rfl
      · exact ⟨n₁, ⟨Or.inl rfl, hn₁_N⟩, rfl⟩
      · exact ⟨n₃, ⟨Or.inr rfl, hn₃_N⟩, rfl⟩
    · rw [hcellG₁_other c hcI] at hwc
      rw [← hdom]
      rcases hd with rfl | rfl | hdI
      · rw [hcellG₁_c₁] at hwd
        exact π.p5 c hcI.1 hint w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₁_le.1 hwd⟩
      · rw [hcellG₁_c₂] at hwd
        exact π.p5 c hcI.1 hint w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₂_le.1 hwd⟩
      · rw [hcellG₁_other d hdI] at hwd
        exact π.p5 c hcI.1 hint w hwc ⟨d, hdI.1, hne_dc, hwd⟩
  let π₁ : Portrayal G :=
    { S := π.S
      top := π.top
      isSurface := π.isSurface
      connected := π.connected
      Γ := Γ₁
      cellGraph := cellG₁
      borderSet := π.borderSet
      domγ := π.Γ.N
      nodeVertex := π.nodeVertex
      cellGraph_le := hcellG₁_le
      borderSet_subset := π.borderSet_subset
      domγ_subset := Subset.rfl
      nodeVertex_mem := fun n hn => π.nodeVertex_mem n (hdom ▸ hn)
      nodeVertex_injOn := fun _ hx _ hy hEq => π.nodeVertex_injOn (hdom ▸ hx) (hdom ▸ hy) hEq
      p1_vertex := fun w hw => by
        obtain ⟨c, hc, hwc⟩ := π.p1_vertex w hw
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ hwc⟩
        · exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
            (hcellG₁_other c ⟨hc, hcc₀⟩).symm ▸ hwc⟩
      p1_edge := fun e he => by
        obtain ⟨c, hc, hec⟩ := π.p1_edge e he
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          by_cases hsub : (π.cellGraph c).ends e ⊆ {π.nodeVertex n₁, π.nodeVertex n₃}
          · exact ⟨c₂, hc₂_C₁, hcellG₁_c₂.symm ▸ ⟨hec, hsub⟩⟩
          · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ ⟨hec, hsub⟩⟩
        · exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
            (hcellG₁_other c ⟨hc, hcc₀⟩).symm ▸ hec⟩
      p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne => by
        rw [hC₁] at hd₁ hd₂
        rcases hd₁ with rfl | rfl | hd₁I <;> rcases hd₂ with rfl | rfl | hd₂I
        · exact (hne rfl).elim
        · rw [hcellG₁_c₁, hcellG₁_c₂]; exact hB_disj
        · rw [hcellG₁_c₁, hcellG₁_other d₂ hd₂I]
          exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hB₁_le.2
        · rw [hcellG₁_c₂, hcellG₁_c₁]; exact hB_disj.symm
        · exact (hne rfl).elim
        · rw [hcellG₁_c₂, hcellG₁_other d₂ hd₂I]
          exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hB₂_le.2
        · rw [hcellG₁_other d₁ hd₁I, hcellG₁_c₁]
          exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hB₁_le.2
        · rw [hcellG₁_other d₁ hd₁I, hcellG₁_c₂]
          exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hB₂_le.2
        · rw [hcellG₁_other d₁ hd₁I, hcellG₁_other d₂ hd₂I]
          exact π.p1_disjoint d₁ hd₁I.1 d₂ hd₂I.1 hne
      p2 := fun c hc n hn => by
        rw [hC₁] at hc
        rcases hc with rfl | rfl | hcI
        · rw [hcellG₁_c₁]
          exact π.p2 c₀ hc₀ n ⟨htc₀.symm ▸ htc₁ ▸ hn.1, hdom ▸ hn.2⟩
        · rw [hcellG₁_c₂]
          have hntc₂ : n ∈ ({n₁, n₃} : Set π.S) := htc₂ ▸ hn.1
          rcases hntc₂ with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rw [hcellG₁_other c hcI]
          exact π.p2 c hcI.1 n ⟨hn.1, hdom ▸ hn.2⟩
      p3_notMem := fun n hn => π.p3_notMem n ⟨hdom ▸ hn.1, hn.2⟩
      p3_subset := fun c hc hbd n hn => by
        rw [hC₁] at hc
        rcases hc with rfl | rfl | hcI
        · exact (hint₁ hbd).elim
        · exact (hint₂ hbd).elim
        · rw [hcellG₁_other c hcI]; exact π.p3_subset c hcI.1 hbd n hn
      p4_disjoint := π.p4_disjoint
      p4_notMem := fun Θ hΘ m₁ hm₁ m₂ hm₂ hnot =>
        π.p4_notMem Θ hΘ m₁ hm₁ m₂ (hdom ▸ hm₂) hnot
      p5 := hp5_aux₁
      p6 := fun c hc hbd w hwc ⟨d, hd, hne_dc, hwd⟩ => by
        rw [hC₁] at hc hd
        rcases hc with rfl | rfl | hcI
        · exact (hint₁ hbd).elim
        · exact (hint₂ hbd).elim
        · rw [hcellG₁_other c hcI] at hwc
          have hw_bp : ∃ n ∈ tilde c, w ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ w = π.nodeVertex n) := by
            rcases hd with rfl | rfl | hdI
            · rw [hcellG₁_c₁] at hwd
              exact π.p6 c hcI.1 hbd w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₁_le.1 hwd⟩
            · rw [hcellG₁_c₂] at hwd
              exact π.p6 c hcI.1 hbd w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₂_le.1 hwd⟩
            · rw [hcellG₁_other d hdI] at hwd
              exact π.p6 c hcI.1 hbd w hwc ⟨d, hdI.1, hne_dc, hwd⟩
          rcases hw_bp with ⟨n, hn_tc, hwn | ⟨hn_dom, hwn⟩⟩
          · exact ⟨n, hn_tc, Or.inl hwn⟩
          · exact ⟨n, hn_tc, Or.inr ⟨hdom ▸ hn_dom, hwn⟩⟩
      p7 := fun Θ hΘ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃ => by
        rw [← hdom] at hw₁ hw₃ ⊢
        exact π.p7 Θ hΘ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃ }
  have hπ₁_central : π₁.IsCentral 𝒯 := by
    intro c hc
    change IsSmallWrt 𝒯 (cellG₁ c)
    have hcases : c ∈ insert c₁ (insert c₂ (π.Γ.C \ {c₀})) := hC₁ ▸ hc
    rcases hcases with rfl | rfl | hcI
    · have hatt_sub : attachments G (cellG₁ c₁) ⊆ π.nodeVertex '' (tilde c₁ ∩ π.Γ.N) := by
        rintro w ⟨hwc₁, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd, hed⟩ := π₁.p1_edge e heG
        have hd_ne : d ≠ c₁ := fun h => he_not (h ▸ hed)
        have hwd : w ∈ (cellG₁ d).vertexSet := by
          have hends := (π₁.cellGraph_le d hd).3 e hed
          exact (cellG₁ d).vertex_mem_of_inc (by change w ∈ (cellG₁ d).ends e; rw [← hends]; exact hinc)
        exact hp5_aux₁ c₁ hc₁_C₁ hint₁ w hwc₁ ⟨d, hd, hd_ne, hwd⟩
      have hfin_tc₁ : (tilde c₁).Finite := Γ₁.finite_tilde_cell hc₁_C₁
      have hfin_dom : (tilde c₁ ∩ π.Γ.N).Finite := hfin_tc₁.inter_of_left _
      have hatt_lt : (attachments G (cellG₁ c₁)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub (hfin_dom.image π.nodeVertex)
        have h2 := ncard_image_le (f := π.nodeVertex) hfin_dom
        have h3 := ncard_le_ncard (inter_subset_left : tilde c₁ ∩ π.Γ.N ⊆ tilde c₁) hfin_tc₁
        have h4 := Γ₁.ncard_tilde_cell_le hc₁_C₁
        omega
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG₁_c₁ ▸ hB₁_le) hatt_lt
    · have hatt_sub : attachments G (cellG₁ c₂) ⊆ π.nodeVertex '' (tilde c₂ ∩ π.Γ.N) := by
        rintro w ⟨hwc₂, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd, hed⟩ := π₁.p1_edge e heG
        have hd_ne : d ≠ c₂ := fun h => he_not (h ▸ hed)
        have hwd : w ∈ (cellG₁ d).vertexSet := by
          have hends := (π₁.cellGraph_le d hd).3 e hed
          exact (cellG₁ d).vertex_mem_of_inc (by change w ∈ (cellG₁ d).ends e; rw [← hends]; exact hinc)
        exact hp5_aux₁ c₂ hc₂_C₁ hint₂ w hwc₂ ⟨d, hd, hd_ne, hwd⟩
      have hfin_tc₂ : (tilde c₂).Finite := Γ₁.finite_tilde_cell hc₂_C₁
      have hfin_dom : (tilde c₂ ∩ π.Γ.N).Finite := hfin_tc₂.inter_of_left _
      have hatt_lt : (attachments G (cellG₁ c₂)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub (hfin_dom.image π.nodeVertex)
        have h2 := ncard_image_le (f := π.nodeVertex) hfin_dom
        have h3 := ncard_le_ncard (inter_subset_left : tilde c₂ ∩ π.Γ.N ⊆ tilde c₂) hfin_tc₂
        have h4 := Γ₁.ncard_tilde_cell_le hc₂_C₁
        omega
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG₁_c₂ ▸ hB₂_le) hatt_lt
    · rw [hcellG₁_other c hcI]
      exact hcentral c hcI.1
  have hΘ_bd : ∀ Θ ∈ cuffs π.S, Θ ⊆ bd π.S := by
    rintro Θ ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hπ₁_warpAt : ∀ Θ ∈ cuffs π.S, π₁.warpAt Θ = π.warpAt Θ := by
    intro Θ hΘ
    have hcw_eq : ∀ c ∈ π.Γ.C \ {c₀}, (c ∩ Θ).Nonempty → π₁.cellWarp c = π.cellWarp c := by
      intro c hcI _
      change sInf {q | π₁.CellWarpLE c q} = sInf {q | π.CellWarpLE c q}
      congr 1; ext q
      have hbp_eq : ∀ n ∈ tilde c, π₁.borderPlus n = π.borderPlus n := by
        intro n _
        ext w
        simp [Portrayal.borderPlus, π₁, hdom]
      constructor <;> intro h n₁' hn₁' n₂' hn₂' hne'
      · have h' := h n₁' hn₁' n₂' hn₂' hne'
        rw [hbp_eq n₁' hn₁', hbp_eq n₂' hn₂'] at h'
        refine ⟨h'.1, h'.2.1, fun h1 h2 => ?_⟩
        have hLP : Portrayal.LinkagePairs (cellG₁ c).skeleton (π.borderPlus n₁') (π.borderPlus n₂')
            (q + 1) (π.nodeVertex n₁') (π.nodeVertex n₂') := h'.2.2 h1 h2
        rwa [hcellG₁_other c hcI] at hLP
      · have h' := h n₁' hn₁' n₂' hn₂' hne'
        rw [hbp_eq n₁' hn₁', hbp_eq n₂' hn₂']
        refine ⟨h'.1, h'.2.1, fun h1 h2 => ?_⟩
        have hLP := h'.2.2 h1 h2
        change Portrayal.LinkagePairs (cellG₁ c).skeleton (π.borderPlus n₁') (π.borderPlus n₂')
          (q + 1) (π.nodeVertex n₁') (π.nodeVertex n₂')
        rwa [hcellG₁_other c hcI]
    change sSup {p | ∃ c ∈ Γ₁.C, (c ∩ Θ).Nonempty ∧ p = π₁.cellWarp c} =
      sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
    congr 1; ext q
    constructor
    · rintro ⟨c, hc', hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ (hΘ_bd Θ hΘ))
      rw [hC₁] at hc'
      rcases hc' with rfl | rfl | hcI
      · exact (hint₁ hbd_c).elim
      · exact (hint₂ hbd_c).elim
      · exact ⟨c, hcI.1, hcΘ, hcw_eq c hcI hcΘ⟩
    · rintro ⟨c, hc_C, hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ (hΘ_bd Θ hΘ))
      have hcc₀ : c ≠ c₀ := fun h => hint₀ (h ▸ hbd_c)
      exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc_C, hcc₀⟩), hcΘ, (hcw_eq c ⟨hc_C, hcc₀⟩ hcΘ).symm⟩
  have htc₁_card : (tilde c₁).ncard = 3 := by
    rw [show tilde c₁ = Δ₁ ∩ π.Γ.N from tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin, hΔ₁_card]
  have htc₂_card : (tilde c₂).ncard = 2 := by
    rw [show tilde c₂ = Δ₂ ∩ π.Γ.N from tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin, hΔ₂_card]
  have hπ₁_truth0 : π₁.truth 0 = π.truth 0 := by
    let S₀ : Set (Set π.S) := {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}
    have hS₀_fin : S₀.Finite := π.Γ.finite_cells.subset fun _ hd => hd.1.1
    have h1 : {c ∈ Γ₁.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3} = insert c₁ S₀ := by
      rw [hC₁]
      ext d
      simp only [S₀, mem_sep_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
        · exact Or.inl rfl
        · omega
        · exact Or.inr ⟨hdI, hint_d, hcard_d⟩
      · rintro (rfl | ⟨hdI, hint_d, hcard_d⟩)
        · exact ⟨Or.inl rfl, hint₁, htc₁_card⟩
        · exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
    have h2 : {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3} = insert c₀ S₀ := by
      ext d
      simp only [S₀, mem_sep_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hd, hint_d, hcard_d⟩
        by_cases h : d = c₀
        · exact Or.inl h
        · exact Or.inr ⟨⟨hd, h⟩, hint_d, hcard_d⟩
      · rintro (rfl | ⟨⟨hd, _⟩, hint_d, hcard_d⟩)
        · exact ⟨hc₀, hint₀, hcard3⟩
        · exact ⟨hd, hint_d, hcard_d⟩
    have hc₁_not_S₀ : c₁ ∉ S₀ := fun h => hc₁_not_I₀ c₁ h.1 rfl
    have hc₀_not_S₀ : c₀ ∉ S₀ := fun h => h.1.2 rfl
    simp only [Portrayal.truth, Fin.val_zero, Nat.sub_zero, Nat.zero_lt_succ, ↓reduceIte]
    change {c ∈ Γ₁.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}.ncard =
      {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}.ncard
    rw [h1, h2, ncard_insert_of_notMem hc₁_not_S₀ hS₀_fin, ncard_insert_of_notMem hc₀_not_S₀ hS₀_fin]
  have hπ₁_res : ResemblesRefl π₁ π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_, fun Θ hΘ => ?_⟩
    · rwa [Homeomorph.refl_apply, image_id]
    · rw [Homeomorph.refl_apply, image_id]
      exact hπ₁_warpAt Θ hΘ
  refine ⟨π₁, c₁, n₁, n₂, n₃, hπ₁_central, rfl, fun hno_iso n hn => ?_,
    hπ₁_res, hπ₁_truth0, hc₁_C₁, hint₁, htc₁, h12, h13, h23, rfl, rfl, rfl,
    ?_, ?_, fun e he => ?_⟩
  · obtain ⟨d, hd, hnd⟩ := hno_iso n hn
    by_cases hdc₀ : d = c₀
    · subst hdc₀
      exact ⟨c₁, hc₁_C₁, htc₁ ▸ htc₀ ▸ hnd⟩
    · exact ⟨d, hC₁.symm ▸ Or.inr (Or.inr ⟨hd, hdc₀⟩), hnd⟩
  · change cellG₁ c₁ ≤ π.cellGraph c₀
    rw [hcellG₁_c₁]
    exact hB₁_le
  · change (cellG₁ c₁).vertexSet = (π.cellGraph c₀).vertexSet
    rw [hcellG₁_c₁]
  · change e ∈ (cellG₁ c₁).edgeSet at he
    change ¬ (cellG₁ c₁).ends e ⊆ {π.nodeVertex n₁, π.nodeVertex n₃}
    rw [hcellG₁_c₁] at he ⊢
    rw [← hB₁_le.3 e he]
    exact he.2

/-- Adding a new internal node `n₀` with `nodeVertex n₀ = v` inside a 3-ended internal cell `c₀`
with `tilde c₀ = {n₁, n₂, n₃}`, splitting `c₀` into a 3-ended cell `c₁` (`tilde c₁ = {n₀, n₁, n₃}`,
`cellGraph c₁ = B₁`) and a 2-ended cell `c₂` (`tilde c₂ = {n₀, n₂}`, `cellGraph c₂ = B₂`),
preserving `IsCentral`, `truth 0`, and `ResemblesRefl`. -/
lemma exists_split_three_two_portrayal {α : Type u} {β : Type v}
    {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hdom : π.domγ = π.Γ.N)
    (hno_iso : ∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ n₃ : π.S} (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    {v : α} (hv : v ∈ (π.cellGraph c₀).vertexSet)
    (hv_ne_n₁ : v ≠ π.nodeVertex n₁) (hv_ne_n₂ : v ≠ π.nodeVertex n₂) (hv_ne_n₃ : v ≠ π.nodeVertex n₃)
    {B₁ B₂ : Hypergraph α β} (hsep : IsSeparation (π.cellGraph c₀) B₁ B₂)
    (hV12 : (B₁ ∩ B₂).vertexSet = {v})
    (hn₁_B₁ : π.nodeVertex n₁ ∈ B₁.vertexSet)
    (hn₃_B₁ : π.nodeVertex n₃ ∈ B₁.vertexSet)
    (hn₂_B₂ : π.nodeVertex n₂ ∈ B₂.vertexSet) :
    ∃ (π₁ : Portrayal G) (c₁ : Set π₁.S) (n₀ n₁' n₃' : π₁.S),
      π₁.IsCentral 𝒯 ∧ π₁.domγ = π₁.Γ.N ∧
      (∀ n ∈ π₁.Γ.N, ∃ d ∈ π₁.Γ.C, n ∈ tilde d) ∧
      ResemblesRefl π₁ π ∧ π₁.truth 0 = π.truth 0 ∧
      c₁ ∈ π₁.Γ.C ∧ ¬ (c₁ ∩ bd π₁.S).Nonempty ∧
      tilde c₁ = {n₀, n₁', n₃'} ∧ n₀ ≠ n₁' ∧ n₀ ≠ n₃' ∧ n₁' ≠ n₃' ∧
      π₁.nodeVertex n₀ = v ∧
      π₁.nodeVertex n₁' = π.nodeVertex n₁ ∧
      π₁.nodeVertex n₃' = π.nodeVertex n₃ ∧
      π₁.cellGraph c₁ = B₁ := by
  have : T2Space π.S := π.isSurface.2.1
  have hn₁_tc : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc : n₃ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inr rfl)
  have hcard3 : (tilde c₀).ncard = 3 := by
    rw [htc₀, ncard_insert_of_notMem, ncard_pair h23]
    rintro (rfl | rfl)
    · exact h12 rfl
    · exact h13 rfl
  have hB₁_le : B₁ ≤ π.cellGraph c₀ := hsep.left_le
  have hB₂_le : B₂ ≤ π.cellGraph c₀ := hsep.right_le
  have hB_disj : Disjoint B₁.edgeSet B₂.edgeSet :=
    Set.disjoint_left.mpr fun e he₁ he₂ => by
      have : e ∈ (B₁ ∩ B₂).edgeSet := ⟨he₁, he₂⟩
      rw [hsep.edgeSet_inter_eq] at this
      exact this
  have hv_not_tc₀ : ∀ n ∈ tilde c₀, v ≠ π.nodeVertex n := by
    rw [htc₀]
    rintro n (rfl | rfl | rfl)
    · exact hv_ne_n₁
    · exact hv_ne_n₂
    · exact hv_ne_n₃
  have hv_not_other : ∀ d ∈ π.Γ.C, d ≠ c₀ → v ∉ (π.cellGraph d).vertexSet := by
    intro d hd hne hvd
    obtain ⟨n, ⟨hn_tc, _⟩, hEq⟩ := π.p5 c₀ hc₀ hint₀ v hv ⟨d, hd, hne, hvd⟩
    exact hv_not_tc₀ n hn_tc hEq.symm
  have hv_not_nodeVertex : ∀ n ∈ π.Γ.N, v ≠ π.nodeVertex n := by
    intro n hn hEq
    by_cases hn_tc₀ : n ∈ tilde c₀
    · exact hv_not_tc₀ n hn_tc₀ hEq
    · obtain ⟨d, hd_C, hn_td⟩ := hno_iso n hn
      have hd_ne : d ≠ c₀ := fun h => hn_tc₀ (h ▸ hn_td)
      exact hv_not_other d hd_C hd_ne (hEq ▸ π.p2 d hd_C n ⟨hn_td, hdom ▸ hn⟩)
  have hv_not_borderSet : ∀ n ∈ π.Γ.N ∩ bd π.S, v ∉ π.borderSet n := by
    rintro n ⟨hnN, hnbd⟩ hvb
    let Θ := connectedComponentIn (bd π.S) n
    have hΘ : Θ ∈ cuffs π.S := ⟨n, hnbd, rfl⟩
    have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
    set k := (π.Γ.N ∩ Θ).ncard
    obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration Θ k) := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hn_Θ : n ∈ π.Γ.N ∩ Θ := ⟨hnN, mem_connectedComponentIn hnbd⟩
    rw [← E.range_node] at hn_Θ
    rcases hn_Θ with ⟨i, hi_eq⟩
    let d := E.cell i
    have hd_mem : d ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := E.range_cell ▸ ⟨i, rfl⟩
    have hΘ_sub_bd : Θ ⊆ bd π.S := connectedComponentIn_subset (bd π.S) n
    have hd_bd : (d ∩ bd π.S).Nonempty := hd_mem.2.mono (inter_subset_inter_right _ hΘ_sub_bd)
    have hn_td : n ∈ tilde d := by
      rw [← hi_eq, E.cell_tilde i]
      exact Or.inl rfl
    have hd_ne : d ≠ c₀ := fun h => hint₀ (h ▸ hd_bd)
    exact hv_not_other d hd_mem.1 hd_ne (π.p3_subset d hd_mem.1 hd_bd n hn_td hvb)
  obtain ⟨n₀, hn₀_c₀, Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hΔ_inter,
    hΔ₁_N', hΔ₂_N', hΔ₁_bdN', hΔ₂_bdN'⟩ :=
    exists_discs_for_9_2 π.Γ hc₀ htc₀ h12 h13 h23
  have hn₀_not_N : n₀ ∉ π.Γ.N := (π.Γ.cell_subset_diff hc₀ hn₀_c₀).2
  have hn₀_not_bd : n₀ ∉ bd π.S := fun hbd => hint₀ ⟨n₀, hn₀_c₀, hbd⟩
  have hn₀_not_tc₀ : n₀ ∉ tilde c₀ := fun h => hn₀_not_N (π.Γ.tilde_subset_N hc₀ h)
  have hn₀_ne_n₁ : n₀ ≠ n₁ := fun h => hn₀_not_tc₀ (h ▸ hn₁_tc)
  have hn₀_ne_n₂ : n₀ ≠ n₂ := fun h => hn₀_not_tc₀ (h ▸ hn₂_tc)
  have hn₀_ne_n₃ : n₀ ≠ n₃ := fun h => hn₀_not_tc₀ (h ▸ hn₃_tc)
  let N' : Set π.S := insert n₀ π.Γ.N
  have hN_sub : π.Γ.N ⊆ N' := subset_insert n₀ π.Γ.N
  have hN'_fin : N'.Finite := π.Γ.finite_N.insert n₀
  have hN'_diff : N' \ π.Γ.N ⊆ Δ₁ ∩ Δ₂ := by
    rw [hΔ_inter]
    rintro x ⟨rfl | hxN, hx_not_N⟩
    · rfl
    · exact (hx_not_N hxN).elim
  have hΔ_inter_N' : Δ₁ ∩ Δ₂ ⊆ N' := by
    rw [hΔ_inter]
    rintro x rfl
    exact Or.inl rfl
  have hΔ₁_card : (Δ₁ ∩ N').ncard = 3 := by
    rw [hΔ₁_N', ncard_insert_of_notMem, ncard_pair h13]
    rintro (rfl | rfl)
    · exact hn₀_ne_n₁ rfl
    · exact hn₀_ne_n₃ rfl
  have hΔ₂_card : (Δ₂ ∩ N').ncard = 2 := by
    rw [hΔ₂_N', ncard_pair hn₀_ne_n₂]
  let c₁ : Set π.S := Δ₁ \ N'
  let c₂ : Set π.S := Δ₂ \ N'
  let Γ₁ : GM17.Painting π.S :=
    splitInternalCell π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter_N' hΔ₁_bdN' hΔ₂_bdN' hΔ₁_card.le (by omega)
  have hC₁ : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})) :=
    splitInternalCell_C π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter_N' hΔ₁_bdN' hΔ₂_bdN' hΔ₁_card.le (by omega)
  have htc₁ : tilde c₁ = {n₀, n₁, n₃} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin, hΔ₁_N']
  have htc₂ : tilde c₂ = {n₀, n₂} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin, hΔ₂_N']
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₁, hxN'⟩ => ⟨hΔ₁_sub hx₁, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₂, hxN'⟩ => ⟨hΔ₂_sub hx₂, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₁_ne : c₁.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset
      (hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₂_ne : c₂.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset
      (hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₁_disj_c₂ : Disjoint c₁ c₂ :=
    Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter_N' ⟨hx₁, hx₂⟩)
  have hc₁_ne_c₂ : c₁ ≠ c₂ := by
    rcases hc₁_ne with ⟨x, hx⟩
    exact fun h => Set.disjoint_left.mp hc₁_disj_c₂ hx (h ▸ hx)
  have hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₁_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₁_sub_c₀ hx)
  have hc₂_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₂ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₂_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₂_sub_c₀ hx)
  have hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₁_sub_c₀))
  have hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₂_sub_c₀))
  have hc₁_C₁ : c₁ ∈ Γ₁.C := hC₁.symm ▸ Or.inl rfl
  have hc₂_C₁ : c₂ ∈ Γ₁.C := hC₁.symm ▸ Or.inr (Or.inl rfl)
  let cellG₁ : Set π.S → Hypergraph α β := fun c =>
    if c = c₁ then B₁ else if c = c₂ then B₂ else π.cellGraph c
  let nodeV₁ : π.S → α := fun n => if n = n₀ then v else π.nodeVertex n
  have hcellG₁_c₁ : cellG₁ c₁ = B₁ := by simp [cellG₁]
  have hcellG₁_c₂ : cellG₁ c₂ = B₂ := by simp [cellG₁, hc₁_ne_c₂.symm]
  have hcellG₁_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG₁ d = π.cellGraph d := fun d hd => by
    simp [cellG₁, hc₁_not_I₀ d hd, hc₂_not_I₀ d hd]
  have hnodeV₁_n₀ : nodeV₁ n₀ = v := by simp [nodeV₁]
  have hnodeV₁_other : ∀ n ∈ π.Γ.N, nodeV₁ n = π.nodeVertex n := fun n hn => by
    have hne : n ≠ n₀ := fun h => hn₀_not_N (h ▸ hn)
    simp [nodeV₁, hne]
  have hbd_N' : N' ∩ bd π.S = π.Γ.N ∩ bd π.S := by
    ext x
    simp only [N', mem_inter_iff, mem_insert_iff]
    exact ⟨fun ⟨h, hbd⟩ => ⟨h.resolve_left (fun hEq => hn₀_not_bd (hEq ▸ hbd)), hbd⟩,
      fun ⟨hxN, hbd⟩ => ⟨Or.inr hxN, hbd⟩⟩
  have hcellG₁_le : ∀ c ∈ Γ₁.C, cellG₁ c ≤ G := by
    intro c hc
    rw [hC₁] at hc
    rcases hc with rfl | rfl | hd
    · rw [hcellG₁_c₁]; exact hB₁_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG₁_c₂]; exact hB₂_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG₁_other c hd]; exact π.cellGraph_le c hd.1
  have hv_mem_B₁ : v ∈ B₁.vertexSet := by
    have : v ∈ (B₁ ∩ B₂).vertexSet := by rw [hV12]; rfl
    exact this.1
  have hv_mem_B₂ : v ∈ B₂.vertexSet := by
    have : v ∈ (B₁ ∩ B₂).vertexSet := by rw [hV12]; rfl
    exact this.2
  have hp5_aux₁ : ∀ c ∈ Γ₁.C, ¬ (c ∩ bd π.S).Nonempty → ∀ w ∈ (cellG₁ c).vertexSet,
      (∃ d ∈ Γ₁.C, d ≠ c ∧ w ∈ (cellG₁ d).vertexSet) → w ∈ nodeV₁ '' (tilde c ∩ N') := by
    intro c hc hint w hwc ⟨d, hd, hne_dc, hwd⟩
    rw [hC₁] at hc hd
    rcases hc with rfl | rfl | hcI
    · rw [hcellG₁_c₁] at hwc
      rw [htc₁]
      rcases hd with rfl | rfl | hdI
      · exact (hne_dc rfl).elim
      · rw [hcellG₁_c₂] at hwd
        have hw_v : w = v := by
          have : w ∈ (B₁ ∩ B₂).vertexSet := ⟨hwc, hwd⟩
          rwa [hV12, mem_singleton_iff] at this
        subst hw_v
        exact ⟨n₀, ⟨Or.inl rfl, Or.inl rfl⟩, hnodeV₁_n₀⟩
      · rw [hcellG₁_other d hdI] at hwd
        obtain ⟨n, ⟨hn_tc₀, hn_dom⟩, hnw⟩ :=
          π.p5 c₀ hc₀ hint₀ w (hB₁_le.1 hwc) ⟨d, hdI.1, hdI.2, hwd⟩
        have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
        rw [htc₀] at hn_tc₀
        rcases hn_tc₀ with hEq | hEq | hEq
        · exact ⟨n, ⟨Or.inr (Or.inl hEq), Or.inr hnN⟩, (hnodeV₁_other n hnN).trans hnw⟩
        · exfalso
          have : π.nodeVertex n₂ ∈ (B₁ ∩ B₂).vertexSet := ⟨hEq ▸ hnw ▸ hwc, hn₂_B₂⟩
          rw [hV12, mem_singleton_iff] at this
          exact hv_ne_n₂ this.symm
        · exact ⟨n, ⟨Or.inr (Or.inr hEq), Or.inr hnN⟩, (hnodeV₁_other n hnN).trans hnw⟩
    · rw [hcellG₁_c₂] at hwc
      rw [htc₂]
      rcases hd with rfl | rfl | hdI
      · rw [hcellG₁_c₁] at hwd
        have hw_v : w = v := by
          have : w ∈ (B₁ ∩ B₂).vertexSet := ⟨hwd, hwc⟩
          rwa [hV12, mem_singleton_iff] at this
        subst hw_v
        exact ⟨n₀, ⟨Or.inl rfl, Or.inl rfl⟩, hnodeV₁_n₀⟩
      · exact (hne_dc rfl).elim
      · rw [hcellG₁_other d hdI] at hwd
        obtain ⟨n, ⟨hn_tc₀, hn_dom⟩, hnw⟩ :=
          π.p5 c₀ hc₀ hint₀ w (hB₂_le.1 hwc) ⟨d, hdI.1, hdI.2, hwd⟩
        have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
        rw [htc₀] at hn_tc₀
        rcases hn_tc₀ with hEq | hEq | hEq
        · exfalso
          have : π.nodeVertex n₁ ∈ (B₁ ∩ B₂).vertexSet := ⟨hn₁_B₁, hEq ▸ hnw ▸ hwc⟩
          rw [hV12, mem_singleton_iff] at this
          exact hv_ne_n₁ this.symm
        · exact ⟨n, ⟨Or.inr hEq, Or.inr hnN⟩, (hnodeV₁_other n hnN).trans hnw⟩
        · exfalso
          have : π.nodeVertex n₃ ∈ (B₁ ∩ B₂).vertexSet := ⟨hn₃_B₁, hEq ▸ hnw ▸ hwc⟩
          rw [hV12, mem_singleton_iff] at this
          exact hv_ne_n₃ this.symm
    · rw [hcellG₁_other c hcI] at hwc
      have hsub : π.nodeVertex '' (tilde c ∩ π.domγ) ⊆ nodeV₁ '' (tilde c ∩ N') := by
        rintro _ ⟨n, ⟨hn_tc, hn_dom⟩, rfl⟩
        have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
        exact ⟨n, ⟨hn_tc, Or.inr hnN⟩, hnodeV₁_other n hnN⟩
      apply hsub
      rcases hd with rfl | rfl | hdI
      · rw [hcellG₁_c₁] at hwd
        exact π.p5 c hcI.1 hint w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₁_le.1 hwd⟩
      · rw [hcellG₁_c₂] at hwd
        exact π.p5 c hcI.1 hint w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₂_le.1 hwd⟩
      · rw [hcellG₁_other d hdI] at hwd
        exact π.p5 c hcI.1 hint w hwc ⟨d, hdI.1, hne_dc, hwd⟩
  have hΘ_bd : ∀ Θ ∈ cuffs π.S, Θ ⊆ bd π.S := by
    rintro Θ ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hN'_Θ : ∀ Θ ∈ cuffs π.S, N' ∩ Θ = π.Γ.N ∩ Θ := by
    intro Θ hΘ
    ext x
    simp only [N', mem_inter_iff, mem_insert_iff]
    exact ⟨fun ⟨hx, hxΘ⟩ => ⟨hx.resolve_left (fun hEq => hn₀_not_bd (hEq ▸ hΘ_bd Θ hΘ hxΘ)), hxΘ⟩,
      fun ⟨hxN, hxΘ⟩ => ⟨Or.inr hxN, hxΘ⟩⟩
  let π₁ : Portrayal G :=
    { S := π.S
      top := π.top
      isSurface := π.isSurface
      connected := π.connected
      Γ := Γ₁
      cellGraph := cellG₁
      borderSet := π.borderSet
      domγ := N'
      nodeVertex := nodeV₁
      cellGraph_le := hcellG₁_le
      borderSet_subset := fun n hn => π.borderSet_subset n (hbd_N' ▸ hn)
      domγ_subset := Subset.rfl
      nodeVertex_mem := fun n hn => by
        rcases hn with rfl | hnN
        · rw [hnodeV₁_n₀]; exact (π.cellGraph_le c₀ hc₀).1 hv
        · rw [hnodeV₁_other n hnN]; exact π.nodeVertex_mem n (hdom ▸ hnN)
      nodeVertex_injOn := fun x hx y hy hEq => by
        rcases hx with rfl | hxN <;> rcases hy with rfl | hyN
        · rfl
        · rw [hnodeV₁_n₀, hnodeV₁_other y hyN] at hEq
          exact (hv_not_nodeVertex y hyN hEq).elim
        · rw [hnodeV₁_other x hxN, hnodeV₁_n₀] at hEq
          exact (hv_not_nodeVertex x hxN hEq.symm).elim
        · rw [hnodeV₁_other x hxN, hnodeV₁_other y hyN] at hEq
          exact π.nodeVertex_injOn (hdom ▸ hxN) (hdom ▸ hyN) hEq
      p1_vertex := fun w hw => by
        obtain ⟨c, hc, hwc⟩ := π.p1_vertex w hw
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          have hwc_union : w ∈ (B₁ ∪ B₂).vertexSet := hsep.union_eq ▸ hwc
          rcases hwc_union with hw₁ | hw₂
          · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ hw₁⟩
          · exact ⟨c₂, hc₂_C₁, hcellG₁_c₂.symm ▸ hw₂⟩
        · exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
            (hcellG₁_other c ⟨hc, hcc₀⟩).symm ▸ hwc⟩
      p1_edge := fun e he => by
        obtain ⟨c, hc, hec⟩ := π.p1_edge e he
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          have hec_union : e ∈ (B₁ ∪ B₂).edgeSet := hsep.union_eq ▸ hec
          rcases hec_union with he₁ | he₂
          · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ he₁⟩
          · exact ⟨c₂, hc₂_C₁, hcellG₁_c₂.symm ▸ he₂⟩
        · exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
            (hcellG₁_other c ⟨hc, hcc₀⟩).symm ▸ hec⟩
      p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne => by
        rw [hC₁] at hd₁ hd₂
        rcases hd₁ with rfl | rfl | hd₁I <;> rcases hd₂ with rfl | rfl | hd₂I
        · exact (hne rfl).elim
        · rw [hcellG₁_c₁, hcellG₁_c₂]
          exact hB_disj
        · rw [hcellG₁_c₁, hcellG₁_other d₂ hd₂I]
          exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hB₁_le.2
        · rw [hcellG₁_c₂, hcellG₁_c₁]
          exact hB_disj.symm
        · exact (hne rfl).elim
        · rw [hcellG₁_c₂, hcellG₁_other d₂ hd₂I]
          exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hB₂_le.2
        · rw [hcellG₁_other d₁ hd₁I, hcellG₁_c₁]
          exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hB₁_le.2
        · rw [hcellG₁_other d₁ hd₁I, hcellG₁_c₂]
          exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hB₂_le.2
        · rw [hcellG₁_other d₁ hd₁I, hcellG₁_other d₂ hd₂I]
          exact π.p1_disjoint d₁ hd₁I.1 d₂ hd₂I.1 hne
      p2 := fun c hc n hn => by
        rw [hC₁] at hc
        rcases hc with rfl | rfl | hcI
        · rw [hcellG₁_c₁]
          have hntc₁ : n ∈ ({n₀, n₁, n₃} : Set π.S) := htc₁ ▸ hn.1
          rcases hntc₁ with hEq | hEq | hEq
          · rw [hEq, hnodeV₁_n₀]; exact hv_mem_B₁
          · rw [hEq, hnodeV₁_other n₁ (π.Γ.tilde_subset_N hc₀ hn₁_tc)]; exact hn₁_B₁
          · rw [hEq, hnodeV₁_other n₃ (π.Γ.tilde_subset_N hc₀ hn₃_tc)]; exact hn₃_B₁
        · rw [hcellG₁_c₂]
          have hntc₂ : n ∈ ({n₀, n₂} : Set π.S) := htc₂ ▸ hn.1
          rcases hntc₂ with hEq | hEq
          · rw [hEq, hnodeV₁_n₀]; exact hv_mem_B₂
          · rw [hEq, hnodeV₁_other n₂ (π.Γ.tilde_subset_N hc₀ hn₂_tc)]; exact hn₂_B₂
        · rw [hcellG₁_other c hcI]
          have hnN : n ∈ π.Γ.N := π.Γ.tilde_subset_N hcI.1 hn.1
          rw [hnodeV₁_other n hnN]
          exact π.p2 c hcI.1 n ⟨hn.1, hdom ▸ hnN⟩
      p3_notMem := fun n hn => by
        have hn' : n ∈ π.Γ.N ∩ bd π.S := hbd_N' ▸ hn
        rw [hnodeV₁_other n hn'.1]
        exact π.p3_notMem n ⟨hdom ▸ hn'.1, hn'.2⟩
      p3_subset := fun c hc hbd n hn => by
        rw [hC₁] at hc
        rcases hc with rfl | rfl | hcI
        · exact (hint₁ hbd).elim
        · exact (hint₂ hbd).elim
        · rw [hcellG₁_other c hcI]
          exact π.p3_subset c hcI.1 hbd n hn
      p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne m₁ hm₁ m₂ hm₂ =>
        π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne m₁ (hN'_Θ Θ₁ hΘ₁ ▸ hm₁) m₂ (hN'_Θ Θ₂ hΘ₂ ▸ hm₂)
      p4_notMem := fun Θ hΘ m₁ hm₁ m₂ hm₂ hnot => by
        have hm₁' : m₁ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hm₁
        rcases hm₂ with hEq | hm₂N
        · rw [hEq, hnodeV₁_n₀]
          exact hv_not_borderSet m₁ ⟨hm₁'.1, hΘ_bd Θ hΘ hm₁'.2⟩
        · rw [hnodeV₁_other m₂ hm₂N]
          exact π.p4_notMem Θ hΘ m₁ hm₁' m₂ (hdom ▸ hm₂N) hnot
      p5 := hp5_aux₁
      p6 := fun c hc hbd w hwc ⟨d, hd, hne_dc, hwd⟩ => by
        rw [hC₁] at hc hd
        rcases hc with rfl | rfl | hcI
        · exact (hint₁ hbd).elim
        · exact (hint₂ hbd).elim
        · rw [hcellG₁_other c hcI] at hwc
          have hw_bp : ∃ n ∈ tilde c, w ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ w = π.nodeVertex n) := by
            rcases hd with rfl | rfl | hdI
            · rw [hcellG₁_c₁] at hwd
              exact π.p6 c hcI.1 hbd w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₁_le.1 hwd⟩
            · rw [hcellG₁_c₂] at hwd
              exact π.p6 c hcI.1 hbd w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hB₂_le.1 hwd⟩
            · rw [hcellG₁_other d hdI] at hwd
              exact π.p6 c hcI.1 hbd w hwc ⟨d, hdI.1, hne_dc, hwd⟩
          rcases hw_bp with ⟨n, hn_tc, hwn | ⟨hn_dom, hwn⟩⟩
          · exact ⟨n, hn_tc, Or.inl hwn⟩
          · have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
            exact ⟨n, hn_tc, Or.inr ⟨Or.inr hnN, hwn.trans (hnodeV₁_other n hnN).symm⟩⟩
      p7 := fun Θ hΘ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃ => by
        have hm₁' : m₁ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hm₁
        have hm₂' : m₂ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hm₂
        have hm₃' : m₃ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hm₃
        have hm₄' : m₄ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hm₄
        have hbp_iff : ∀ m ∈ π.Γ.N ∩ Θ,
            (w ∈ π.borderSet m ∨ (m ∈ N' ∧ w = nodeV₁ m)) ↔
            (w ∈ π.borderSet m ∨ (m ∈ π.domγ ∧ w = π.nodeVertex m)) := by
          rintro m ⟨hmN, _⟩
          have hmN' : m ∈ N' := Or.inr hmN
          have hmdom : m ∈ π.domγ := hdom ▸ hmN
          simp [hmN', hmdom, hnodeV₁_other m hmN]
        have hw₁' := (hbp_iff m₁ hm₁').mp hw₁
        have hw₃' := (hbp_iff m₃ hm₃').mp hw₃
        rcases π.p7 Θ hΘ m₁ hm₁' m₂ hm₂' m₃ hm₃' m₄ hm₄' hord w hw₁' hw₃' with hw₂' | hw₄'
        · exact Or.inl ((hbp_iff m₂ hm₂').mpr hw₂')
        · exact Or.inr ((hbp_iff m₄ hm₄').mpr hw₄') }
  have hπ₁_central : π₁.IsCentral 𝒯 := by
    intro c hc
    change IsSmallWrt 𝒯 (cellG₁ c)
    have hcases : c ∈ insert c₁ (insert c₂ (π.Γ.C \ {c₀})) := hC₁ ▸ hc
    rcases hcases with rfl | rfl | hcI
    · have hatt_sub : attachments G (cellG₁ c₁) ⊆ nodeV₁ '' (tilde c₁ ∩ N') := by
        rintro w ⟨hwc₁, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd, hed⟩ := π₁.p1_edge e heG
        have hd_ne : d ≠ c₁ := fun h => he_not (h ▸ hed)
        have hwd : w ∈ (cellG₁ d).vertexSet := by
          have hends := (π₁.cellGraph_le d hd).3 e hed
          exact (cellG₁ d).vertex_mem_of_inc (by change w ∈ (cellG₁ d).ends e; rw [← hends]; exact hinc)
        exact hp5_aux₁ c₁ hc₁_C₁ hint₁ w hwc₁ ⟨d, hd, hd_ne, hwd⟩
      have hfin_tc₁ : (tilde c₁).Finite := Γ₁.finite_tilde_cell hc₁_C₁
      have hfin_dom : (tilde c₁ ∩ N').Finite := hfin_tc₁.inter_of_left _
      have hatt_lt : (attachments G (cellG₁ c₁)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub (hfin_dom.image nodeV₁)
        have h2 := ncard_image_le (f := nodeV₁) hfin_dom
        have h3 := ncard_le_ncard (inter_subset_left : tilde c₁ ∩ N' ⊆ tilde c₁) hfin_tc₁
        have h4 := Γ₁.ncard_tilde_cell_le hc₁_C₁
        omega
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG₁_c₁ ▸ hB₁_le) hatt_lt
    · have hatt_sub : attachments G (cellG₁ c₂) ⊆ nodeV₁ '' (tilde c₂ ∩ N') := by
        rintro w ⟨hwc₂, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd, hed⟩ := π₁.p1_edge e heG
        have hd_ne : d ≠ c₂ := fun h => he_not (h ▸ hed)
        have hwd : w ∈ (cellG₁ d).vertexSet := by
          have hends := (π₁.cellGraph_le d hd).3 e hed
          exact (cellG₁ d).vertex_mem_of_inc (by change w ∈ (cellG₁ d).ends e; rw [← hends]; exact hinc)
        exact hp5_aux₁ c₂ hc₂_C₁ hint₂ w hwc₂ ⟨d, hd, hd_ne, hwd⟩
      have hfin_tc₂ : (tilde c₂).Finite := Γ₁.finite_tilde_cell hc₂_C₁
      have hfin_dom : (tilde c₂ ∩ N').Finite := hfin_tc₂.inter_of_left _
      have hatt_lt : (attachments G (cellG₁ c₂)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub (hfin_dom.image nodeV₁)
        have h2 := ncard_image_le (f := nodeV₁) hfin_dom
        have h3 := ncard_le_ncard (inter_subset_left : tilde c₂ ∩ N' ⊆ tilde c₂) hfin_tc₂
        have h4 := Γ₁.ncard_tilde_cell_le hc₂_C₁
        omega
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG₁_c₂ ▸ hB₂_le) hatt_lt
    · rw [hcellG₁_other c hcI]
      exact hcentral c hcI.1
  have hπ₁_warpAt : ∀ Θ ∈ cuffs π.S, π₁.warpAt Θ = π.warpAt Θ := by
    intro Θ hΘ
    have hcw_eq : ∀ c ∈ π.Γ.C \ {c₀}, (c ∩ Θ).Nonempty → π₁.cellWarp c = π.cellWarp c := by
      intro c hcI _
      change sInf {q | π₁.CellWarpLE c q} = sInf {q | π.CellWarpLE c q}
      congr 1; ext q
      have hbp_eq : ∀ n ∈ tilde c, π₁.borderPlus n = π.borderPlus n := by
        intro n hn_tc
        have hnN : n ∈ π.Γ.N := π.Γ.tilde_subset_N hcI.1 hn_tc
        have hnN' : n ∈ N' := Or.inr hnN
        have hndom : n ∈ π.domγ := hdom ▸ hnN
        ext w
        simp [Portrayal.borderPlus, π₁, hnN', hndom, hnodeV₁_other n hnN]
      have hnv_eq : ∀ n ∈ tilde c, nodeV₁ n = π.nodeVertex n :=
        fun n hn_tc => hnodeV₁_other n (π.Γ.tilde_subset_N hcI.1 hn_tc)
      constructor <;> intro h n₁' hn₁' n₂' hn₂' hne'
      · have h' := h n₁' hn₁' n₂' hn₂' hne'
        rw [hbp_eq n₁' hn₁', hbp_eq n₂' hn₂'] at h'
        refine ⟨h'.1, h'.2.1, fun h1 h2 => ?_⟩
        have hLP : Portrayal.LinkagePairs (cellG₁ c).skeleton (π.borderPlus n₁') (π.borderPlus n₂')
            (q + 1) (nodeV₁ n₁') (nodeV₁ n₂') := h'.2.2 h1 h2
        rw [hcellG₁_other c hcI, hnv_eq n₁' hn₁', hnv_eq n₂' hn₂'] at hLP
        exact hLP
      · have h' := h n₁' hn₁' n₂' hn₂' hne'
        rw [hbp_eq n₁' hn₁', hbp_eq n₂' hn₂']
        refine ⟨h'.1, h'.2.1, fun h1 h2 => ?_⟩
        have hLP := h'.2.2 h1 h2
        change Portrayal.LinkagePairs (cellG₁ c).skeleton (π.borderPlus n₁') (π.borderPlus n₂')
          (q + 1) (nodeV₁ n₁') (nodeV₁ n₂')
        rw [hcellG₁_other c hcI, hnv_eq n₁' hn₁', hnv_eq n₂' hn₂']
        exact hLP
    change sSup {p | ∃ c ∈ Γ₁.C, (c ∩ Θ).Nonempty ∧ p = π₁.cellWarp c} =
      sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
    congr 1; ext q
    constructor
    · rintro ⟨c, hc', hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ (hΘ_bd Θ hΘ))
      rw [hC₁] at hc'
      rcases hc' with rfl | rfl | hcI
      · exact (hint₁ hbd_c).elim
      · exact (hint₂ hbd_c).elim
      · exact ⟨c, hcI.1, hcΘ, hcw_eq c hcI hcΘ⟩
    · rintro ⟨c, hc_C, hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ (hΘ_bd Θ hΘ))
      have hcc₀ : c ≠ c₀ := fun h => hint₀ (h ▸ hbd_c)
      exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc_C, hcc₀⟩), hcΘ, (hcw_eq c ⟨hc_C, hcc₀⟩ hcΘ).symm⟩
  have htc₁_card : (tilde c₁).ncard = 3 := by
    rw [show tilde c₁ = Δ₁ ∩ N' from tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin, hΔ₁_card]
  have htc₂_card : (tilde c₂).ncard = 2 := by
    rw [show tilde c₂ = Δ₂ ∩ N' from tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin, hΔ₂_card]
  have hπ₁_truth0 : π₁.truth 0 = π.truth 0 := by
    let S₀ : Set (Set π.S) := {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}
    have hS₀_fin : S₀.Finite := π.Γ.finite_cells.subset fun _ hd => hd.1.1
    have h1 : {c ∈ Γ₁.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3} = insert c₁ S₀ := by
      rw [hC₁]
      ext d
      simp only [S₀, mem_sep_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
        · exact Or.inl rfl
        · omega
        · exact Or.inr ⟨hdI, hint_d, hcard_d⟩
      · rintro (rfl | ⟨hdI, hint_d, hcard_d⟩)
        · exact ⟨Or.inl rfl, hint₁, htc₁_card⟩
        · exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
    have h2 : {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3} = insert c₀ S₀ := by
      ext d
      simp only [S₀, mem_sep_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hd, hint_d, hcard_d⟩
        by_cases h : d = c₀
        · exact Or.inl h
        · exact Or.inr ⟨⟨hd, h⟩, hint_d, hcard_d⟩
      · rintro (rfl | ⟨⟨hd, _⟩, hint_d, hcard_d⟩)
        · exact ⟨hc₀, hint₀, hcard3⟩
        · exact ⟨hd, hint_d, hcard_d⟩
    have hc₁_not_S₀ : c₁ ∉ S₀ := fun h => hc₁_not_I₀ c₁ h.1 rfl
    have hc₀_not_S₀ : c₀ ∉ S₀ := fun h => h.1.2 rfl
    simp only [Portrayal.truth, Fin.val_zero, Nat.sub_zero, Nat.zero_lt_succ, ↓reduceIte]
    change {c ∈ Γ₁.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}.ncard =
      {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}.ncard
    rw [h1, h2, ncard_insert_of_notMem hc₁_not_S₀ hS₀_fin, ncard_insert_of_notMem hc₀_not_S₀ hS₀_fin]
  have hπ₁_res : ResemblesRefl π₁ π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_, fun Θ hΘ => ?_⟩
    · rwa [Homeomorph.refl_apply, image_id]
    · rw [Homeomorph.refl_apply, image_id]
      exact hπ₁_warpAt Θ hΘ
  refine ⟨π₁, c₁, n₀, n₁, n₃, hπ₁_central, rfl, fun n hn => ?_,
    hπ₁_res, hπ₁_truth0, hc₁_C₁, hint₁, htc₁, hn₀_ne_n₁, hn₀_ne_n₃, h13,
    hnodeV₁_n₀, hnodeV₁_other n₁ (π.Γ.tilde_subset_N hc₀ hn₁_tc),
    hnodeV₁_other n₃ (π.Γ.tilde_subset_N hc₀ hn₃_tc), hcellG₁_c₁⟩
  rcases hn with hEq | hnN
  · rw [hEq]
    exact ⟨c₁, hc₁_C₁, htc₁ ▸ Or.inl rfl⟩
  · obtain ⟨d, hd, hnd⟩ := hno_iso n hnN
    by_cases hdc₀ : d = c₀
    · subst hdc₀
      rw [htc₀] at hnd
      rcases hnd with hEq | hEq | hEq
      · rw [hEq]; exact ⟨c₁, hc₁_C₁, htc₁ ▸ Or.inr (Or.inl rfl)⟩
      · rw [hEq]; exact ⟨c₂, hc₂_C₁, htc₂ ▸ Or.inr rfl⟩
      · rw [hEq]; exact ⟨c₁, hc₁_C₁, htc₁ ▸ Or.inr (Or.inr rfl)⟩
    · exact ⟨d, hC₁.symm ▸ Or.inr (Or.inr ⟨hd, hdc₀⟩), hnd⟩

/-- Monotonicity of `deleteVertices` with respect to the subhypergraph order `≤`. -/
lemma deleteVertices_mono {α : Type u} {β : Type v} {H₁ H₂ : Hypergraph α β}
    (hle : H₁ ≤ H₂) (X : Set α) :
    H₁.deleteVertices X ≤ H₂.deleteVertices X := by
  refine ⟨sdiff_le_sdiff_right hle.1, fun e he => ⟨hle.2 he.1, fun w hw hinc => ?_⟩, fun e he => ?_⟩
  · have hends := hle.3 e he.1
    have hinc₁ : w ∈ H₁.ends e := hends ▸ hinc
    exact he.2 w hw hinc₁
  · have hends := hle.3 e he.1
    ext v
    simp only [Hypergraph.ends, Hypergraph.deleteVertices, mem_ofPred_eq]
    constructor
    · rintro ⟨hinc₂, hnot₂⟩
      have hinc₁ : H₁.Inc e v := by
        change v ∈ H₁.ends e; rw [← hends]; exact hinc₂
      exact ⟨hinc₁, he.2⟩
    · rintro ⟨hinc₁, _⟩
      have hinc₂ : H₂.Inc e v := by
        change v ∈ H₂.ends e; rw [hends]; exact hinc₁
      refine ⟨hinc₂, fun w hw hincw => he.2 w hw ?_⟩
      change w ∈ H₁.ends e; rw [← hends]; exact hincw

/-- If a finite set `S` has `S.ncard ≤ 2` and contains two distinct elements `x ≠ y`, then
`S = {x, y}`. -/
lemma eq_pair_of_mem_of_ncard_le_two {α : Type u} {S : Set α} (hfin : S.Finite)
    (hcard : S.ncard ≤ 2) {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    S = {x, y} := by
  have hsub : ({x, y} : Set α) ⊆ S := by
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  have hcard_pair : ({x, y} : Set α).ncard = 2 := ncard_pair hne
  exact (eq_of_subset_of_ncard_le hsub (by omega) hfin).symm

/-- Inductive helper for 3-ended internal cells: if `(π.cellGraph c₀) \ {x₃}` has vertex set
indexed by an injective sequence `v₀, ..., v_{k+1}` from `x₁` to `x₂` such that adjacency in
`((π.cellGraph c₀) \ {x₃}).skeleton` only occurs between consecutive indices, then there is a
`𝒯`-central portrayal `π'` resembling `π` with `π'.truth 0 < π.truth 0`. -/
lemma exists_truer_of_three_ended_path_minus_vertex {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG_graph : G.IsGraph)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ) :
    ∀ (k : ℕ) (π : Portrayal G),
      π.IsCentral 𝒯 → π.domγ = π.Γ.N →
      (∀ n ∈ π.Γ.N, ∃ d ∈ π.Γ.C, n ∈ tilde d) →
      ∀ {c₀ : Set π.S}, c₀ ∈ π.Γ.C → ¬ (c₀ ∩ bd π.S).Nonempty →
      ∀ {n₁ n₂ n₃ : π.S}, tilde c₀ = {n₁, n₂, n₃} →
      n₁ ≠ n₂ → n₁ ≠ n₃ → n₂ ≠ n₃ →
      ∀ (v : Fin (k + 2) → α), Function.Injective v →
      v 0 = π.nodeVertex n₁ →
      v ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = π.nodeVertex n₂ →
      ((π.cellGraph c₀).deleteVertices {π.nodeVertex n₃}).vertexSet = range v →
      (∀ i j : Fin (k + 2),
        ((π.cellGraph c₀).deleteVertices {π.nodeVertex n₃}).skeleton.Adj (v i) (v j) →
          (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)) →
      ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ ResemblesRefl π' π ∧ π'.truth 0 < π.truth 0
  | k, π, hcentral, hdom, hno_iso, c₀, hc₀, hint₀, n₁, n₂, n₃, htc₀, h12, h13, h23,
    v, hv_inj, hv0, hvm, hV, hAdj => by
    obtain ⟨π₁, c₁, n₁', n₂', n₃', hπ₁_central, hdom₁, hno_iso₁_imp, hres₁, htruth₁,
      hc₁, hint₁, htc₁, h12', h13', h23', hx₁_eq, hx₂_eq, hx₃_eq, hle₁, hV₁, hpeel⟩ :=
      exists_peel_portrayal h𝒯 hθ π hcentral hdom hc₀ hint₀ htc₀ h12 h13 h23
    have hno_iso₁ : ∀ n ∈ π₁.Γ.N, ∃ d ∈ π₁.Γ.C, n ∈ tilde d := hno_iso₁_imp hno_iso
    let H₁ := π₁.cellGraph c₁
    let x₁ := π₁.nodeVertex n₁'
    let x₂ := π₁.nodeVertex n₂'
    let x₃ := π₁.nodeVertex n₃'
    let v₁ := v ⟨1, by omega⟩
    have hn₁'_tc : n₁' ∈ tilde c₁ := htc₁ ▸ Or.inl rfl
    have hn₂'_tc : n₂' ∈ tilde c₁ := htc₁ ▸ Or.inr (Or.inl rfl)
    have hn₃'_tc : n₃' ∈ tilde c₁ := htc₁ ▸ Or.inr (Or.inr rfl)
    have hn₁'_dom : n₁' ∈ π₁.domγ := hdom₁ ▸ π₁.Γ.tilde_subset_N hc₁ hn₁'_tc
    have hn₂'_dom : n₂' ∈ π₁.domγ := hdom₁ ▸ π₁.Γ.tilde_subset_N hc₁ hn₂'_tc
    have hn₃'_dom : n₃' ∈ π₁.domγ := hdom₁ ▸ π₁.Γ.tilde_subset_N hc₁ hn₃'_tc
    have hx₁_H₁ : x₁ ∈ H₁.vertexSet := π₁.p2 c₁ hc₁ n₁' ⟨hn₁'_tc, hn₁'_dom⟩
    have hx₂_H₁ : x₂ ∈ H₁.vertexSet := π₁.p2 c₁ hc₁ n₂' ⟨hn₂'_tc, hn₂'_dom⟩
    have hx₃_H₁ : x₃ ∈ H₁.vertexSet := π₁.p2 c₁ hc₁ n₃' ⟨hn₃'_tc, hn₃'_dom⟩
    have hx12 : x₁ ≠ x₂ := fun h => h12' (π₁.nodeVertex_injOn hn₁'_dom hn₂'_dom h)
    have hx13 : x₁ ≠ x₃ := fun h => h13' (π₁.nodeVertex_injOn hn₁'_dom hn₃'_dom h)
    have hx23 : x₂ ≠ x₃ := fun h => h23' (π₁.nodeVertex_injOn hn₂'_dom hn₃'_dom h)
    have hv0' : v 0 = x₁ := hv0.trans hx₁_eq.symm
    have hvm' : v ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = x₂ := hvm.trans hx₂_eq.symm
    have hV_del₁ : (H₁.deleteVertices {x₃}).vertexSet = range v := by
      change H₁.vertexSet \ {x₃} = range v
      rw [hV₁, show x₃ = π.nodeVertex n₃ from hx₃_eq]
      exact hV
    have hv₁_del : v₁ ∈ (H₁.deleteVertices {x₃}).vertexSet := by
      rw [hV_del₁]; exact ⟨⟨1, by omega⟩, rfl⟩
    have hv₁_H₁ : v₁ ∈ H₁.vertexSet := hv₁_del.1
    have hv₁_ne_x₃ : v₁ ≠ x₃ := by
      intro hEq
      exact hv₁_del.2 (mem_singleton_iff.mpr hEq)
    have hv₁_ne_x₁ : v₁ ≠ x₁ := by
      rw [← hv0']
      intro hEq
      have hval := congrArg Fin.val (hv_inj hEq)
      change 1 = 0 at hval
      omega
    have hAdj₁ : ∀ i j : Fin (k + 2),
        (H₁.deleteVertices {x₃}).skeleton.Adj (v i) (v j) → (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
      intro i j hadj
      apply hAdj i j
      have hmono : H₁.deleteVertices {x₃} ≤ (π.cellGraph c₀).deleteVertices {π.nodeVertex n₃} := by
        rw [show x₃ = π.nodeVertex n₃ from hx₃_eq]
        exact deleteVertices_mono hle₁ {π.nodeVertex n₃}
      rcases hadj with ⟨hne, e, hi, hj⟩
      have he_mem : e ∈ (H₁.deleteVertices {x₃}).edgeSet :=
        (H₁.deleteVertices {x₃}).edge_mem_of_inc hi
      have hends := hmono.3 e he_mem
      refine ⟨hne, e, ?_, ?_⟩
      · change v i ∈ ((π.cellGraph c₀).deleteVertices {π.nodeVertex n₃}).ends e
        rw [hends]; exact hi
      · change v j ∈ ((π.cellGraph c₀).deleteVertices {π.nodeVertex n₃}).ends e
        rw [hends]; exact hj
    have h_inc_x₁ : ∀ e ∈ H₁.edgeSet, H₁.Inc e x₁ → H₁.ends e = {x₁, v₁} := by
      intro e he hx₁_inc
      have hH₁_G : H₁ ≤ G := π₁.cellGraph_le c₁ hc₁
      have heG : e ∈ G.edgeSet := hH₁_G.2 he
      have hends_G : G.ends e = H₁.ends e := hH₁_G.3 e he
      have hcard_le2 : (H₁.ends e).ncard ≤ 2 := hends_G ▸ (hG_graph e heG).2
      have hfin_ends : (H₁.ends e).Finite :=
        H₁.vertexSet_finite.subset fun _ hw => H₁.vertex_mem_of_inc hw
      have hnot_sub : ¬ H₁.ends e ⊆ {x₁, x₃} := hpeel e he
      obtain ⟨y, hy_end, hy_not⟩ := not_subset.mp hnot_sub
      have hy_ne_x₁ : y ≠ x₁ := fun h => hy_not (Or.inl h)
      have hy_ne_x₃ : y ≠ x₃ := fun h => hy_not (Or.inr h)
      have hends_eq : H₁.ends e = {x₁, y} :=
        eq_pair_of_mem_of_ncard_le_two hfin_ends hcard_le2 hx₁_inc hy_end hy_ne_x₁.symm
      have hx₃_not_end : ¬ H₁.Inc e x₃ := by
        intro hx₃_inc
        have : x₃ ∈ ({x₁, y} : Set α) := hends_eq ▸ hx₃_inc
        rcases this with hEq | hEq
        · exact hx13 hEq.symm
        · exact hy_ne_x₃ hEq.symm
      have hy_del : y ∈ (H₁.deleteVertices {x₃}).vertexSet :=
        ⟨H₁.vertex_mem_of_inc hy_end, fun h => hy_ne_x₃ (mem_singleton_iff.mp h)⟩
      rw [hV_del₁] at hy_del
      rcases hy_del with ⟨j, rfl⟩
      have hadj : (H₁.deleteVertices {x₃}).skeleton.Adj (v 0) (v j) := by
        refine ⟨hv0'.symm ▸ hy_ne_x₁.symm, e, ?_, ?_⟩
        · rw [hv0']
          exact ⟨hx₁_inc, fun w hw => by rwa [mem_singleton_iff.mp hw]⟩
        · exact ⟨hy_end, fun w hw => by rwa [mem_singleton_iff.mp hw]⟩
      have hj1 : j = ⟨1, by omega⟩ := by
        have hstep := hAdj₁ 0 j hadj
        have h0 : (0 : Fin (k + 2)).1 = 0 := rfl
        rw [h0] at hstep
        apply Fin.ext
        change j.1 = 1
        omega
      rw [hj1] at hends_eq
      exact hends_eq
    let B₁ : Hypergraph α β := H₁.deleteVertices {x₁}
    let B₂ : Hypergraph α β :=
      { vertexSet := {x₁, v₁}
        edgeSet := {e ∈ H₁.edgeSet | H₁.Inc e x₁}
        Inc := fun e w => H₁.Inc e x₁ ∧ H₁.Inc e w
        vertex_mem_of_inc := fun e w h => by
          have he : e ∈ H₁.edgeSet := H₁.edge_mem_of_inc h.1
          have hends := h_inc_x₁ e he h.1
          change w ∈ ({x₁, v₁} : Set α)
          rw [← hends]
          exact h.2
        edge_mem_of_inc := fun _ _ h => ⟨H₁.edge_mem_of_inc h.1, h.1⟩
        vertexSet_finite := (finite_singleton _).insert _
        edgeSet_finite := H₁.edgeSet_finite.subset fun _ h => h.1 }
    have hB₁_le : B₁ ≤ H₁ := by
      refine ⟨sdiff_subset, fun _ h => h.1, fun e he => ?_⟩
      ext w
      exact ⟨fun hw => ⟨hw, he.2⟩, fun hw => hw.1⟩
    have hB₂_le : B₂ ≤ H₁ := by
      refine ⟨?_, fun _ h => h.1, fun e he => ?_⟩
      · rintro w (rfl | rfl)
        · exact hx₁_H₁
        · exact hv₁_H₁
      · ext w
        exact ⟨fun hw => ⟨he.2, hw⟩, fun hw => hw.2⟩
    have hB_union_V : B₁.vertexSet ∪ B₂.vertexSet = H₁.vertexSet := by
      refine Subset.antisymm (union_subset hB₁_le.1 hB₂_le.1) fun w hw => ?_
      by_cases hwx₁ : w = x₁
      · exact Or.inr (Or.inl hwx₁)
      · exact Or.inl ⟨hw, hwx₁⟩
    have hB_union_E : B₁.edgeSet ∪ B₂.edgeSet = H₁.edgeSet := by
      refine Subset.antisymm (union_subset hB₁_le.2 hB₂_le.2) fun e he => ?_
      by_cases hex₁ : H₁.Inc e x₁
      · exact Or.inr ⟨he, hex₁⟩
      · exact Or.inl ⟨he, fun w hw => by rwa [mem_singleton_iff.mp hw]⟩
    have hB_disj_E : Disjoint B₁.edgeSet B₂.edgeSet := by
      refine Set.disjoint_left.mpr fun e he₁ he₂ => ?_
      exact he₁.2 x₁ rfl he₂.2
    have hB_inter_V : (B₁ ∩ B₂).vertexSet = {v₁} := by
      ext w
      simp only [Inter.inter, B₁, B₂, Hypergraph.deleteVertices, mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, hne⟩, rfl | rfl⟩
        · exact (hne rfl).elim
        · rfl
      · rintro rfl
        exact ⟨⟨hv₁_H₁, hv₁_ne_x₁⟩, Or.inr rfl⟩
    have hx₂_B₁ : x₂ ∈ B₁.vertexSet := ⟨hx₂_H₁, hx12.symm⟩
    have hx₃_B₁ : x₃ ∈ B₁.vertexSet := ⟨hx₃_H₁, hx13.symm⟩
    have hx₁_B₂ : x₁ ∈ B₂.vertexSet := Or.inl rfl
    by_cases hk0 : k = 0
    · have hv₁_eq_x₂ : v₁ = x₂ := by
        rw [← hvm']
        apply congrArg v
        apply Fin.ext
        change 1 = k + 1
        omega
      have hcard3 : (tilde c₁).ncard = 3 := by
        rw [htc₁, ncard_insert_of_notMem, ncard_pair h23']
        rintro (rfl | rfl)
        · exact h12' rfl
        · exact h13' rfl
      obtain ⟨π', hπ'_central, _, _, h3_imp⟩ :=
        exists_truer_of_splitInternalCell h𝒯 hθ π₁ hπ₁_central hdom₁ hc₁ hint₁
          (by omega : 2 ≤ (tilde c₁).ncard) hn₁'_tc hn₃'_tc h13' hB₂_le hB₁_le
          ((Set.union_comm B₂.vertexSet B₁.vertexSet).trans hB_union_V)
          ((Set.union_comm B₂.edgeSet B₁.edgeSet).trans hB_union_E) hB_disj_E.symm
          (by
            rintro n ⟨hn_tc, hn_ne₃⟩
            rw [htc₁] at hn_tc
            rcases hn_tc with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr hv₁_eq_x₂.symm
            · exact (hn_ne₃ rfl).elim)
          (by
            rintro n ⟨hn_tc, hn_ne₁⟩
            rw [htc₁] at hn_tc
            rcases hn_tc with rfl | rfl | rfl
            · exact (hn_ne₁ rfl).elim
            · exact hx₂_B₁
            · exact hx₃_B₁)
          (by
            rintro (hEq | hEq)
            · exact hx13 hEq.symm
            · exact hv₁_ne_x₃ hEq.symm)
          (fun h => h.2 rfl)
          (by
            rintro w ⟨hw₂, hw₁⟩
            have hw_v₁ : w ∈ (B₁ ∩ B₂).vertexSet := ⟨hw₁, hw₂⟩
            rw [hB_inter_V, mem_singleton_iff] at hw_v₁
            rw [hw_v₁, hv₁_eq_x₂]
            exact ⟨n₂', ⟨hn₂'_tc, fun h => by
              rcases h with rfl | rfl
              · exact h12' rfl
              · exact h23' rfl⟩, rfl⟩)
      obtain ⟨htruth', hres_fn⟩ := h3_imp hcard3
      obtain ⟨ψ, hψ_cuffs, hψ_warp⟩ := hres_fn π₁.warpAt (fun _ _ => rfl)
      have hres' : ResemblesRefl π' π₁ := ⟨ψ, hψ_cuffs, hψ_warp⟩
      exact ⟨π', hπ'_central, hres'.trans hres₁, htruth₁ ▸ htruth'⟩
    · let k' := k - 1
      have hv₁_ne_x₂ : v₁ ≠ x₂ := by
        rw [← hvm']
        intro hEq
        have hval := congrArg Fin.val (hv_inj hEq)
        change 1 = k + 1 at hval
        omega
      have hsep_B : H₁.IsSeparation B₁ B₂ := by
        refine ⟨hB₁_le, hB₂_le, ?_, ?_⟩
        · refine Hypergraph.ext hB_union_V hB_union_E ?_
          funext e w
          apply propext
          constructor
          · rintro (h₁ | h₂)
            · exact h₁.1
            · exact h₂.2
          · intro hinc
            by_cases hex₁ : H₁.Inc e x₁
            · exact Or.inr ⟨hex₁, hinc⟩
            · exact Or.inl ⟨hinc, fun u hu => by rwa [mem_singleton_iff.mp hu]⟩
        · rw [Set.disjoint_iff_inter_eq_empty] at hB_disj_E
          exact hB_disj_E
      have htc₁_swap : tilde c₁ = {n₂', n₁', n₃'} := by rw [htc₁, insert_comm]
      obtain ⟨π₂, c₂, n₀, n₂'', n₃'', hπ₂_central, hdom₂, hno_iso₂, hres₂, htruth₂,
        hc₂, hint₂, htc₂, hn₀_ne_n₂'', hn₀_ne_n₃'', hn₂''_ne_n₃'',
        hnode_n₀, hnode_n₂'', hnode_n₃'', hcellG₂⟩ :=
        exists_split_three_two_portrayal h𝒯 hθ π₁ hπ₁_central hdom₁ hno_iso₁ hc₁ hint₁
          htc₁_swap (Ne.symm h12') h23' h13' hv₁_H₁ hv₁_ne_x₂ hv₁_ne_x₁ hv₁_ne_x₃
          hsep_B hB_inter_V hx₂_B₁ hx₃_B₁ hx₁_B₂
      let v' : Fin (k' + 2) → α := fun i => v ⟨i.1 + 1, by omega⟩
      have hv'_inj : Function.Injective v' := by
        intro i j hEq
        have := hv_inj hEq
        have hval := congrArg Fin.val this
        dsimp at hval
        ext; omega
      have hv'0 : v' 0 = π₂.nodeVertex n₀ := hnode_n₀.symm
      have hv'm : v' ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ = π₂.nodeVertex n₂'' := by
        have hidx : (⟨(⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ : Fin (k' + 2)).1 + 1, by omega⟩ : Fin (k + 2)) =
            ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := by
          ext; dsimp; omega
        change v ⟨(⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ : Fin (k' + 2)).1 + 1, _⟩ = π₂.nodeVertex n₂''
        rw [hidx, hvm', hnode_n₂'']
      have hV' : ((π₂.cellGraph c₂).deleteVertices {π₂.nodeVertex n₃''}).vertexSet = range v' := by
        change (π₂.cellGraph c₂).vertexSet \ {π₂.nodeVertex n₃''} = range v'
        rw [hcellG₂, hnode_n₃'']
        change (H₁.vertexSet \ {x₁}) \ {x₃} = range v'
        ext w
        simp only [mem_sdiff, mem_singleton_iff, mem_range]
        constructor
        · rintro ⟨⟨hw_H₁, hw_ne_x₁⟩, hw_ne_x₃⟩
          have hw_del : w ∈ (H₁.deleteVertices {x₃}).vertexSet := ⟨hw_H₁, hw_ne_x₃⟩
          rw [hV_del₁] at hw_del
          rcases hw_del with ⟨j, rfl⟩
          have hj0 : j.1 ≠ 0 := by
            intro hj0
            have hj_eq : j = 0 := by ext; exact hj0
            exact hw_ne_x₁ (hj_eq ▸ hv0')
          exact ⟨⟨j.1 - 1, by omega⟩, by dsimp [v']; congr 1; ext; dsimp; omega⟩
        · rintro ⟨i, rfl⟩
          have hi_del : v' i ∈ (H₁.deleteVertices {x₃}).vertexSet := by
            rw [hV_del₁]; exact ⟨⟨i.1 + 1, by omega⟩, rfl⟩
          refine ⟨⟨hi_del.1, ?_⟩, hi_del.2⟩
          rw [← hv0']
          intro hEq
          have := hv_inj hEq
          have hval := congrArg Fin.val this
          dsimp at hval
          omega
      have hAdj' : ∀ i j : Fin (k' + 2),
          ((π₂.cellGraph c₂).deleteVertices {π₂.nodeVertex n₃''}).skeleton.Adj (v' i) (v' j) →
            (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
        intro i j hadj
        have hmono : (π₂.cellGraph c₂).deleteVertices {π₂.nodeVertex n₃''} ≤
            H₁.deleteVertices {x₃} := by
          rw [hcellG₂, hnode_n₃'']
          exact deleteVertices_mono hB₁_le {x₃}
        rcases hadj with ⟨hne, e, hi, hj⟩
        have he_mem := ((π₂.cellGraph c₂).deleteVertices {π₂.nodeVertex n₃''}).edge_mem_of_inc hi
        have hends := hmono.3 e he_mem
        have hadj₁ : (H₁.deleteVertices {x₃}).skeleton.Adj (v ⟨i.1 + 1, by omega⟩) (v ⟨j.1 + 1, by omega⟩) := by
          refine ⟨hne, e, ?_, ?_⟩
          · change v' i ∈ (H₁.deleteVertices {x₃}).ends e; rw [hends]; exact hi
          · change v' j ∈ (H₁.deleteVertices {x₃}).ends e; rw [hends]; exact hj
        have hstep := hAdj₁ ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩ hadj₁
        dsimp at hstep
        omega
      obtain ⟨π', hπ'_central, hres', htruth'⟩ :=
        exists_truer_of_three_ended_path_minus_vertex hG_graph h𝒯 hθ k' π₂
          hπ₂_central hdom₂ hno_iso₂ hc₂ hint₂ htc₂ hn₀_ne_n₂'' hn₀_ne_n₃'' hn₂''_ne_n₃''
          v' hv'_inj hv'0 hv'm hV' hAdj'
      exact ⟨π', hπ'_central, (hres'.trans hres₂).trans hres₁, by omega⟩
termination_by k => k
decreasing_by omega

/-- In a true `(2p + 3)`-redundant portrayal `π` of a graph `G`, no 3-ended cell `c₀` satisfies
`CanBeDrawnInDisc21 (π.cellGraph c₀) (π.nodeVertex '' tilde c₀)` ((R9) of Graph Minors XXI,
Section 9, page 38 of the preprint). -/
theorem not_canBeDrawnInDisc21_of_true_portrayal {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG_graph : G.IsGraph)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hcard3 : (tilde c₀).ncard = 3) :
    ¬ CanBeDrawnInDisc21 (π.cellGraph c₀) (π.nodeVertex '' tilde c₀) := by
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    GM17.theorem_8_4_proof h𝒯 π htrue hred hwarp hθ
  obtain ⟨_, _, hno_iso⟩ :=
    GM17.theorem_8_2_proof h𝒯 π htrue hred hwarp hθ
  have hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty := fun hbd => by
    have := (π.Γ.border_cell c₀ hc₀ hbd).1
    omega
  have hcontra_of_truer0 :
      (∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ ResemblesRefl π' π ∧ π'.truth 0 < π.truth 0) → False := by
    rintro ⟨π', hπ'_central, hres', htruth'⟩
    have htruer' : π'.IsTruer π := ⟨0, fun i hi => (Fin.not_lt_zero i hi).elim, htruth'⟩
    exact htrue.2.2 π' hπ'_central htruer' hres'.to_resembles
  rintro (hV_eq | ⟨_, x₁, hx₁_X, x₂, hx₂_X, hx12, hpath⟩ |
    ⟨_, x₃, hx₃_X, x₁, ⟨hx₁_X, hx₁_ne₃⟩, x₂, ⟨hx₂_X, hx₂_ne₃⟩, hx12, hpath⟩)
  · -- Disjunct 1: V(α(c₀)) = π.nodeVertex '' tilde c₀
    obtain ⟨n₁, n₂, n₃, h12, h13, h23, htc₀⟩ := ncard_eq_three.mp hcard3
    have hn₁_dom : n₁ ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀ (htc₀ ▸ Or.inl rfl)
    have hn₂_dom : n₂ ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀ (htc₀ ▸ Or.inr (Or.inl rfl))
    have hn₃_dom : n₃ ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀ (htc₀ ▸ Or.inr (Or.inr rfl))
    have hx12 : π.nodeVertex n₁ ≠ π.nodeVertex n₂ :=
      fun h => h12 (π.nodeVertex_injOn hn₁_dom hn₂_dom h)
    have hx13 : π.nodeVertex n₁ ≠ π.nodeVertex n₃ :=
      fun h => h13 (π.nodeVertex_injOn hn₁_dom hn₃_dom h)
    have hx23 : π.nodeVertex n₂ ≠ π.nodeVertex n₃ :=
      fun h => h23 (π.nodeVertex_injOn hn₂_dom hn₃_dom h)
    let v : Fin 2 → α := ![π.nodeVertex n₁, π.nodeVertex n₂]
    have hv_inj : Function.Injective v := by
      intro i j hEq
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hx12 hEq).elim
      · exact (hx12 hEq.symm).elim
      · rfl
    have hV_del : ((π.cellGraph c₀).deleteVertices {π.nodeVertex n₃}).vertexSet = range v := by
      change (π.cellGraph c₀).vertexSet \ {π.nodeVertex n₃} = range v
      rw [hV_eq, htc₀]
      ext w
      simp only [image_insert_eq, image_singleton, mem_sdiff, mem_insert_iff, mem_singleton_iff,
        mem_range]
      constructor
      · rintro ⟨rfl | rfl | rfl, hne₃⟩
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact (hne₃ rfl).elim
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact ⟨Or.inl rfl, hx13⟩
        · exact ⟨Or.inr (Or.inl rfl), hx23⟩
    have hAdj : ∀ i j : Fin 2,
        ((π.cellGraph c₀).deleteVertices {π.nodeVertex n₃}).skeleton.Adj (v i) (v j) →
          (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
      intro i j hadj
      have hne_ij : i ≠ j := fun h => hadj.1 (h ▸ rfl)
      fin_cases i <;> fin_cases j
      · exact (hne_ij rfl).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hne_ij rfl).elim
    exact hcontra_of_truer0
      (exists_truer_of_three_ended_path_minus_vertex hG_graph h𝒯 (by omega) 0 π
        htrue.1 hdom hno_iso hc₀ hint₀ htc₀ h12 h13 h23 v hv_inj rfl rfl hV_del hAdj)
  · -- Disjunct 2: IsIndexedPath (π.cellGraph c₀) x₁ x₂
    rcases hx₁_X with ⟨n₁, hn₁_tc, rfl⟩
    rcases hx₂_X with ⟨n₂, hn₂_tc, rfl⟩
    have h12 : n₁ ≠ n₂ := fun h => hx12 (h ▸ rfl)
    have hdiff_ne : (tilde c₀ \ {n₁, n₂}).Nonempty := by
      obtain ⟨a, b, c, hab, hac, hbc, htc₀_eq⟩ := ncard_eq_three.mp hcard3
      by_cases ha : a ∉ ({n₁, n₂} : Set π.S)
      · exact ⟨a, htc₀_eq ▸ Or.inl rfl, ha⟩
      · by_cases hb : b ∉ ({n₁, n₂} : Set π.S)
        · exact ⟨b, htc₀_eq ▸ Or.inr (Or.inl rfl), hb⟩
        · by_cases hc : c ∉ ({n₁, n₂} : Set π.S)
          · exact ⟨c, htc₀_eq ▸ Or.inr (Or.inr rfl), hc⟩
          · push Not at ha hb hc
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
              first | exact (hab rfl).elim | exact (hac rfl).elim | exact (hbc rfl).elim
    rcases hdiff_ne with ⟨n₃, hn₃_tc, hn₃_not⟩
    have h13 : n₁ ≠ n₃ := fun h => hn₃_not (Or.inl h.symm)
    have h23 : n₂ ≠ n₃ := fun h => hn₃_not (Or.inr h.symm)
    have htc₀ : tilde c₀ = {n₁, n₂, n₃} := by
      have hsub : ({n₁, n₂, n₃} : Set π.S) ⊆ tilde c₀ := by
        rintro x (rfl | rfl | rfl)
        · exact hn₁_tc
        · exact hn₂_tc
        · exact hn₃_tc
      have hcard_triple : ({n₁, n₂, n₃} : Set π.S).ncard = 3 := by
        rw [ncard_insert_of_notMem, ncard_pair h23]
        rintro (rfl | rfl)
        · exact h12 rfl
        · exact h13 rfl
      exact (eq_of_subset_of_ncard_le hsub (by omega) (π.Γ.finite_tilde_cell hc₀)).symm
    have hn₁_dom : n₁ ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀ hn₁_tc
    have hn₂_dom : n₂ ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀ hn₂_tc
    have hn₃_dom : n₃ ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀ hn₃_tc
    have hx13 : π.nodeVertex n₁ ≠ π.nodeVertex n₃ :=
      fun h => h13 (π.nodeVertex_injOn hn₁_dom hn₃_dom h)
    have hx23 : π.nodeVertex n₂ ≠ π.nodeVertex n₃ :=
      fun h => h23 (π.nodeVertex_injOn hn₂_dom hn₃_dom h)
    have hx₃_mem : π.nodeVertex n₃ ∈ (π.cellGraph c₀).vertexSet :=
      π.p2 c₀ hc₀ n₃ ⟨hn₃_tc, hn₃_dom⟩
    rcases hpath with ⟨m, hm, v, hv_inj, hv0, hvm, hV, hAdj⟩
    have hx₃_range : π.nodeVertex n₃ ∈ range v := hV ▸ hx₃_mem
    rcases hx₃_range with ⟨r, hr⟩
    have hr_ne0 : r.1 ≠ 0 := by
      intro h0
      have hr0 : r = 0 := by ext; exact h0
      exact hx13 (hv0.symm.trans (hr0 ▸ hr))
    have hr_nem : r.1 ≠ m := by
      intro hm'
      have hrm : r = ⟨m, Nat.lt_succ_self m⟩ := by ext; exact hm'
      exact hx23 (hvm.symm.trans (hrm ▸ hr))
    let H₀ := π.cellGraph c₀
    let V₁ : Set α := {w | ∃ i : Fin (m + 1), i.1 ≤ r.1 ∧ v i = w}
    let V₂ : Set α := {w | ∃ i : Fin (m + 1), r.1 ≤ i.1 ∧ v i = w}
    have hV₁_sub : V₁ ⊆ H₀.vertexSet := by
      rintro _ ⟨i, _, rfl⟩; rw [hV]; exact ⟨i, rfl⟩
    have hV₂_sub : V₂ ⊆ H₀.vertexSet := by
      rintro _ ⟨i, _, rfl⟩; rw [hV]; exact ⟨i, rfl⟩
    have hE₂_ends : ∀ e ∈ H₀.edgeSet, ¬ H₀.ends e ⊆ V₁ → H₀.ends e ⊆ V₂ := by
      intro e he hnot w hw_end
      obtain ⟨y, hy_end, hy_not⟩ := not_subset.mp hnot
      have hy_range : y ∈ range v := hV ▸ H₀.vertex_mem_of_inc hy_end
      have hw_range : w ∈ range v := hV ▸ H₀.vertex_mem_of_inc hw_end
      rcases hy_range with ⟨j, rfl⟩
      rcases hw_range with ⟨i, rfl⟩
      have hj_gt : r.1 < j.1 := by
        by_contra hle
        exact hy_not ⟨j, Nat.le_of_not_lt hle, rfl⟩
      by_cases hij : i = j
      · subst hij; exact ⟨i, Nat.le_of_lt hj_gt, rfl⟩
      · have hadj : H₀.skeleton.Adj (v i) (v j) := ⟨hv_inj.ne hij, e, hw_end, hy_end⟩
        have hstep := (hAdj i j).mp hadj
        exact ⟨i, by omega, rfl⟩
    let A₁ : Hypergraph α β :=
      { vertexSet := V₁
        edgeSet := {e ∈ H₀.edgeSet | H₀.ends e ⊆ V₁}
        Inc := fun e w => e ∈ H₀.edgeSet ∧ H₀.ends e ⊆ V₁ ∧ H₀.Inc e w
        vertex_mem_of_inc := fun _ _ h => h.2.1 h.2.2
        edge_mem_of_inc := fun _ _ h => ⟨h.1, h.2.1⟩
        vertexSet_finite := H₀.vertexSet_finite.subset hV₁_sub
        edgeSet_finite := H₀.edgeSet_finite.subset fun _ h => h.1 }
    let A₂ : Hypergraph α β :=
      { vertexSet := V₂
        edgeSet := {e ∈ H₀.edgeSet | ¬ H₀.ends e ⊆ V₁}
        Inc := fun e w => e ∈ H₀.edgeSet ∧ ¬ H₀.ends e ⊆ V₁ ∧ H₀.Inc e w
        vertex_mem_of_inc := fun e w h => hE₂_ends e h.1 h.2.1 h.2.2
        edge_mem_of_inc := fun _ _ h => ⟨h.1, h.2.1⟩
        vertexSet_finite := H₀.vertexSet_finite.subset hV₂_sub
        edgeSet_finite := H₀.edgeSet_finite.subset fun _ h => h.1 }
    have hA₁_le : A₁ ≤ H₀ := by
      refine ⟨hV₁_sub, fun _ h => h.1, fun e he => ?_⟩
      ext w; exact ⟨fun h => ⟨he.1, he.2, h⟩, fun h => h.2.2⟩
    have hA₂_le : A₂ ≤ H₀ := by
      refine ⟨hV₂_sub, fun _ h => h.1, fun e he => ?_⟩
      ext w; exact ⟨fun h => ⟨he.1, he.2, h⟩, fun h => h.2.2⟩
    have hA_union_V : A₁.vertexSet ∪ A₂.vertexSet = H₀.vertexSet := by
      refine Subset.antisymm (union_subset hV₁_sub hV₂_sub) fun w hw => ?_
      rw [hV] at hw
      rcases hw with ⟨i, rfl⟩
      by_cases hi : i.1 ≤ r.1
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr ⟨i, by omega, rfl⟩
    have hA_union_E : A₁.edgeSet ∪ A₂.edgeSet = H₀.edgeSet := by
      refine Subset.antisymm (union_subset hA₁_le.2 hA₂_le.2) fun e he => ?_
      by_cases hsub : H₀.ends e ⊆ V₁
      · exact Or.inl ⟨he, hsub⟩
      · exact Or.inr ⟨he, hsub⟩
    have hA_disj_E : Disjoint A₁.edgeSet A₂.edgeSet :=
      Set.disjoint_left.mpr fun _ he₁ he₂ => he₂.2 he₁.2
    obtain ⟨π', hπ'_central, hπ'_res, hπ'_truer, _⟩ :=
      exists_truer_of_splitInternalCell h𝒯 (by omega) π htrue.1 hdom hc₀ hint₀
        (by omega : 2 ≤ (tilde c₀).ncard) hn₁_tc hn₂_tc h12 hA₁_le hA₂_le
        hA_union_V hA_union_E hA_disj_E
        (by
          rintro n ⟨hn_tc, hn_ne₂⟩
          rw [htc₀] at hn_tc
          rcases hn_tc with rfl | rfl | rfl
          · exact ⟨0, Nat.zero_le _, hv0⟩
          · exact (hn_ne₂ rfl).elim
          · exact ⟨r, le_rfl, hr⟩)
        (by
          rintro n ⟨hn_tc, hn_ne₁⟩
          rw [htc₀] at hn_tc
          rcases hn_tc with rfl | rfl | rfl
          · exact (hn_ne₁ rfl).elim
          · exact ⟨⟨m, Nat.lt_succ_self m⟩, by dsimp; omega, hvm⟩
          · exact ⟨r, le_rfl, hr⟩)
        (by
          rintro ⟨i, hi, hi_eq⟩
          have him : i = ⟨m, Nat.lt_succ_self m⟩ := hv_inj (hi_eq.trans hvm.symm)
          have hval := congrArg Fin.val him
          change i.1 = m at hval
          omega)
        (by
          rintro ⟨i, hi, hi_eq⟩
          have hi0 : i = 0 := hv_inj (hi_eq.trans hv0.symm)
          have hval := congrArg Fin.val hi0
          change i.1 = 0 at hval
          omega)
        (by
          rintro w ⟨⟨i, hi, rfl⟩, ⟨j, hj, hij_eq⟩⟩
          have hij : i = j := hv_inj hij_eq.symm
          have hval : i.1 = j.1 := congrArg Fin.val hij
          have hir : i = r := by ext; omega
          rw [hir, hr]
          exact ⟨n₃, ⟨hn₃_tc, fun h => by
            rcases h with rfl | rfl
            · exact h13 rfl
            · exact h23 rfl⟩, rfl⟩)
    exact htrue.2.2 π' hπ'_central hπ'_truer hπ'_res
  · -- Disjunct 3: IsIndexedPath ((π.cellGraph c₀).deleteVertices {x₃}) x₁ x₂
    rcases hx₃_X with ⟨n₃, hn₃_tc, rfl⟩
    rcases hx₁_X with ⟨n₁, hn₁_tc, rfl⟩
    rcases hx₂_X with ⟨n₂, hn₂_tc, rfl⟩
    have h12 : n₁ ≠ n₂ := fun h => hx12 (h ▸ rfl)
    have h13 : n₁ ≠ n₃ := fun h => hx₁_ne₃ (h ▸ rfl)
    have h23 : n₂ ≠ n₃ := fun h => hx₂_ne₃ (h ▸ rfl)
    have htc₀ : tilde c₀ = {n₁, n₂, n₃} := by
      have hsub : ({n₁, n₂, n₃} : Set π.S) ⊆ tilde c₀ := by
        rintro x (rfl | rfl | rfl)
        · exact hn₁_tc
        · exact hn₂_tc
        · exact hn₃_tc
      have hcard_triple : ({n₁, n₂, n₃} : Set π.S).ncard = 3 := by
        rw [ncard_insert_of_notMem, ncard_pair h23]
        rintro (rfl | rfl)
        · exact h12 rfl
        · exact h13 rfl
      exact (eq_of_subset_of_ncard_le hsub (by omega) (π.Γ.finite_tilde_cell hc₀)).symm
    rcases hpath with ⟨m, hm, v, hv_inj, hv0, hvm, hV, hAdj⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact hcontra_of_truer0
      (exists_truer_of_three_ended_path_minus_vertex hG_graph h𝒯 (by omega) k π
        htrue.1 hdom hno_iso hc₀ hint₀ htc₀ h12 h13 h23 v hv_inj hv0 hvm hV
        (fun i j hadj => (hAdj i j).mp hadj))

/-- Every true `(2p + 3)`-redundant portrayal `π` of a graph `G` with `warp ≤ p` and
`4p + 6 ≤ θ` yields a Section 9 portrait `(π.Γ, α)` of `G` in `π.S` of depth at most `p + 1`
surrounding `𝒯`. -/
theorem exists_portrait_of_true_portrayal {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG_graph : G.IsGraph)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 6 ≤ θ) :
    ∃ (ιN : π.S → α) (α_cell : Set π.S → Hypergraph α β) (α_vert : π.S → Hypergraph α β),
      PortraitHasDepthLe21 G π.Γ ιN α_cell α_vert (p + 1) ∧
      PortraitSurroundsTangle21 π.Γ α_cell 𝒯 := by
  have : T2Space π.S := π.isSurface.2.1
  have hθ' : 4 * p + 5 < θ := by omega
  have h1_le_p : 1 ≤ p := by
    have : 1 ≤ π.warp := by
      unfold Portrayal.warp
      split_ifs <;> omega
    omega
  have hdom : π.domγ = π.Γ.N :=
    GM17.theorem_8_4_proof h𝒯 π htrue hred hwarp hθ'
  obtain ⟨_, hcard_ge2, hno_iso⟩ :=
    GM17.theorem_8_2_proof h𝒯 π htrue hred hwarp hθ'
  let ιN : π.S → α := π.nodeVertex
  let α_cell : Set π.S → Hypergraph α β := π.cellGraph
  let α_vert : π.S → Hypergraph α β := fun v =>
    { vertexSet := π.borderPlus v ∩ G.vertexSet
      edgeSet := ∅
      Inc := fun _ _ => False
      vertex_mem_of_inc := fun _ _ h => h.elim
      edge_mem_of_inc := fun _ _ h => h.elim
      vertexSet_finite := G.vertexSet_finite.subset inter_subset_right
      edgeSet_finite := finite_empty }
  let q_cuff : Set π.S → ℕ := fun C => π.warpAt C + 1
  have hbp_sub_G : ∀ v ∈ π.Γ.N ∩ bd π.S, π.borderPlus v ⊆ G.vertexSet := by
    rintro v ⟨hvN, hvbd⟩ w (hw_bs | ⟨hv_dom, rfl⟩)
    · exact π.borderSet_subset v ⟨hvN, hvbd⟩ hw_bs
    · exact π.nodeVertex_mem v hv_dom
  have hvert_V : ∀ v ∈ π.Γ.N ∩ bd π.S, (α_vert v).vertexSet = π.borderPlus v := by
    intro v hv
    exact inter_eq_left.mpr (hbp_sub_G v hv)
  have hbp_eq : ∀ v ∈ π.Γ.N, π.borderPlus v = insert (π.nodeVertex v) (π.borderSet v) := by
    intro v hvN
    ext w
    simp only [Portrayal.borderPlus, mem_insert_iff, hdom, hvN, true_and, or_comm]
    rfl
  have hΘ_bd : ∀ C ∈ cuffs π.S, C ⊆ bd π.S := by
    rintro C ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hr2_inter : ∀ c ∈ π.Γ.C, (α_cell c).vertexSet ∩ (ιN '' π.Γ.N) = ιN '' (tilde c) := by
    intro c hc
    refine Subset.antisymm ?_ ?_
    · rintro w ⟨hwc, n, hnN, rfl⟩
      by_cases hntc : n ∈ tilde c
      · exact ⟨n, hntc, rfl⟩
      · obtain ⟨d, hd, hnd⟩ := hno_iso n hnN
        have hne : d ≠ c := fun h => hntc (h ▸ hnd)
        have hwd : π.nodeVertex n ∈ (π.cellGraph d).vertexSet :=
          π.p2 d hd n ⟨hnd, hdom ▸ hnN⟩
        by_cases hbd : (c ∩ bd π.S).Nonempty
        · obtain ⟨m, hmtc, hwm | ⟨_, hwm⟩⟩ := π.p6 c hc hbd (π.nodeVertex n) hwc ⟨d, hd, hne, hwd⟩
          · rcases hbd with ⟨x₀, hx₀_c, hx₀_bd⟩
            let C := connectedComponentIn (bd π.S) x₀
            have hC : C ∈ cuffs π.S := ⟨x₀, hx₀_bd, rfl⟩
            have hc_C : (c ∩ C).Nonempty := ⟨x₀, hx₀_c, mem_connectedComponentIn hx₀_bd⟩
            have hm_C : m ∈ π.Γ.N ∩ C :=
              (π.Γ.border_cell_subset_cuff hc hC hc_C).2.2.2.1 hmtc
            have hmbd : m ∈ π.Γ.N ∩ bd π.S := ⟨hm_C.1, hΘ_bd C hC hm_C.2⟩
            have hdisj :=
              GM17.theorem_9_7_proof
                h𝒯 π htrue hred hwarp hθ' hmbd
            exact (Set.disjoint_left.mp hdisj hwm ⟨n, hnN, rfl⟩).elim
          · exact ⟨m, hmtc, hwm.symm⟩
        · obtain ⟨m, ⟨hmtc, _⟩, hwm⟩ := π.p5 c hc hbd (π.nodeVertex n) hwc ⟨d, hd, hne, hwd⟩
          exact ⟨m, hmtc, hwm⟩
    · rintro _ ⟨n, hntc, rfl⟩
      have hnN : n ∈ π.Γ.N := π.Γ.tilde_subset_N hc hntc
      exact ⟨π.p2 c hc n ⟨hntc, hdom ▸ hnN⟩, n, hnN, rfl⟩
  have hportrait : IsPortrait21 G π.Γ ιN α_cell α_vert q_cuff :=
    { is_surface := π.isSurface
      is_connected_surface := π.connected
      r1_painting := fun c hc => by
        have h1 := hcard_ge2 c hc
        have h2 := π.Γ.ncard_tilde_cell_le hc
        omega
      r1_injOn := hdom ▸ π.nodeVertex_injOn
      r1_subset := by
        rintro _ ⟨n, hnN, rfl⟩
        exact π.nodeVertex_mem n (hdom ▸ hnN)
      r2_cell_le := π.cellGraph_le
      r2_cell_inter := hr2_inter
      r3_union_V := by
        refine Subset.antisymm ?_ ?_
        · intro w hw
          obtain ⟨c, hc, hwc⟩ := π.p1_vertex w hw
          exact mem_biUnion hc hwc
        · exact iUnion₂_subset fun c hc => (π.cellGraph_le c hc).1
      r3_union_E := by
        refine Subset.antisymm ?_ ?_
        · intro e he
          obtain ⟨c, hc, hec⟩ := π.p1_edge e he
          exact mem_biUnion hc hec
        · exact iUnion₂_subset fun c hc => (π.cellGraph_le c hc).2
      r3_edge_disjoint := π.p1_disjoint
      r4_vert := fun v hv => by
        refine ⟨⟨inter_subset_right, empty_subset _, fun _ h => h.elim⟩, rfl, ?_⟩
        rw [hvert_V v hv, hbp_eq v hv.1]
        have hdisj :=
          GM17.theorem_9_7_proof
            h𝒯 π htrue hred hwarp hθ' hv
        ext w
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨rfl | hw_bs, hw_img⟩
          · rfl
          · exact (Set.disjoint_left.mp hdisj hw_bs hw_img).elim
        · rintro rfl
          exact ⟨Or.inl rfl, v, hv.1, rfl⟩
      r5_cuff_pos := fun _ _ => by dsimp [q_cuff]; omega
      r5_cuff_card := fun C hC v hv => by
        have hv_bd : v ∈ π.Γ.N ∩ bd π.S := ⟨hv.1, hΘ_bd C hC hv.2⟩
        rw [hvert_V v hv_bd, hbp_eq v hv.1]
        have hnot_mem : π.nodeVertex v ∉ π.borderSet v :=
          π.p3_notMem v ⟨hdom ▸ hv.1, hv_bd.2⟩
        have hfin_bs : (π.borderSet v).Finite :=
          G.vertexSet_finite.subset (π.borderSet_subset v hv_bd)
        rw [ncard_insert_of_notMem hnot_mem hfin_bs,
          GM17.theorem_9_4_proof
            h𝒯 π htrue hred hwarp hθ' hC hv]
      r6_border := fun c hc hbd u v huv htc => by
        have hu_tc : u ∈ tilde c := htc ▸ Or.inl rfl
        have hv_tc : v ∈ tilde c := htc ▸ Or.inr rfl
        have hu_N : u ∈ π.Γ.N := π.Γ.tilde_subset_N hc hu_tc
        have hv_N : v ∈ π.Γ.N := π.Γ.tilde_subset_N hc hv_tc
        rcases hbd with ⟨x₀, hx₀_c, hx₀_bd⟩
        let C := connectedComponentIn (bd π.S) x₀
        have hC : C ∈ cuffs π.S := ⟨x₀, hx₀_bd, rfl⟩
        have hc_C : (c ∩ C).Nonempty := ⟨x₀, hx₀_c, mem_connectedComponentIn hx₀_bd⟩
        have htc_C : tilde c ⊆ π.Γ.N ∩ C :=
          (π.Γ.border_cell_subset_cuff hc hC hc_C).2.2.2.1
        have hu_C : u ∈ π.Γ.N ∩ C := htc_C hu_tc
        have hv_C : v ∈ π.Γ.N ∩ C := htc_C hv_tc
        have hu_bd : u ∈ π.Γ.N ∩ bd π.S := ⟨hu_N, hΘ_bd C hC hu_C.2⟩
        have hv_bd : v ∈ π.Γ.N ∩ bd π.S := ⟨hv_N, hΘ_bd C hC hv_C.2⟩
        have hbp_u_sub : π.borderPlus u ⊆ (π.cellGraph c).vertexSet := by
          rw [hbp_eq u hu_N]
          rintro w (rfl | hw_bs)
          · exact π.p2 c hc u ⟨hu_tc, hdom ▸ hu_N⟩
          · exact π.p3_subset c hc ⟨x₀, hx₀_c, hx₀_bd⟩ u hu_tc hw_bs
        have hbp_v_sub : π.borderPlus v ⊆ (π.cellGraph c).vertexSet := by
          rw [hbp_eq v hv_N]
          rintro w (rfl | hw_bs)
          · exact π.p2 c hc v ⟨hv_tc, hdom ▸ hv_N⟩
          · exact π.p3_subset c hc ⟨x₀, hx₀_c, hx₀_bd⟩ v hv_tc hw_bs
        have hu_le : α_vert u ≤ α_cell c :=
          ⟨(hvert_V u hu_bd).symm ▸ hbp_u_sub, empty_subset _, fun _ h => h.elim⟩
        have hv_le : α_vert v ≤ α_cell c :=
          ⟨(hvert_V v hv_bd).symm ▸ hbp_v_sub, empty_subset _, fun _ h => h.elim⟩
        refine ⟨hu_le, hv_le, ?_⟩
        obtain ⟨hbs_u_card, _, _, _, L, hL_disj, _, hL_cases⟩ :=
          GM17.theorem_9_8_proof
            h𝒯 π htrue hred hwarp hθ' hC hc hc_C hu_tc hv_tc huv
        rcases hL_cases with ⟨L₀, hL₀_disj⟩ | ⟨c', hc', _, hcard3', htc_sub'⟩
        · left
          have hcard_u : (α_vert u).vertexSet.ncard = π.warpAt C + 1 := by
            rw [hvert_V u hu_bd, hbp_eq u hu_N,
              ncard_insert_of_notMem (π.p3_notMem u ⟨hdom ▸ hu_N, hu_bd.2⟩)
                (G.vertexSet_finite.subset (π.borderSet_subset u hu_bd)),
              hbs_u_card]
          rw [hcard_u]
          let P : Fin (π.warpAt C + 1) →
              PathFromTo (α_cell c).skeleton (α_vert u).vertexSet (α_vert v).vertexSet :=
            Fin.snoc
              (fun i =>
                { first := (L i).first
                  last := (L i).last
                  walk := (L i).walk
                  isPath := (L i).isPath
                  first_mem := (hvert_V u hu_bd).symm ▸ Or.inl (L i).first_mem
                  last_mem := (hvert_V v hv_bd).symm ▸ Or.inl (L i).last_mem })
              { first := L₀.first
                last := L₀.last
                walk := L₀.walk
                isPath := L₀.isPath
                first_mem := (hvert_V u hu_bd).symm ▸
                  Or.inr ⟨hdom ▸ hu_N, mem_singleton_iff.mp L₀.first_mem⟩
                last_mem := (hvert_V v hv_bd).symm ▸
                  Or.inr ⟨hdom ▸ hv_N, mem_singleton_iff.mp L₀.last_mem⟩ }
          refine ⟨P, fun i j hij => ?_⟩
          induction i using Fin.lastCases with
          | last =>
            induction j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j' =>
              dsimp [P]
              rw [Fin.snoc_last, Fin.snoc_castSucc]
              exact hL₀_disj j'
          | cast i' =>
            induction j using Fin.lastCases with
            | last =>
              dsimp [P]
              rw [Fin.snoc_castSucc, Fin.snoc_last]
              exact (hL₀_disj i').symm
            | cast j' =>
              dsimp [P]
              rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
              exact hL_disj (fun h => hij (congrArg Fin.castSucc h))
        · exact Or.inr ⟨c', hc', hcard3', htc_sub' hu_tc, htc_sub' hv_tc⟩
      r7_inter := fun c₁ hc₁ c₂ hc₂ hne hno_cuff => by
        refine Subset.antisymm ?_ ?_
        · rintro w ⟨hw₁, hw₂⟩
          by_cases hbd₁ : (c₁ ∩ bd π.S).Nonempty
          · by_cases hbd₂ : (c₂ ∩ bd π.S).Nonempty
            · rcases hbd₁ with ⟨x₁, hx₁_c₁, hx₁_bd⟩
              rcases hbd₂ with ⟨x₂, hx₂_c₂, hx₂_bd⟩
              let C₁ := connectedComponentIn (bd π.S) x₁
              let C₂ := connectedComponentIn (bd π.S) x₂
              have hC₁ : C₁ ∈ cuffs π.S := ⟨x₁, hx₁_bd, rfl⟩
              have hC₂ : C₂ ∈ cuffs π.S := ⟨x₂, hx₂_bd, rfl⟩
              have hc₁_C₁ : (c₁ ∩ C₁).Nonempty := ⟨x₁, hx₁_c₁, mem_connectedComponentIn hx₁_bd⟩
              have hc₂_C₂ : (c₂ ∩ C₂).Nonempty := ⟨x₂, hx₂_c₂, mem_connectedComponentIn hx₂_bd⟩
              have hC_ne : C₁ ≠ C₂ := fun hEq => hno_cuff C₁ hC₁ ⟨hc₁_C₁, hEq ▸ hc₂_C₂⟩
              obtain ⟨m₁, hm₁_tc, hwm₁⟩ := π.p6 c₁ hc₁ ⟨x₁, hx₁_c₁, hx₁_bd⟩ w hw₁ ⟨c₂, hc₂, hne.symm, hw₂⟩
              obtain ⟨m₂, hm₂_tc, hwm₂⟩ := π.p6 c₂ hc₂ ⟨x₂, hx₂_c₂, hx₂_bd⟩ w hw₂ ⟨c₁, hc₁, hne, hw₁⟩
              have hm₁_C₁ : m₁ ∈ π.Γ.N ∩ C₁ :=
                (π.Γ.border_cell_subset_cuff hc₁ hC₁ hc₁_C₁).2.2.2.1 hm₁_tc
              have hm₂_C₂ : m₂ ∈ π.Γ.N ∩ C₂ :=
                (π.Γ.border_cell_subset_cuff hc₂ hC₂ hc₂_C₂).2.2.2.1 hm₂_tc
              have hm₁_bd : m₁ ∈ π.Γ.N ∩ bd π.S := ⟨hm₁_C₁.1, hΘ_bd C₁ hC₁ hm₁_C₁.2⟩
              have hm₂_bd : m₂ ∈ π.Γ.N ∩ bd π.S := ⟨hm₂_C₂.1, hΘ_bd C₂ hC₂ hm₂_C₂.2⟩
              rcases hwm₁ with hwm₁_bs | ⟨_, rfl⟩ <;> rcases hwm₂ with hwm₂_bs | ⟨_, hEq⟩
              · exact (Set.disjoint_left.mp (π.p4_disjoint C₁ hC₁ C₂ hC₂ hC_ne m₁ hm₁_C₁ m₂ hm₂_C₂)
                  hwm₁_bs hwm₂_bs).elim
              · have hdisj :=
                  GM17.theorem_9_7_proof
                    h𝒯 π htrue hred hwarp hθ' hm₁_bd
                exact (Set.disjoint_left.mp hdisj hwm₁_bs ⟨m₂, hm₂_C₂.1, hEq.symm⟩).elim
              · have hdisj :=
                  GM17.theorem_9_7_proof
                    h𝒯 π htrue hred hwarp hθ' hm₂_bd
                exact (Set.disjoint_left.mp hdisj hwm₂_bs ⟨m₁, hm₁_C₁.1, rfl⟩).elim
              · have hm_eq : m₁ = m₂ := π.nodeVertex_injOn (hdom ▸ hm₁_C₁.1) (hdom ▸ hm₂_C₂.1) hEq
                exact ⟨m₁, ⟨hm₁_tc, hm_eq ▸ hm₂_tc⟩, rfl⟩
            · obtain ⟨m₂, ⟨hm₂_tc, hm₂_dom⟩, rfl⟩ := π.p5 c₂ hc₂ hbd₂ w hw₂ ⟨c₁, hc₁, hne, hw₁⟩
              have hm₂_N : m₂ ∈ π.Γ.N := hdom ▸ hm₂_dom
              have hmem₁ : ιN m₂ ∈ (α_cell c₁).vertexSet ∩ (ιN '' π.Γ.N) := ⟨hw₁, m₂, hm₂_N, rfl⟩
              rw [hr2_inter c₁ hc₁] at hmem₁
              rcases hmem₁ with ⟨m₁, hm₁_tc, hEq⟩
              have hm_eq : m₁ = m₂ :=
                π.nodeVertex_injOn (hdom ▸ π.Γ.tilde_subset_N hc₁ hm₁_tc) hm₂_dom hEq
              exact ⟨m₂, ⟨hm_eq ▸ hm₁_tc, hm₂_tc⟩, rfl⟩
          · obtain ⟨m₁, ⟨hm₁_tc, hm₁_dom⟩, rfl⟩ := π.p5 c₁ hc₁ hbd₁ w hw₁ ⟨c₂, hc₂, hne.symm, hw₂⟩
            have hm₁_N : m₁ ∈ π.Γ.N := hdom ▸ hm₁_dom
            have hmem₂ : ιN m₁ ∈ (α_cell c₂).vertexSet ∩ (ιN '' π.Γ.N) := ⟨hw₂, m₁, hm₁_N, rfl⟩
            rw [hr2_inter c₂ hc₂] at hmem₂
            rcases hmem₂ with ⟨m₂, hm₂_tc, hEq⟩
            have hm_eq : m₂ = m₁ :=
              π.nodeVertex_injOn (hdom ▸ π.Γ.tilde_subset_N hc₂ hm₂_tc) hm₁_dom hEq
            exact ⟨m₁, ⟨hm₁_tc, hm_eq ▸ hm₂_tc⟩, rfl⟩
        · rintro _ ⟨n, ⟨hn₁, hn₂⟩, rfl⟩
          exact ⟨π.p2 c₁ hc₁ n ⟨hn₁, hdom ▸ π.Γ.tilde_subset_N hc₁ hn₁⟩,
            π.p2 c₂ hc₂ n ⟨hn₂, hdom ▸ π.Γ.tilde_subset_N hc₂ hn₂⟩⟩
      r8_order := fun C hC c₁ hc₁ c₂ hc₂ hc₁_C hc₂_C u₁ hu₁ u₂ hu₂ hord => by
        rcases hord with ⟨f, a₁, b₁, t₁, a₂, b₂, t₂, hab₁, hbt₁, hta₂, hab₂, hbt₂, ht₂a₁,
          hu₁_eq, hu₂_eq, _, hcl₁_sub, _, hcl₂_sub⟩
        have hc₁_ne_c₂ : c₁ ≠ c₂ := by
          rintro rfl
          rcases hc₁_C with ⟨x, hx_c₁, hx_C⟩
          have hx_not_N : x ∉ π.Γ.N := (π.Γ.cell_subset_diff hc₁ hx_c₁).2
          have hx_cl : x ∈ closure c₁ ∩ C := ⟨subset_closure hx_c₁, hx_C⟩
          obtain ⟨s₁, ⟨has₁, hsb₁⟩, hs₁_eq⟩ := hcl₁_sub hx_cl
          obtain ⟨s₂, ⟨has₂, hsb₂⟩, hs₂_eq⟩ := hcl₂_sub hx_cl
          have hs₁_ne_t₁ : s₁ ≠ t₁ := fun h => hx_not_N (hs₁_eq ▸ h ▸ hu₁_eq.symm ▸ hu₁.1)
          have hs₂_ne_t₁ : s₂ ≠ t₁ := fun h => hx_not_N (hs₂_eq ▸ h ▸ hu₁_eq.symm ▸ hu₁.1)
          have hs₂_ne_t₂ : s₂ ≠ t₂ := fun h => hx_not_N (hs₂_eq ▸ h ▸ hu₂_eq.symm ▸ hu₂.1)
          have hs₁_lt_t₁ : s₁ < t₁ := lt_of_le_of_ne (hsb₁.trans hbt₁) hs₁_ne_t₁
          have ht₁_lt_s₂ : t₁ < s₂ := lt_of_le_of_ne (hta₂.trans has₂) hs₂_ne_t₁.symm
          have hs₂_lt_t₂ : s₂ < t₂ := lt_of_le_of_ne (hsb₂.trans hbt₂) hs₂_ne_t₂
          have hEq_s :=
            cuffPoint_injOn_Ico f a₁ ⟨has₁, by linarith⟩ ⟨by linarith, by linarith⟩
              (hs₁_eq.trans hs₂_eq.symm)
          linarith
        have hdisj_E : (α_cell c₁ ∩ α_cell c₂).edgeSet = ∅ :=
          Set.disjoint_iff_inter_eq_empty.mp (π.p1_disjoint c₁ hc₁ c₂ hc₂ hc₁_ne_c₂)
        refine ⟨?_, ?_, fun e he => (hdisj_E ▸ he).elim⟩
        · rintro w ⟨hw₁, hw₂⟩
          have hbd₁ : (c₁ ∩ bd π.S).Nonempty := hc₁_C.mono (inter_subset_inter_right _ (hΘ_bd C hC))
          have hbd₂ : (c₂ ∩ bd π.S).Nonempty := hc₂_C.mono (inter_subset_inter_right _ (hΘ_bd C hC))
          obtain ⟨m₁, hm₁_tc, hwm₁⟩ := π.p6 c₁ hc₁ hbd₁ w hw₁ ⟨c₂, hc₂, hc₁_ne_c₂.symm, hw₂⟩
          obtain ⟨m₂, hm₂_tc, hwm₂⟩ := π.p6 c₂ hc₂ hbd₂ w hw₂ ⟨c₁, hc₁, hc₁_ne_c₂, hw₁⟩
          have hm₁_C : m₁ ∈ π.Γ.N ∩ C :=
            (π.Γ.border_cell_subset_cuff hc₁ hC hc₁_C).2.2.2.1 hm₁_tc
          have hm₂_C : m₂ ∈ π.Γ.N ∩ C :=
            (π.Γ.border_cell_subset_cuff hc₂ hC hc₂_C).2.2.2.1 hm₂_tc
          have hm₁_cl : m₁ ∈ closure c₁ ∩ C := ⟨ hm₁_tc.1, hm₁_C.2⟩
          have hm₂_cl : m₂ ∈ closure c₂ ∩ C := ⟨ hm₂_tc.1, hm₂_C.2⟩
          obtain ⟨s₁, ⟨has₁, hsb₁⟩, hs₁_eq⟩ := hcl₁_sub hm₁_cl
          obtain ⟨s₂, ⟨has₂, hsb₂⟩, hs₂_eq⟩ := hcl₂_sub hm₂_cl
          have hInOrder : GM19.InOrderOn C m₁ u₁ m₂ u₂ :=
            ⟨f, s₁, t₁, s₂, t₂, hsb₁.trans hbt₁, hta₂.trans has₂, hsb₂.trans hbt₂,
              by linarith, hs₁_eq, hu₁_eq, hs₂_eq, hu₂_eq⟩
          have hu₁_bd : u₁ ∈ π.Γ.N ∩ bd π.S := ⟨hu₁.1, hΘ_bd C hC hu₁.2⟩
          have hu₂_bd : u₂ ∈ π.Γ.N ∩ bd π.S := ⟨hu₂.1, hΘ_bd C hC hu₂.2⟩
          change w ∈ (α_vert u₁).vertexSet ∪ (α_vert u₂).vertexSet
          rw [hvert_V u₁ hu₁_bd, hvert_V u₂ hu₂_bd]
          exact π.p7 C hC m₁ hm₁_C u₁ hu₁ m₂ hm₂_C u₂ hu₂ hInOrder w hwm₁ hwm₂
        · rw [hdisj_E]; exact empty_subset _
      r9_three := fun c hc hcard3 =>
        not_canBeDrawnInDisc21_of_true_portrayal hG_graph h𝒯 π htrue hred hwarp hθ' hc hcard3
      r10_null := fun C hC => by
        refine eq_empty_iff_forall_notMem.mpr fun w hw => ?_
        have hC_arc : IsOArc C := (cuff_statement.{0} π.S π.isSurface).2.2 C hC
        set k := (π.Γ.N ∩ C).ncard
        obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration C k) := π.Γ.exists_cuffEnumeration hC hC_arc
        have hk_ge2 : 2 ≤ k := E.two_le
        have hn₀_mem : E.node ⟨0, by omega⟩ ∈ π.Γ.N ∩ C := E.range_node ▸ ⟨⟨0, by omega⟩, rfl⟩
        have hw_G : w ∈ G.vertexSet := (mem_iInter₂.mp hw (E.node ⟨0, by omega⟩) hn₀_mem).2
        have hX_sub : ({w} : Set α) ⊆ G.vertexSet := singleton_subset_iff.mpr hw_G
        have hX_card : 3 * ({w} : Set α).ncard ≤ 2 * p + 3 := by
          rw [ncard_singleton]; omega
        have hθ_66 : (2 * p + 3) + max 3 (2 * p + 2) < θ := by omega
        apply GM17.theorem_6_6_proof h𝒯 π htrue.1 hwarp hred hθ_66
          hC hX_sub hX_card
        intro n hn
        exact ⟨w, rfl, (mem_iInter₂.mp hw n hn).1⟩ }
  refine ⟨ιN, α_cell, α_vert, ⟨q_cuff, hportrait, fun C hC => ?_⟩, htrue.1⟩
  dsimp [q_cuff]
  have := (π.warpAt_le_warp hC).trans hwarp
  omega

end GraphMinor.GM21
