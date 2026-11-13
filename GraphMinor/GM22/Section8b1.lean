module

public import GraphMinor.GM22.Section8a
public import GraphMinor.Surface.Gluing
public import GraphMinor.GM09.DiscDrawing
public import GraphMinor.GM12.Section4CircleQuad
public import GraphMinor.GM12.Section4FourBoundaryParameters
public import GraphMinor.GM12.Section4ResidualArc
public import GraphMinor.GM12.Section4NormalArcDisc
public import GraphMinor.GM12.Section4FiniteMarkedDiscJoin
public import GraphMinor.GM14.Whitney
import GraphMinor.GM11.RadialCorners
import GraphMinor.GM11.Section7
import GraphMinor.Surface.DiscGrow
import GraphMinor.GM19.PadFlower
import Mathlib.Data.Finset.Sort

/-!
# Graph Minors XXII, Section 8 (Part b1: Disc $\Delta_0$ and Claim 1 of Theorem 8.3)

This file constructs the closed disc $\Delta_0 \subseteq \Sigma$ containing $U(\Gamma)$ and proves
Claim (1) of Theorem (8.3) of Robertson and Seymour, *Graph Minors. XXII. Irrelevant Vertices in
Linkage Problems*, J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 559–560).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14

universe u v w

variable {α : Type u} {β : Type v}
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## Radial Shrinking of a Closed Disc Fixing a Closed Subset of its Boundary -/

/-- Radial shrink factor on `ℂ` fixing a subset `F₀` of the unit circle and shrinking the rest
toward the origin. -/
private noncomputable def radialShrinkFactor (F₀ : Set ℂ) (z : ℂ) : ℝ :=
  if F₀.Nonempty then (1 / 8 : ℝ) * Metric.infDist z F₀ else (1 / 2 : ℝ)

/-- Radial shrink map `z ↦ (1 - τ(z)) z` on `ℂ`. -/
private noncomputable def radialShrinkMap (F₀ : Set ℂ) (z : ℂ) : ℂ :=
  ((1 - radialShrinkFactor F₀ z : ℝ) : ℂ) * z

private theorem continuous_radialShrinkFactor (F₀ : Set ℂ) :
    Continuous (radialShrinkFactor F₀) := by
  unfold radialShrinkFactor
  split_ifs
  · exact continuous_const.mul (Metric.continuous_infDist_pt F₀)
  · exact continuous_const

private theorem continuous_radialShrinkMap (F₀ : Set ℂ) :
    Continuous (radialShrinkMap F₀) := by
  unfold radialShrinkMap
  exact (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_radialShrinkFactor F₀))).mul
    continuous_id

private theorem radialShrinkFactor_nonneg (F₀ : Set ℂ) (z : ℂ) :
    0 ≤ radialShrinkFactor F₀ z := by
  by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
  · exact mul_nonneg (by norm_num) Metric.infDist_nonneg
  · norm_num

private theorem radialShrinkFactor_le_half {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    radialShrinkFactor F₀ z ≤ 1 / 2 := by
  by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
  · rcases hne with ⟨w, hw⟩
    have hle : Metric.infDist z F₀ ≤ dist z w := Metric.infDist_le_dist_of_mem hw
    have hzw : dist z w ≤ 2 := by
      have hz0 : dist z 0 ≤ 1 := Metric.mem_closedBall.mp hz
      have hw0 : dist w 0 = 1 := Metric.mem_sphere.mp (hF₀ hw)
      calc dist z w ≤ dist z 0 + dist 0 w := dist_triangle z 0 w
        _ = dist z 0 + dist w 0 := by rw [dist_comm 0 w]
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    linarith
  · norm_num

private theorem abs_radialShrinkFactor_sub_le (F₀ : Set ℂ) (z w : ℂ) :
    |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| ≤ (1 / 8 : ℝ) * dist z w := by
  by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
  · have hsub : (1 / 8 : ℝ) * Metric.infDist z F₀ - (1 / 8 : ℝ) * Metric.infDist w F₀ =
        (1 / 8 : ℝ) * (Metric.infDist z F₀ - Metric.infDist w F₀) := by ring
    have hdist : |Metric.infDist z F₀ - Metric.infDist w F₀| ≤ dist z w := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · linarith [Metric.infDist_le_infDist_add_dist (x := z) (y := w) (s := F₀)]
      · have h2 := Metric.infDist_le_infDist_add_dist (x := w) (y := z) (s := F₀)
        rw [dist_comm] at h2
        linarith
    rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
    exact mul_le_mul_of_nonneg_left hdist (by norm_num)
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num) dist_nonneg

private theorem injOn_radialShrinkMap {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1) :
    InjOn (radialShrinkMap F₀) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz w hw heq
  have hτz : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hτz0 : 0 ≤ radialShrinkFactor F₀ z := radialShrinkFactor_nonneg F₀ z
  have hlip : |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| ≤ (1 / 8 : ℝ) * ‖z - w‖ := by
    simpa [dist_eq_norm] using abs_radialShrinkFactor_sub_le F₀ z w
  have hw1 : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hid : z - w = ((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w) +
      ((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w := by
    have heq' : ((1 - radialShrinkFactor F₀ z : ℝ) : ℂ) * z =
        ((1 - radialShrinkFactor F₀ w : ℝ) : ℂ) * w := heq
    push_cast at heq' ⊢
    linear_combination heq'
  have hnorm1 : ‖((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w)‖ =
      |radialShrinkFactor F₀ z| * ‖z - w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm2 : ‖((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ =
      |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖z - w‖ ≤ (5 / 8 : ℝ) * ‖z - w‖ := by
    calc ‖z - w‖
      _ = ‖((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w) +
            ((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ := by
          rw [← hid]
      _ ≤ ‖((radialShrinkFactor F₀ z : ℝ) : ℂ) * (z - w)‖ +
            ‖((radialShrinkFactor F₀ z - radialShrinkFactor F₀ w : ℝ) : ℂ) * w‖ :=
          norm_add_le _ _
      _ = |radialShrinkFactor F₀ z| * ‖z - w‖ +
            |radialShrinkFactor F₀ z - radialShrinkFactor F₀ w| * ‖w‖ := by
          rw [hnorm1, hnorm2]
      _ ≤ (1 / 2 : ℝ) * ‖z - w‖ + ((1 / 8 : ℝ) * ‖z - w‖) * 1 := by
          rw [abs_of_nonneg hτz0]
          gcongr
      _ = (5 / 8 : ℝ) * ‖z - w‖ := by ring
  have hzero : ‖z - w‖ = 0 := by
    have hnonneg : 0 ≤ ‖z - w‖ := norm_nonneg _
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

private theorem radialShrinkMap_eq_self {F₀ : Set ℂ} {z : ℂ} (hz : z ∈ F₀) :
    radialShrinkMap F₀ z = z := by
  have hne : F₀.Nonempty := ⟨z, hz⟩
  have hdist : Metric.infDist z F₀ = 0 := Metric.infDist_zero_of_mem hz
  simp [radialShrinkMap, radialShrinkFactor, hne, hdist]

private theorem radialShrinkMap_mem_ball {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    (hF₀_closed : IsClosed F₀) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (hzF : z ∉ F₀) :
    radialShrinkMap F₀ z ∈ Metric.ball (0 : ℂ) 1 := by
  have hτ_pos : 0 < radialShrinkFactor F₀ z := by
    by_cases hne : F₀.Nonempty <;> simp only [radialShrinkFactor, hne, ite_true, ite_false]
    · have hpos : 0 < Metric.infDist z F₀ :=
        (hF₀_closed.notMem_iff_infDist_pos hne).mp hzF
      linarith
    · norm_num
  have hτ_le : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  rw [Metric.mem_ball, dist_zero_right, radialShrinkMap, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]
  nlinarith

private theorem radialShrinkMap_mem_closedBall {F₀ : Set ℂ} (hF₀ : F₀ ⊆ Metric.sphere (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    radialShrinkMap F₀ z ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hτ_nonneg : 0 ≤ radialShrinkFactor F₀ z := radialShrinkFactor_nonneg F₀ z
  have hτ_le : radialShrinkFactor F₀ z ≤ 1 / 2 := radialShrinkFactor_le_half hF₀ hz
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  rw [Metric.mem_closedBall, dist_zero_right, radialShrinkMap, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]
  nlinarith

/-- Given a closed disc `D` in a `T2Space` `S` and a closed subset `F ⊆ discBd D`, there is a
continuous injective self-map `Ψ : S → S` on `D` with a continuous left inverse `Ψ'` on `Ψ '' D`
that fixes `F` pointwise and sends `D \ F` into `D \ discBd D`. -/
theorem exists_disc_shrink_map_8_3 [Nonempty S]
    {D F : Set S} (hD : IsClosedDisc D) (hF_closed : IsClosed F) (hF_sub : F ⊆ discBd D) :
    ∃ Ψ Ψ' : S → S,
      ContinuousOn Ψ D ∧
      ContinuousOn Ψ' (Ψ '' D) ∧
      LeftInvOn Ψ' Ψ D ∧
      InjOn Ψ D ∧
      Ψ '' D ⊆ D ∧
      (∀ x ∈ F, Ψ x = x) ∧
      (∀ x ∈ D \ F, Ψ x ∈ D \ discBd D) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hFD : F ⊆ D := hF_sub.trans (Surface.discBd_subset D)
  let F₀ : Set ℂ := h '' F
  have hF₀_sphere : F₀ ⊆ Metric.sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact image_mono hF_sub
  have hF_compact : IsCompact F := hD.isCompact.of_isClosed_subset hF_closed hFD
  have hF₀_closed : IsClosed F₀ :=
    (hF_compact.image_of_continuousOn (c.hc.mono hFD)).isClosed
  let Ψ : S → S := fun x => g (radialShrinkMap F₀ (h x))
  have hΦ_maps : MapsTo (radialShrinkMap F₀) (Metric.closedBall (0 : ℂ) 1)
      (Metric.closedBall (0 : ℂ) 1) :=
    fun z hz => radialShrinkMap_mem_closedBall hF₀_sphere hz
  have hΨ_cont : ContinuousOn Ψ D := by
    refine c.gc.comp ((continuous_radialShrinkMap F₀).continuousOn.comp c.hc c.hm) ?_
    exact hΦ_maps.comp c.hm
  have hΨ_inj : InjOn Ψ D := by
    intro x hx y hy heq
    have h₁ : radialShrinkMap F₀ (h x) = radialShrinkMap F₀ (h y) :=
      c.injOn (hΦ_maps (c.hm hx)) (hΦ_maps (c.hm hy)) heq
    have h₂ : h x = h y := injOn_radialShrinkMap hF₀_sphere (c.hm hx) (c.hm hy) h₁
    exact c.gh.injOn hx hy h₂
  obtain ⟨Ψ', hΨ'_cont, hΨ'_left⟩ := Surface.exists_inv_of_compactOn hD.isCompact hΨ_cont hΨ_inj
  refine ⟨Ψ, Ψ', hΨ_cont, hΨ'_cont, hΨ'_left, hΨ_inj, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← c.g_closedBall]
    exact mem_image_of_mem g (hΦ_maps (c.hm hx))
  · intro x hx
    have hx₀ : h x ∈ F₀ := mem_image_of_mem h hx
    show g (radialShrinkMap F₀ (h x)) = x
    rw [radialShrinkMap_eq_self hx₀, c.gh (hFD hx)]
  · rintro x ⟨hxD, hxF⟩
    have hxhF₀ : h x ∉ F₀ := by
      rintro ⟨y, hyF, hyx⟩
      exact hxF (c.gh.injOn hxD (hFD hyF) hyx.symm ▸ hyF)
    have hball : radialShrinkMap F₀ (h x) ∈ Metric.ball (0 : ℂ) 1 :=
      radialShrinkMap_mem_ball hF₀_sphere hF₀_closed (c.hm hxD) hxhF₀
    have hmem : g (radialShrinkMap F₀ (h x)) ∈ g '' Metric.ball (0 : ℂ) 1 :=
      mem_image_of_mem g hball
    have hball_sub : g '' Metric.ball (0 : ℂ) 1 ⊆ D \ discBd D := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨c.gm (ball_subset_closedBall hz), ?_⟩
      rw [← c.g_sphere]
      rintro ⟨w, hw, heq⟩
      have hzw : w = z := c.injOn (sphere_subset_closedBall hw) (ball_subset_closedBall hz) heq
      rw [hzw] at hw
      have h1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have h2 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      linarith
    exact hball_sub hmem

/-- In the setup of Theorem (8.3), there exists a closed disc `Δ₀ ⊆ S` such that
`univ \ r₀ ⊆ Δ₀`, `Γ.U ⊆ Δ₀`, `subBd Δ₀ ∩ Γ.U = PiSet`, `univ \ Δ₀ ⊆ r₀`,
`subBd Δ₀ ⊆ r₀ ∪ PiSet`, `IsClosedDisc (univ \ r₀)`, `discBd (univ \ r₀) = C₀.U`, and a
boundary homeomorphism `e_bd : C₀.U ≃ₜ subBd Δ₀` fixing `PiSet` pointwise. -/
lemma exists_disc_Δ₀_8_3
    (hS : IsSphere S) (Γ : Drawing S) (C₀ : Drawing S) (r₀ : Set S) (PiSet : Set S)
    (hC₀ : C₀.IsCircuit) (hr₀_mem : r₀ ∈ C₀.R)
    (hΓ_disj_r₀ : Disjoint Γ.U r₀) (hPi_fin : PiSet.Finite) (hPi_sub : PiSet ⊆ C₀.V)
    (hC₀_V_sub : C₀.V ⊆ Γ.V) :
    ∃ Δ₀ : Set S, IsClosedDisc Δ₀ ∧
      univ \ r₀ ⊆ Δ₀ ∧
      Γ.U ⊆ Δ₀ ∧
      subBd Δ₀ ∩ Γ.U = PiSet ∧
      univ \ Δ₀ ⊆ r₀ ∧
      subBd Δ₀ ⊆ r₀ ∪ PiSet ∧
      IsClosedDisc (univ \ r₀) ∧
      discBd (univ \ r₀) = C₀.U ∧
      ∃ e_bd : C₀.U ≃ₜ subBd Δ₀, ∀ y : C₀.U, y.1 ∈ PiSet → (e_bd y).1 = y.1 := by
  have hC₀_oarc : IsOArc C₀.U := GM11.IsCircuit.isOArc_U hC₀
  obtain ⟨Δ₁, Δ₂, -, hD₁, hD₂, hbd₁, hbd₂, hcup, hcap, hcomp, -⟩ :=
    sphere_disc S hS C₀.U hC₀_oarc
  have hr₀_cases : r₀ = Δ₁ \ C₀.U ∨ r₀ = Δ₂ \ C₀.U := by
    change r₀ ∈ componentsIn (univ \ C₀.U) at hr₀_mem
    rwa [hcomp, mem_insert_iff, mem_singleton_iff] at hr₀_mem
  let D_r₀ : Set S := r₀ ∪ C₀.U
  have hD_r₀_facts : IsClosedDisc D_r₀ ∧ discBd D_r₀ = C₀.U ∧ D_r₀ \ discBd D_r₀ = r₀ ∧
      IsClosedDisc (univ \ r₀) ∧ discBd (univ \ r₀) = C₀.U := by
    rcases hr₀_cases with hr₀_eq | hr₀_eq
    · have hD_eq : D_r₀ = Δ₁ := by
        dsimp [D_r₀]
        rw [hr₀_eq, sdiff_union_self, union_eq_left.mpr (hbd₁ ▸ Surface.discBd_subset Δ₁)]
      have hcompl_eq : univ \ r₀ = Δ₂ := by
        ext x
        rw [hr₀_eq, ← hcup, mem_sdiff, mem_union, mem_sdiff]
        constructor
        · rintro ⟨hx₁ | hx₂, hxnot⟩
          · exact Surface.discBd_subset Δ₂ (hbd₂.symm ▸ by_contra fun hxC => hxnot ⟨hx₁, hxC⟩)
          · exact hx₂
        · intro hx₂
          refine ⟨Or.inr hx₂, fun ⟨hx₁, hxC⟩ => ?_⟩
          exact hxC (hcap ▸ ⟨hx₁, hx₂⟩)
      refine ⟨hD_eq ▸ hD₁, hD_eq.symm ▸ hbd₁, ?_, hcompl_eq ▸ hD₂, hcompl_eq.symm ▸ hbd₂⟩
      rw [hD_eq, hbd₁, hr₀_eq]
    · have hD_eq : D_r₀ = Δ₂ := by
        dsimp [D_r₀]
        rw [hr₀_eq, sdiff_union_self, union_eq_left.mpr (hbd₂ ▸ Surface.discBd_subset Δ₂)]
      have hcompl_eq : univ \ r₀ = Δ₁ := by
        ext x
        rw [hr₀_eq, ← hcup, mem_sdiff, mem_union, mem_sdiff]
        constructor
        · rintro ⟨hx₁ | hx₂, hxnot⟩
          · exact hx₁
          · exact Surface.discBd_subset Δ₁ (hbd₁.symm ▸ by_contra fun hxC => hxnot ⟨hx₂, hxC⟩)
        · intro hx₁
          refine ⟨Or.inl hx₁, fun ⟨hx₂, hxC⟩ => ?_⟩
          exact hxC (hcap ▸ ⟨hx₁, hx₂⟩)
      refine ⟨hD_eq ▸ hD₂, hD_eq.symm ▸ hbd₂, ?_, hcompl_eq ▸ hD₁, hcompl_eq.symm ▸ hbd₁⟩
      rw [hD_eq, hbd₂, hr₀_eq]
  obtain ⟨hD_r₀, hbd_r₀, hint_r₀, hdisc_compl, hbd_compl⟩ := hD_r₀_facts
  have : Nonempty S := (GM14.IsClosedDisc.nonempty hD_r₀).nonempty
  have hPi_sub_bd : PiSet ⊆ discBd D_r₀ := by
    rw [hbd_r₀]
    exact hPi_sub.trans C₀.V_subset_U
  obtain ⟨Ψ, Ψ', hΨ_cont, hΨ'_cont, hΨ_left, hΨ_inj, hΨ_sub, hΨ_fix, hΨ_int⟩ :=
    exists_disc_shrink_map_8_3 hD_r₀ hPi_fin.isClosed hPi_sub_bd
  let D' : Set S := Ψ '' D_r₀
  obtain ⟨hD'_disc, hD'_bd⟩ := hD_r₀.image hΨ_cont hΨ'_cont hΨ_left
  obtain ⟨hS_surf, _⟩ := GM11.IsSphere.isClosedSurface hS
  have hsubBd_D' : subBd D' = discBd D' := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS_surf hD'_disc]
  obtain ⟨Δ₀, hΔ₀_disc, hbd_Δ₀, hΔ₀_eq, hΔ₀_int⟩ :=
    exists_complementary_closedDisc_in_sphere hS hD'_disc
  have hbd_Δ₀_eq_image : subBd Δ₀ = Ψ '' C₀.U := by
    rw [hbd_Δ₀, hsubBd_D', hD'_bd, hbd_r₀]
  have hC₀_sub_Dr₀ : C₀.U ⊆ D_r₀ := hbd_r₀ ▸ Surface.discBd_subset D_r₀
  let e_bd : C₀.U ≃ₜ subBd Δ₀ :=
    { toFun := fun y => ⟨Ψ y.1, hbd_Δ₀_eq_image ▸ ⟨y.1, y.2, rfl⟩⟩
      invFun := fun z => ⟨Ψ' z.1, by
        have hz : z.1 ∈ Ψ '' C₀.U := hbd_Δ₀_eq_image ▸ z.2
        obtain ⟨x, hx, hzx⟩ := hz
        rw [← hzx, hΨ_left (hC₀_sub_Dr₀ hx)]
        exact hx⟩
      left_inv := fun y => Subtype.ext (hΨ_left (hC₀_sub_Dr₀ y.2))
      right_inv := fun z => by
        have hz : z.1 ∈ Ψ '' C₀.U := hbd_Δ₀_eq_image ▸ z.2
        obtain ⟨x, hx, hzx⟩ := hz
        apply Subtype.ext
        change Ψ (Ψ' z.1) = z.1
        rw [← hzx, hΨ_left (hC₀_sub_Dr₀ hx)]
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (hΨ_cont.mono hC₀_sub_Dr₀).comp_continuous continuous_subtype_val Subtype.prop
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        have hbd_sub_D' : subBd Δ₀ ⊆ D' := by
          rw [hbd_Δ₀_eq_image]
          exact image_mono hC₀_sub_Dr₀
        exact (hΨ'_cont.mono hbd_sub_D').comp_continuous continuous_subtype_val Subtype.prop }
  have hD'_sub : D' ⊆ r₀ ∪ PiSet := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxPi : x ∈ PiSet
    · right
      rw [hΨ_fix x hxPi]
      exact hxPi
    · left
      rw [← hint_r₀]
      exact hΨ_int x ⟨hx, hxPi⟩
  have hbd_Δ₀_sub : subBd Δ₀ ⊆ r₀ ∪ PiSet := by
    rw [hbd_Δ₀, hsubBd_D']
    exact (Surface.discBd_subset D').trans hD'_sub
  have hPi_sub_bd_Δ₀ : PiSet ⊆ subBd Δ₀ := by
    intro x hx
    rw [hbd_Δ₀, hsubBd_D', hD'_bd]
    exact ⟨x, hPi_sub_bd hx, hΨ_fix x hx⟩
  have huniv_diff_Δ₀ : univ \ Δ₀ ⊆ r₀ := by
    intro y ⟨_, hyΔ₀⟩
    have hyD' : y ∈ D' := by
      by_contra hyD'
      exact hyΔ₀ (hΔ₀_eq.symm ▸ Or.inl ⟨mem_univ y, hyD'⟩)
    have hy_not_bd : y ∉ subBd D' := fun h => hyΔ₀ (hΔ₀_eq.symm ▸ Or.inr h)
    rcases hD'_sub hyD' with hyr₀ | hyPi
    · exact hyr₀
    · exact (hy_not_bd (hbd_Δ₀ ▸ hPi_sub_bd_Δ₀ hyPi)).elim
  have huniv_diff_r₀ : univ \ r₀ ⊆ Δ₀ := by
    intro y ⟨_, hyr₀⟩
    by_contra hyΔ₀
    exact hyr₀ (huniv_diff_Δ₀ ⟨mem_univ y, hyΔ₀⟩)
  have hΓ_sub_Δ₀ : Γ.U ⊆ Δ₀ := fun y hy =>
    huniv_diff_r₀ ⟨mem_univ y, fun hyr₀ => hΓ_disj_r₀.le_bot ⟨hy, hyr₀⟩⟩
  refine ⟨Δ₀, hΔ₀_disc, huniv_diff_r₀, hΓ_sub_Δ₀, ?_, huniv_diff_Δ₀, hbd_Δ₀_sub,
    hdisc_compl, hbd_compl, e_bd, fun y hy => hΨ_fix y.1 hy⟩
  apply Subset.antisymm
  · rintro x ⟨hxbd, hxΓ⟩
    rcases hbd_Δ₀_sub hxbd with hxr₀ | hxPi
    · exact (hΓ_disj_r₀.le_bot ⟨hxΓ, hxr₀⟩).elim
    · exact hxPi
  · intro x hxPi
    exact ⟨hPi_sub_bd_Δ₀ hxPi, Γ.V_subset_U (hC₀_V_sub (hPi_sub hxPi))⟩

/-- Given `HasDiscDrawingWithBoundaryOrder ιV C₀ PiSet Z 𝒜` and a boundary homeomorphism
`e_C_Δ₀ : C₀.U ≃ₜ subBd Δ₀` fixing `PiSet` pointwise, the bipartite incidence graph
`divisionIncidenceGraph Z 𝒜` can be drawn in `Δ₀` with each vertex of `PiSet` represented by
itself and with `gd₀.drawing.U ∩ subBd Δ₀ = PiSet`. -/
lemma exists_transported_incidence_drawing_8_3
    (hS : IsSphere S) {ιV : S ↪ α} {C₀ : Drawing S} {PiSet : Set S}
    {Z : Set α} {𝒜 : Set (Graph α β)} {Δ₀ : Set S}
    (hPi_sub : PiSet ⊆ C₀.V) (hPi_card : PiSet.ncard = 4)
    (hΔ₀ : IsClosedDisc Δ₀)
    (e_C_Δ₀ : C₀.U ≃ₜ subBd Δ₀)
    (he_C_Δ₀ : ∀ y : C₀.U, y.1 ∈ PiSet → (e_C_Δ₀ y).1 = y.1)
    (hyp_x : HasDiscDrawingWithBoundaryOrder ιV C₀ PiSet Z 𝒜) :
    ∃ gd₀ : GraphDrawing (divisionIncidenceGraph Z 𝒜) S,
      gd₀.drawing.U ⊆ Δ₀ ∧
      gd₀.drawing.U ∩ subBd Δ₀ = PiSet ∧
      (∀ p ∈ PiSet, ∀ hp : Sum.inl (ιV p) ∈ V(divisionIncidenceGraph Z 𝒜),
        (gd₀.iso.vertexEquiv ⟨Sum.inl (ιV p), hp⟩).1 = p) := by
  obtain ⟨D_E, gd, φ_C, φ_D, hD_E, hgd_U, hPi_bd, _, horder⟩ := hyp_x
  have hPi_fin : PiSet.Finite := finite_of_ncard_ne_zero (by omega)
  have hPi_C : PiSet ⊆ C₀.U := hPi_sub.trans C₀.V_subset_U
  let q : Circle → S := fun w => (φ_C w).val
  let : Fintype PiSet := hPi_fin.fintype
  have hex : ∀ n : PiSet, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ φ_C.symm ⟨n.val, hPi_C n.property⟩ = ee t :=
    fun n => GM19.exists_ee (φ_C.symm ⟨n.val, hPi_C n.property⟩)
  choose t ht0 ht1 ht using hex
  have hmark : ∀ n : PiSet, q (ee (t n)) = n.val := by
    intro n
    rw [← ht n]
    exact congrArg Subtype.val (φ_C.apply_symm_apply ⟨n.val, hPi_C n.property⟩)
  have hti : Function.Injective t := by
    intro n m hnm
    apply Subtype.ext
    rw [← hmark n, ← hmark m, hnm]
  let τ : PiSet ≃ range t := Equiv.ofInjective t hti
  let : Fintype (range t) := (finite_range t).fintype
  have hcardN : Fintype.card PiSet = 4 := (fintypeCard_eq_ncard PiSet).trans hPi_card
  have hcardT : Fintype.card (range t) = 4 := (Fintype.card_congr τ).symm.trans hcardN
  let σ : Fin 4 ≃o range t := Fintype.orderIsoFinOfCardEq _ hcardT
  let b : Fin 4 → ℝ := fun i => (σ i).val
  have hb_mono : StrictMono b := fun _ _ hij => σ.strictMono hij
  have hb01 : ∀ i, b i ∈ Ico (0 : ℝ) 1 := by
    intro i
    obtain ⟨n, hn⟩ := (σ i).property
    change t n = b i at hn
    rw [← hn]
    exact ⟨ht0 n, ht1 n⟩
  have hPi_range : PiSet = range (fun i : Fin 4 => q (ee (b i))) := by
    apply Subset.antisymm
    · intro n hn
      let z : range t := ⟨t ⟨n, hn⟩, mem_range_self (f := t) (⟨n, hn⟩ : PiSet)⟩
      refine ⟨σ.symm z, ?_⟩
      change q (ee (b (σ.symm z))) = n
      have hβ : b (σ.symm z) = t ⟨n, hn⟩ := congrArg Subtype.val (σ.apply_symm_apply z)
      rw [hβ]
      exact hmark ⟨n, hn⟩
    · rintro _ ⟨i, rfl⟩
      change q (ee (b i)) ∈ PiSet
      obtain ⟨n, hn⟩ := (σ i).property
      change t n = b i at hn
      rw [← hn, hmark n]
      exact n.property
  let t₁ : ℝ := 2 * Real.pi * b 0
  let t₂ : ℝ := 2 * Real.pi * b 1
  let t₃ : ℝ := 2 * Real.pi * b 2
  let t₄ : ℝ := 2 * Real.pi * b 3
  let p₁ : S := q (ee (b 0))
  let p₂ : S := q (ee (b 1))
  let p₃ : S := q (ee (b 2))
  let p₄ : S := q (ee (b 3))
  have hPi_eq : PiSet = {p₁, p₂, p₃, p₄} := by
    rw [hPi_range]
    ext x
    simp only [mem_range, Fin.exists_fin_succ, Fin.isValue, IsEmpty.exists_iff, or_false,
      mem_insert_iff, mem_singleton_iff, p₁, p₂, p₃, p₄]
    tauto
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  obtain ⟨s₁, s₂, s₃, s₄, hp₁, hp₂, hp₃, hp₄, hs₁, hs₁₂, hs₂₃, hs₃₄, hs₄, hq₁, hq₂, hq₃, hq₄⟩ :=
    horder t₁ t₂ t₃ t₄ p₁ p₂ p₃ p₄
      (by nlinarith [(hb01 0).1])
      (by nlinarith [hb_mono (show (0 : Fin 4) < 1 by decide)])
      (by nlinarith [hb_mono (show (1 : Fin 4) < 2 by decide)])
      (by nlinarith [hb_mono (show (2 : Fin 4) < 3 by decide)])
      (by nlinarith [(hb01 3).2])
      hPi_eq rfl rfl rfl rfl
  let q₁ : EuclideanPlane := (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₁), hp₁⟩).1
  let q₂ : EuclideanPlane := (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₂), hp₂⟩).1
  let q₃ : EuclideanPlane := (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₃), hp₃⟩).1
  let q₄ : EuclideanPlane := (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₄), hp₄⟩).1
  have htwopi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hee_div : ∀ s : ℝ, ee (s / (2 * Real.pi)) = Circle.exp s := by
    intro s
    unfold ee
    rw [mul_div_cancel₀ _ htwopi_pos.ne']
  obtain ⟨h_circ, -, hh₀, hh₁, hh₂, hh₃⟩ :=
    exists_circle_four_point_move
      (a₀ := s₁ / (2 * Real.pi)) (a₁ := s₂ / (2 * Real.pi))
      (a₂ := s₃ / (2 * Real.pi)) (a₃ := s₄ / (2 * Real.pi))
      (b₀ := b 0) (b₁ := b 1) (b₂ := b 2) (b₃ := b 3)
      (div_lt_div_of_pos_right hs₁₂ htwopi_pos)
      (div_lt_div_of_pos_right hs₂₃ htwopi_pos)
      (div_lt_div_of_pos_right hs₃₄ htwopi_pos)
      (by
        have h1 : s₄ / (2 * Real.pi) < 1 := (div_lt_one htwopi_pos).mpr hs₄
        have h2 : 0 ≤ s₁ / (2 * Real.pi) := div_nonneg hs₁ htwopi_pos.le
        linarith)
      (hb_mono (show (0 : Fin 4) < 1 by decide))
      (hb_mono (show (1 : Fin 4) < 2 by decide))
      (hb_mono (show (2 : Fin 4) < 3 by decide))
      (by linarith [(hb01 0).1, (hb01 3).2])
  rw [hee_div] at hh₀ hh₁ hh₂ hh₃
  obtain ⟨hS_surf, _⟩ := GM11.IsSphere.isClosedSurface hS
  have hsubBd_DE : subBd D_E = discBd D_E := subBd_eq_discBd_plane hD_E
  have hsubBd_Δ₀ : subBd Δ₀ = discBd Δ₀ := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS_surf hΔ₀]
  let e_bd : discBd D_E ≃ₜ discBd Δ₀ :=
    (Homeomorph.setCongr hsubBd_DE.symm).trans
      (φ_D.symm.trans (h_circ.trans (φ_C.trans (e_C_Δ₀.trans (Homeomorph.setCongr hsubBd_Δ₀)))))
  have hq₁_bd : q₁ ∈ discBd D_E := by
    rw [← hsubBd_DE]
    change (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₁), hp₁⟩).1 ∈ subBd D_E
    rw [← hq₁]
    exact (φ_D (Circle.exp s₁)).2
  have hq₂_bd : q₂ ∈ discBd D_E := by
    rw [← hsubBd_DE]
    change (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₂), hp₂⟩).1 ∈ subBd D_E
    rw [← hq₂]
    exact (φ_D (Circle.exp s₂)).2
  have hq₃_bd : q₃ ∈ discBd D_E := by
    rw [← hsubBd_DE]
    change (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₃), hp₃⟩).1 ∈ subBd D_E
    rw [← hq₃]
    exact (φ_D (Circle.exp s₃)).2
  have hq₄_bd : q₄ ∈ discBd D_E := by
    rw [← hsubBd_DE]
    change (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₄), hp₄⟩).1 ∈ subBd D_E
    rw [← hq₄]
    exact (φ_D (Circle.exp s₄)).2
  have hp₁_Pi : p₁ ∈ PiSet := hPi_eq ▸ by simp
  have hp₂_Pi : p₂ ∈ PiSet := hPi_eq ▸ by simp
  have hp₃_Pi : p₃ ∈ PiSet := hPi_eq ▸ by simp
  have hp₄_Pi : p₄ ∈ PiSet := hPi_eq ▸ by simp
  have he_bd_val : ∀ (x : discBd D_E) (s : ℝ) (i : Fin 4),
      (φ_D (Circle.exp s)).1 = x.1 → h_circ (Circle.exp s) = ee (b i) →
      (e_bd x).1 = q (ee (b i)) := by
    intro x s i hφs hhs
    have hx_eq : (⟨x.1, hsubBd_DE.symm ▸ x.2⟩ : subBd D_E) = φ_D (Circle.exp s) :=
      Subtype.ext hφs.symm
    have hsymm : φ_D.symm ⟨x.1, hsubBd_DE.symm ▸ x.2⟩ = Circle.exp s := by
      rw [hx_eq, φ_D.symm_apply_apply]
    change (e_C_Δ₀ (φ_C (h_circ (φ_D.symm ⟨x.1, hsubBd_DE.symm ▸ x.2⟩)))).1 = q (ee (b i))
    rw [hsymm, hhs]
    have hmem : (φ_C (ee (b i))).1 ∈ PiSet := by
      rw [hPi_range]
      exact ⟨i, rfl⟩
    exact he_C_Δ₀ (φ_C (ee (b i))) hmem
  have he_q₁ : (e_bd ⟨q₁, hq₁_bd⟩).1 = p₁ := he_bd_val ⟨q₁, hq₁_bd⟩ s₁ 0 hq₁ hh₀
  have he_q₂ : (e_bd ⟨q₂, hq₂_bd⟩).1 = p₂ := he_bd_val ⟨q₂, hq₂_bd⟩ s₂ 1 hq₂ hh₁
  have he_q₃ : (e_bd ⟨q₃, hq₃_bd⟩).1 = p₃ := he_bd_val ⟨q₃, hq₃_bd⟩ s₃ 2 hq₃ hh₂
  have he_q₄ : (e_bd ⟨q₄, hq₄_bd⟩).1 = p₄ := he_bd_val ⟨q₄, hq₄_bd⟩ s₄ 3 hq₄ hh₃
  let g : EuclideanPlane → S := fun x => if hx : x ∈ discBd D_E then (e_bd ⟨x, hx⟩).1 else p₁
  let g' : S → EuclideanPlane := fun y => if hy : y ∈ discBd Δ₀ then (e_bd.symm ⟨y, hy⟩).1 else q₁
  have hPH_bd : Whitney.PH (discBd D_E) (discBd Δ₀) g g' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [g, hx, dite_true]
      exact (e_bd ⟨x, hx⟩).2
    · intro y hy
      simp only [g', hy, dite_true]
      exact (e_bd.symm ⟨y, hy⟩).2
    · intro x hx
      simp only [g, g', hx, dite_true, (e_bd ⟨x, hx⟩).2]
      exact congrArg Subtype.val (e_bd.symm_apply_apply ⟨x, hx⟩)
    · intro y hy
      simp only [g, g', hy, dite_true, (e_bd.symm ⟨y, hy⟩).2]
      exact congrArg Subtype.val (e_bd.apply_symm_apply ⟨y, hy⟩)
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : (discBd D_E).domRestrict g = fun x : discBd D_E => (e_bd x).1 := by
        funext x
        simp [g, x.2]
      rw [heq]
      exact continuous_subtype_val.comp e_bd.continuous
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : (discBd Δ₀).domRestrict g' = fun y : discBd Δ₀ => (e_bd.symm y).1 := by
        funext y
        simp [g', y.2]
      rw [heq]
      exact continuous_subtype_val.comp e_bd.symm.continuous
  obtain ⟨f, f', hPH, hfg, _⟩ := Whitney.exists_disc_PH hD_E hΔ₀ hPH_bd
  have hfq₁ : f q₁ = p₁ := by rw [hfg hq₁_bd]; simp only [g, hq₁_bd, dite_true, he_q₁]
  have hfq₂ : f q₂ = p₂ := by rw [hfg hq₂_bd]; simp only [g, hq₂_bd, dite_true, he_q₂]
  have hfq₃ : f q₃ = p₃ := by rw [hfg hq₃_bd]; simp only [g, hq₃_bd, dite_true, he_q₃]
  have hfq₄ : f q₄ = p₄ := by rw [hfg hq₄_bd]; simp only [g, hq₄_bd, dite_true, he_q₄]
  have hf_int : ∀ x ∈ D_E \ discBd D_E, f x ∈ Δ₀ \ subBd Δ₀ := by
    rintro x ⟨hxD, hxnot⟩
    refine ⟨hPH.1 hxD, ?_⟩
    rw [hsubBd_Δ₀]
    intro hfx_bd
    have hfx_eq : g' (f x) = x := by
      have h1 : f (g' (f x)) = f x := by
        rw [hfg (hPH_bd.2.1 hfx_bd)]
        exact hPH_bd.2.2.2.1 hfx_bd
      exact hPH.2.2.1.injOn (Surface.discBd_subset D_E (hPH_bd.2.1 hfx_bd)) hxD h1
    exact hxnot (hfx_eq ▸ hPH_bd.2.1 hfx_bd)
  let Q_set : Set EuclideanPlane := {q₁, q₂, q₃, q₄}
  have hQ_fin : Q_set.Finite := by simp [Q_set]
  have hQ_sub : Q_set ⊆ discBd D_E := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact hq₁_bd
    · exact hq₂_bd
    · exact hq₃_bd
    · exact hq₄_bd
  obtain ⟨Ψ_E, _, hΨ_cont, _, _, hΨ_inj, hΨ_sub, hΨ_fix, hΨ_int⟩ :=
    exists_disc_shrink_map_8_3 hD_E hQ_fin.isClosed hQ_sub
  let Φ : EuclideanPlane → S := f ∘ Ψ_E
  have hΨ_maps : MapsTo Ψ_E D_E D_E := fun x hx => hΨ_sub ⟨x, hx, rfl⟩
  have hΦ_cont_DE : ContinuousOn Φ D_E := hPH.2.2.2.2.1.comp hΨ_cont hΨ_maps
  have hΦ_inj_DE : InjOn Φ D_E :=
    hPH.2.2.1.injOn.comp hΨ_inj hΨ_maps
  have hUc : IsCompact gd.drawing.U :=
    hD_E.isCompact.of_isClosed_subset gd.drawing.isClosed_U hgd_U
  obtain ⟨gd₀, hU₀, hV₀, hvert₀, _, _, _⟩ :=
    GraphDrawing.transportOn gd hUc (hΦ_cont_DE.mono hgd_U) (hΦ_inj_DE.mono hgd_U)
  have hΦ_q₁ : Φ q₁ = p₁ := by
    change f (Ψ_E q₁) = p₁
    rw [hΨ_fix q₁ (by simp [Q_set]), hfq₁]
  have hΦ_q₂ : Φ q₂ = p₂ := by
    change f (Ψ_E q₂) = p₂
    rw [hΨ_fix q₂ (by simp [Q_set]), hfq₂]
  have hΦ_q₃ : Φ q₃ = p₃ := by
    change f (Ψ_E q₃) = p₃
    rw [hΨ_fix q₃ (by simp [Q_set]), hfq₃]
  have hΦ_q₄ : Φ q₄ = p₄ := by
    change f (Ψ_E q₄) = p₄
    rw [hΨ_fix q₄ (by simp [Q_set]), hfq₄]
  refine ⟨gd₀, ?_, ?_, ?_⟩
  · rw [hU₀]
    rintro _ ⟨x, hx, rfl⟩
    exact hPH.1 (hΨ_maps (hgd_U hx))
  · rw [hU₀]
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hΦx_bd⟩
      by_cases hxQ : x ∈ Q_set
      · rcases hxQ with rfl | rfl | rfl | rfl
        · rw [hΦ_q₁]; exact hp₁_Pi
        · rw [hΦ_q₂]; exact hp₂_Pi
        · rw [hΦ_q₃]; exact hp₃_Pi
        · rw [hΦ_q₄]; exact hp₄_Pi
      · exact False.elim ((hf_int (Ψ_E x) (hΨ_int x ⟨hgd_U hx, hxQ⟩)).2 hΦx_bd)
    · intro p hp
      rw [hPi_eq] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨⟨q₁, gd.drawing.V_subset_U (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₁), hp₁⟩).2, hΦ_q₁⟩,
          hsubBd_Δ₀.symm ▸ he_q₁ ▸ (e_bd ⟨q₁, hq₁_bd⟩).2⟩
      · exact ⟨⟨q₂, gd.drawing.V_subset_U (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₂), hp₂⟩).2, hΦ_q₂⟩,
          hsubBd_Δ₀.symm ▸ he_q₂ ▸ (e_bd ⟨q₂, hq₂_bd⟩).2⟩
      · exact ⟨⟨q₃, gd.drawing.V_subset_U (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₃), hp₃⟩).2, hΦ_q₃⟩,
          hsubBd_Δ₀.symm ▸ he_q₃ ▸ (e_bd ⟨q₃, hq₃_bd⟩).2⟩
      · exact ⟨⟨q₄, gd.drawing.V_subset_U (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₄), hp₄⟩).2, hΦ_q₄⟩,
          hsubBd_Δ₀.symm ▸ he_q₄ ▸ (e_bd ⟨q₄, hq₄_bd⟩).2⟩
  · intro p hp hp_mem
    rw [hvert₀ ⟨Sum.inl (ιV p), hp_mem⟩]
    rw [hPi_eq] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hΦ_q₁
    · exact hΦ_q₂
    · exact hΦ_q₃
    · exact hΦ_q₄

/-! ## Vertex-Star Thickening for Bipartite Incidence Drawings -/

/-- Small pairwise disjoint closed discs around the vertices of a drawing `Γ₀`, contained in a
prescribed open set `W₀` whenever the vertex lies in `W₀`. -/
theorem exists_vertex_disc_family_in_open
    {S₀ : Type*} [TopologicalSpace S₀] [T2Space S₀]
    (hS₀ : IsClosedSurface S₀) (Γ₀ : Drawing S₀) {W₀ : Set S₀} (hW₀ : IsOpen W₀) :
    ∃ D : Γ₀.V → Set S₀,
      (∀ v, IsClosedDisc (D v) ∧ v.val ∈ interior (D v) ∧ D v ∩ Γ₀.V = {v.val} ∧
        (v.val ∈ W₀ → D v ⊆ W₀) ∧
        ∀ e ∈ Γ₀.E, ¬ Γ₀.toGraph.Inc e v.val → Disjoint (D v) (closure e)) ∧
      (∀ v w, v ≠ w → Disjoint (D v) (D w)) := by
  classical
  obtain ⟨U, hU, hUdisj⟩ := Γ₀.finite_V.t2_separation
  have hex : ∀ v : Γ₀.V, ∃ D : Set S₀, IsClosedDisc D ∧ v.val ∈ interior D ∧ D ⊆ U v.val ∧
      (v.val ∈ W₀ → D ⊆ W₀) ∧
      ∀ e ∈ Γ₀.E, ¬ Γ₀.toGraph.Inc e v.val → Disjoint D (closure e) := by
    intro v
    let F : Set (Set S₀) := {e ∈ Γ₀.E | ¬ Γ₀.toGraph.Inc e v.val}
    let Z : Set S₀ := ⋃ e ∈ F, closure e
    have hF : F.Finite := Γ₀.finite_edges.subset (fun _ h => h.1)
    have hZ : IsClosed Z := hF.isClosed_biUnion fun _ _ => isClosed_closure
    have hvZ : v.val ∉ Z := by
      intro hvZ
      obtain ⟨e, ⟨he, hnot⟩, hve⟩ := mem_iUnion₂.mp hvZ
      obtain ⟨x, y, hl⟩ := Γ₀.toGraph.exists_isLink_of_mem_edgeSet he
      have hends : v.val ∈ ({x, y} : Set S₀) := hl.2.2.2 ▸ ⟨hve, v.property⟩
      rcases hends with hx | hy
      · exact hnot (hx ▸ hl.inc_left)
      · exact hnot ((Set.mem_singleton_iff.mp hy) ▸ hl.inc_right)
    let W_v : Set S₀ := if v.val ∈ W₀ then W₀ else univ
    have hWv_open : IsOpen W_v := by
      dsimp [W_v]
      split_ifs
      · exact hW₀
      · exact isOpen_univ
    have hvWv : v.val ∈ W_v := by
      dsimp [W_v]
      split_ifs with h
      · exact h
      · exact mem_univ _
    have hO : IsOpen ((U v.val ∩ W_v) ∩ Zᶜ) := ((hU v.val).2.inter hWv_open).inter hZ.isOpen_compl
    obtain ⟨D, D', hD, hD'o, hvD', hD'D, hDO, _⟩ :=
      exists_closedDisc_nbhd hS₀ hO ⟨⟨(hU v.val).1, hvWv⟩, hvZ⟩
    refine ⟨D, hD, interior_maximal hD'D hD'o hvD',
      hDO.trans (inter_subset_left.trans inter_subset_left),
      fun hvW₀ x hxD => ?_, ?_⟩
    · have hxWv : x ∈ W_v := (hDO hxD).1.2
      simpa [W_v, hvW₀] using hxWv
    · intro e he hnot
      apply Set.disjoint_left.mpr
      intro x hxD hxe
      exact (hDO hxD).2 (mem_iUnion₂.mpr ⟨e, ⟨he, hnot⟩, hxe⟩)
  choose D hD hvD hDU hDW hDoff using hex
  refine ⟨D, ?_, ?_⟩
  · intro v
    refine ⟨hD v, hvD v, ?_, hDW v, hDoff v⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxD, hxV⟩
      by_contra hxv
      have hvx : v.val ≠ x := Ne.symm hxv
      exact Set.disjoint_left.mp (hUdisj v.property hxV hvx) (hDU v hxD) (hU x).1
    · intro x hx
      have hxv := Set.mem_singleton_iff.mp hx
      exact hxv ▸ ⟨interior_subset (hvD v), v.property⟩
  · intro v w hvw
    have hvw' : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
    exact (hUdisj v.property w.property hvw').mono (hDU v) (hDU w)

/-- Residual arcs whose `0`-endpoints are distinct from all other arcs and whose pairwise
intersections lie in `{a i 1}` can be thickened into thin closed discs `Q i` with
`Q i ∩ Q j = {a i 1} ∩ {a j 1}` for `i ≠ j`. -/
theorem exists_bipartite_arm_discs
    {S₀ ι : Type*} [TopologicalSpace S₀] [T2Space S₀] [ConnectedSpace S₀]
    (hS₀ : IsClosedSurface S₀) {F : Set ι} (hF : F.Finite) (a : ι → unitInterval → S₀)
    (hArc : ∀ i ∈ F, IsArcMap (a i))
    (h0_notMem : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → a i 0 ∉ range (a j))
    (hinter : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → range (a i) ∩ range (a j) ⊆ {a i 1}) :
    ∀ B : Set S₀, IsClosed B → (∀ i ∈ F, range (a i) ∩ B = {a i 0, a i 1}) →
    ∃ Q : ι → Set S₀,
      (∀ i ∈ F, IsClosedDisc (Q i) ∧ Q i ∩ B = {a i 0, a i 1} ∧
        ({a i 0, a i 1} : Set S₀) ⊆ discBd (Q i) ∧ range (a i) ⊆ Q i) ∧
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Q i ∩ Q j = ({a i 1} : Set S₀) ∩ {a j 1}) := by
  classical
  revert hArc h0_notMem hinter
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    intro _ _ _ B _ _
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert i F hi hF ih =>
    intro hArc h0_notMem hinter B hB hcontact
    have hArcF := fun j hj => hArc j (Or.inr hj)
    have h0F := fun j hj k hk hjk => h0_notMem j (Or.inr hj) k (Or.inr hk) hjk
    have hinterF := fun j hj k hk hjk => hinter j (Or.inr hj) k (Or.inr hk) hjk
    have hAi : IsClosed (range (a i)) := (isCompact_range (hArc i (Or.inl rfl)).1).isClosed
    let B' : Set S₀ := B ∪ range (a i)
    have hcontact' : ∀ j ∈ F, range (a j) ∩ B' = {a j 0, a j 1} := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      change range (a j) ∩ (B ∪ range (a i)) = _
      rw [inter_union_distrib_left, hcontact j (Or.inr hj)]
      apply Subset.antisymm
      · rintro z (hz | hz)
        · exact hz
        · exact Or.inr (hinter j (Or.inr hj) i (Or.inl rfl) hji hz)
      · exact subset_union_left
    obtain ⟨Q, hQ, hQQ⟩ := ih hArcF h0F hinterF B' (hB.union hAi) hcontact'
    have hendsB : ∀ j ∈ insert i F, ({a j 0, a j 1} : Set S₀) ⊆ B := by
      intro j hj z hz
      exact ((hcontact j hj).symm.subset hz).2
    have hQ_range : ∀ j ∈ F, Q j ∩ range (a i) ⊆ ({a i 1} : Set S₀) ∩ {a j 1} := by
      intro j hj z ⟨hzQ, hzAi⟩
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hzends : z ∈ ({a j 0, a j 1} : Set S₀) := (hQ j hj).2.1.subset ⟨hzQ, Or.inr hzAi⟩
      rcases hzends with rfl | hzj1
      · exact False.elim (h0_notMem j (Or.inr hj) i (Or.inl rfl) hji hzAi)
      · have hzj1' : z = a j 1 := mem_singleton_iff.mp hzj1
        subst hzj1'
        refine ⟨?_, rfl⟩
        exact hinter i (Or.inl rfl) j (Or.inr hj) hji.symm ⟨hzAi, mem_range_self 1⟩
    let Z : Set S₀ := B ∪ ⋃ j ∈ F, Q j
    have hZ : IsClosed Z := hB.union (hF.isClosed_biUnion fun j hj => (hQ j hj).1.isClosed)
    have hmeet : range (a i) ∩ Z ⊆ {a i 0, a i 1} := by
      rintro z ⟨hzA, hzZ⟩
      rcases hzZ with hzB | hzQ
      · exact (hcontact i (Or.inl rfl)).subset ⟨hzA, hzB⟩
      · obtain ⟨j, hj, hzQj⟩ := mem_iUnion₂.mp hzQ
        exact Or.inr (hQ_range j hj ⟨hzQj, hzA⟩).1
    obtain ⟨Qi, hQi, hQiZ, hQibd, haQi⟩ := exists_normal_arc_disc hS₀ (hArc i (Or.inl rfl)) hZ
      (Or.inl (hendsB i (Or.inl rfl) (by simp)))
      (Or.inl (hendsB i (Or.inl rfl) (by simp))) hmeet
    have hQiB : Qi ∩ B = {a i 0, a i 1} := by
      apply Subset.antisymm
      · exact fun z hz => hQiZ.subset ⟨hz.1, Or.inl hz.2⟩
      · intro z hz
        exact ⟨Surface.discBd_subset Qi (hQibd hz), hendsB i (Or.inl rfl) hz⟩
    have hQB : ∀ j ∈ F, Q j ∩ B = {a j 0, a j 1} := by
      intro j hj
      apply Subset.antisymm
      · exact fun z hz => (hQ j hj).2.1.subset ⟨hz.1, Or.inl hz.2⟩
      · intro z hz
        exact ⟨Surface.discBd_subset (Q j) ((hQ j hj).2.2.1 hz), hendsB j (Or.inr hj) hz⟩
    have hQiQ : ∀ j ∈ F, Qi ∩ Q j = ({a i 1} : Set S₀) ∩ {a j 1} := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      apply Subset.antisymm
      · rintro z ⟨hzQi, hzQj⟩
        have hzends : z ∈ ({a i 0, a i 1} : Set S₀) :=
          hQiZ.subset ⟨hzQi, Or.inr (mem_iUnion₂.mpr ⟨j, hj, hzQj⟩)⟩
        rcases hzends with rfl | hzi1
        · have h0_in : a i 0 ∈ ({a i 1} : Set S₀) ∩ {a j 1} :=
            hQ_range j hj ⟨hzQj, mem_range_self 0⟩
          have h0_eq : a i 0 = a j 1 := mem_singleton_iff.mp h0_in.2
          exact False.elim (h0_notMem i (Or.inl rfl) j (Or.inr hj) hij (h0_eq ▸ mem_range_self 1))
        · have hzi1' : z = a i 1 := mem_singleton_iff.mp hzi1
          subst hzi1'
          exact hQ_range j hj ⟨hzQj, mem_range_self 1⟩
      · rintro z ⟨hzi, hzj⟩
        have hzi' : z = a i 1 := mem_singleton_iff.mp hzi
        have hzj' : z = a j 1 := mem_singleton_iff.mp hzj
        exact ⟨hzi' ▸ haQi (mem_range_self 1), hzj' ▸ (hQ j hj).2.2.2 (mem_range_self 1)⟩
    let Q' : ι → Set S₀ := fun j => if j = i then Qi else Q j
    refine ⟨Q', ?_, ?_⟩
    · intro j hj
      rcases hj with rfl | hj
      · simpa only [Q', ↓reduceIte] using
          (show IsClosedDisc Qi ∧ Qi ∩ B = {a j 0, a j 1} ∧
            ({a j 0, a j 1} : Set S₀) ⊆ discBd Qi ∧ range (a j) ⊆ Qi from
              ⟨hQi, hQiB, hQibd, haQi⟩)
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [Q', hji, ↓reduceIte] using
          (show IsClosedDisc (Q j) ∧ Q j ∩ B = {a j 0, a j 1} ∧
            ({a j 0, a j 1} : Set S₀) ⊆ discBd (Q j) ∧ range (a j) ⊆ Q j from
              ⟨(hQ j hj).1, hQB j hj, (hQ j hj).2.2⟩)
    · intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        simpa only [Q', ↓reduceIte, hki] using hQiQ k (hk.resolve_left hki)
      · have hjF : j ∈ F := hj.resolve_left hji
        by_cases hki : k = i
        · subst k
          simpa only [Q', hji, ↓reduceIte] using
            (Set.inter_comm Qi (Q j)).symm.trans
              ((hQiQ j hjF).trans (Set.inter_comm ({a i 1} : Set S₀) {a j 1}))
        · have hkF : k ∈ F := hk.resolve_left hki
          simpa only [Q', hji, hki, ↓reduceIte] using hQQ j hjF k hkF hjk

/-- Joining a finite family of stars `C_disc A ∪ ⋃ i ∈ F_arm A, B_arm i` into closed discs `D₀ A`
while preserving all intersections with a closed set `K_forbid` and all pairwise intersections
between distinct stars. -/
theorem exists_family_star_join
    {S₀ ι : Type} [TopologicalSpace S₀] (hS₀ : IsClosedSurface S₀)
    {γ : Type*} {𝒜 : Set γ} (h𝒜_fin : 𝒜.Finite)
    (C_disc : γ → Set S₀) (F_arm : γ → Finset ι) (B_arm : ι → Set S₀) (p_att : ι → S₀)
    (K_forbid : Set S₀) (hK_closed : IsClosed K_forbid)
    (hC_disc : ∀ A ∈ 𝒜, IsClosedDisc (C_disc A))
    (hB_disc : ∀ A ∈ 𝒜, ∀ i ∈ F_arm A, IsClosedDisc (B_arm i))
    (hB_disj : ∀ A ∈ 𝒜, ∀ i ∈ F_arm A, ∀ j ∈ F_arm A, i ≠ j → Disjoint (B_arm i) (B_arm j))
    (hCB_inter : ∀ A ∈ 𝒜, ∀ i ∈ F_arm A, C_disc A ∩ B_arm i = {p_att i})
    (hp_C : ∀ A ∈ 𝒜, ∀ i ∈ F_arm A, p_att i ∈ discBd (C_disc A))
    (hp_B : ∀ A ∈ 𝒜, ∀ i ∈ F_arm A, p_att i ∈ discBd (B_arm i))
    (hp_not_K : ∀ A ∈ 𝒜, ∀ i ∈ F_arm A, p_att i ∉ K_forbid)
    (hp_not_other : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A' ≠ A → ∀ i ∈ F_arm A,
      p_att i ∉ C_disc A' ∪ ⋃ j ∈ F_arm A', B_arm j) :
    let Star : γ → Set S₀ := fun A => C_disc A ∪ ⋃ i ∈ F_arm A, B_arm i
    ∃ D₀ : γ → Set S₀,
      (∀ A ∈ 𝒜, IsClosedDisc (D₀ A) ∧ Star A ⊆ D₀ A ∧
        D₀ A ∩ K_forbid = Star A ∩ K_forbid ∧
        (discBd (C_disc A) ∪ ⋃ i ∈ F_arm A, discBd (B_arm i)) ∩ K_forbid ⊆ discBd (D₀ A)) ∧
      (∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' → D₀ A ∩ D₀ A' = Star A ∩ Star A') := by
  classical
  have ht2 : T2Space S₀ := hS₀.2.1
  let Star : γ → Set S₀ := fun A => C_disc A ∪ ⋃ i ∈ F_arm A, B_arm i
  have hStar_closed : ∀ A ∈ 𝒜, IsClosed (Star A) := by
    intro A hA
    exact (hC_disc A hA).isClosed.union
      ((F_arm A).finite_toSet.isClosed_biUnion fun i hi => (hB_disc A hA i hi).isClosed)
  suffices h_ind : ∀ ℱ : Set γ, ℱ.Finite → ℱ ⊆ 𝒜 →
      ∃ D₀ : γ → Set S₀,
        (∀ A ∈ ℱ, IsClosedDisc (D₀ A) ∧ Star A ⊆ D₀ A ∧
          D₀ A ∩ (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ ℱ, Star A'') =
            Star A ∩ (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ ℱ, Star A'') ∧
          (discBd (C_disc A) ∪ ⋃ i ∈ F_arm A, discBd (B_arm i)) ∩ K_forbid ⊆ discBd (D₀ A)) ∧
        (∀ A ∈ ℱ, ∀ A' ∈ ℱ, A ≠ A' → D₀ A ∩ D₀ A' = Star A ∩ Star A') by
    obtain ⟨D₀, hD₀, hD₀_inter⟩ := h_ind 𝒜 h𝒜_fin Subset.rfl
    refine ⟨D₀, fun A hA => ?_, hD₀_inter⟩
    obtain ⟨h1, h2, h3, h4⟩ := hD₀ A hA
    simp only [sdiff_self, biUnion_empty, union_empty] at h3
    exact ⟨h1, h2, h3, h4⟩
  intro ℱ hℱ_fin
  induction ℱ, hℱ_fin using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert A ℱ hA_not_ℱ hℱ_fin ih =>
    intro h_sub
    have hA_𝒜 : A ∈ 𝒜 := h_sub (mem_insert A ℱ)
    have hℱ_sub : ℱ ⊆ 𝒜 := (subset_insert A ℱ).trans h_sub
    obtain ⟨D₀, hD₀, hD₀_inter⟩ := ih hℱ_sub
    have hA_in_diff : A ∈ 𝒜 \ ℱ := ⟨hA_𝒜, hA_not_ℱ⟩
    have hD₀_StarA : ∀ A' ∈ ℱ, D₀ A' ∩ Star A = Star A' ∩ Star A := by
      intro A' hA'
      have h_eq := (hD₀ A' hA').2.2.1
      ext x
      constructor
      · rintro ⟨hxD, hxSA⟩
        have hx_in : x ∈ D₀ A' ∩ (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ ℱ, Star A'') :=
          ⟨hxD, Or.inr (mem_iUnion₂.mpr ⟨A, hA_in_diff, hxSA⟩)⟩
        rw [h_eq] at hx_in
        exact ⟨hx_in.1, hxSA⟩
      · rintro ⟨hxSA', hxSA⟩
        exact ⟨(hD₀ A' hA').2.1 hxSA', hxSA⟩
    let Z : Set S₀ :=
      (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ insert A ℱ, Star A'') ∪ ⋃ A' ∈ ℱ, D₀ A'
    have hZ_closed : IsClosed Z := by
      refine (hK_closed.union ?_).union ?_
      · exact (h𝒜_fin.subset sdiff_subset).isClosed_biUnion fun A'' hA'' =>
          hStar_closed A'' hA''.1
      · exact hℱ_fin.isClosed_biUnion fun A' hA' => (hD₀ A' hA').1.isClosed
    have hp_not_Z : ∀ i ∈ F_arm A, p_att i ∉ Z := by
      intro i hi hpZ
      have hp_in_SA : p_att i ∈ Star A :=
        Or.inl (Surface.discBd_subset (C_disc A) (hp_C A hA_𝒜 i hi))
      rcases hpZ with (hpK | hp_rem) | hp_done
      · exact hp_not_K A hA_𝒜 i hi hpK
      · obtain ⟨A'', hA'', hpA''⟩ := mem_iUnion₂.mp hp_rem
        have hne : A'' ≠ A := fun heq => hA''.2 (heq ▸ mem_insert A ℱ)
        exact hp_not_other A hA_𝒜 A'' hA''.1 hne i hi hpA''
      · obtain ⟨A', hA', hpD₀⟩ := mem_iUnion₂.mp hp_done
        have hne : A' ≠ A := fun heq => hA_not_ℱ (heq ▸ hA')
        have hp_SA' : p_att i ∈ Star A' := ((hD₀_StarA A' hA').subset ⟨hpD₀, hp_in_SA⟩).1
        exact hp_not_other A hA_𝒜 A' (hℱ_sub hA') hne i hi hp_SA'
    obtain ⟨D_A, hDA_disc, hDA_sub, -, hDA_Z, hDA_bd⟩ :=
      exists_finite_join_preserving_contacts hS₀ (C_disc A) univ B_arm p_att
        (hC_disc A hA_𝒜) isOpen_univ (subset_univ _) (F_arm A) Z hZ_closed
        (hB_disc A hA_𝒜) (hB_disj A hA_𝒜) (hCB_inter A hA_𝒜)
        (hp_C A hA_𝒜) (hp_B A hA_𝒜) (fun _ _ => subset_univ _) hp_not_Z
    let D₀' : γ → Set S₀ := fun B => if B = A then D_A else D₀ B
    refine ⟨D₀', ?_, ?_⟩
    · intro B hB
      rcases hB with rfl | hB_ℱ
      · simp only [D₀', ↓reduceIte]
        refine ⟨hDA_disc, hDA_sub, ?_, ?_⟩
        · ext x
          constructor
          · rintro ⟨hxD, hxrem⟩
            have hxZ : x ∈ D_A ∩ Z := ⟨hxD, Or.inl hxrem⟩
            rw [hDA_Z] at hxZ
            exact ⟨hxZ.1, hxrem⟩
          · rintro ⟨hxS, hxrem⟩
            exact ⟨hDA_sub hxS, hxrem⟩
        · intro x ⟨hxbd, hxK⟩
          exact hDA_bd ⟨hxbd, Or.inl (Or.inl hxK)⟩
      · have hBA : B ≠ A := fun heq => hA_not_ℱ (heq ▸ hB_ℱ)
        simp only [D₀', hBA, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := hD₀ B hB_ℱ
        refine ⟨h1, h2, ?_, h4⟩
        have h_sub_rem : (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ insert A ℱ, Star A'') ⊆
            (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ ℱ, Star A'') := by
          refine union_subset_union_right K_forbid (biUnion_subset_biUnion_left ?_)
          exact sdiff_subset_sdiff Subset.rfl (subset_insert A ℱ)
        ext x
        constructor
        · rintro ⟨hxD, hxrem⟩
          have hx_in : x ∈ D₀ B ∩ (K_forbid ∪ ⋃ A'' ∈ 𝒜 \ ℱ, Star A'') :=
            ⟨hxD, h_sub_rem hxrem⟩
          rw [h3] at hx_in
          exact ⟨hx_in.1, hxrem⟩
        · rintro ⟨hxS, hxrem⟩
          exact ⟨h2 hxS, hxrem⟩
    · intro B₁ hB₁ B₂ hB₂ hne
      have hDA_D₀ : ∀ A' ∈ ℱ, D_A ∩ D₀ A' = Star A ∩ Star A' := by
        intro A' hA'
        have h1 : D_A ∩ D₀ A' = Star A ∩ D₀ A' := by
          ext x
          constructor
          · rintro ⟨hxDA, hxD₀⟩
            have hxZ : x ∈ D_A ∩ Z := ⟨hxDA, Or.inr (mem_iUnion₂.mpr ⟨A', hA', hxD₀⟩)⟩
            rw [hDA_Z] at hxZ
            exact ⟨hxZ.1, hxD₀⟩
          · rintro ⟨hxSA, hxD₀⟩
            exact ⟨hDA_sub hxSA, hxD₀⟩
        rw [h1, Set.inter_comm (Star A), hD₀_StarA A' hA', Set.inter_comm (Star A')]
      by_cases hB₁A : B₁ = A
      · subst B₁
        have hB₂A : B₂ ≠ A := Ne.symm hne
        have hB₂_ℱ : B₂ ∈ ℱ := hB₂.resolve_left hB₂A
        simpa only [D₀', ↓reduceIte, hB₂A] using hDA_D₀ B₂ hB₂_ℱ
      · have hB₁_ℱ : B₁ ∈ ℱ := hB₁.resolve_left hB₁A
        by_cases hB₂A : B₂ = A
        · subst B₂
          simpa only [D₀', hB₁A, ↓reduceIte] using
            (Set.inter_comm D_A (D₀ B₁)).symm.trans
              ((hDA_D₀ B₁ hB₁_ℱ).trans (Set.inter_comm (Star A) (Star B₁)))
        · have hB₂_ℱ : B₂ ∈ ℱ := hB₂.resolve_left hB₂A
          simpa only [D₀', hB₁A, hB₂A, ↓reduceIte] using hD₀_inter B₁ hB₁_ℱ B₂ hB₂_ℱ hne

/-- **Graph Minors XXII, (8.3), Claim (1)** (Section 8, page 560):
"(1) For each $v \in Z$ there exists $\alpha(v) \in \Delta_0$, and for each $A \in \mathcal{A}$
there exists a closed disc $D(A) \subseteq \Delta_0$, such that
- $\alpha(v) = v$ for all $v \in \Pi$;
- for each $A \in \mathcal{A}$ and $v \in \bar{\pi}(A)$, $\alpha(v) \in \text{bd}(D(A))$;
  and for each $v \in Z$ and $A \in \mathcal{A}$, if $\alpha(v) \in D(A)$ then
  $v \in \bar{\pi}(A)$;
- for all distinct $A, A' \in \mathcal{A}$,
  $D(A) \cap D(A') = \{\alpha(v) : v \in \bar{\pi}(A) \cap \bar{\pi}(A')\}$;
- for all $A \in \mathcal{A}$,
  $D(A) \cap \text{bd}(\Delta_0) = \{\alpha(v) : v \in \bar{\pi}(A) \cap \Pi\}$;
- for all distinct $v, v' \in Z$, $\alpha(v) \ne \alpha(v')$." -/
theorem lemma_8_3_claim_1
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (e_C_Δ₀ : C₀.U ≃ₜ subBd Δ₀)
    (he_C_Δ₀ : ∀ y : C₀.U, y.1 ∈ PiSet → (e_C_Δ₀ y).1 = y.1) :
    ∃ (α_map : α → S) (D : Graph α β → Set S),
      (∀ v ∈ Z, α_map v ∈ Δ₀) ∧
      (∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀) ∧
      (∀ p ∈ PiSet, α_map (ιV p) = p) ∧
      (∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A)) ∧
      (∀ v ∈ Z, ∀ A ∈ 𝒜, α_map v ∈ D A → v ∈ Set.range (πA A)) ∧
      (∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
        D A ∩ D A' = α_map '' (Set.range (πA A) ∩ Set.range (πA A'))) ∧
      (∀ A ∈ 𝒜,
        D A ∩ subBd Δ₀ = α_map '' (Set.range (πA A) ∩ (ιV '' PiSet))) ∧
      (∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' → α_map v ≠ α_map v') := by
  classical
  obtain ⟨gd₀, hgd₀_U, hgd₀_bd, hgd₀_Pi⟩ :=
    exists_transported_incidence_drawing_8_3
      h83.hyp_i.1 h83.hyp_iii.1 h83.hyp_iii.2 hΔ₀ e_C_Δ₀ he_C_Δ₀ h83.hyp_x
  have hπ_eq_Z : ∀ A ∈ 𝒜, Set.range (πA A) = Z ∩ V(A) :=
    fun A hA => (h83.hyp_vii A hA).2.2
  let S₀ : Type := OnePoint EuclideanPlane
  obtain ⟨e_sph⟩ := h83.hyp_i.1
  have hS₀_sph : IsSphere S₀ := ⟨Homeomorph.refl S₀⟩
  obtain ⟨hS₀_surf, hS₀_conn⟩ := GM11.IsSphere.isClosedSurface hS₀_sph
  obtain ⟨hS_surf, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have : ConnectedSpace S₀ := hS₀_conn
  have : T2Space S₀ := hS₀_surf.2.1
  have hUc₀ : IsCompact gd₀.drawing.U :=
    hΔ₀.isCompact.of_isClosed_subset gd₀.drawing.isClosed_U hgd₀_U
  obtain ⟨gd₁, hU₁, hV₁, hvert₁, hedge₁, _, _⟩ :=
    GraphDrawing.transportOn gd₀ hUc₀ e_sph.continuous.continuousOn e_sph.injective.injOn
  let Δ₀_S₀ : Set S₀ := e_sph '' Δ₀
  have hΔ₀_S₀ : IsClosedDisc Δ₀_S₀ := by
    rcases hΔ₀ with ⟨φ⟩
    exact ⟨φ.trans (e_sph.image Δ₀)⟩
  have hbd_Δ₀_eq : subBd Δ₀ = discBd Δ₀ := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS_surf hΔ₀]
  have hbd_Δ₀_S₀_eq : subBd Δ₀_S₀ = discBd Δ₀_S₀ := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS₀_surf hΔ₀_S₀]
  have hbd_S₀_img : subBd Δ₀_S₀ = e_sph '' subBd Δ₀ := by
    rw [GM11.subBd_eq_frontier, GM11.subBd_eq_frontier]
    exact (e_sph.image_frontier Δ₀).symm
  have hint_S₀_img : interior Δ₀_S₀ = e_sph '' interior Δ₀ :=
    (e_sph.image_interior Δ₀).symm
  have hint_Δ₀ : Δ₀ \ subBd Δ₀ = interior Δ₀ := by
    rw [GM11.subBd_eq_frontier, frontier, hΔ₀.isClosed.closure_eq]
    ext x
    simp only [mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hx, h⟩ => h hx, fun hx => ⟨interior_subset hx, fun _ => hx⟩⟩
  have hint_Δ₀_S₀ : Δ₀_S₀ \ subBd Δ₀_S₀ = interior Δ₀_S₀ := by
    rw [GM11.subBd_eq_frontier, frontier, hΔ₀_S₀.isClosed.closure_eq]
    ext x
    simp only [mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hx, h⟩ => h hx, fun hx => ⟨interior_subset hx, fun _ => hx⟩⟩
  let vZ_G' (v : α) (hv : v ∈ Z) : V(divisionIncidenceGraph Z 𝒜) :=
    ⟨Sum.inl v, Or.inl ⟨v, hv, rfl⟩⟩
  let vA_G' (A : Graph α β) (hA : A ∈ 𝒜) : V(divisionIncidenceGraph Z 𝒜) :=
    ⟨Sum.inr A, Or.inr ⟨A, hA, rfl⟩⟩
  have hPi_card_eq : PiSet.ncard = 4 := h83.hyp_iii.2
  have hPi_ne : PiSet.Nonempty := nonempty_of_ncard_ne_zero (by omega : PiSet.ncard ≠ 0)
  let s_def : S := hPi_ne.some
  let α_map : α → S := fun v =>
    if hv : v ∈ Z then (gd₀.iso.vertexEquiv (vZ_G' v hv)).1 else s_def
  have hα_Z : ∀ (v : α) (hv : v ∈ Z), α_map v = (gd₀.iso.vertexEquiv (vZ_G' v hv)).1 :=
    fun v hv => by simp [α_map, hv]
  have hα_mem_V₀ : ∀ v ∈ Z, α_map v ∈ gd₀.drawing.V := by
    intro v hv
    rw [hα_Z v hv]
    exact (gd₀.iso.vertexEquiv (vZ_G' v hv)).2
  have hα_mem_Δ₀ : ∀ v ∈ Z, α_map v ∈ Δ₀ :=
    fun v hv => hgd₀_U (gd₀.drawing.V_subset_U (hα_mem_V₀ v hv))
  have hα_Pi : ∀ p ∈ PiSet, α_map (ιV p) = p := by
    intro p hp
    have hpZ : ιV p ∈ Z := h83.hyp_vi.2.1 ⟨p, hp, rfl⟩
    rw [hα_Z (ιV p) hpZ]
    exact hgd₀_Pi p hp (Or.inl ⟨ιV p, hpZ, rfl⟩)
  have hα_inj : ∀ v ∈ Z, ∀ v' ∈ Z, α_map v = α_map v' → v = v' := by
    intro v hv v' hv' heq
    rw [hα_Z v hv, hα_Z v' hv'] at heq
    have h1 := gd₀.iso.vertexEquiv.injective (Subtype.ext heq)
    exact Sum.inl.inj (congrArg Subtype.val h1)
  have hα_bd_iff : ∀ v ∈ Z, α_map v ∈ subBd Δ₀ ↔ v ∈ ιV '' PiSet := by
    intro v hv
    constructor
    · intro hbd
      have h_in_Pi : α_map v ∈ PiSet := by
        rw [← hgd₀_bd]
        exact ⟨gd₀.drawing.V_subset_U (hα_mem_V₀ v hv), hbd⟩
      have hpZ : ιV (α_map v) ∈ Z := h83.hyp_vi.2.1 ⟨α_map v, h_in_Pi, rfl⟩
      have heq : α_map (ιV (α_map v)) = α_map v := hα_Pi (α_map v) h_in_Pi
      have hv_eq : v = ιV (α_map v) := (hα_inj (ιV (α_map v)) hpZ v hv heq).symm
      exact ⟨α_map v, h_in_Pi, hv_eq.symm⟩
    · rintro ⟨p, hp, rfl⟩
      rw [hα_Pi p hp]
      have h_in : p ∈ gd₀.drawing.U ∩ subBd Δ₀ := hgd₀_bd.symm ▸ hp
      exact h_in.2
  let wZ (v : α) (hv : v ∈ Z) : gd₁.drawing.V := gd₁.iso.vertexEquiv (vZ_G' v hv)
  let wA (A : Graph α β) (hA : A ∈ 𝒜) : gd₁.drawing.V := gd₁.iso.vertexEquiv (vA_G' A hA)
  have hwZ_val : ∀ (v : α) (hv : v ∈ Z), (wZ v hv).1 = e_sph (α_map v) := by
    intro v hv
    rw [hα_Z v hv]
    exact hvert₁ (vZ_G' v hv)
  have hwA_val : ∀ (A : Graph α β) (hA : A ∈ 𝒜),
      (wA A hA).1 = e_sph (gd₀.iso.vertexEquiv (vA_G' A hA)).1 :=
    fun A hA => hvert₁ (vA_G' A hA)
  have hwA_int : ∀ (A : Graph α β) (hA : A ∈ 𝒜), (wA A hA).1 ∈ interior Δ₀_S₀ := by
    intro A hA
    rw [← hint_Δ₀_S₀, hwA_val A hA, hbd_S₀_img]
    refine ⟨⟨_, hgd₀_U (gd₀.drawing.V_subset_U (gd₀.iso.vertexEquiv (vA_G' A hA)).2), rfl⟩, ?_⟩
    rintro ⟨y, hy_bd, hy_eq⟩
    have hy_val : (gd₀.iso.vertexEquiv (vA_G' A hA)).1 = y := e_sph.injective hy_eq.symm
    have hy_Pi : y ∈ PiSet := by
      rw [← hgd₀_bd]
      exact ⟨hy_val ▸ gd₀.drawing.V_subset_U (gd₀.iso.vertexEquiv (vA_G' A hA)).2, hy_bd⟩
    have hpZ : ιV y ∈ Z := h83.hyp_vi.2.1 ⟨y, hy_Pi, rfl⟩
    have heq : (gd₀.iso.vertexEquiv (vA_G' A hA)).1 =
        (gd₀.iso.vertexEquiv (vZ_G' (ιV y) hpZ)).1 :=
      hy_val.trans (hgd₀_Pi y hy_Pi (Or.inl ⟨ιV y, hpZ, rfl⟩)).symm
    have hcontr := congrArg Subtype.val (gd₀.iso.vertexEquiv.injective (Subtype.ext heq))
    exact Sum.inr_ne_inl hcontr
  have h𝒜_fin : 𝒜.Finite := by
    have : Finite gd₀.drawing.V := gd₀.drawing.finite_V.to_subtype
    have hV₀_fin : V(divisionIncidenceGraph Z 𝒜).Finite :=
      Finite.of_equiv gd₀.drawing.V gd₀.iso.vertexEquiv.symm
    have hinj : Function.Injective (fun A : 𝒜 => (⟨Sum.inr A.1, Or.inr ⟨A.1, A.2, rfl⟩⟩ :
        V(divisionIncidenceGraph Z 𝒜))) := by
      intro A₁ A₂ h
      exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    have : Finite V(divisionIncidenceGraph Z 𝒜) := hV₀_fin
    exact Finite.of_injective _ hinj
  obtain ⟨D_v, hD_v, hDD_v⟩ :=
    exists_vertex_disc_family_in_open hS₀_surf gd₁.drawing
      (W₀ := interior Δ₀_S₀) isOpen_interior
  let e₀_of (e : gd₁.drawing.E) : E(divisionIncidenceGraph Z 𝒜) :=
    gd₁.iso.edgeEquiv.symm e
  let u_of (e : gd₁.drawing.E) : gd₁.drawing.V :=
    wA (e₀_of e).1.2 (e₀_of e).2.2.1
  let v_of (e : gd₁.drawing.E) : gd₁.drawing.V :=
    wZ (e₀_of e).1.1 (e₀_of e).2.1
  have hl_uv : ∀ e : gd₁.drawing.E,
      gd₁.drawing.toGraph.IsLink e.1 (u_of e).1 (v_of e).1 := by
    intro e
    have hlink_G' : (divisionIncidenceGraph Z 𝒜).IsLink (e₀_of e).1
        (vA_G' (e₀_of e).1.2 (e₀_of e).2.2.1).1 (vZ_G' (e₀_of e).1.1 (e₀_of e).2.1).1 :=
      ⟨(e₀_of e).2.1, (e₀_of e).2.2.1, (e₀_of e).2.2.2, Or.inr ⟨rfl, rfl⟩⟩
    have hlink₁ := (gd₁.iso.isLink_iff (e := e₀_of e)
      (x := vA_G' (e₀_of e).1.2 (e₀_of e).2.2.1)
      (y := vZ_G' (e₀_of e).1.1 (e₀_of e).2.1)).mp hlink_G'
    have he_eq : (gd₁.iso.edgeEquiv (e₀_of e)).1 = e.1 :=
      congrArg Subtype.val (gd₁.iso.edgeEquiv.apply_symm_apply e)
    rw [he_eq] at hlink₁
    exact hlink₁
  have hne_uv : ∀ e : gd₁.drawing.E, u_of e ≠ v_of e := by
    intro e h
    have h1 := congrArg Subtype.val (gd₁.iso.vertexEquiv.injective h)
    exact Sum.inr_ne_inl h1
  have he_sub_int : ∀ e : gd₁.drawing.E, e.1 ⊆ interior Δ₀_S₀ := by
    intro e x hxe
    rw [← hint_Δ₀_S₀]
    have hxU₁ : x ∈ gd₁.drawing.U := (e.2.2.1 hxe).1
    rw [hU₁] at hxU₁
    obtain ⟨y, hyU₀, rfl⟩ := hxU₁
    refine ⟨⟨y, hgd₀_U hyU₀, rfl⟩, ?_⟩
    rw [hbd_S₀_img]
    rintro ⟨y', hy'_bd, hy'_eq⟩
    have hy_eq : y = y' := e_sph.injective hy'_eq.symm
    subst hy_eq
    have hy_Pi : y ∈ PiSet := by
      rw [← hgd₀_bd]
      exact ⟨hyU₀, hy'_bd⟩
    have hpZ : ιV y ∈ Z := h83.hyp_vi.2.1 ⟨y, hy_Pi, rfl⟩
    have hy_V₀ : y ∈ gd₀.drawing.V := by
      rw [← hα_Pi y hy_Pi]
      exact hα_mem_V₀ (ιV y) hpZ
    have hxy_V₁ : e_sph y ∈ gd₁.drawing.V := by
      rw [hV₁]
      exact ⟨y, hy_V₀, rfl⟩
    exact (e.2.2.1 hxe).2 hxy_V₁
  have hex_b : ∀ e : gd₁.drawing.E, ∃ b : unitInterval → S₀,
      IsArcMap b ∧ range b ⊆ closure e.1 ∧
        b 0 ∈ discBd (D_v (u_of e)) ∧ b 1 = (v_of e).1 ∧
        range b ∩ D_v (u_of e) = {b 0} ∧ range b ∩ {(v_of e).1} = {b 1} := by
    intro e
    have huv : (u_of e).1 ≠ (v_of e).1 := fun h => hne_uv e (Subtype.ext h)
    have hline := GM11.isLine_closure e.2 huv (hl_uv e).2.2.2
    obtain ⟨a, ha, har, ha0, ha1⟩ := hline.exists_arc
    have hdisj_u_v : Disjoint (D_v (u_of e)) {(v_of e).1} := by
      rw [disjoint_singleton_right]
      intro hv_in
      have hv_inter : (v_of e).1 ∈ D_v (u_of e) ∩ gd₁.drawing.V := ⟨hv_in, (v_of e).2⟩
      rw [(hD_v (u_of e)).2.2.1] at hv_inter
      exact huv (mem_singleton_iff.mp hv_inter).symm
    obtain ⟨b, hb, hba, hb0, hb1, hbD, hbE⟩ :=
      GM12.exists_residual_arc_between_closed_sets ha
        (hD_v (u_of e)).1.isClosed isClosed_singleton hdisj_u_v
        (ha0 ▸ interior_subset (hD_v (u_of e)).2.1) (ha1 ▸ mem_singleton _)
    have hbd0 : b 0 ∈ discBd (D_v (u_of e)) := by
      rwa [GM11.IsClosedDisc.frontier_eq_discBd hS₀_surf (hD_v (u_of e)).1] at hb0
    have hb1_eq : b 1 = (v_of e).1 :=
      mem_singleton_iff.mp (isClosed_singleton.closure_subset hb1.1)
    exact ⟨b, hb, hba.trans har.subset, hbd0, hb1_eq, hbD, hbE⟩
  choose b hb hsub hb0 hb1 hbD hbE using hex_b
  have hrange_V : ∀ e : gd₁.drawing.E, range (b e) ∩ gd₁.drawing.V = {b e 1} := by
    intro e
    apply Subset.antisymm
    · rintro z ⟨hzb, hzV⟩
      have hz_ends : z ∈ ({(u_of e).1, (v_of e).1} : Set S₀) :=
        (hl_uv e).2.2.2 ▸ ⟨hsub e hzb, hzV⟩
      rcases hz_ends with rfl | hzv
      · have hzDu : (u_of e).1 ∈ D_v (u_of e) := interior_subset (hD_v (u_of e)).2.1
        have hz0 : (u_of e).1 = b e 0 := mem_singleton_iff.mp ((hbD e).subset ⟨hzb, hzDu⟩)
        have hfr : b e 0 ∈ frontier (D_v (u_of e)) := by
          rw [GM11.IsClosedDisc.frontier_eq_discBd hS₀_surf (hD_v (u_of e)).1]
          exact hb0 e
        exact False.elim (hfr.2 (hz0 ▸ (hD_v (u_of e)).2.1))
      · rw [hb1 e]
        exact hzv
    · intro z hz
      rw [mem_singleton_iff.mp hz]
      exact ⟨⟨1, rfl⟩, (hb1 e).symm ▸ (v_of e).2⟩
  have hrange_int : ∀ e : gd₁.drawing.E, range (b e) \ {b e 1} ⊆ interior Δ₀_S₀ := by
    intro e x ⟨hxb, hx1⟩
    have hx_cl : x ∈ closure e.1 := hsub e hxb
    by_cases hxe : x ∈ e.1
    · exact he_sub_int e hxe
    · have hxV : x ∈ gd₁.drawing.V := by
        by_contra hxV
        exact hxe ((gd₁.drawing.closure_diff_V e.2).subset ⟨hx_cl, hxV⟩)
      have hx_in : x ∈ range (b e) ∩ gd₁.drawing.V := ⟨hxb, hxV⟩
      rw [hrange_V e] at hx_in
      exact False.elim (hx1 hx_in)
  have hoff : ∀ (e : gd₁.drawing.E) (w : gd₁.drawing.V),
      w ≠ u_of e → w ≠ v_of e → Disjoint (range (b e)) (D_v w) := by
    intro e w hwu hwv
    have hnot : ¬ gd₁.drawing.toGraph.Inc e.1 w.1 := by
      intro hinc
      rcases hinc.eq_or_eq_of_isLink (hl_uv e) with hw | hw
      · exact hwu (Subtype.ext hw)
      · exact hwv (Subtype.ext hw)
    exact ((hD_v w).2.2.2.2 e.1 e.2 hnot).symm.mono_left (hsub e)
  have hb_inter : ∀ e f : gd₁.drawing.E, e ≠ f → range (b e) ∩ range (b f) ⊆ {b e 1} := by
    intro e f hef z ⟨hze, hzf⟩
    have hef' : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
    have hzV : z ∈ gd₁.drawing.V :=
      GM11.closure_inter_subset_V e.2 f.2 hef' ⟨hsub e hze, hsub f hzf⟩
    have hz_in : z ∈ range (b e) ∩ gd₁.drawing.V := ⟨hze, hzV⟩
    rwa [hrange_V e] at hz_in
  have hb0_not_range : ∀ e f : gd₁.drawing.E, e ≠ f → b e 0 ∉ range (b f) := by
    intro e f hef h0f
    have h0e : b e 0 ∈ range (b e) := ⟨0, rfl⟩
    have h01 : b e 0 = b e 1 := mem_singleton_iff.mp (hb_inter e f hef ⟨h0e, h0f⟩)
    have h01' : (0 : unitInterval) = 1 := (hb e).2 h01
    exact zero_ne_one (congrArg Subtype.val h01')
  let V_Z : Set S₀ := {x ∈ gd₁.drawing.V | ∃ (v : α) (hv : v ∈ Z), x = (wZ v hv).1}
  have hVZ_fin : V_Z.Finite := gd₁.drawing.finite_V.subset (fun _ h => h.1)
  let V_𝒜 : Set gd₁.drawing.V := {w : gd₁.drawing.V | ∃ (A : Graph α β) (hA : A ∈ 𝒜), w = wA A hA}
  have hV𝒜_fin : V_𝒜.Finite :=
    (@Set.finite_univ gd₁.drawing.V gd₁.drawing.finite_V.to_subtype).subset (subset_univ _)
  let K_forbid : Set S₀ := (interior Δ₀_S₀)ᶜ ∪ V_Z
  have hK_closed : IsClosed K_forbid := isOpen_interior.isClosed_compl.union hVZ_fin.isClosed
  let B : Set S₀ := K_forbid ∪ ⋃ w ∈ V_𝒜, D_v w
  have hB_closed : IsClosed B :=
    hK_closed.union (hV𝒜_fin.isClosed_biUnion fun w _ => (hD_v w).1.isClosed)
  have hu_mem_V𝒜 : ∀ e : gd₁.drawing.E, u_of e ∈ V_𝒜 :=
    fun e => ⟨(e₀_of e).1.2, (e₀_of e).2.2.1, rfl⟩
  have hv_mem_VZ : ∀ e : gd₁.drawing.E, b e 1 ∈ V_Z := by
    intro e
    rw [hb1 e]
    exact ⟨(v_of e).2, (e₀_of e).1.1, (e₀_of e).2.1, rfl⟩
  have hDu_sub_int : ∀ w ∈ V_𝒜, D_v w ⊆ interior Δ₀_S₀ := by
    rintro w ⟨A, hA, rfl⟩
    exact (hD_v (wA A hA)).2.2.2.1 (hwA_int A hA)
  have hDu_disj_K : ∀ w ∈ V_𝒜, Disjoint (D_v w) K_forbid := by
    intro w hw
    rw [disjoint_union_right]
    refine ⟨disjoint_compl_right_iff_subset.mpr (hDu_sub_int w hw), ?_⟩
    rcases hw with ⟨A, hA, rfl⟩
    rw [disjoint_left]
    rintro x hxD ⟨hxV, v, hv, rfl⟩
    have hx_inter : (wZ v hv).1 ∈ D_v (wA A hA) ∩ gd₁.drawing.V := ⟨hxD, (wZ v hv).2⟩
    rw [(hD_v (wA A hA)).2.2.1, mem_singleton_iff] at hx_inter
    have h1 := congrArg Subtype.val (gd₁.iso.vertexEquiv.injective (Subtype.ext hx_inter))
    exact Sum.inl_ne_inr h1
  have hb_inter_B : ∀ e : gd₁.drawing.E, range (b e) ∩ B = {b e 0, b e 1} := by
    intro e
    apply Subset.antisymm
    · rintro x ⟨hxb, hxB⟩
      rcases hxB with (hx_compl | hx_VZ) | hx_V𝒜
      · by_cases hx1 : x = b e 1
        · exact Or.inr hx1
        · exact False.elim (hx_compl (hrange_int e ⟨hxb, hx1⟩))
      · have hx_in : x ∈ range (b e) ∩ gd₁.drawing.V := ⟨hxb, hx_VZ.1⟩
        rw [hrange_V e] at hx_in
        exact Or.inr (mem_singleton_iff.mp hx_in)
      · obtain ⟨w, hw_𝒜, hxw⟩ := mem_iUnion₂.mp hx_V𝒜
        by_cases hwu : w = u_of e
        · subst hwu
          have hx_in : x ∈ range (b e) ∩ D_v (u_of e) := ⟨hxb, hxw⟩
          rw [hbD e] at hx_in
          exact Or.inl (mem_singleton_iff.mp hx_in)
        · have hwv : w ≠ v_of e := by
            rcases hw_𝒜 with ⟨A, hA, rfl⟩
            intro h
            have h1 := congrArg Subtype.val (gd₁.iso.vertexEquiv.injective h)
            exact Sum.inr_ne_inl h1
          exact False.elim ((hoff e w hwu hwv).le_bot ⟨hxb, hxw⟩)
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, rfl⟩, Or.inr (mem_iUnion₂.mpr ⟨u_of e, hu_mem_V𝒜 e,
          Surface.discBd_subset _ (hb0 e)⟩)⟩
      · exact ⟨⟨1, rfl⟩, Or.inl (Or.inr (hv_mem_VZ e))⟩
  let _ : Fintype gd₁.drawing.E := gd₁.drawing.finite_edges.fintype
  have hE_univ_fin : (univ : Set gd₁.drawing.E).Finite := finite_univ
  obtain ⟨Q, hQ₀, hQQ₀⟩ :=
    exists_bipartite_arm_discs hS₀_surf hE_univ_fin b
      (fun e _ => hb e) (fun e _ f _ => hb0_not_range e f)
      (fun e _ f _ => hb_inter e f) B hB_closed (fun e _ => hb_inter_B e)
  have hQ := fun e => hQ₀ e (mem_univ e)
  have hQQ := fun e₁ e₂ hne => hQQ₀ e₁ (mem_univ e₁) e₂ (mem_univ e₂) hne
  let C_disc : Graph α β → Set S₀ := fun A =>
    if hA : A ∈ 𝒜 then D_v (wA A hA) else ∅
  let F_arm : Graph α β → Finset gd₁.drawing.E := fun A =>
    Finset.univ.filter (fun e : gd₁.drawing.E => (e₀_of e).1.2 = A)
  let p_att : gd₁.drawing.E → S₀ := fun e => b e 0
  have hC_disc_eq : ∀ (A : Graph α β) (hA : A ∈ 𝒜), C_disc A = D_v (wA A hA) :=
    fun A hA => by simp [C_disc, hA]
  have hu_eq_wA : ∀ (A : Graph α β) (hA : A ∈ 𝒜) (e : gd₁.drawing.E),
      e ∈ F_arm A → u_of e = wA A hA := by
    intro A hA e he
    have heA : (e₀_of e).1.2 = A := (Finset.mem_filter.mp he).2
    apply Subtype.ext
    dsimp [u_of, wA, vA_G']
    congr 2
    exact Subtype.ext (congrArg Sum.inr heA)
  have hQ_disj_in_F : ∀ A ∈ 𝒜, ∀ e₁ ∈ F_arm A, ∀ e₂ ∈ F_arm A, e₁ ≠ e₂ →
      Disjoint (Q e₁) (Q e₂) := by
    intro A hA e₁ he₁ e₂ he₂ hne
    rw [Set.disjoint_iff_inter_eq_empty, hQQ e₁ e₂ hne]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx₁, hx₂⟩
    have h12 : b e₁ 1 = b e₂ 1 := (mem_singleton_iff.mp hx₁).symm.trans (mem_singleton_iff.mp hx₂)
    rw [hb1 e₁, hb1 e₂] at h12
    have hv12 := congrArg Subtype.val (gd₁.iso.vertexEquiv.injective (Subtype.ext h12))
    have hz_eq : (e₀_of e₁).1.1 = (e₀_of e₂).1.1 := Sum.inl.inj hv12
    have hA_eq : (e₀_of e₁).1.2 = (e₀_of e₂).1.2 :=
      ((Finset.mem_filter.mp he₁).2).trans ((Finset.mem_filter.mp he₂).2).symm
    have he₀_eq : e₀_of e₁ = e₀_of e₂ := Subtype.ext (Prod.ext hz_eq hA_eq)
    exact hne (gd₁.iso.edgeEquiv.symm.injective he₀_eq)
  have hCB_inter : ∀ A ∈ 𝒜, ∀ e ∈ F_arm A, C_disc A ∩ Q e = {p_att e} := by
    intro A hA e he
    rw [hC_disc_eq A hA, ← hu_eq_wA A hA e he]
    apply Subset.antisymm
    · rintro x ⟨hxD, hxQ⟩
      have hxB : x ∈ Q e ∩ B :=
        ⟨hxQ, Or.inr (mem_iUnion₂.mpr ⟨u_of e, hu_mem_V𝒜 e, hxD⟩)⟩
      rw [(hQ e).2.1] at hxB
      rcases hxB with rfl | h1
      · exact mem_singleton _
      · exfalso
        have hx1 : b e 1 ∈ D_v (u_of e) ∩ K_forbid :=
          ⟨h1 ▸ hxD, Or.inr (hv_mem_VZ e)⟩
        exact (hDu_disj_K (u_of e) (hu_mem_V𝒜 e)).le_bot hx1
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨Surface.discBd_subset _ (hb0 e), (hQ e).2.2.2 ⟨0, rfl⟩⟩
  have hp_C : ∀ A ∈ 𝒜, ∀ e ∈ F_arm A, p_att e ∈ discBd (C_disc A) := by
    intro A hA e he
    rw [hC_disc_eq A hA, ← hu_eq_wA A hA e he]
    exact hb0 e
  have hp_B : ∀ A ∈ 𝒜, ∀ e ∈ F_arm A, p_att e ∈ discBd (Q e) :=
    fun _ _ e _ => (hQ e).2.2.1 (Or.inl rfl)
  have hp_not_K : ∀ A ∈ 𝒜, ∀ e ∈ F_arm A, p_att e ∉ K_forbid := by
    intro A hA e he hpK
    exact (hDu_disj_K (u_of e) (hu_mem_V𝒜 e)).le_bot
      ⟨Surface.discBd_subset _ (hb0 e), hpK⟩
  have hp_not_other : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A' ≠ A → ∀ e ∈ F_arm A,
      p_att e ∉ C_disc A' ∪ ⋃ j ∈ F_arm A', Q j := by
    intro A hA A' hA' hne e he hp_in
    have hp_Du : p_att e ∈ D_v (u_of e) := Surface.discBd_subset _ (hb0 e)
    have hu_ne : wA A' hA' ≠ u_of e := by
      rw [hu_eq_wA A hA e he]
      intro h
      have h1 := congrArg Subtype.val (gd₁.iso.vertexEquiv.injective h)
      exact hne (Sum.inr.inj h1)
    rcases hp_in with hpC' | hpQ'
    · rw [hC_disc_eq A' hA'] at hpC'
      exact (hDD_v (wA A' hA') (u_of e) hu_ne).le_bot ⟨hpC', hp_Du⟩
    · obtain ⟨j, hj, hpQj⟩ := mem_iUnion₂.mp hpQ'
      have hpB : p_att e ∈ Q j ∩ B :=
        ⟨hpQj, Or.inr (mem_iUnion₂.mpr ⟨u_of e, hu_mem_V𝒜 e, hp_Du⟩)⟩
      rw [(hQ j).2.1] at hpB
      rcases hpB with hp0 | hp1
      · have huj : u_of j = wA A' hA' := hu_eq_wA A' hA' j hj
        have hp_Dj : p_att e ∈ D_v (wA A' hA') :=
          hp0 ▸ huj ▸ Surface.discBd_subset _ (hb0 j)
        exact (hDD_v (wA A' hA') (u_of e) hu_ne).le_bot ⟨hp_Dj, hp_Du⟩
      · have hpK : p_att e ∈ K_forbid := hp1.symm ▸ Or.inr (hv_mem_VZ j)
        exact hp_not_K A hA e he hpK
  obtain ⟨D₀, hD₀, hD₀_inter⟩ :=
    exists_family_star_join hS₀_surf h𝒜_fin C_disc F_arm Q p_att K_forbid hK_closed
      (fun A hA => hC_disc_eq A hA ▸ (hD_v (wA A hA)).1)
      (fun _ _ e _ => (hQ e).1)
      hQ_disj_in_F hCB_inter hp_C hp_B hp_not_K hp_not_other
  let Star : Graph α β → Set S₀ := fun A => C_disc A ∪ ⋃ e ∈ F_arm A, Q e
  have hQ_inter_K : ∀ e : gd₁.drawing.E, Q e ∩ K_forbid = {b e 1} := by
    intro e
    apply Subset.antisymm
    · rintro x ⟨hxQ, hxK⟩
      have hxB : x ∈ Q e ∩ B := ⟨hxQ, Or.inl hxK⟩
      rw [(hQ e).2.1] at hxB
      rcases hxB with rfl | h1
      · exact False.elim ((hDu_disj_K (u_of e) (hu_mem_V𝒜 e)).le_bot
          ⟨Surface.discBd_subset _ (hb0 e), hxK⟩)
      · exact h1
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨(hQ e).2.2.2 ⟨1, rfl⟩, Or.inr (hv_mem_VZ e)⟩
  have hF_arm_b1 : ∀ A ∈ 𝒜, (⋃ e ∈ F_arm A, ({b e 1} : Set S₀)) =
      (e_sph ∘ α_map) '' (Z ∩ V(A)) := by
    intro A hA
    ext x
    simp only [mem_iUnion, mem_singleton_iff, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨e, he, rfl⟩
      have heA : (e₀_of e).1.2 = A := (Finset.mem_filter.mp he).2
      refine ⟨(e₀_of e).1.1, ⟨(e₀_of e).2.1, heA ▸ (e₀_of e).2.2.2⟩, ?_⟩
      rw [hb1 e, ← hwZ_val (e₀_of e).1.1 (e₀_of e).2.1]
    · rintro ⟨v, ⟨hvZ, hvA⟩, rfl⟩
      let e₀ : E(divisionIncidenceGraph Z 𝒜) := ⟨(v, A), ⟨hvZ, hA, hvA⟩⟩
      let e : gd₁.drawing.E := gd₁.iso.edgeEquiv e₀
      have he₀ : e₀_of e = e₀ := gd₁.iso.edgeEquiv.symm_apply_apply e₀
      have he_F : e ∈ F_arm A := by
        simp only [F_arm, Finset.mem_filter, Finset.mem_univ, he₀, true_and]
        rfl
      refine ⟨e, he_F, ?_⟩
      have hv_eq : v_of e = wZ v hvZ := by
        apply Subtype.ext
        dsimp [v_of, wZ, vZ_G']
        congr 2
        exact Subtype.ext (congrArg Sum.inl (by rw [he₀]))
      rw [hb1 e, hv_eq, hwZ_val v hvZ]
  have hStar_inter_K : ∀ A ∈ 𝒜, Star A ∩ K_forbid = (e_sph ∘ α_map) '' (Z ∩ V(A)) := by
    intro A hA
    dsimp [Star]
    rw [union_inter_distrib_right, hC_disc_eq A hA,
      (hDu_disj_K (wA A hA) ⟨A, hA, rfl⟩).inter_eq, empty_union]
    have h_bi : (⋃ e ∈ F_arm A, Q e) ∩ K_forbid = ⋃ e ∈ F_arm A, (Q e ∩ K_forbid) := by
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      exact ⟨fun ⟨⟨e, he, hxe⟩, hxK⟩ => ⟨e, he, hxe, hxK⟩,
        fun ⟨e, he, hxe, hxK⟩ => ⟨⟨e, he, hxe⟩, hxK⟩⟩
    rw [h_bi]
    simp_rw [hQ_inter_K]
    exact hF_arm_b1 A hA
  have hD₀_inter_K : ∀ A ∈ 𝒜, D₀ A ∩ K_forbid = (e_sph ∘ α_map) '' (Z ∩ V(A)) := by
    intro A hA
    rw [(hD₀ A hA).2.2.1, hStar_inter_K A hA]
  have hD₀_sub_Δ₀ : ∀ A ∈ 𝒜, D₀ A ⊆ Δ₀_S₀ := by
    intro A hA x hxD
    by_cases hx_int : x ∈ interior Δ₀_S₀
    · exact interior_subset hx_int
    · have hxK : x ∈ D₀ A ∩ K_forbid := ⟨hxD, Or.inl hx_int⟩
      rw [hD₀_inter_K A hA] at hxK
      obtain ⟨v, ⟨hvZ, _⟩, rfl⟩ := hxK
      exact ⟨α_map v, hα_mem_Δ₀ v hvZ, rfl⟩
  have hStar_inter_Star : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
      Star A ∩ Star A' = (e_sph ∘ α_map) '' ((Z ∩ V(A)) ∩ (Z ∩ V(A'))) := by
    intro A hA A' hA' hne
    have hCA_disj_CA' : Disjoint (C_disc A) (C_disc A') := by
      rw [hC_disc_eq A hA, hC_disc_eq A' hA']
      refine hDD_v (wA A hA) (wA A' hA') (fun h => ?_)
      exact hne (Sum.inr.inj (congrArg Subtype.val (gd₁.iso.vertexEquiv.injective h)))
    have hCA_disj_Q' : ∀ e' ∈ F_arm A', Disjoint (C_disc A) (Q e') := by
      intro e' he'
      rw [hC_disc_eq A hA]
      apply Set.disjoint_iff_inter_eq_empty.mpr
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxC, hxQ⟩
      have hxB : x ∈ Q e' ∩ B :=
        ⟨hxQ, Or.inr (mem_iUnion₂.mpr ⟨wA A hA, ⟨A, hA, rfl⟩, hxC⟩)⟩
      rw [(hQ e').2.1] at hxB
      rcases hxB with rfl | h1
      · have hu' : u_of e' = wA A' hA' := hu_eq_wA A' hA' e' he'
        have hxC' : b e' 0 ∈ C_disc A' := by
          rw [hC_disc_eq A' hA', ← hu']
          exact Surface.discBd_subset _ (hb0 e')
        exact hCA_disj_CA'.le_bot ⟨(hC_disc_eq A hA).symm ▸ hxC, hxC'⟩
      · exact (hDu_disj_K (wA A hA) ⟨A, hA, rfl⟩).le_bot
          ⟨h1 ▸ hxC, Or.inr (hv_mem_VZ e')⟩
    have hCA'_disj_Q : ∀ e ∈ F_arm A, Disjoint (Q e) (C_disc A') := by
      intro e he
      rw [hC_disc_eq A' hA']
      apply Set.disjoint_iff_inter_eq_empty.mpr
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxQ, hxC'⟩
      have hxB : x ∈ Q e ∩ B :=
        ⟨hxQ, Or.inr (mem_iUnion₂.mpr ⟨wA A' hA', ⟨A', hA', rfl⟩, hxC'⟩)⟩
      rw [(hQ e).2.1] at hxB
      rcases hxB with rfl | h1
      · have hu : u_of e = wA A hA := hu_eq_wA A hA e he
        have hxC : b e 0 ∈ C_disc A := by
          rw [hC_disc_eq A hA, ← hu]
          exact Surface.discBd_subset _ (hb0 e)
        exact hCA_disj_CA'.le_bot ⟨hxC, (hC_disc_eq A' hA').symm ▸ hxC'⟩
      · exact (hDu_disj_K (wA A' hA') ⟨A', hA', rfl⟩).le_bot
          ⟨h1 ▸ hxC', Or.inr (hv_mem_VZ e)⟩
    apply Subset.antisymm
    · rintro x ⟨hxA, hxA'⟩
      rcases hxA with hxCA | hxQA <;> rcases hxA' with hxCA' | hxQA'
      · exact False.elim (hCA_disj_CA'.le_bot ⟨hxCA, hxCA'⟩)
      · obtain ⟨e', he', hxQe'⟩ := mem_iUnion₂.mp hxQA'
        exact False.elim ((hCA_disj_Q' e' he').le_bot ⟨hxCA, hxQe'⟩)
      · obtain ⟨e, he, hxQe⟩ := mem_iUnion₂.mp hxQA
        exact False.elim ((hCA'_disj_Q e he).le_bot ⟨hxQe, hxCA'⟩)
      · obtain ⟨e, he, hxQe⟩ := mem_iUnion₂.mp hxQA
        obtain ⟨e', he', hxQe'⟩ := mem_iUnion₂.mp hxQA'
        have hee' : e ≠ e' := by
          intro h
          subst h
          have h1 := (Finset.mem_filter.mp he).2
          have h2 := (Finset.mem_filter.mp he').2
          exact hne (h1.symm.trans h2)
        have hx_inter : x ∈ Q e ∩ Q e' := ⟨hxQe, hxQe'⟩
        rw [hQQ e e' hee'] at hx_inter
        have hx1 : x ∈ ⋃ j ∈ F_arm A, ({b j 1} : Set S₀) :=
          mem_iUnion₂.mpr ⟨e, he, hx_inter.1⟩
        have hx2 : x ∈ ⋃ j ∈ F_arm A', ({b j 1} : Set S₀) :=
          mem_iUnion₂.mpr ⟨e', he', hx_inter.2⟩
        rw [hF_arm_b1 A hA] at hx1
        rw [hF_arm_b1 A' hA'] at hx2
        obtain ⟨v₁, hv₁, hxv₁⟩ := hx1
        obtain ⟨v₂, hv₂, hxv₂⟩ := hx2
        have hv12 : v₁ = v₂ :=
          hα_inj v₁ hv₁.1 v₂ hv₂.1 (e_sph.injective (hxv₁.trans hxv₂.symm))
        subst hv12
        exact ⟨v₁, ⟨hv₁, hv₂⟩, hxv₁⟩
    · rintro x ⟨v, ⟨hvA, hvA'⟩, rfl⟩
      have hx1 : (e_sph ∘ α_map) v ∈ Star A ∩ K_forbid := by
        rw [hStar_inter_K A hA]
        exact ⟨v, hvA, rfl⟩
      have hx2 : (e_sph ∘ α_map) v ∈ Star A' ∩ K_forbid := by
        rw [hStar_inter_K A' hA']
        exact ⟨v, hvA', rfl⟩
      exact ⟨hx1.1, hx2.1⟩
  let D : Graph α β → Set S := fun A =>
    if A ∈ 𝒜 then e_sph.symm '' D₀ A else ∅
  have hD_eq : ∀ A ∈ 𝒜, D A = e_sph.symm '' D₀ A := fun A hA => by simp [D, hA]
  refine ⟨α_map, D, hα_mem_Δ₀, ?_, hα_Pi, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rw [hD_eq A hA]
    refine ⟨?_, ?_⟩
    · rcases (hD₀ A hA).1 with ⟨φ⟩
      exact ⟨φ.trans (e_sph.symm.image (D₀ A))⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hD₀_sub_Δ₀ A hA hy
      simpa using hx
  · intro A hA v hv
    rw [hπ_eq_Z A hA] at hv
    rw [hD_eq A hA, GM11.subBd_eq_frontier]
    have hfr_img : frontier (e_sph.symm '' D₀ A) = e_sph.symm '' discBd (D₀ A) := by
      rw [← e_sph.symm.image_frontier (D₀ A),
        GM11.IsClosedDisc.frontier_eq_discBd hS₀_surf (hD₀ A hA).1]
    rw [hfr_img]
    refine ⟨e_sph (α_map v), ?_, e_sph.symm_apply_apply (α_map v)⟩
    apply (hD₀ A hA).2.2.2
    have hx_b1 : e_sph (α_map v) ∈ ⋃ e ∈ F_arm A, ({b e 1} : Set S₀) := by
      rw [hF_arm_b1 A hA]
      exact ⟨v, hv, rfl⟩
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx_b1
    rw [mem_singleton_iff.mp hxe]
    exact ⟨Or.inr (mem_iUnion₂.mpr ⟨e, he, (hQ e).2.2.1 (Or.inr rfl)⟩),
      Or.inr (hv_mem_VZ e)⟩
  · intro v hvZ A hA hα_in
    rw [hπ_eq_Z A hA]
    rw [hD_eq A hA] at hα_in
    obtain ⟨y, hyD₀, hy_eq⟩ := hα_in
    have hy_val : y = e_sph (α_map v) := by
      rw [← hy_eq, e_sph.apply_symm_apply]
    subst hy_val
    have hyK : e_sph (α_map v) ∈ D₀ A ∩ K_forbid := by
      refine ⟨hyD₀, Or.inr ?_⟩
      rw [← hwZ_val v hvZ]
      exact ⟨(wZ v hvZ).2, v, hvZ, rfl⟩
    rw [hD₀_inter_K A hA] at hyK
    obtain ⟨v', hv', hv'_eq⟩ := hyK
    have hv_eq : v = v' := (hα_inj v' hv'.1 v hvZ (e_sph.injective hv'_eq)).symm
    exact hv_eq ▸ hv'
  · intro A hA A' hA' hne
    rw [hD_eq A hA, hD_eq A' hA', hπ_eq_Z A hA, hπ_eq_Z A' hA']
    rw [← image_inter e_sph.symm.injective, (hD₀_inter A hA A' hA' hne),
      hStar_inter_Star A hA A' hA' hne, ← image_comp]
    have hcomp : e_sph.symm ∘ (e_sph ∘ α_map) = α_map := by
      funext x
      exact e_sph.symm_apply_apply (α_map x)
    rw [hcomp]
  · intro A hA
    rw [hD_eq A hA, hπ_eq_Z A hA]
    apply Subset.antisymm
    · rintro x ⟨⟨y, hyD₀, rfl⟩, hx_bd⟩
      have hy_bd_S₀ : y ∈ subBd Δ₀_S₀ := by
        rw [hbd_S₀_img]
        exact ⟨e_sph.symm y, hx_bd, e_sph.apply_symm_apply y⟩
      have hy_not_int : y ∉ interior Δ₀_S₀ := by
        rw [← hint_Δ₀_S₀]
        intro h
        exact h.2 hy_bd_S₀
      have hyK : y ∈ D₀ A ∩ K_forbid := ⟨hyD₀, Or.inl hy_not_int⟩
      rw [hD₀_inter_K A hA] at hyK
      obtain ⟨v, hv, rfl⟩ := hyK
      simp only [Function.comp_apply, Homeomorph.symm_apply_apply] at hx_bd ⊢
      have hv_Pi : v ∈ ιV '' PiSet := (hα_bd_iff v hv.1).mp hx_bd
      exact ⟨v, ⟨hv, hv_Pi⟩, rfl⟩
    · rintro _ ⟨v, ⟨hv, hv_Pi⟩, rfl⟩
      refine ⟨?_, (hα_bd_iff v hv.1).mpr hv_Pi⟩
      have hyK : e_sph (α_map v) ∈ D₀ A ∩ K_forbid := by
        rw [hD₀_inter_K A hA]
        exact ⟨v, hv, rfl⟩
      exact ⟨e_sph (α_map v), hyK.1, e_sph.symm_apply_apply (α_map v)⟩
  · intro v hv v' hv' hne heq
    exact hne (hα_inj v hv v' hv' heq)

end GraphMinor.GM22
