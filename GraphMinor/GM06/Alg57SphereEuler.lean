module

public import GraphMinor.GM06.Euler
public import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Section5
import GraphMinor.GM11.PerimeterPull
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.Gluing
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Euler's lower bound for a drawing in the sphere

The proof of Lemma 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) compares the face
orbits with the regions of a drawing in the sphere. It needs Euler's lower bound
`#edges + 2 ≤ #vertices + #regions` there. The library has this bound on a closed disc
(`GM06.euler_lower_bound`). This file moves it to the sphere `OnePoint EuclideanPlane`, for a
drawing that misses the point at infinity.

Such a drawing lies in a round ball of radius `ρ`. Let `C` be the closed ball of radius `ρ`,
seen in the sphere. It is a closed disc, and the drawing read in `C` has the same vertices and
edges. Its regions are the traces `r ∩ C` of the regions `r` in the sphere. The one point to
check is that each trace is connected. The radial projection onto `C` maps `r` minus the point
at infinity onto `r ∩ C`: a point of `r` outside `C` shows that the whole outside of the ball
lies in `r`, since the outside is connected and misses the drawing.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 OnePoint

/-- The sphere, as the one-point compactification of the plane. -/
local notation "Sph" => OnePoint EuclideanPlane

/-- The radial projection of the plane onto the closed ball of radius `ρ`. -/
noncomputable def radialClamp (ρ : ℝ) (z : EuclideanPlane) : EuclideanPlane :=
  (ρ / max ‖z‖ ρ) • z

theorem continuous_radialClamp {ρ : ℝ} (hρ : 0 < ρ) : Continuous (radialClamp ρ) := by
  unfold radialClamp
  refine Continuous.smul (continuous_const.div (continuous_norm.max continuous_const) ?_)
    continuous_id
  exact fun z => (lt_of_lt_of_le hρ (le_max_right _ _)).ne'

theorem radialClamp_of_le {ρ : ℝ} (hρ : 0 < ρ) {z : EuclideanPlane} (hz : ‖z‖ ≤ ρ) :
    radialClamp ρ z = z := by
  simp [radialClamp, max_eq_right hz, hρ.ne']

theorem norm_radialClamp_of_lt {ρ : ℝ} (hρ : 0 < ρ) {z : EuclideanPlane} (hz : ρ < ‖z‖) :
    ‖radialClamp ρ z‖ = ρ := by
  have hz0 : 0 < ‖z‖ := hρ.trans hz
  rw [radialClamp, max_eq_left hz.le, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hρ hz0)]
  field_simp

theorem norm_radialClamp_le {ρ : ℝ} (hρ : 0 < ρ) (z : EuclideanPlane) :
    ‖radialClamp ρ z‖ ≤ ρ := by
  rcases le_or_gt ‖z‖ ρ with hz | hz
  · rwa [radialClamp_of_le hρ hz]
  · exact (norm_radialClamp_of_lt hρ hz).le

/-- The outside of an open round ball of the plane is connected. -/
theorem isPreconnected_norm_ge (ρ : ℝ) (hρ : 0 < ρ) :
    IsPreconnected {w : EuclideanPlane | ρ ≤ ‖w‖} := by
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    apply Module.lt_rank_of_lt_finrank
    simp
  have hsph : IsPreconnected (Metric.sphere (0 : EuclideanPlane) 1) :=
    isPreconnected_sphere hrank 0 1
  have hprod : IsPreconnected (Ici ρ ×ˢ Metric.sphere (0 : EuclideanPlane) 1) :=
    isPreconnected_Ici.prod hsph
  have hEq : {w : EuclideanPlane | ρ ≤ ‖w‖} =
      (fun q : ℝ × EuclideanPlane => q.1 • q.2) '' (Ici ρ ×ˢ Metric.sphere (0 : EuclideanPlane) 1) := by
    ext x
    constructor
    · intro hx
      have hd : 0 < ‖x‖ := lt_of_lt_of_le hρ hx
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hx, ?_⟩, ?_⟩
      · simp [norm_smul, hd.ne']
      · simp [smul_smul, hd.ne']
    · rintro ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
      have hw' : ‖w‖ = 1 := by simpa using hw
      have ht0 : 0 ≤ t := hρ.le.trans ht
      change ρ ≤ ‖t • w‖
      rw [norm_smul, hw', Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
      exact ht
  rw [hEq]
  exact hprod.image _ (by fun_prop)

/-- A closed set of the sphere that misses the point at infinity lies in a round ball. -/
theorem exists_ball_of_infty_notMem {U : Set Sph} (hU : IsClosed U) (h : (∞ : Sph) ∉ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y := by
  obtain ⟨-, hK⟩ := (isClosed_iff_of_notMem h).mp hU
  obtain ⟨ρ₀, hρ₀⟩ := (Metric.isBounded_iff_subset_ball (0 : EuclideanPlane)).mp hK.isBounded
  refine ⟨max ρ₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
  have hy' : y ≠ ∞ := fun h' => h (h' ▸ hy)
  obtain ⟨w, rfl⟩ := ne_infty_iff_exists.mp hy'
  have hw := hρ₀ (show w ∈ ((↑) : EuclideanPlane → Sph) ⁻¹' U from hy)
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact ⟨w, lt_of_lt_of_le hw (le_max_left _ _), rfl⟩

section Ball

variable {ρ : ℝ}

/-- The closed ball of radius `ρ`, as a map of the closed unit disc into the sphere. -/
noncomputable def sphereBallMap (ρ : ℝ) (x : ClosedUnitDisc) : Sph :=
  ((ρ • x.1 : EuclideanPlane) : Sph)

theorem mem_range_sphereBallMap (hρ : 0 < ρ) {y : Sph} :
    y ∈ range (sphereBallMap ρ) ↔ ∃ w : EuclideanPlane, ‖w‖ ≤ ρ ∧ (w : Sph) = y := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨ρ • x.1, ?_, rfl⟩
    have hx : ‖x.1‖ ≤ 1 := by
      have := x.2
      simpa [ClosedUnitDisc] using this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨ρ⁻¹ • w, ?_⟩, ?_⟩
    · change ρ⁻¹ • w ∈ Metric.closedBall (0 : EuclideanPlane) 1
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      rw [inv_mul_le_iff₀ hρ, mul_one]
      exact hw
    · simp [sphereBallMap, smul_smul, hρ.ne']

theorem isClosedEmbedding_sphereBallMap (hρ : 0 < ρ) : IsClosedEmbedding (sphereBallMap ρ) := by
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  refine Continuous.isClosedEmbedding ?_ ?_
  · exact OnePoint.continuous_coe.comp (by fun_prop : Continuous fun x : ClosedUnitDisc => ρ • x.1)
  · intro x y h
    have h' : ρ • x.1 = ρ • y.1 := OnePoint.coe_injective h
    exact Subtype.ext (smul_right_injective _ hρ.ne' h')

/-- The closed ball of radius `ρ` in the sphere is a closed disc space. -/
theorem isClosedDiscSpace_sphereBall (hρ : 0 < ρ) :
    IsClosedDiscSpace (range (sphereBallMap ρ)) :=
  ⟨(isClosedEmbedding_sphereBallMap hρ).isEmbedding.toHomeomorph⟩

end Ball

section Drawing

variable {Γ : Drawing Sph} {ρ : ℝ}

/-- If a region of a drawing inside the ball of radius `ρ` has a point outside that ball, then
the whole outside lies in it. -/
theorem norm_ge_subset_region (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) {r : Set Sph}
    (hr : r ∈ Γ.R) {z : EuclideanPlane} (hz : ρ ≤ ‖z‖) (hzr : (z : Sph) ∈ r) {w : EuclideanPlane}
    (hw : ρ ≤ ‖w‖) : (w : Sph) ∈ r := by
  have hA : IsPreconnected (((↑) : EuclideanPlane → Sph) '' {w | ρ ≤ ‖w‖}) :=
    (isPreconnected_norm_ge ρ hρ).image _ OnePoint.continuous_coe.continuousOn
  have hdis : Disjoint (((↑) : EuclideanPlane → Sph) '' {w | ρ ≤ ‖w‖}) Γ.U := by
    rw [disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ hvU
    obtain ⟨v', hv', hvv'⟩ := hU _ hvU
    rw [OnePoint.coe_injective hvv'] at hv'
    exact absurd hv (not_le.mpr hv')
  exact subset_region hr hA hdis ⟨z, hz, rfl⟩ hzr ⟨w, hw, rfl⟩

/-- The radial projection maps the finite part of a region into the region. -/
theorem radialClamp_mem_region (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) {r : Set Sph}
    (hr : r ∈ Γ.R) {z : EuclideanPlane} (hzr : (z : Sph) ∈ r) :
    ((radialClamp ρ z : EuclideanPlane) : Sph) ∈ r := by
  rcases le_or_gt ‖z‖ ρ with hz | hz
  · rwa [radialClamp_of_le hρ hz]
  · exact norm_ge_subset_region hρ hU hr hz.le hzr (norm_radialClamp_of_lt hρ hz).ge

/-- The trace of a region on the ball of radius `ρ` is the radial projection of its finite
part. -/
theorem region_inter_ball_eq (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) {r : Set Sph}
    (hr : r ∈ Γ.R) :
    range (sphereBallMap ρ) ∩ r = (fun z => ((radialClamp ρ z : EuclideanPlane) : Sph)) ''
      (((↑) : EuclideanPlane → Sph) ⁻¹' r) := by
  ext y
  constructor
  · rintro ⟨hyC, hyr⟩
    obtain ⟨w, hw, rfl⟩ := (mem_range_sphereBallMap hρ).mp hyC
    refine ⟨w, hyr, ?_⟩
    show ((radialClamp ρ w : EuclideanPlane) : Sph) = w
    rw [radialClamp_of_le hρ hw]
  · rintro ⟨z, hzr, rfl⟩
    exact ⟨(mem_range_sphereBallMap hρ).mpr ⟨_, norm_radialClamp_le hρ z, rfl⟩,
      radialClamp_mem_region hρ hU hr hzr⟩

/-- The trace of a region on the ball is connected. -/
theorem isPreconnected_region_inter_ball (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) {r : Set Sph}
    (hr : r ∈ Γ.R) : IsPreconnected (range (sphereBallMap ρ) ∩ r) := by
  have hS : IsClosedSurface Sph := (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have : LocallyConnectedSpace Sph := IsClosedSurface.locallyConnectedSpace hS
  have hpunct : IsPreconnected (r \ {∞}) :=
    isPreconnected_sdiff_finite hS (region_isOpen hr) (region_isPreconnected hr)
      (finite_singleton _)
  have hP : IsPreconnected (((↑) : EuclideanPlane → Sph) ⁻¹' r) := by
    rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image]
    convert hpunct using 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, OnePoint.coe_ne_infty z⟩
    · rintro ⟨hy, hyi⟩
      obtain ⟨z, rfl⟩ := ne_infty_iff_exists.mp hyi
      exact ⟨z, hy, rfl⟩
  rw [region_inter_ball_eq hρ hU hr]
  exact hP.image _ (OnePoint.continuous_coe.comp (continuous_radialClamp hρ)).continuousOn

/-- Every region meets the ball. -/
theorem region_inter_ball_nonempty (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) {r : Set Sph}
    (hr : r ∈ Γ.R) : (range (sphereBallMap ρ) ∩ r).Nonempty := by
  have hS : IsClosedSurface Sph := (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have : LocallyConnectedSpace Sph := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨y, hy⟩ := OnePoint.denseRange_coe.inter_open_nonempty r (region_isOpen hr)
    (region_nonempty hr)
  obtain ⟨hyr, z, rfl⟩ := hy
  rw [region_inter_ball_eq hρ hU hr]
  exact ⟨_, z, hyr, rfl⟩

theorem drawing_subset_ball (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) :
    Γ.U ⊆ range (sphereBallMap ρ) := fun y hy => by
  obtain ⟨w, hw, rfl⟩ := hU y hy
  exact (mem_range_sphereBallMap hρ).mpr ⟨w, hw.le, rfl⟩

/-- The drawing read in the ball of radius `ρ`. -/
noncomputable def ballDrawing (Γ : Drawing Sph) (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) :
    Drawing (range (sphereBallMap ρ)) :=
  GM12.drawingInSubspace Γ (range (sphereBallMap ρ)) (drawing_subset_ball hρ hU)

theorem mem_ballDrawing_U (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y)
    {x : range (sphereBallMap ρ)} : x ∈ (ballDrawing Γ hρ hU).U ↔ x.1 ∈ Γ.U := by
  rw [ballDrawing, GM12.drawingInSubspace_U]
  rfl

/-- A point of the drawing is an interior point of the ball. -/
theorem isInteriorPoint_of_mem_ballDrawing (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y)
    {x : range (sphereBallMap ρ)} (hx : x.1 ∈ Γ.U) : IsInteriorPoint x := by
  have hS : IsClosedSurface Sph := (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  let W : Set Sph := ((↑) : EuclideanPlane → Sph) '' Metric.ball 0 ρ
  have hWo : IsOpen W := OnePoint.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hWC : W ⊆ range (sphereBallMap ρ) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact (mem_range_sphereBallMap hρ).mpr ⟨w, hw.le, rfl⟩
  have he : IsOpenEmbedding (inclusion hWC) := by
    refine ⟨IsEmbedding.inclusion hWC, ?_⟩
    rw [range_inclusion]
    exact hWo.preimage continuous_subtype_val
  obtain ⟨w, hw, hwx⟩ := hU x.1 hx
  have hxW : x.1 ∈ W := ⟨w, by rwa [Metric.mem_ball, dist_zero_right], hwx⟩
  have hint : IsInteriorPoint (⟨x.1, hxW⟩ : W) := (isInteriorPoint_sub hWo).mpr (hS.2.2 _)
  have := isInteriorPoint_of_isOpenEmbedding he hint
  exact this

theorem ballDrawing_isProper (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) :
    (ballDrawing Γ hρ hU).IsProper := by
  rintro x ⟨hxbd, hxU⟩
  exact absurd (isInteriorPoint_of_mem_ballDrawing hρ hU ((mem_ballDrawing_U hρ hU).mp hxU)) hxbd

theorem ballDrawing_V_ncard (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) :
    (ballDrawing Γ hρ hU).V.ncard = Γ.V.ncard := by
  rw [ballDrawing, GM12.drawingInSubspace_V]
  refine ncard_preimage_of_injective_subset_range Subtype.val_injective fun y hy => ?_
  obtain ⟨w, hw, rfl⟩ := hU y (Γ.V_subset_U hy)
  exact ⟨⟨_, (mem_range_sphereBallMap hρ).mpr ⟨w, hw.le, rfl⟩⟩, rfl⟩

theorem ballDrawing_E_ncard (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) :
    (ballDrawing Γ hρ hU).E.ncard = Γ.E.ncard := by
  rw [ballDrawing, GM12.drawingInSubspace_E]
  refine InjOn.ncard_image fun e he e' he' h => ?_
  have hsub : ∀ {e}, e ∈ Γ.E → e ⊆ range (sphereBallMap ρ) := fun {e} he y hy => by
    obtain ⟨w, hw, rfl⟩ := hU y (Γ.closure_subset_U he (subset_closure hy))
    exact (mem_range_sphereBallMap hρ).mpr ⟨w, hw.le, rfl⟩
  have h' := Subtype.preimage_coe_eq_preimage_coe_iff.mp h
  rwa [inter_eq_right.mpr (hsub he), inter_eq_right.mpr (hsub he')] at h'

/-- The trace of a region of the sphere is a region of the ball. -/
theorem preimage_region_mem_ballDrawing_R (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) {r : Set Sph}
    (hr : r ∈ Γ.R) : (Subtype.val ⁻¹' r : Set (range (sphereBallMap ρ))) ∈
      (ballDrawing Γ hρ hU).R := by
  obtain ⟨y, hyC, hyr⟩ := region_inter_ball_nonempty hρ hU hr
  let x : range (sphereBallMap ρ) := ⟨y, hyC⟩
  have hxU : x ∉ (ballDrawing Γ hρ hU).U := fun h =>
    region_subset hr hyr ((mem_ballDrawing_U hρ hU).mp h)
  refine (mem_R_iff _).mpr ⟨x, hxU, ?_⟩
  apply Subset.antisymm
  · have hpre : IsPreconnected (Subtype.val ⁻¹' r : Set (range (sphereBallMap ρ))) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe]
      exact isPreconnected_region_inter_ball hρ hU hr
    refine hpre.subset_connectedComponentIn hyr fun z hz => ⟨mem_univ _, ?_⟩
    exact fun hzU => region_subset hr hz ((mem_ballDrawing_U hρ hU).mp hzU)
  · intro z hz
    have hK := (isPreconnected_connectedComponentIn (F := univ \ (ballDrawing Γ hρ hU).U)
      (x := x)).image Subtype.val continuous_subtype_val.continuousOn
    have hdis : Disjoint (Subtype.val '' connectedComponentIn
        (univ \ (ballDrawing Γ hρ hU).U) x) Γ.U := by
      rw [disjoint_left]
      rintro _ ⟨u, hu, rfl⟩ huU
      exact (connectedComponentIn_subset _ _ hu).2 ((mem_ballDrawing_U hρ hU).mpr huU)
    exact subset_region hr hK hdis ⟨x, mem_connectedComponentIn ⟨mem_univ _, hxU⟩, rfl⟩ hyr
      ⟨z, hz, rfl⟩

/-- The regions of the ball are the traces of the regions of the sphere. -/
theorem nat_card_ballDrawing_R (hρ : 0 < ρ)
    (hU : ∀ y ∈ Γ.U, ∃ w : EuclideanPlane, ‖w‖ < ρ ∧ (w : Sph) = y) :
    Nat.card (ballDrawing Γ hρ hU).R = Nat.card Γ.R := by
  let f : Γ.R → (ballDrawing Γ hρ hU).R := fun r =>
    ⟨_, preimage_region_mem_ballDrawing_R hρ hU r.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun r r' h => ?_, fun K => ?_⟩
    · obtain ⟨y, hyC, hyr⟩ := region_inter_ball_nonempty hρ hU r.2
      have hy : (⟨y, hyC⟩ : range (sphereBallMap ρ)) ∈ (f r').1 := by
        rw [← h]; exact hyr
      exact Subtype.ext (region_eq_of_mem r.2 r'.2 hyr hy)
    · obtain ⟨x, hx⟩ := region_nonempty K.2
      have hxU : x.1 ∉ Γ.U := fun h => region_subset K.2 hx ((mem_ballDrawing_U hρ hU).mpr h)
      obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
      refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
      exact region_eq_of_mem (preimage_region_mem_ballDrawing_R hρ hU hr) K.2 hxr hx
  exact (Nat.card_eq_of_bijective f hf).symm

end Drawing

/-- **Euler's lower bound in the sphere.** A drawing in the sphere that misses the point at
infinity and has a vertex satisfies `#edges + 2 ≤ #vertices + #regions`. -/
theorem sphere_euler_lower_bound {Γ : Drawing Sph} (h : (∞ : Sph) ∉ Γ.U)
    (hV : Γ.V.Nonempty) : Γ.E.ncard + 2 ≤ Γ.V.ncard + Γ.R.ncard := by
  obtain ⟨ρ, hρ, hU⟩ := exists_ball_of_infty_notMem Γ.isClosed_U h
  have hVne : (ballDrawing Γ hρ hU).V.Nonempty := by
    obtain ⟨v, hv⟩ := hV
    obtain ⟨w, hw, rfl⟩ := hU v (Γ.V_subset_U hv)
    refine ⟨⟨_, (mem_range_sphereBallMap hρ).mpr ⟨w, hw.le, rfl⟩⟩, ?_⟩
    rw [ballDrawing, GM12.drawingInSubspace_V]
    exact hv
  have key := (euler_lower_bound (isClosedDiscSpace_sphereBall hρ)
    (ballDrawing_isProper hρ hU)).2 hVne
  rw [ballDrawing_V_ncard, ballDrawing_E_ncard] at key
  have hR := nat_card_ballDrawing_R hρ hU
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hR
  omega

end GraphMinor.GM06
