module

public import GraphMinor.GM13.Section7FourMetric
import GraphMinor.GM11.Regions
import GraphMinor.GM13.Section7WallWalks

/-!
# Graph Minors XIII, (7.4): two vertices on one region are close

A region of the sphere drawing of a wall drawn as in Fig. 1 is a connected open set missing the
drawing. Its points in the plane form a connected set too, also when the region contains the
point at infinity (`isPreconnected_preimage_coe`), since the plane outside a large disc is
connected. Two points in the closure of one region are therefore joined by a free cell walk
between two cells next to them, and their distance `d` is at most `2`
(`planeWallDist_le_two_of_mem_closure_region`).
-/

public section

namespace GraphMinor.GM13

open Set Function Topology Filter
open GraphMinor
open GraphMinor.Surface

/-- The plane outside a closed disc is connected. -/
theorem isPreconnected_compl_closedBall_plane (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected ((Metric.closedBall (0 : EuclideanPlane) R)ᶜ) := by
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]; norm_num
  have hS := (isPathConnected_sphere hrank (0 : EuclideanPlane) zero_le_one).isConnected
  have hP : IsPreconnected (Metric.sphere (0 : EuclideanPlane) 1 ×ˢ Ioi R) :=
    hS.isPreconnected.prod isPreconnected_Ioi
  have himage : (fun p : EuclideanPlane × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : EuclideanPlane) 1 ×ˢ Ioi R) = (Metric.closedBall (0 : EuclideanPlane) R)ᶜ := by
    ext z
    simp only [mem_image, mem_prod, Metric.mem_sphere, dist_zero_right, mem_Ioi, Prod.exists,
      mem_compl_iff, Metric.mem_closedBall, not_le]
    constructor
    · rintro ⟨v, t, ⟨hv, ht⟩, rfl⟩
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact ht
    · intro hz
      have hz0 : ‖z‖ ≠ 0 := by linarith
      refine ⟨‖z‖⁻¹ • z, ‖z‖, ⟨?_, hz⟩, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz0]
      · rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
  rw [← himage]
  exact hP.image _ (by fun_prop : Continuous fun p : EuclideanPlane × ℝ => p.2 • p.1).continuousOn

/-- **Removing the point at infinity.** If an open connected set `U` of the sphere contains the
point at infinity, its points in the plane form a connected set. -/
theorem isPreconnected_preimage_coe_of_mem {U : Set (OnePoint EuclideanPlane)} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∈ U) :
    IsPreconnected (((↑) : EuclideanPlane → OnePoint EuclideanPlane) ⁻¹' U) := by
  set V := ((↑) : EuclideanPlane → OnePoint EuclideanPlane) ⁻¹' U
  obtain ⟨-, hK⟩ := (OnePoint.isOpen_iff_of_mem hinf).mp hU
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanPlane)).mp hK.isBounded
  set R' := max R 0
  have hO : (Metric.closedBall (0 : EuclideanPlane) R')ᶜ ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (Metric.closedBall_subset_closedBall (le_max_left R 0) (hR hzV))
  have hOc := isPreconnected_compl_closedBall_plane R' (le_max_right R 0)
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  have hOcov : (Metric.closedBall (0 : EuclideanPlane) R')ᶜ ⊆ u ∪ v := hO.trans hcov
  have hOdisj : (Metric.closedBall (0 : EuclideanPlane) R')ᶜ ∩ (u ∩ v) = ∅ :=
    subset_empty_iff.mp ((inter_subset_inter_left _ hO).trans hdisj.subset)
  -- the side that contains the outside of the disc
  have key : ∀ u v : Set EuclideanPlane, IsOpen u → IsOpen v → V ⊆ u ∪ v →
      V ∩ (u ∩ v) = ∅ → (Metric.closedBall (0 : EuclideanPlane) R')ᶜ ⊆ u → V ⊆ u := by
    intro u v hu hv hcov hdisj hOu
    let u' : Set (OnePoint EuclideanPlane) := ((↑) '' u) ∪ {OnePoint.infty}
    let v' : Set (OnePoint EuclideanPlane) := (↑) '' v
    have hpre_u : ((↑) : EuclideanPlane → OnePoint EuclideanPlane) ⁻¹' u' = u := by
      ext z; simp [u']
    have hpre_v : ((↑) : EuclideanPlane → OnePoint EuclideanPlane) ⁻¹' v' = v := by
      ext z; simp [v']
    have hu' : IsOpen u' := by
      rw [OnePoint.isOpen_iff_of_mem (Or.inr rfl), hpre_u]
      refine ⟨hu.isClosed_compl, ?_⟩
      refine (isCompact_closedBall (0 : EuclideanPlane) R').of_isClosed_subset hu.isClosed_compl ?_
      intro z hz
      by_contra hzB
      exact hz (hOu hzB)
    have hv' : IsOpen v' := by
      rw [OnePoint.isOpen_iff_of_notMem (by simp [v']), hpre_v]
      exact hv
    have hcov' : U ⊆ u' ∪ v' := by
      intro x hx
      induction x using OnePoint.rec with
      | infty => exact Or.inl (Or.inr rfl)
      | coe z =>
        rcases hcov (show z ∈ V from hx) with hz | hz
        · exact Or.inl (Or.inl ⟨z, hz, rfl⟩)
        · exact Or.inr ⟨z, hz, rfl⟩
    have hdisj' : U ∩ (u' ∩ v') = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxU hxu hxv
      obtain ⟨z, hz, rfl⟩ := hxv
      have hzu : z ∈ u := by rw [← hpre_u]; exact hxu
      have : z ∈ V ∩ (u ∩ v) := ⟨hxU, hzu, hz⟩
      rw [hdisj] at this
      exact this
    rcases (isPreconnected_iff_subset_of_disjoint.mp hUc) u' v' hu' hv' hcov' hdisj' with h | h
    · intro z hz
      have := h hz
      rw [← hpre_u]; exact this
    · exact absurd (h hinf) (by simp [v'])
  rcases (isPreconnected_iff_subset_of_disjoint.mp hOc) u v hu hv hOcov hOdisj with h | h
  · exact Or.inl (key u v hu hv hcov hdisj h)
  · refine Or.inr (key v u hv hu (by rw [union_comm]; exact hcov) ?_ h)
    rw [inter_comm v u]; exact hdisj

/-- The points in the plane of an open connected set of the sphere form a connected set. -/
theorem isPreconnected_preimage_coe {U : Set (OnePoint EuclideanPlane)} (hU : IsOpen U)
    (hUc : IsPreconnected U) :
    IsPreconnected (((↑) : EuclideanPlane → OnePoint EuclideanPlane) ⁻¹' U) := by
  by_cases hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∈ U
  · exact isPreconnected_preimage_coe_of_mem hU hUc hinf
  · have hsub : U ⊆ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) := by
      intro x hx
      induction x using OnePoint.rec with
      | infty => exact (hinf hx).elim
      | coe z => exact ⟨z, rfl⟩
    rw [← OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image, image_preimage_eq_of_subset hsub]
    exact hUc

/-- The points in Fig. 1 coordinates of an open connected set of the sphere form a connected
set. -/
theorem isPreconnected_preimage_fig1Sph (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    {U : Set (OnePoint EuclideanPlane)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsPreconnected (fig1Sph φ ⁻¹' U) := by
  have h1 := isPreconnected_preimage_coe hU hUc
  have h2 := (φ.isPreconnected_preimage).mpr h1
  exact (fig1PlaneEquiv.isPreconnected_preimage).mpr h2

/-- **Two points on one region are close.** Let `D` be a drawing in the sphere whose point set is
the Fig. 1 drawing of the elementary wall of height `h`, carried by `fig1Sph φ`. If the images of
`s` and `t` are in the closure of one region of `D`, then `s` and `t` are at distance at most `2`
in the Fig. 1 drawing. -/
theorem planeWallDist_le_two_of_mem_closure_region {h : ℕ} (hh : 1 ≤ h) (he : Even h)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {D : Drawing (OnePoint EuclideanPlane)}
    (hDU : D.U = fig1Sph φ '' fig1Set h) {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ D.R)
    {s t : ℝ × ℝ} (hs : fig1Sph φ s ∈ closure r) (ht : fig1Sph φ t ∈ closure r) :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h)) (fig1PlaneEquiv s)
      (fig1PlaneEquiv t) ≤ 2 := by
  have N := fig1FaceNaming hh he
  by_cases hst : cellCode s = cellCode t
  · exact N.planeWallDist_le_two_of_cellCode_eq hst
  have hS := GM09.isClosedSurface_sphere
  have : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    GM11.IsClosedSurface.locallyConnectedSpace hS
  set P := fig1Sph φ ⁻¹' r
  have hP : IsPreconnected P :=
    isPreconnected_preimage_fig1Sph φ (GM11.region_isOpen hr) (GM11.region_isPreconnected hr)
  have hfree : ∀ z ∈ P, cellCode z ∉ fig1WallCells h := by
    intro z hz hzc
    have hzU : fig1Sph φ z ∈ D.U := by
      rw [hDU]; refine ⟨z, ?_, rfl⟩
      rw [fig1Set_eq_cellSet]; exact hzc
    exact GM11.region_subset hr hz hzU
  have hcl : ∀ {z : ℝ × ℝ}, fig1Sph φ z ∈ closure r →
      ∃ p ∈ P, CellLE (cellCode z) (cellCode p) := by
    intro z hz
    have hz' : z ∈ closure P := by
      rw [← (isOpenEmbedding_fig1Sph φ).isOpenMap.preimage_closure_eq_closure_preimage
        (isOpenEmbedding_fig1Sph φ).continuous]
      exact hz
    exact ((mem_closure_iff_frequently.mp hz').and_eventually (eventually_cellLE z)).exists
  obtain ⟨p, hp, hsp⟩ := hcl hs
  obtain ⟨p', hp', htp'⟩ := hcl ht
  obtain ⟨w, hw⟩ := exists_cellWalk_of_isPreconnected hP hfree hp hp'
  have h1 : cellDist (fig1WallCells h) (cellCode s) (cellCode p) = 0 := by
    have := cellDist_le_of_cellRel (fig1WallCells h) (Or.inl hsp : CellRel _ _)
    rw [cellInd_of_not_mem (hfree p hp)] at this
    omega
  have h2 : cellDist (fig1WallCells h) (cellCode p) (cellCode p') = 0 := by
    have := cellDist_le (fig1WallCells h) w
    rw [CellWalk.cost_eq_ind_add_costTail] at hw
    omega
  have h3 : cellDist (fig1WallCells h) (cellCode p') (cellCode t) ≤ 1 :=
    (cellDist_le_of_cellRel (fig1WallCells h) (Or.inr htp' : CellRel _ _)).trans
      (cellInd_le_one _ _)
  have t1 := cellDist_triangle (fig1WallCells h) (cellCode s) (cellCode p) (cellCode p')
  have t2 := cellDist_triangle (fig1WallCells h) (cellCode s) (cellCode p') (cellCode t)
  have h4 := planeWallDist_cellSet_le_cellDist (fig1WallCells_not_square h) hst
  have h5 := cellInd_le_one (fig1WallCells h) (cellCode s)
  omega

end GraphMinor.GM13
