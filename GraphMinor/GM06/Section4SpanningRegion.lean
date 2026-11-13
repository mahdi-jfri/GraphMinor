module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4TreeRegion
import GraphMinor.GM06.Section4Annulus
import GraphMinor.GM07.Section11c
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# A forest has a region reaching both cuffs

Graph Minors VI (4.2), claim (2), page 126, chooses a region of a tree
meeting both cuffs. In the plane, the complement of the forest is
connected. Join a point in the inner hole to a point outside the annulus,
then take the portion between its last inner-circle hit and first
outer-circle hit. Pulling this portion back to the cylinder supplies
the required region.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

private theorem subPathSeg_mem_band
    (γ : C(unitInterval, EuclideanPlane)) {s t : unitInterval} (hst : s ≤ t)
    (hband : ∀ v ∈ Icc s t, ‖γ v‖ ∈ Icc (1 / 2 : ℝ) 1)
    (u : unitInterval) : ‖GM07.subPathSeg γ s t u‖ ∈ Icc (1 / 2 : ℝ) 1 := by
  apply hband
  constructor
  · change (s : ℝ) ≤ (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ)
    have hsr : (s : ℝ) ≤ (t : ℝ) := hst
    nlinarith only [hsr, u.2.1]
  · change (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ) ≤ (t : ℝ)
    have hsr : (s : ℝ) ≤ (t : ℝ) := hst
    nlinarith only [hsr, u.2.2]

/-- A forest on the cylinder has a curve off its point set joining the
two cuffs. This is the region-access fact used in VI (4.2), claim (2). -/
theorem exists_curve_between_cuffs_off_forest
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph) :
    ∃ f : Curve ClosedCylinder, f 0 ∈ cylinderCuff1 ∧ f 1 ∈ cylinderCuff2 ∧
      range f ⊆ H.Uᶜ := by
  let A := cylToPlane '' H.U
  let z : EuclideanPlane := complexPlane (2 : ℂ)
  have hz : ‖z‖ = 2 := by simp [z]
  have hzero : (0 : EuclideanPlane) ∈ Aᶜ := by
    rintro ⟨p, _, hp⟩
    have hn := congrArg norm hp
    rw [norm_cylToPlane, norm_zero] at hn
    linarith only [hn, p.2.1.1]
  have hzA : z ∈ Aᶜ := by
    rintro ⟨p, _, hp⟩
    have hn := congrArg norm hp
    rw [norm_cylToPlane, hz] at hn
    linarith only [hn, p.2.1.2]
  have hAc : IsClosed A :=
    (H.isClosed_U.isCompact.image continuous_cylToPlane).isClosed
  have hApre : IsPreconnected Aᶜ :=
    isPreconnected_compl_image_forest isClosedEmbedding_cylToPlane.isEmbedding hH
  have hApath : IsPathConnected Aᶜ :=
    hAc.isOpen_compl.isConnected_iff_isPathConnected.mp ⟨⟨0, hzero⟩, hApre⟩
  obtain ⟨γ, hγ⟩ := hApath.joinedIn 0 hzero z hzA
  let a : C(unitInterval, ℝ) := ⟨fun u => ‖γ u‖, continuous_norm.comp γ.continuous⟩
  obtain ⟨s, t, hst, has, hat, hband⟩ := exists_subinterval_crossing_band a
    (show (1 / 2 : ℝ) < 1 by norm_num)
    (by change ‖γ 0‖ ≤ (1 / 2 : ℝ); simp)
    (by change 1 ≤ ‖γ 1‖; rw [γ.target, hz]; norm_num)
  let p := GM07.subPathSeg γ.toContinuousMap s t
  have hp : ∀ u, p u ∈ range cylToPlane := by
    intro u
    rw [range_cylToPlane]
    exact subPathSeg_mem_band γ.toContinuousMap hst.le hband u
  let e := isClosedEmbedding_cylToPlane.isEmbedding.toHomeomorph
  let f : Curve ClosedCylinder :=
    ⟨fun u => e.symm ⟨p u, hp u⟩,
      e.symm.continuous.comp (p.continuous.subtype_mk hp)⟩
  have hf (u : unitInterval) : cylToPlane (f u) = p u :=
    congrArg (fun q : range cylToPlane => q.1) (e.apply_symm_apply ⟨p u, hp u⟩)
  have hf0 : f 0 ∈ cylinderCuff1 := by
    have hn := congrArg norm (hf 0)
    rw [norm_cylToPlane] at hn
    change (f 0).1.1 / 2 = ‖GM07.subPathSeg γ.toContinuousMap s t 0‖ at hn
    rw [GM07.subPathSeg_zero] at hn
    change (f 0).1.1 / 2 = ‖γ s‖ at hn
    change ‖γ s‖ = (1 / 2 : ℝ) at has
    change (f 0).1.1 = 1
    linarith only [hn, has]
  have hf1 : f 1 ∈ cylinderCuff2 := by
    have hn := congrArg norm (hf 1)
    rw [norm_cylToPlane] at hn
    change (f 1).1.1 / 2 = ‖GM07.subPathSeg γ.toContinuousMap s t 1‖ at hn
    rw [GM07.subPathSeg_one] at hn
    change (f 1).1.1 / 2 = ‖γ t‖ at hn
    change ‖γ t‖ = (1 : ℝ) at hat
    change (f 1).1.1 = 2
    linarith only [hn, hat]
  refine ⟨f, hf0, hf1, ?_⟩
  rintro x ⟨u, rfl⟩ hxu
  have hpu : p u ∈ A := hf u ▸ mem_image_of_mem cylToPlane hxu
  exact hγ _ hpu

/-- The region meeting both cuffs used in Graph Minors VI (4.2),
claim (2), page 126. This holds for the whole forest as well as a tree. -/
theorem exists_region_meeting_both_cuffs_of_forest
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph) :
    ∃ R ∈ H.R, (R ∩ cylinderCuff1).Nonempty ∧ (R ∩ cylinderCuff2).Nonempty := by
  obtain ⟨f, hf0, hf1, hfU⟩ := exists_curve_between_cuffs_off_forest hH
  let R := connectedComponentIn (univ \ H.U) (f 0)
  have h0 : f 0 ∈ univ \ H.U := ⟨mem_univ _, hfU (mem_range_self 0)⟩
  have hsub : range f ⊆ R := (isConnected_range f.continuous).isPreconnected
    |>.subset_connectedComponentIn (mem_range_self 0) (fun x hx => ⟨mem_univ _, hfU hx⟩)
  exact ⟨R, ⟨f 0, h0, rfl⟩, ⟨f 0, hsub (mem_range_self 0), hf0⟩,
    ⟨f 1, hsub (mem_range_self 1), hf1⟩⟩

end GraphMinor.GM06
