module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Helix
import GraphMinor.GM06.Section5HelixClaim1
import GraphMinor.GM06.Section5DeletedEdgeRegion
import GraphMinor.GM06.Section5RegionVisit
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Section5CutInitialGap
import GraphMinor.GM06.Section5LastRegionSegmentLift
import GraphMinor.GM06.Section5ClockwiseApproachFace
import GraphMinor.GM06.Section5CutApproachProjection
import GraphMinor.GM06.Section5HalfGapCover
import GraphMinor.GM06.Section5AuxiliaryCover
import GraphMinor.GM06.Section5HelixReturnComparison
import GraphMinor.GM06.Section5ThreeSubpaths
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5DeletedEdgeTail
import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5SubpathCount
import GraphMinor.Surface.CutComp

/-!
# Lifting a helix across a clockwise one-path edge deletion

This proves the one-path Reduction 1 case of VI (5.5), pages
130–132. Normalize the helix by claim (1), then choose its last
vertex before its last region visit. Lift that region segment into
the cut disc, choose the old approach face at its actual endpoint
copy, and return from the prescribed clockwise initial copy.
The auxiliary cover and the direct crossing count compare the
potentials. Cutting the old helix preserves its potential.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

private theorem cut_cover_coordinates_mem {D : Set (ℝ × ℝ)}
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (p : D) :
    cylinderCoverCoordinates (planeToCylinderCover p.1) ∈ D := by
  change (max 1 (min 2 p.1.1), p.1.2) ∈ D
  rw [min_eq_right (hstrip p.2).2, max_eq_right (hstrip p.2).1]
  exact p.2

/-- Graph Minors VI (5.5), Reduction 1 for one linkage path, with
clockwise incidence retained in the cut cylinder. All approach and
crossing bounds are supplied by the constructed lifted curves. -/
theorem theorem_5_5_red1_of_one
    {G G' : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) (L' : CylinderLinkage 1 G')
    (hG : IsCylinderSection5Drawing 1 G) (hG' : IsCylinderSection5Drawing 1 G')
    (hRed : Section5Reduction1Step 1 G L G' L')
    (f' : Curve ClosedCylinder) (hf' : IsHelix 1 G' f') :
    ∃ f : Curve ClosedCylinder, IsHelix 1 G f ∧ curvePhi 1 G f ≤ curvePhi 1 G' f' := by
  classical
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  obtain ⟨i, e, he, hside, hV, _, hU, hpaths, _⟩ := hRed
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  by_cases hdis : Disjoint (range f') e
  · obtain ⟨hf, hphi⟩ := helix_of_delete_edge_of_disjoint 1 G G' e f' hV hU hf' hdis
    exact ⟨f', hf, hphi.le⟩
  have hHit : (range f' ∩ e).Nonempty := nonempty_iff_ne_empty.mpr
    (fun h => hdis (disjoint_iff_inter_eq_empty.mpr h))
  obtain ⟨R, hR, heR⟩ := exists_region_containing_deleted_edge he hU
  have hVisit : (f' ⁻¹' R).Nonempty := by
    obtain ⟨_, ⟨t, rfl⟩, hte⟩ := hHit
    exact ⟨t, heR hte⟩
  obtain ⟨z₂', hz₂'⟩ := exists_last_region_visit f' R hVisit
  have hs := hside.incident_and_subset
  obtain ⟨f, z₂, hf, hPhi, hz₂, _, _, hprior⟩ := lemma_5_5_claim_1 L L' hG hG'
    hpaths 0 he hs.1 hs.2 f' hf' hR heR hHit hz₂'
  obtain ⟨z₁, hz₁₂, hz₁V, hNo⟩ := exists_last_vertex_hit_before f hf.2.2.2 hprior
  have hz₁pos : 0 < z₁ := by
    by_contra hnot
    have hz₁0 : z₁ = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have h0V : f 0 ∈ G'.V := hz₁0 ▸ hz₁V
    obtain ⟨j, hj⟩ := hf.2.1
    rw [← hj] at h0V
    exact cylinderN1Point_not_mem_U hG' j (G'.V_subset_U h0V)
  have hPH0 : (L.pathDrawing 0).U ⊆ G'.U := by
    have hh := (L'.isSubdrawing 0).2
    rw [hpaths] at hh
    exact hh
  have hPH : ∀ j, (L.pathDrawing j).U ⊆ G'.U := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    exact hj ▸ hPH0
  have hHU : G'.U ⊆ G.U := by rw [hU]; exact sdiff_subset
  have hEndOff : f 1 ∉ G.U := by
    obtain ⟨j, hj⟩ := hf.2.2.1
    rw [← hj]
    exact cylinderN2Point_not_mem_U hG j
  have hEndV : f 1 ∉ G.V := fun hv => hEndOff (G.V_subset_U hv)
  have hEndBd : f 1 ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    apply Or.inr
    obtain ⟨j, hj⟩ := hf.2.2.1
    rw [← hj]
    rfl
  have hLast := (last_region_visit_mem_vertex_or_terminal f hf.1 hR hz₂).2
  have hw : f z₂ ∈ G.V ∨ f z₂ ∉ G.U := by
    rcases hLast with hv | hz1
    · exact Or.inl (hV ▸ hv)
    · exact Or.inr (hz1.symm ▸ hEndOff)
  have hwBd : f z₂ ∈ G.V ∨ f z₂ ∈ bd ClosedCylinder := by
    rcases hLast with hv | hz1
    · exact Or.inl (hV ▸ hv)
    · exact Or.inr (hz1.symm ▸ hEndBd)
  obtain ⟨θ, hθ⟩ := CylinderLinkage.exists_hasTheta hG.1 L
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ 1
  obtain ⟨F, hFU, hFV, hEdges₀⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  have hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges₀ ec hec with h | ⟨e, he, heq⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, he.1, heq⟩
  obtain ⟨gap, hgap, _, _, _⟩ := exists_single_strip_initial_gap_curve L hG hBd
  obtain ⟨Q, hQproj, hQcl⟩ := exists_lift_of_last_region_segment L hG hθ hD hBd hstrip
    hPH0 f hf.1 hR hz₂ hz₁₂ hNo
  have hQend : radialCylinderProjection (Q 1).1 = f z₂ := by
    simpa only [Icc.convexComb_one] using hQproj 1
  have hTarget : radialCylinderProjection (Q 1).1 ∈ G.V ∨
      radialCylinderProjection (Q 1).1 ∈ bd ClosedCylinder := hQend.symm ▸ hwBd
  obtain ⟨A, hA0, hA1, hAOff⟩ := exists_clockwise_cut_approach_curve_at_contact
    L hG hθ hD hBd hstrip F hFU hFV hEdges hPH0 gap hgap he hside hU hV hR heR
    (Q 1) (hQcl 1) hTarget
  obtain ⟨ga, hgaMap, hga0, hga1, _, _, _, _⟩ := exists_projected_right_cut_approach
    hG gap A hgap hA0 hA1 hQend hw hAOff
  let old : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let p := old.subpath 0 z₁
  let q := old.subpath z₁ z₂
  let r := old.subpath z₂ 1
  let g : Path (cylinderM1Point 1 0) (f z₂) := ⟨ga, hga0, hga1⟩
  have hFinG : (curveVertexHits G f).Finite := by
    have hEq : curveVertexHits G f = curveVertexHits G' f := by simp only [curveVertexHits, hV]
    exact hEq.symm ▸ hf.2.2.2
  have hpFin := (curveL_subpath old hz₁pos.ne hFinG).1
  have hbG : old 1 ∉ G.V := hEndV
  have hrFin := (curveL_subpath_of_end_not_vertex old z₂ 1 hbG hFinG).1
  have hqNo : ∀ t : unitInterval, 0 < t → t < 1 → q t ∉ G.V := by
    intro t ht0 ht1 htV
    have ht := convexComb_mem_Ioo_of_lt hz₁₂ ⟨ht0, ht1⟩
    have hV' : f (Icc.convexComb z₁ z₂ t) ∈ G'.V := hV.symm ▸ htV
    exact hNo _ ht.1 ht.2 hV'
  have hgOff : ∀ t : unitInterval, 0 < t → t < 1 → g t ∉ G.U := by
    intro t ht0 ht1
    change ga t ∉ G.U
    rw [hgaMap t]
    exact hAOff t ht0 ht1
  have hende : f 1 ∉ e := fun h => hEndOff (he.2.1 h).1
  have hrN : IsNormalCurve G r.toContinuousMap :=
    isNormalCurve_tail_of_deleted_edge he hV hU f hf.1 hende hR heR hz₂
  let QC : C(unitInterval, CylinderCover) := ⟨fun t => planeToCylinderCover (Q t).1,
    continuous_planeToCylinderCover.comp (continuous_subtype_val.comp Q.continuous)⟩
  let AC : C(unitInterval, CylinderCover) := ⟨fun t => planeToCylinderCover (A t).1,
    continuous_planeToCylinderCover.comp (continuous_subtype_val.comp A.continuous)⟩
  let s : CylinderCover := planeToCylinderCover (gap 1).1
  have hQCproj : ∀ t, cylinderCoverProjection (QC t) = q t := hQproj
  have hACproj : ∀ t, cylinderCoverProjection (AC t) = g t := fun t => (hgaMap t).symm
  have hAC0 : AC 0 = s := by
    change planeToCylinderCover (A 0).1 = _
    rw [hA0]
  have hAC1 : AC 1 = QC 1 := by
    change planeToCylinderCover (A 1).1 = _
    rw [hA1]
    rfl
  have hsRad : s.1.1 = 1 := by
    change max 1 (min 2 (gap 1).1.1) = 1
    rw [hgap 1]
    norm_num
  have hsAngle : s.2 = 4 * π := by
    change (gap 1).1.2 = 4 * π
    rw [hgap 1]
    norm_num
  have hsProj : cylinderCoverProjection s = cylinderM1Point 1 0 := by
    rw [← hAC0, hACproj 0]
    exact Path.source g
  obtain ⟨HC, hHC1, hHCproj, hHC0, hHCgap⟩ :=
    exists_half_gap_cover_ending_at_initial_copy hG.1 0 s hsRad hsProj
  let h : Path (cylinderN1Point 1 0) (cylinderM1Point 1 0) :=
    ⟨initialCuffHalfBacktrackCurve 1 0, initialCuffHalfBacktrackCurve_zero 0,
      initialCuffHalfBacktrackCurve_one 0⟩
  have hQCin : ∀ t, cylinderCoverCoordinates (QC t) ∈ D :=
    fun t => cut_cover_coordinates_mem hstrip (Q t)
  have hACin : ∀ t, cylinderCoverCoordinates (AC t) ∈ D :=
    fun t => cut_cover_coordinates_mem hstrip (A t)
  have hHCapprox : ∀ t, cylinderCoverCoordinates (HC t) ∈ ({1} ×ˢ Icc (4 * π) (5 * π)) := by
    intro t
    have ht := hHCgap t
    simpa only [hsAngle, Nat.cast_one, div_one, show 4 * π + π = 5 * π by ring] using ht
  obtain ⟨B, hBproj, hB1, hBReturn⟩ := exists_auxiliary_cover_from_region_lifts p q g h QC AC HC
    hQCproj hACproj hHCproj (hAC0.trans hHC1.symm) hAC1 hQCin hACin hHCapprox
  have hBReturn' : ∀ t, leftHalfTime 1 ≤ t → cylinderCoverCoordinates (B t) ∈
      D ∪ ({1} ×ˢ Icc (2 * (((1 : ℤ) : ℝ) + 1) * π / (1 : ℕ))
        ((2 * (((1 : ℤ) : ℝ) + 1) + 1) * π / (1 : ℕ))) := by
    intro t ht
    convert hBReturn t ht using 1; norm_num
  have hBEndAngle : (B 1).2 = (2 * (((1 : ℤ) : ℝ) + 1) + 1) * π / (1 : ℕ) := by
    rw [hB1, hHC0, hsAngle]
    norm_num
    ring
  have hxG : f z₁ ∈ G.V := hV ▸ hz₁V
  obtain ⟨fNew, hfNew, hNewLe⟩ := helix_replacement_comparison_of_return_strip L hG hG' hθ hPH
    hHU hV 1 hD hBd hstrip 0 p q g r hf.2.1 hf.2.2.1 hxG hw
    (isNormalCurve_path_subpath old hf.1 0 z₁) (isNormalCurve_path_subpath old hf.1 z₁ z₂)
    hrN hpFin hrFin hqNo hgOff B hBproj hBReturn' hBEndAngle
  have hbH : f 1 ∉ G'.V := by rw [hV]; exact hEndV
  have hSplit := curvePhi_three_subpaths (k := 1) old hf.2.2.2 hz₁pos hz₁₂ hbH
  exact ⟨fNew, hfNew, hNewLe.trans_eq (hSplit.trans hPhi)⟩

end GraphMinor.GM06
