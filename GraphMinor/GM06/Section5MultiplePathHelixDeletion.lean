module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Helix
import GraphMinor.GM06.Section5HelixClaim1
import GraphMinor.GM06.Section5DeletedEdgeRegion
import GraphMinor.GM06.Section5RegionVisit
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5IndexedStripImage
import GraphMinor.GM06.Section5InitialStripNeighbourhood
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.GM06.Section5ClosedStripCurveLift
import GraphMinor.GM06.Section5DeletedEdgeCylinderFaces
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5RegionBridge
import GraphMinor.GM06.Section5HalfGapCover
import GraphMinor.GM06.Section5AuxiliaryCover
import GraphMinor.GM06.Section5HelixReturnComparison
import GraphMinor.GM06.Section5ThreeSubpaths
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5DeletedEdgeTail
import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5SubpathCount
import GraphMinor.GM11.Regions
import GraphMinor.Surface.CutComp

/-!
# Lifting a helix across an edge deletion with at least two paths

This proves the multiple-path Reduction 1 case of VI (5.5), pages
130–132. The old approach region and the last region segment lie in
the closed preceding linkage strip. Its injective projection lifts
both curves with the same contact. Reverse that approach and the
following half gap to obtain the auxiliary return. The direct
crossing count and the exact potential identity finish the proof.
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

/-- Graph Minors VI (5.5), Reduction 1 for at least two linkage
paths, following the old-region approach and crossing argument. -/
theorem theorem_5_5_red1_of_two_le
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G')
    (hRed : Section5Reduction1Step k G L G' L')
    (f' : Curve ClosedCylinder) (hf' : IsHelix k G' f') :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f ≤ curvePhi k G' f' := by
  classical
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  obtain ⟨i, e, he, hside, hV, _, hU, hpaths, _⟩ := hRed
  by_cases hdis : Disjoint (range f') e
  · obtain ⟨hf, hphi⟩ := helix_of_delete_edge_of_disjoint k G G' e f' hV hU hf' hdis
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
    hpaths i he hs.1 hs.2 f' hf' hR heR hHit hz₂'
  obtain ⟨z₁, hz₁₂, hz₁V, hNo⟩ := exists_last_vertex_hit_before f hf.2.2.2 hprior
  have hz₁pos : 0 < z₁ := by
    by_contra hnot
    have hz₁0 : z₁ = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have h0V : f 0 ∈ G'.V := hz₁0 ▸ hz₁V
    obtain ⟨j, hj⟩ := hf.2.1
    rw [← hj] at h0V
    exact cylinderN1Point_not_mem_U hG' j (G'.V_subset_U h0V)
  have hPH : ∀ j, (L.pathDrawing j).U ⊆ G'.U := by
    intro j
    have hh := (L'.isSubdrawing j).2
    rw [hpaths] at hh
    exact hh
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
  let m : ℤ := i.1
  obtain ⟨D, hD, hBd, hstrip, hImage⟩ := exists_indexed_stripDisc_with_image L hG hθ m
  have hiPred : modIdx k hG.1 m = finPredCycle i := modIdx_natCast_eq_finPredCycle hG.1 i
  rw [hiPred] at hImage
  obtain ⟨xe, hxe⟩ := he.1
  have hRS : R ⊆ cylinderStrip L (finPredCycle i) :=
    region_subset_strip_of_retained_linkage L L' hpaths hR (finPredCycle i)
      ⟨xe, heR hxe, hs.2 hxe⟩
  have hwcl : f z₂ ∈ closure R := (last_region_visit_mem_vertex_or_terminal f hf.1 hR hz₂).1
  obtain ⟨rOld, hrOld, hrSub, hscl, hwclOld⟩ :=
    exists_old_cylinder_region_at_deleted_edge_region_closure L hG he hU hR heR hs.1 hwcl
  obtain ⟨F, _, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  have hsV : cylinderM1Point k i ∈ G.V := by
    have hv : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hv).1
  obtain ⟨ga, hga0, hga1, hgaR⟩ := exists_curve_from_vertex_through_incident_region
    hFU hFV hrOld hsV hscl hwclOld hw
  let old : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let p := old.subpath 0 z₁
  let q := old.subpath z₁ z₂
  let r := old.subpath z₂ 1
  let g : Path (cylinderM1Point k i) (f z₂) := ⟨ga, hga0, hga1⟩
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
    intro t ht0 ht1 htG
    exact GM11.region_subset hrOld (hgaR t ht0 ht1) htG
  have hende : f 1 ∉ e := fun h => hEndOff (he.2.1 h).1
  have hrN : IsNormalCurve G r.toContinuousMap :=
    isNormalCurve_tail_of_deleted_edge he hV hU f hf.1 hende hR heR hz₂
  have hQrangeR : range q ⊆ closure R := by
    rintro x ⟨t, rfl⟩
    exact (curve_between_last_vertex_and_region_visit f hf.1 hR hz₂ hz₁₂ hNo).2
      _ (Icc.le_convexComb hz₁₂.le t) (Icc.convexComb_le hz₁₂.le t)
  have hGrangeR : range g ⊆ closure R := by
    rintro x ⟨t, rfl⟩
    by_cases ht0 : t = 0
    · rw [ht0, Path.source]
      exact closure_mono hrSub hscl
    · by_cases ht1 : t = 1
      · rw [ht1, Path.target]
        exact hwcl
      · exact subset_closure (hrSub (hgaR t (lt_of_le_of_ne bot_le (Ne.symm ht0))
          (lt_of_le_of_ne le_top ht1)))
  have hQrangeD : range q ⊆ radialCylinderProjection '' D := by
    rw [hImage]
    exact hQrangeR.trans (closure_mono hRS)
  have hGrangeD : range g ⊆ radialCylinderProjection '' D := by
    rw [hImage]
    exact hGrangeR.trans (closure_mono hRS)
  obtain ⟨Q, hQproj⟩ := exists_curve_lift_to_injective_strip L hG hk hθ m hD hBd hstrip q.toContinuousMap hQrangeD
  obtain ⟨A, hAproj⟩ := exists_curve_lift_to_injective_strip L hG hk hθ m hD hBd hstrip g.toContinuousMap hGrangeD
  have hinj := injOn_radialCylinderProjection_stripDisc L hG hk hθ m hD hBd hstrip
  let right := liftedLinkageCurve hG.1 L (m + 1) 0
  have hrightD : right ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inr (mem_range_self 0)))
  have hiRight : modIdx k hG.1 (m + 1) = i := modIdx_natCast_succ hG.1 i
  have hrightProj : radialCylinderProjection right = cylinderM1Point k i := by
    rw [radialCylinderProjection_liftedLinkageCurve, hiRight]
    exact (L.curve_parametrizes i).2.2.1
  have hA0raw : (A 0).1 = right := hinj (A 0).2 hrightD
    (((hAproj 0).trans (Path.source g)).trans hrightProj.symm)
  have hA1raw : (A 1).1 = (Q 1).1 := hinj (A 1).2 (Q 1).2
    (((hAproj 1).trans (Path.target g)).trans ((hQproj 1).trans (Path.target q)).symm)
  let QC : C(unitInterval, CylinderCover) := ⟨fun t => planeToCylinderCover (Q t).1,
    continuous_planeToCylinderCover.comp (continuous_subtype_val.comp Q.continuous)⟩
  let AC : C(unitInterval, CylinderCover) := ⟨fun t => planeToCylinderCover (A t).1,
    continuous_planeToCylinderCover.comp (continuous_subtype_val.comp A.continuous)⟩
  let s : CylinderCover := planeToCylinderCover right
  have hQCproj : ∀ t, cylinderCoverProjection (QC t) = q t := hQproj
  have hACproj : ∀ t, cylinderCoverProjection (AC t) = g t := hAproj
  have hAC0 : AC 0 = s := congrArg planeToCylinderCover hA0raw
  have hAC1 : AC 1 = QC 1 := congrArg planeToCylinderCover hA1raw
  have hsRad : s.1.1 = 1 := by
    change max 1 (min 2 (liftedLinkageCurve hG.1 L (m + 1) 0).1) = 1
    rw [(liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.1]
    norm_num
  have hsAngle : s.2 = 2 * ((m : ℝ) + 1) * π / k := by
    change (liftedLinkageCurve hG.1 L (m + 1) 0).2 = _
    simpa only [Int.cast_add, Int.cast_one] using
      (liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.2.1
  have hsProj : cylinderCoverProjection s = cylinderM1Point k i := hrightProj
  obtain ⟨HC, hHC1, hHCproj, hHC0, hHCgap⟩ :=
    exists_half_gap_cover_ending_at_initial_copy hG.1 i s hsRad hsProj
  let h : Path (cylinderN1Point k i) (cylinderM1Point k i) :=
    ⟨initialCuffHalfBacktrackCurve k i, initialCuffHalfBacktrackCurve_zero i,
      initialCuffHalfBacktrackCurve_one i⟩
  have hQCin : ∀ t, cylinderCoverCoordinates (QC t) ∈ D :=
    fun t => cut_cover_coordinates_mem hstrip (Q t)
  have hACin : ∀ t, cylinderCoverCoordinates (AC t) ∈ D :=
    fun t => cut_cover_coordinates_mem hstrip (A t)
  have hUpper : 2 * ((m : ℝ) + 1) * π / k + π / k = (2 * ((m : ℝ) + 1) + 1) * π / k := by ring
  have hHCin : ∀ t, cylinderCoverCoordinates (HC t) ∈
      ({1} ×ˢ Icc (2 * ((m : ℝ) + 1) * π / k) ((2 * ((m : ℝ) + 1) + 1) * π / k)) := by
    intro t
    simpa only [hsAngle, hUpper] using hHCgap t
  obtain ⟨B, hBproj, hB1, hBReturn⟩ := exists_auxiliary_cover_from_region_lifts p q g h QC AC HC
    hQCproj hACproj hHCproj (hAC0.trans hHC1.symm) hAC1 hQCin hACin hHCin
  have hBEndAngle : (B 1).2 = (2 * ((m : ℝ) + 1) + 1) * π / k := by
    rw [hB1, hHC0, hsAngle, hUpper]
  have hxG : f z₁ ∈ G.V := hV ▸ hz₁V
  obtain ⟨fNew, hfNew, hNewLe⟩ := helix_replacement_comparison_of_return_strip L hG hG' hθ hPH
    hHU hV m hD hBd hstrip i p q g r hf.2.1 hf.2.2.1 hxG hw
    (isNormalCurve_path_subpath old hf.1 0 z₁) (isNormalCurve_path_subpath old hf.1 z₁ z₂)
    hrN hpFin hrFin hqNo hgOff B hBproj hBReturn hBEndAngle
  have hbH : f 1 ∉ G'.V := by rw [hV]; exact hEndV
  have hSplit := curvePhi_three_subpaths (k := k) old hf.2.2.2 hz₁pos hz₁₂ hbH
  exact ⟨fNew, hfNew, hNewLe.trans_eq (hSplit.trans hPhi)⟩

end GraphMinor.GM06
