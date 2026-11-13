module

public import GraphMinor.GM06.Section5CutInitialArcExclusion
public import GraphMinor.GM06.Section5PrefixLiftSeam
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Section5CutGapEdge
import GraphMinor.GM06.Section5ProperPaths
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4PathTools

/-!
# An incident initial prefix forces valency one

Place the aligned prefix lift on the left seam of the new linkage
path. In its cut disc this is an injective boundary arc which leaves
the initial cuff and ends at a drawing vertex. If the initial valency
were different from one, the proved obstruction using only Reductions
1 and 2 would forbid its whole incidence with the chosen region.
This is the larger-valency case of the Reduction 4 progress argument
in VI Section 5, page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- With Reductions 1 and 2 unavailable, a nontrivial initial subpath
whose aligned lift is incident with the chosen region forces initial
valency one. -/
theorem valency_initial_eq_one_of_incident_prefix_of_no_reductions12
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    {Q : Drawing ClosedCylinder} {v : ClosedCylinder}
    (hQ : IsSubpathOf G Q (cylinderM1Point 1 0) v) (hQL : Q.U ⊆ (L.pathDrawing 0).U)
    (q : Curve ClosedCylinder) (hq : ParametrizesSet q Q.U (cylinderM1Point 1 0) v)
    (hqR : range (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2) ⊆
      closure (cylinderCoverRegion 1 G 0)) :
    vertexValency G.toGraph (cylinderM1Point 1 0) = 1 := by
  by_contra hval
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ 1
  obtain ⟨F, hFU, hFV, hEdges⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  have hEdges' : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges ec hec with hbd | ⟨e, he, heq⟩
    · exact Or.inl hbd
    · exact Or.inr ⟨e, he.1, heq⟩
  obtain ⟨g, hgcoord, hginj, hgbd, hgproj⟩ := exists_single_strip_initial_gap_curve L hG hBd
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  obtain ⟨b, hb, hbBd, hgap, _⟩ := exists_boundary_edge_containing_cut_initial_gap hG F hFV hbdF
    hEdges' g hgbd hgproj
  let a := (cylinderInitialLift 1 0).2
  let qLift := cylinderCurveLiftAt q a
  have hqa : Circle.exp a = (q 0).1.2 := by rw [hq.2.2.1]; rfl
  have hproj (t : unitInterval) : cylinderCoverProjection (qLift t) = q t :=
    cylinderCoverProjection_curveLiftAt q a hqa t
  have hqP : range q ⊆ (L.pathDrawing 0).U := by
    rw [hq.2.1]
    exact hQL
  have hcoords (t : unitInterval) : cylinderCoverCoordinates (qLift t) ∈ discBd D := by
    obtain ⟨u, _, hu⟩ := exists_left_seam_parameter_of_path_prefix L hG q hqP hq.2.2.1 t
    change cylinderCoverCoordinates (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 t) ∈ _
    rw [hu]
    change (max 1 (min 2 (liftedLinkageCurve hG.1 L 1 u).1),
      (liftedLinkageCurve hG.1 L 1 u).2) ∈ discBd D
    have hr := (liftedLinkageCurve_props_raw hG.1 L 1).1 u
    rw [min_eq_right hr.2, max_eq_right hr.1, hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self u)))
  have hcont : Continuous (fun t => cylinderCoverCoordinates (qLift t)) :=
    ((continuous_subtype_val.comp (continuous_fst.comp qLift.continuous)).prodMk
      (continuous_snd.comp qLift.continuous))
  let f : Curve D := ⟨fun t => ⟨cylinderCoverCoordinates (qLift t), discBd_subset D (hcoords t)⟩,
    hcont.subtype_mk _⟩
  have hfproj (t : unitInterval) : radialCylinderProjection (f t).1 = q t := by
    change cylinderCoverProjection (planeToCylinderCover (cylinderCoverCoordinates (qLift t))) = q t
    rw [planeToCylinderCover_coordinates]
    exact hproj t
  have hf : Function.Injective f := by
    intro s t hst
    apply hq.1
    exact (hfproj s).symm.trans ((congrArg (fun p : D => radialCylinderProjection p.1) hst).trans (hfproj t))
  have hf0 : f 0 = g 0 := by
    apply Subtype.ext
    change cylinderCoverCoordinates (cylinderCurveLiftAt q a 0) = (g 0).1
    rw [cylinderCurveLiftAt_zero, hq.2.2.1, hgcoord]
    norm_num [cylinderCoverCoordinates, a, cylinderInitialLift, cylinderM1Point, cylinderPoint]
  have hfBd : range f ⊆ bd D := by
    rintro p ⟨t, rfl⟩
    obtain ⟨z, hz, heq⟩ := hcoords t
    exact (Subtype.ext heq : z = f t) ▸ hz
  have hf1 : f 1 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (f 1).1 ∈ G.V
    rw [hfproj, hq.2.2.2]
    exact hQ.1.1 (isPathDrawing_end_vertices hQ.2.2).2
  have haway (t : unitInterval) (ht : 0 < t) : (f t).1.1 ≠ 1 := by
    change (q t).1.1 ≠ 1
    intro hrad
    have hqtP : q t ∈ (L.pathDrawing 0).U := hqP (mem_range_self t)
    have hqtBd : q t ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl hrad
    have hends : q t ∈ ({cylinderM1Point 1 0, L.curve 0 1} : Set ClosedCylinder) :=
      L.U_inter_boundary hG 0 ▸ ⟨hqtP, hqtBd⟩
    rcases hends with hs | hend
    · have heq : q t = q 0 := hs.trans hq.2.2.1.symm
      exact ht.ne' (hq.1 heq)
    · have htRad : (L.curve 0 1).1.1 = 2 := by
        obtain ⟨j, hj⟩ := L.curve_one_mem 0
        rw [← hj]
        rfl
      have hbad : (1 : ℝ) = 2 := hrad.symm.trans
        ((congrArg (fun p : ClosedCylinder => p.1.1) (mem_singleton_iff.mp hend)).trans htRad)
      norm_num at hbad
  obtain ⟨_, hcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  apply cut_initial_boundary_arc_not_subset_region_closure_of_no_reductions12 L hG hθ hno1 hno2 hval
    hD hBd hstrip F hFU hFV hEdges g hgcoord hginj hgproj hb hbBd hgap f hf hf0 hfBd hf1 haway
  rintro p ⟨t, rfl⟩
  obtain ⟨z, hz, heq⟩ := hcl.symm ▸ hqR (mem_range_self t)
  have hft : planeToCylinderCover (f t).1 = qLift t := planeToCylinderCover_coordinates (qLift t)
  exact hemb.injective (heq.trans hft.symm) ▸ hz

end GraphMinor.GM06
