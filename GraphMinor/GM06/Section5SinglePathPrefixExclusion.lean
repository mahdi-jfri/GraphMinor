module

public import GraphMinor.GM06.Section5CutInitialArcExclusion
public import GraphMinor.GM06.Section5CoverLinkageLift
import GraphMinor.GM06.Section5CutStripBoundary
import GraphMinor.GM06.Section5CutGapEdge
import GraphMinor.GM06.Section5CutInitialGap
import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5StripImage

/-!
# The lifted old prefix fails incidence in the one-path case

Construct the augmented cut drawing and its initial gap edge.
Parametrize the left seam from its initial copy to the given old
path vertex. Every positive parameter leaves the initial cuff, so
the proved initial-boundary-arc obstruction applies. The indexed
seam is exactly the aligned lift used in Reduction 4, and the cut
region has the same lifted closure. Thus the required failed
incidence follows from geometry in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- At larger initial valency, every nontrivial initial prefix of the
sole linkage lift has a point outside the chosen cover region closure. -/
theorem single_path_initial_lift_prefix_not_subset_coverRegion
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (u : unitInterval) (hu : 0 < u) (huV : L.curve 0 u ∈ (L.pathDrawing 0).V) :
    ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
      closure (cylinderCoverRegion 1 G 0)) := by
  intro hprefix
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
  let Γ := liftedLinkageCurve hG.1 L 1
  have hΓBd (t : unitInterval) : Γ t ∈ discBd D := by
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
  let f : Curve D := ⟨fun t => ⟨Γ (t * u), discBd_subset D (hΓBd (t * u))⟩, by fun_prop⟩
  have hf : Function.Injective f := by
    intro s t hst
    have heq := (isArcMap_liftedLinkageCurve hG.1 L 1).2 (congrArg Subtype.val hst)
    have heqR : (s : ℝ) * (u : ℝ) = (t : ℝ) * (u : ℝ) := congrArg Subtype.val heq
    exact Subtype.ext (mul_right_cancel₀ (show (u : ℝ) ≠ 0 from ne_of_gt hu) heqR)
  have hΓ0 : Γ 0 = (1, 2 * π) := by
    apply Prod.ext
    · exact (liftedLinkageCurve_props_raw hG.1 L 1).2.1
    · simpa using (liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1
  have hf0 : f 0 = g 0 := by
    apply Subtype.ext
    change Γ (0 * u) = (g 0).1
    rw [zero_mul, hΓ0, hgcoord]
    norm_num
  have hfBd : range f ⊆ bd D := by
    rintro p ⟨t, rfl⟩
    obtain ⟨q, hq, heq⟩ := hΓBd (t * u)
    exact (Subtype.ext heq : q = f t) ▸ hq
  have hf1 : f 1 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (Γ (1 * u)) ∈ G.V
    rw [one_mul, radialCylinderProjection_liftedLinkageCurve]
    have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
    rw [hi]
    exact (L.isSubdrawing 0).1.1 huV
  have haway (t : unitInterval) (ht : 0 < t) : (f t).1.1 ≠ 1 := by
    have hpos : 0 < t * u := by
      change (0 : ℝ) < (t : ℝ) * (u : ℝ)
      exact mul_pos ht hu
    change (Γ (t * u)).1 ≠ 1
    by_cases htu : t * u = 1
    · rw [htu]
      have hΓ1 : (Γ 1).1 = 2 := (liftedLinkageCurve_props_raw hG.1 L 1).2.2.1
      rw [hΓ1]
      norm_num
    · exact ne_of_gt (liftedLinkageCurve_interior_radius L hG 1
        ⟨hpos, unitInterval.lt_one_iff_ne_one.mpr htu⟩).1
  have hLift (t : unitInterval) :
      cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 t = planeToCylinderCover (Γ t) := by
    have h := cylinderCurveLiftAt_eq_indexed_linkage_lift hG.1 L 1 t
    have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
    rw [hi] at h
    simpa [cylinderInitialLift] using h
  obtain ⟨_, hcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  apply cut_initial_boundary_arc_not_subset_region_closure L hG hθ hno hval hD hBd hstrip F hFU hFV
    hEdges g hgcoord hginj hgproj hb hbBd hgap f hf hf0 hfBd hf1 haway
  rintro p ⟨t, rfl⟩
  have hcov : planeToCylinderCover (f t).1 ∈ closure (cylinderCoverRegion 1 G 0) := by
    change planeToCylinderCover (Γ (t * u)) ∈ _
    rw [← hLift]
    exact hprefix ⟨t * u, ⟨bot_le, unitInterval.mul_le_right⟩, rfl⟩
  obtain ⟨q, hq, heq⟩ := hcl.symm ▸ hcov
  exact hemb.injective heq ▸ hq

end GraphMinor.GM06
