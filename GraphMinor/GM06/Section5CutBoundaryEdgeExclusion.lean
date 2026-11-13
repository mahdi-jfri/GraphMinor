module

public import GraphMinor.GM06.Section5CutGapIncidence
import GraphMinor.GM06.Section5CutLeftEdgeIncidence
import GraphMinor.GM06.Section5CutPunctured
import GraphMinor.GM06.Section5CutEdgePreimage
import GraphMinor.GM06.Section5DiscBoundaryCorner
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5BranchArc
import GraphMinor.GM06.DiscRegions

/-!
# No other boundary edge is incident with the chosen region at the left copy

If the original initial vertex has valency greater than one, an
extra non-linkage edge lifts at the left initial copy. It lies off
the cut-disc boundary. The added initial gap edge is incident with
the chosen region. A second boundary edge incident with that region
would exclude every third edge by the connected-puncture corner
lemma, contradicting the extra edge. This is the initial-edge
exclusion in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- At the left initial copy, no boundary edge other than the added
gap edge is incident with the selected cut region when the original
initial vertex has valency different from one and Reductions 1 and 2 are unavailable. -/
theorem cut_boundary_edge_not_subset_region_closure_of_no_reductions12
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    (hgproj : ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t)
    {b a : Set D} (hb : b ∈ F.E) (hbBd : b ⊆ bd D) (hgap : g '' Ioo 0 1 ⊆ b)
    (ha : a ∈ F.E) (haBd : a ⊆ bd D) (hab : a ≠ b) (hsa : g 0 ∈ closure a) :
    ¬ a ⊆ closure (((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) := by
  intro har
  let r := ((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D
  obtain ⟨hr, _⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  obtain ⟨hbr, hgb⟩ := cut_gap_edge_incidence L hG hθ hD hBd hstrip F hFU g hgcoord hb hgap
  have hsb : g 0 ∈ closure b := hgb (mem_range_self 0)
  have hsr : g 0 ∈ closure r := (closure_minimal hbr isClosed_closure) hsb
  have hsproj : radialCylinderProjection (g 0).1 = cylinderM1Point 1 0 := by
    rw [hgproj, (initialCuffGapCurve_props hG 0).1]
  have hsV : g 0 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (g 0).1 ∈ G.V
    rw [hsproj]
    exact (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).1
  have hpun := isConnected_punctured_single_strip_drawing_of_no_reduction2 L hG hθ hno2 hD hBd hstrip
    F hFU hFV hEdges (g 0) hsproj
  obtain ⟨e, he, v, _, hl, heP⟩ := exists_extra_initial_edge_of_valency_ne_one_of_no_reduction2 L hG hno2 0 hval
  have hse : cylinderM1Point 1 0 ∈ closure e :=
    (show cylinderM1Point 1 0 ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ {v}).1
  let ec := (fun p : D => radialCylinderProjection p.1) ⁻¹' e
  have hec : ec ∈ F.E := full_preimage_non_seam_edge_mem L hG hθ hD hBd hstrip F hFU hFV hEdges he heP
  have hsec : g 0 ∈ closure ec :=
    left_gap_end_mem_closure_cut_initial_edge_of_no_reduction1 L hG hθ hno1 hD hBd hstrip hec he heP rfl hse g hgcoord
  have hbd : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  have hBdClosed := isClosed_bd_of_isClosedDiscSpace (show IsClosedDiscSpace D from hD)
  have haClBd : closure a ⊆ bd D := closure_minimal haBd hBdClosed
  have hbClBd : closure b ⊆ bd D := closure_minimal hbBd hBdClosed
  have heChoice := eq_or_eq_of_two_boundary_edges_incident_disc_region
    (show IsClosedDiscSpace D from hD) hbd hsV hpun.isPreconnected hr hsr ha hb hab hsa hsb
    har hbr haClBd hbClBd hec hsec
  obtain ⟨p, hp⟩ := hec.1
  have hpBd : p ∈ bd D := by
    rcases heChoice with hea | heb
    · exact haBd (hea ▸ hp)
    · exact hbBd (heb ▸ hp)
  exact disjoint_left.mp (preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip he heP) hp hpBd


/-- At the left initial copy, no boundary edge other than the added
gap edge is incident with the selected cut region when the original
initial vertex has valency different from one. -/
theorem cut_boundary_edge_not_subset_region_closure
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    (hgproj : ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t)
    {b a : Set D} (hb : b ∈ F.E) (hbBd : b ⊆ bd D) (hgap : g '' Ioo 0 1 ⊆ b)
    (ha : a ∈ F.E) (haBd : a ⊆ bd D) (hab : a ≠ b) (hsa : g 0 ∈ closure a) :
    ¬ a ⊆ closure (((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) := by
  exact cut_boundary_edge_not_subset_region_closure_of_no_reductions12 L hG hθ
    (fun H M hH h1 => hno ⟨H, M, hH, Or.inl h1⟩)
    (fun H M hH h2 => hno ⟨H, M, hH, Or.inr (Or.inl h2)⟩)
    hval hD hBd hstrip F hFU hFV hEdges g hgcoord hgproj hb hbBd hgap ha haBd hab hsa

end GraphMinor.GM06
