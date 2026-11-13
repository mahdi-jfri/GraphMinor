module

public import GraphMinor.GM06.Section5CutGapEdge
public import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5DiscFrontierPaths
import GraphMinor.GM06.Section5CutConnected
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Section5CoverRegionRight
import GraphMinor.GM06.Section4PathTools

/-!
# A region path between the two initial copies

In the one-path cut disc, both copies of the initial vertex are
incident with the chosen lifted region. The augmented drawing is
connected when no reduction applies. Its region walk joins the two
copies while avoiding the added initial gap edge. Every point of the
path remains incident with the chosen cover region. This is the
boundary-path step in VI (5.1), page 129, before taking the first
contact with the other seam copy.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The region walk on the cut disc joins the distinct initial copies,
avoiding the added gap edge and retaining the specified lifted incidences. -/
theorem exists_initial_copies_subpath_on_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    (hginj : Function.Injective g) (hgbd : range g ⊆ bd D)
    (hgproj : ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t) :
    ∃ (Q : Drawing D) (e : Set D), IsSubpathOf F Q (g 0) (g 1) ∧
      (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0) ∧
      e ∈ F.E ∧ e ⊆ bd D ∧ g '' Ioo 0 1 ⊆ e ∧ e ∉ Q.E := by
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  let r := (a ⁻¹' cylinderCoverRegion 1 G 0) \ bd D
  obtain ⟨hr, hcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  have ha0 : a (g 0) = cylinderInitialLift 1 0 := by
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 (g 0).1.1) = 1
      rw [hgcoord]
      norm_num
    · change (g 0).1.2 = _
      rw [hgcoord]
      norm_num [cylinderInitialLift]
  have ha1 : a (g 1) = (⟨1, by norm_num⟩, 2 * ((0 + 2 : ℕ) : ℝ) * π / (1 : ℕ)) := by
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 (g 1).1.1) = 1
      rw [hgcoord]
      norm_num
    · change (g 1).1.2 = _
      rw [hgcoord]
      norm_num
  have hends (t : unitInterval) (ht : a (g t) ∈ closure (cylinderCoverRegion 1 G 0)) :
      g t ∈ closure r := by
    obtain ⟨q, hq, heq⟩ := hcl.symm ▸ ht
    exact hemb.injective heq ▸ hq
  have h0cl : g 0 ∈ closure r := hends 0 (ha0.symm ▸ cylinderInitialLift_mem_closure_coverRegion hG 0)
  have h1cl : g 1 ∈ closure r := hends 1 (by
    rw [ha1]
    simpa only [Fin.val_zero, zero_add] using right_initialLift_mem_closure_coverRegion hG (0 : Fin 1))
  have hsV : cylinderM1Point 1 0 ∈ G.V :=
    (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).1
  have hg0V : g 0 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (g 0).1 ∈ G.V
    rw [hgproj, (initialCuffGapCurve_props hG 0).1]
    exact hsV
  have hg1V : g 1 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (g 1).1 ∈ G.V
    rw [hgproj, (initialCuffGapCurve_props hG 0).2.1]
    have hi : finSuccCycle (0 : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hi]
    exact hsV
  have hbd : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  obtain ⟨e, he, heBd, hgap, _⟩ := exists_boundary_edge_containing_cut_initial_gap hG F hFV hbd hEdges
    g hgbd hgproj
  have hconn := isConnected_augmented_single_strip_of_no_reduction L hG hθ hno hD hBd hstrip hFU
  obtain ⟨Q, hQ, hQr, heQ⟩ := exists_subpath_in_disc_region_closure_avoiding_boundary_edge
    (show IsClosedDiscSpace D from hD) hconn hbd hr ⟨hg0V, h0cl⟩ ⟨hg1V, h1cl⟩
    (fun h => zero_ne_one (hginj h)) he heBd
  refine ⟨Q, e, hQ, ?_, he, heBd, hgap, heQ⟩
  exact (image_mono hQr).trans (subset_of_eq hcl)

end GraphMinor.GM06
