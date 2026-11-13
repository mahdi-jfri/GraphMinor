module

public import GraphMinor.GM06.Section5CutRegionCoordinates
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5CutSheetComponent

/-!
# Clockwise edges reach the right initial copy in the cut disc

For the one-path case of VI (5.5), the clockwise edge certificate
chooses the initial-vertex copy for region access. Translate its
connected cover lift by one full turn into the selected cut sheet.
That sheet lies in the closed strip disc. The translated lift is
therefore contained in the full lifted edge and approaches the
right initial copy, at angle four pi.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A clockwise initial edge approaches the right initial copy in
the chosen one-path cut disc, fixing the side used in VI (5.5). -/
theorem right_initialLift_mem_closure_cut_edge_of_clockwise
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {e : Set ClosedCylinder} (hside : IsClockwiseInitialEdge L 0 e) :
    (⟨1, by norm_num⟩, 4 * π) ∈
      closure ((fun p : D => planeToCylinderCover p.1) ''
        ((fun p : D => radialCylinderProjection p.1) ⁻¹' e)) := by
  obtain ⟨A, _, hproj, hinc, hAS⟩ := hside
  let E := cylinderCoverTranslation 1
  let B := E '' A
  have hpoint : E (cylinderInitialLift 1 0) = (⟨1, by norm_num⟩, 4 * π) := by
    apply Prod.ext
    · rfl
    · change (cylinderInitialLift 1 0).2 + ((1 : ℤ) : ℝ) * (2 * π) = 4 * π
      norm_num [cylinderInitialLift]
      ring
  have hincB : (⟨1, by norm_num⟩, 4 * π) ∈ closure B := by
    rw [← hpoint]
    exact mem_closure_image E.continuous.continuousAt hinc
  have hBS : B ⊆ cylinderCoverStrip L 1 := by
    have hshift := image_cylinderCoverStrip_translation L 0 1
    simpa only [Int.zero_add] using (image_mono hAS : B ⊆ E '' cylinderCoverStrip L 0)
      |>.trans hshift.subset
  have hBproj : cylinderCoverProjection '' B = e := by
    rw [show B = E '' A from rfl, image_image]
    have hcomp : cylinderCoverProjection ∘ E = cylinderCoverProjection := by
      funext p
      exact cylinderCoverProjection_translation 1 p
    change (cylinderCoverProjection ∘ E) '' A = e
    rw [hcomp, hproj]
  apply closure_mono _ hincB
  intro p hp
  have hpSheet := hBS hp
  rw [cylinderCoverStrip_eq_single_strip_sheet L hG hθ hD hBd hstrip] at hpSheet
  obtain ⟨q, hq, hqp⟩ := hpSheet.1
  refine ⟨⟨q, hq⟩, ?_, hqp⟩
  change radialCylinderProjection q ∈ e
  change cylinderCoverProjection (planeToCylinderCover q) ∈ e
  rw [hqp]
  exact hBproj ▸ mem_image_of_mem cylinderCoverProjection hp

/-- The right endpoint of the lifted cuff gap is incident with the
full cut-disc edge selected by the clockwise certificate. This is
incidence at the actual vertex copy used for VI (5.5). -/
theorem right_gap_end_mem_closure_cut_edge_of_clockwise
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    {e : Set ClosedCylinder} (hside : IsClockwiseInitialEdge L 0 e) :
    g 1 ∈ closure ((fun p : D => radialCylinderProjection p.1) ⁻¹' e) := by
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  have ha := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hpoint : a (g 1) = (⟨1, by norm_num⟩, 4 * π) := by
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 (g 1).1.1) = 1
      rw [hgcoord 1]
      norm_num
    · change (g 1).1.2 = 4 * π
      rw [hgcoord 1]
      norm_num
  have hinc := right_initialLift_mem_closure_cut_edge_of_clockwise L hG hθ hD hBd hstrip hside
  change (⟨1, by norm_num⟩, 4 * π) ∈ closure (a ''
    ((fun p : D => radialCylinderProjection p.1) ⁻¹' e)) at hinc
  rw [← hpoint, ha.closure_image_eq] at hinc
  obtain ⟨p, hp, heq⟩ := hinc
  exact ha.injective heq ▸ hp

end GraphMinor.GM06
