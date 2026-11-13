module

public import GraphMinor.GM06.Section5CutRegionCoordinates
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5RightInitialEdge
import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM11.CircuitRegions

/-!
# Excluding arrival at the right initial copy along an original edge

A lifted original edge off the linkage misses both seams. Its points
lie in the closed cut disc, so the sheet identification puts it
inside the selected strip. Incidence with the right initial
copy would then give the clockwise-side certificate for Reduction 1.
Thus an unreduced drawing excludes this arrival in the one-path
boundary argument of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Incidence of a full lifted non-seam edge at the clockwise initial
copy supplies the actual clockwise-side certificate. -/
theorem isClockwiseInitialEdge_of_right_cut_edge_incidence
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} {ec : Set D} (hec : ec ∈ F.E)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (heq : ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    (⟨1, by norm_num⟩, 4 * π) ∈
      closure ((fun p : D => planeToCylinderCover p.1) '' ec) → IsClockwiseInitialEdge L 0 e := by
  intro hinc
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  have hconn : IsConnected (a '' ec) := hec.2.2.1.isConnected.image a
    (continuous_planeToCylinderCover.comp continuous_subtype_val).continuousOn
  have himage : cylinderCoverProjection '' (a '' ec) = e := by
    rw [image_image]
    change (fun p : D => radialCylinderProjection p.1) '' ec = e
    rw [heq, image_preimage_eq _ (surjective_single_strip_projection L hG hθ hD hBd hstrip)]
  have hdis : Disjoint e (L.pathDrawing 0).U :=
    GM11.edge_disjoint_U (L.isSubdrawing 0).1 he heP
  have hsub : a '' ec ⊆ cylinderCoverStrip L 1 := by
    rw [cylinderCoverStrip_eq_single_strip_sheet L hG hθ hD hBd hstrip]
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hp
    refine ⟨⟨x.1, x.2, rfl⟩, ?_⟩
    change cylinderCoverProjection (a x) ∉ (L.pathDrawing 0).U
    have hxe : radialCylinderProjection x.1 ∈ e := by
      rw [heq] at hx
      exact hx
    exact disjoint_left.mp hdis hxe
  exact isClockwiseInitialEdge_of_incident_right_initialLift L hconn himage hinc hsub

/-- A full lifted original edge off the seam cannot approach the right
initial copy when Reduction 1 does not apply. -/
theorem not_right_initialLift_mem_closure_cut_edge_of_no_reduction1
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} {ec : Set D} (hec : ec ∈ F.E)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (heq : ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    (⟨1, by norm_num⟩, 4 * π) ∉
      closure ((fun p : D => planeToCylinderCover p.1) '' ec) := by
  intro hinc
  have hside := isClockwiseInitialEdge_of_right_cut_edge_incidence L hG hθ hD hBd hstrip
    hec he heP heq hinc
  obtain ⟨G', L', hG', hstep⟩ := exists_reduction1_of_clockwise_initial_edge L hG he hside
  exact hno1 G' L' hG' hstep

/-- A full lifted original edge off the seam cannot approach the right
initial copy when no reduction applies. -/
theorem not_right_initialLift_mem_closure_cut_edge
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} {ec : Set D} (hec : ec ∈ F.E)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (heq : ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    (⟨1, by norm_num⟩, 4 * π) ∉
      closure ((fun p : D => planeToCylinderCover p.1) '' ec) := by
  exact not_right_initialLift_mem_closure_cut_edge_of_no_reduction1 L hG hθ
    (fun H M hH h1 => hno ⟨H, M, hH, Or.inl h1⟩) hD hBd hstrip hec he heP heq

end GraphMinor.GM06
