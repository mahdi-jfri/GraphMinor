module

public import GraphMinor.GM06.Section5CapDrawing
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5ClosedLocalSheet
import GraphMinor.GM06.Section5CoverStripDiscSheet

/-!
# A closed local set for the clockwise side

For VI (5.7), page 133, restrict the compact lifted strip disc to
one inverse cover chart before mapping it to the capped sphere.
This gives a closed set whose local membership, away from the
linkage, is exactly membership in the clockwise cover strip.
For one path the restriction keeps the two endpoint copies apart.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Near an initial vertex the selected cover strip is represented
by a closed sphere set, with exact membership off the linkage. -/
theorem exists_closed_local_clockwise_side
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source) :
    ∃ B O : Set (OnePoint EuclideanPlane), IsClosed B ∧ IsOpen O ∧
      cylinderToSphere (cylinderM1Point k i) ∈ O ∧ B ⊆ range cylinderToSphere ∧
      ∀ y : ClosedCylinder, cylinderToSphere y ∈ O → y ∈ η.target ∧
        (y ∉ ⋃ j, (L.pathDrawing j).U →
          (cylinderToSphere y ∈ B ↔ η.symm y ∈ cylinderCoverStrip L (i.val : ℤ))) := by
  obtain ⟨D, hD, _, _, hsheet⟩ := exists_cover_strip_disc_sheet L hG hθ (i.val : ℤ)
  have hK : IsCompact (planeToCylinderCover '' D) :=
    hD.isCompact.image continuous_planeToCylinderCover
  obtain ⟨B, O, hBc, hOo, hsO, hBr, hmem⟩ := exists_closed_local_sheet_image η
    isClosedEmbedding_cylinderToSphere.isEmbedding hsη hK
  have hs : η (cylinderInitialLift k i) = cylinderM1Point k i := by rw [hη]; rfl
  rw [hs] at hsO
  refine ⟨B, O, hBc, hOo, hsO, hBr, ?_⟩
  intro y hyO
  obtain ⟨hyη, hyB⟩ := hmem y hyO
  refine ⟨hyη, ?_⟩
  intro hyL
  have hproj : cylinderCoverProjection (η.symm y) = y := by
    rw [← hη, η.right_inv hyη]
  have hoff : cylinderCoverProjection (η.symm y) ∉ ⋃ j, (L.pathDrawing j).U := by
    rw [hproj]
    exact hyL
  rw [hsheet]
  exact hyB.trans ⟨fun hh => ⟨hh, mem_univ _, hoff⟩, fun hh => hh.1⟩

end GraphMinor.GM06
