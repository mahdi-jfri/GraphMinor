module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section5PolarRimCoordinates
public import GraphMinor.GM11.LocalCone
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5ClockwiseLocalPoint
import GraphMinor.GM06.Section5PolarClosedSideRim
import GraphMinor.GM06.Section5CappedBarrierNice

/-!
# A clockwise rim point away from the three barrier directions

For the crossing criterion in VI (5.7), page 133, the closed
local side must have a rim point outside its boundary directions.
First find a cover-strip point off the cuffs in the interior of
the polar chart. It misses the full linkage-and-cuff barrier.
That barrier is nice, so the point moves to the rim without
crossing the local side's frontier or meeting the barrier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A closed local clockwise-side representative has a polar rim
point away from the whole linkage-and-cuff barrier. -/
theorem exists_polar_rim_point_in_clockwise_side_off_barrier
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    {B O : Set (OnePoint EuclideanPlane)} (hB : IsClosed B) (hOo : IsOpen O)
    (hsO : cylinderToSphere (cylinderM1Point k i) ∈ O) (hΦO : range Φ ⊆ O)
    (hmem : ∀ y : ClosedCylinder, cylinderToSphere y ∈ O → y ∈ η.target ∧
      (y ∉ ⋃ j, (L.pathDrawing j).U →
        (cylinderToSphere y ∈ B ↔ η.symm y ∈ cylinderCoverStrip L (i.val : ℤ))))
    (hfr : frontier B ∩ O ⊆ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder)) :
    ∃ w : Circle, polarRimMap Φ w ∈ B ∧
      polarRimMap Φ w ∉ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
  obtain ⟨y, hyΦ, hyB, hybar⟩ := exists_local_clockwise_side_point_off_barrier
    L hG hθ i η hη hsη hOo hsO hmem isOpen_interior hp.nhd
  have hsbar : cylinderToSphere (cylinderM1Point k i) ∈
      cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
    refine ⟨cylinderM1Point k i, Or.inr ?_, rfl⟩
    rw [bd_closedCylinder]
    exact Or.inl rfl
  exact exists_polar_rim_point_of_closed_local_side hp
    (isGammaNice_capped_linkage_and_cuffs L hGF hbdF) hsbar hB hΦO hfr
    (interior_subset hyΦ) hyB hybar

end GraphMinor.GM06
