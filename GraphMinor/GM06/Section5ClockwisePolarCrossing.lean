module

public import GraphMinor.GM06.Section5ClockwisePolarRay
public import GraphMinor.GM06.Section5PolarRimCoordinates
public import GraphMinor.GM06.Section2Dual
import GraphMinor.GM06.Section5ClockwiseRim
import GraphMinor.GM06.Section5ClockwiseRimInteriorPoint
import GraphMinor.GM06.Section5RimSideCrossing

/-!
# Reading clockwise edge incidence as a rim crossing test

For VI (5.7), page 133, the local barrier has three distinct
rim directions: two cuff ends and the linkage end. The closed
clockwise side misses the counterclockwise cuff end. Its local
frontier is therefore contained in the other two directions.
It also has a rim point off the barrier. The closed-circle side
criterion now turns membership into a four-point crossing test.
The earlier radial access criterion applies this to both ends of
an edge, including loops.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- In a three-direction initial chart, clockwise incidence is the
crossing test against the counterclockwise cuff direction. -/
theorem clockwise_edge_iff_polar_crossing_of_local_side
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
    (hfr : frontier B ∩ O ⊆ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder))
    (p q c : Circle) (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c)
    (hbar : ∀ w : Circle, polarRimMap Φ w ∈
      cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) ↔ w = p ∨ w = q ∨ w = c)
    (hcB : polarRimMap Φ c ∉ B)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (hoff : Disjoint e (⋃ j, (L.pathDrawing j).U)) :
    IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
      polarRimMap Φ w ∈ cylinderToSphere '' e ∧ CrossesOn (univ : Set Circle) p q w c := by
  let K := (polarRimMap Φ) ⁻¹' B
  have hKc : IsClosed K := hB.preimage (polarRimMap Φ).continuous
  have hKfr : frontier K ⊆ {p, q} := by
    intro w hw
    have hwfr := (polarRimMap Φ).continuous.frontier_preimage_subset B hw
    have hwbar := hfr ⟨hwfr, hΦO (mem_range_self (polarDiscPoint 1 w))⟩
    rcases (hbar w).mp hwbar with hwp | hwq | hwc
    · exact mem_insert_iff.mpr (Or.inl hwp)
    · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr hwq))
    · have hwB : polarRimMap Φ w ∈ B := hB.closure_eq ▸ frontier_subset_closure hwfr
      exact False.elim (hcB (hwc ▸ hwB))
  obtain ⟨a, haB, haOff⟩ := exists_polar_rim_point_in_clockwise_side_off_barrier
    L hG hGF hbdF hθ i η hη hsη hp hB hOo hsO hΦO hmem hfr
  have hKne : (K \ {p, q}).Nonempty := by
    refine ⟨a, haB, ?_⟩
    intro hh
    rcases mem_insert_iff.mp hh with hap | haq
    · exact haOff ((hbar a).mpr (Or.inl hap))
    · exact haOff ((hbar a).mpr (Or.inr (Or.inl (mem_singleton_iff.mp haq))))
  have hcross (w : Circle) (hwOff : polarRimMap Φ w ∉
      cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder)) :
      polarRimMap Φ w ∈ B ↔ CrossesOn (univ : Set Circle) p q w c := by
    have hwp : w ≠ p := fun hh => hwOff ((hbar w).mpr (Or.inl hh))
    have hwq : w ≠ q := fun hh => hwOff ((hbar w).mpr (Or.inr (Or.inl hh)))
    have hwc : w ≠ c := fun hh => hwOff ((hbar w).mpr (Or.inr (Or.inr hh)))
    exact mem_closed_circle_side_iff_crossesOn hKc hpq hKfr hKne hcB
      hpc.symm hqc.symm hwp hwq hwc
  have heOff (w : Circle) (y : ClosedCylinder) (hw : polarRimMap Φ w = cylinderToSphere y)
      (hy : y ∈ e) : polarRimMap Φ w ∉
        cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
    rintro ⟨z, hz, hzw⟩
    have hzy : z = y := injective_cylinderToSphere (hzw.trans hw)
    rw [hzy] at hz
    rcases hz with hzL | hzbd
    · exact disjoint_left.mp hoff hy hzL
    · exact (he.2.1 hy).2 (hG.2.1 ⟨hzbd, (he.2.1 hy).1⟩)
  have hsmall (y : ClosedCylinder) (hyΦ : cylinderToSphere y ∈ range Φ) : y ∈ η.target :=
    (hmem y (hΦO hyΦ)).1
  have hCW := isClockwiseInitialEdge_iff_polar_rim_direction L i hGF he hp η hη hsη hsmall hoff
  constructor
  · intro h
    obtain ⟨w, y, hw, hy, hside⟩ := hCW.mp h
    have hyΦ : cylinderToSphere y ∈ range Φ := hw ▸ mem_range_self (polarDiscPoint 1 w)
    have hyOff : y ∉ ⋃ j, (L.pathDrawing j).U := fun hh => disjoint_left.mp hoff hy hh
    have hyB : cylinderToSphere y ∈ B := ((hmem y (hΦO hyΦ)).2 hyOff).mpr hside
    have hwB : polarRimMap Φ w ∈ B := hw.symm ▸ hyB
    exact ⟨w, ⟨y, hy, hw.symm⟩, (hcross w (heOff w y hw hy)).mp hwB⟩
  · rintro ⟨w, ⟨y, hy, hyw⟩, hwcross⟩
    have hw : polarRimMap Φ w = cylinderToSphere y := hyw.symm
    have hyΦ : cylinderToSphere y ∈ range Φ := hw ▸ mem_range_self (polarDiscPoint 1 w)
    have hyOff : y ∉ ⋃ j, (L.pathDrawing j).U := fun hh => disjoint_left.mp hoff hy hh
    have hwB := (hcross w (heOff w y hw hy)).mpr hwcross
    have hyB : cylinderToSphere y ∈ B := by rw [hyw]; exact hwB
    exact hCW.mpr ⟨w, y, hw, hy, ((hmem y (hΦO hyΦ)).2 hyOff).mp hyB⟩

end GraphMinor.GM06
