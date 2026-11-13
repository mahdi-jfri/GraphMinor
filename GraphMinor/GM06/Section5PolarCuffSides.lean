module

public import GraphMinor.GM06.Section5PolarCuffLift
import GraphMinor.GM06.Section5CoverCuffInterval

/-!
# The signed cuff directions select the correct lifted side

For VI (5.7), page 133, a positive angular cuff arc leaves the
initial lift beyond the right endpoint of the preceding strip,
so it is outside. A negative angular arc leaves to its left.
When the inverse chart is narrower than one initial-vertex spacing,
that point lies in the preceding strip. This uses the explicit
initial-cuff interval and works for a one-path linkage.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A positive-angle cuff direction lies outside the preceding
lifted strip, with no restriction on the number of paths. -/
theorem polar_positive_cuff_direction_not_mem_preceding_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (i : Fin k) {Γ : Drawing (OnePoint EuclideanPlane)}
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ (cylinderToSphere (cylinderM1Point k i)) Φ)
    (g : I → ClosedCylinder) (hg : IsArcMap g) (hg0 : g 0 = cylinderM1Point k i)
    (δ : ℝ) (hδ : 0 < δ)
    (hgAngle : ∀ t : I, g t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + δ * (t : ℝ)))
    (w : Circle) (hw : range (polarRayMap Φ w) ⊆ range (cylinderToSphere ∘ g))
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    (hsmall : ∀ y : ClosedCylinder, cylinderToSphere y ∈ range Φ → y ∈ η.target) :
    ∃ y : ClosedCylinder, polarRimMap Φ w = cylinderToSphere y ∧
      η.symm y ∉ cylinderCoverStrip L (i.val : ℤ) := by
  obtain ⟨r, hr, hwr, hangle⟩ := exists_positive_parameter_of_polar_cuff_direction i hp
    g hg hg0 δ hgAngle w hw η hη hsη hsmall
  refine ⟨g r, hwr, ?_⟩
  intro hin
  have hrad : (η.symm (g r)).1.1 = 1 := by rw [hangle]
  have hbound := ((mem_cover_strip_on_initial_cuff_iff L hG hθ (i.val : ℤ)
    (η.symm (g r)) hrad).mp hin).2
  have hright : 2 * (((i.val : ℤ) + 1 : ℤ) : ℝ) * π / k = (cylinderInitialLift k i).2 := by
    simp only [cylinderInitialLift, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
      Nat.cast_one]
  rw [hright, hangle] at hbound
  have hpos : 0 < δ * (r : ℝ) := mul_pos hδ hr
  change (cylinderInitialLift k i).2 + δ * (r : ℝ) < (cylinderInitialLift k i).2 at hbound
  linarith only [hpos, hbound]

/-- A negative-angle cuff direction lies in the preceding strip
when its inverse chart stays within one initial-vertex spacing. -/
theorem polar_negative_cuff_direction_mem_preceding_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (i : Fin k) {Γ : Drawing (OnePoint EuclideanPlane)}
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ (cylinderToSphere (cylinderM1Point k i)) Φ)
    (g : I → ClosedCylinder) (hg : IsArcMap g) (hg0 : g 0 = cylinderM1Point k i)
    (δ : ℝ) (hδ : δ < 0)
    (hgAngle : ∀ t : I, g t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + δ * (t : ℝ)))
    (w : Circle) (hw : range (polarRayMap Φ w) ⊆ range (cylinderToSphere ∘ g))
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    (hsmall : ∀ y : ClosedCylinder, cylinderToSphere y ∈ range Φ → y ∈ η.target)
    (hnarrow : ∀ y : ClosedCylinder, cylinderToSphere y ∈ range Φ →
      (cylinderInitialLift k i).2 - 2 * π / k < (η.symm y).2) :
    ∃ y : ClosedCylinder, polarRimMap Φ w = cylinderToSphere y ∧
      η.symm y ∈ cylinderCoverStrip L (i.val : ℤ) := by
  obtain ⟨r, hr, hwr, hangle⟩ := exists_positive_parameter_of_polar_cuff_direction i hp
    g hg hg0 δ hgAngle w hw η hη hsη hsmall
  refine ⟨g r, hwr, ?_⟩
  have hrad : (η.symm (g r)).1.1 = 1 := by rw [hangle]
  apply (mem_cover_strip_on_initial_cuff_iff L hG hθ (i.val : ℤ) (η.symm (g r)) hrad).mpr
  have hlow := hnarrow (g r) (hwr ▸ mem_range_self (polarDiscPoint 1 w))
  have hleft : 2 * ((i.val : ℤ) : ℝ) * π / k = (cylinderInitialLift k i).2 - 2 * π / k := by
    simp only [cylinderInitialLift, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    ring
  have hright : 2 * (((i.val : ℤ) + 1 : ℤ) : ℝ) * π / k = (cylinderInitialLift k i).2 := by
    simp only [cylinderInitialLift, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
      Nat.cast_one]
  refine ⟨hleft ▸ hlow, ?_⟩
  rw [hright, hangle]
  have hneg : δ * (r : ℝ) < 0 := mul_neg_of_neg_of_pos hδ hr
  change (cylinderInitialLift k i).2 + δ * (r : ℝ) < (cylinderInitialLift k i).2
  linarith only [hneg]

end GraphMinor.GM06
