module

public import GraphMinor.GM06.Section5CapDrawing
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# A small inverse angular chart at an initial vertex

For the side test in VI (5.7), page 133, the selected inverse
cover chart can be made narrower than one initial-vertex spacing.
Restrict its target to the inverse image of an angular band.
The cylinder embedding induces its topology, so this target is
the cylinder part of an open sphere neighbourhood.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A sphere neighbourhood of an initial vertex can confine the
chosen inverse chart to any positive angular width. -/
theorem exists_sphere_neighbourhood_in_cover_angle_band
    {k : ℕ} (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source) (ε : ℝ) (hε : 0 < ε) :
    ∃ O : Set (OnePoint EuclideanPlane), IsOpen O ∧
      cylinderToSphere (cylinderM1Point k i) ∈ O ∧
      ∀ y : ClosedCylinder, cylinderToSphere y ∈ O → y ∈ η.target ∧
        |(η.symm y).2 - (cylinderInitialLift k i).2| < ε := by
  let V := {p : CylinderCover | |p.2 - (cylinderInitialLift k i).2| < ε}
  have hVo : IsOpen V := isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const
  let W := η.target ∩ η.symm ⁻¹' V
  have hWo : IsOpen W := η.symm.isOpen_inter_preimage hVo
  have hs : η (cylinderInitialLift k i) = cylinderM1Point k i := by rw [hη]; rfl
  have hback : η.symm (cylinderM1Point k i) = cylinderInitialLift k i := by
    rw [← hs, η.left_inv hsη]
  have hsW : cylinderM1Point k i ∈ W := by
    refine ⟨hs ▸ η.map_source hsη, ?_⟩
    change |(η.symm (cylinderM1Point k i)).2 - (cylinderInitialLift k i).2| < ε
    rw [hback, sub_self, abs_zero]
    exact hε
  obtain ⟨O, hOo, hO⟩ := isClosedEmbedding_cylinderToSphere.isEmbedding.isInducing.isOpen_iff.mp hWo
  refine ⟨O, hOo, ?_, ?_⟩
  · change cylinderM1Point k i ∈ cylinderToSphere ⁻¹' O
    rwa [hO]
  · intro y hyO
    have hyW : y ∈ W := hO ▸ hyO
    exact hyW

end GraphMinor.GM06
