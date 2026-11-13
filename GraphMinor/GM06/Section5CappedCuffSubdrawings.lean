module

public import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM11.PerimeterPull

/-!
# The two cuffs as subdrawings in the capped sphere

For the initial barrier in VI (5.7), page 133, the augmented
drawing contains both cuffs. Each cuff is a circle in the sphere,
so the circle-subdrawing theorem supplies its circuit. These
subdrawings let polar rays retain cuff membership and exclude
the opposite cuff near an initial vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- When a cylinder drawing contains its boundary, both capped
cuffs are point sets of circuit subdrawings. -/
theorem exists_capped_cuff_subdrawings
    (F : Drawing ClosedCylinder) (hbdF : bd ClosedCylinder ⊆ F.U) :
    ∃ C₁ C₂ : Drawing (OnePoint EuclideanPlane),
      C₁.IsSubdrawing (cylinderSphereDrawing F) ∧
      C₂.IsSubdrawing (cylinderSphereDrawing F) ∧
      C₁.U = cylinderToSphere '' cylinderCuff1 ∧
      C₂.U = cylinderToSphere '' cylinderCuff2 ∧ C₁.IsCircuit ∧ C₂.IsCircuit := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  have hcircle {C : Set ClosedCylinder} (hc : IsOArc C) : IsOArc (cylinderToSphere '' C) := by
    obtain ⟨b⟩ := hc
    exact ⟨b.trans (isClosedEmbedding_cylinderToSphere.isEmbedding.homeomorphImage C)⟩
  have hsub {C : Set ClosedCylinder} (hC : C ⊆ bd ClosedCylinder) :
      cylinderToSphere '' C ⊆ (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    exact image_mono (hC.trans hbdF)
  obtain ⟨C₁, hC₁, hC₁F, hC₁U⟩ := exists_circuit_of_oArc (hcircle isOArc_cylinderCuff1)
    (hsub (by rw [bd_closedCylinder]; exact subset_union_left))
  obtain ⟨C₂, hC₂, hC₂F, hC₂U⟩ := exists_circuit_of_oArc (hcircle isOArc_cylinderCuff2)
    (hsub (by rw [bd_closedCylinder]; exact subset_union_right))
  exact ⟨C₁, C₂, hC₁F, hC₂F, hC₁U, hC₂U, hC₁, hC₂⟩

end GraphMinor.GM06
