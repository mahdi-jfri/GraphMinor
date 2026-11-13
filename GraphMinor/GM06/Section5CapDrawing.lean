module

public import GraphMinor.GM06.Section4
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM07.Matched
import GraphMinor.GM06.Section5SphereRegions
import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM11.PerimeterPull

/-!
# Viewing the cylinder drawing in a sphere

For the region-boundary argument in VI (5.1), page 129, map the
cylinder to its round planar annulus and include the plane in its
one-point compactification. This is a closed embedding. The image
of any drawing has exactly the image vertices and edges. A connected
point set gives open-disc regions in the sphere, so its boundary can
be read as a graph walk.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- The round annulus embedding of the cylinder in the sphere. -/
@[expose] noncomputable def cylinderToSphere (p : ClosedCylinder) : OnePoint EuclideanPlane :=
  (cylToPlane p : OnePoint EuclideanPlane)

/-- The annulus embedding in the sphere is continuous. -/
theorem continuous_cylinderToSphere : Continuous cylinderToSphere :=
  OnePoint.isOpenEmbedding_coe.continuous.comp continuous_cylToPlane

/-- The annulus embedding in the sphere is injective. -/
theorem injective_cylinderToSphere : Function.Injective cylinderToSphere :=
  OnePoint.coe_injective.comp injective_cylToPlane

/-- Compactness makes the annulus embedding a closed embedding. -/
theorem isClosedEmbedding_cylinderToSphere : IsClosedEmbedding cylinderToSphere :=
  continuous_cylinderToSphere.isClosedEmbedding injective_cylinderToSphere

/-- The image of a cylinder drawing in the sphere used for its region walks. -/
noncomputable def cylinderSphereDrawing (G : Drawing ClosedCylinder) : Drawing (OnePoint EuclideanPlane) :=
  GM07.embedDrawing isClosedEmbedding_cylinderToSphere G

/-- The point set of the image drawing is the image of its point set. -/
theorem cylinderSphereDrawing_U (G : Drawing ClosedCylinder) :
    (cylinderSphereDrawing G).U = cylinderToSphere '' G.U := by
  rw [cylinderSphereDrawing, GM07.embedDrawing_U]

/-- The vertices of the image drawing are the images of its vertices. -/
theorem cylinderSphereDrawing_V (G : Drawing ClosedCylinder) :
    (cylinderSphereDrawing G).V = cylinderToSphere '' G.V := by
  rw [cylinderSphereDrawing, GM07.embedDrawing_V]

/-- The edges of the image drawing are the images of its edges. -/
theorem cylinderSphereDrawing_E (G : Drawing ClosedCylinder) :
    (cylinderSphereDrawing G).E = (image cylinderToSphere) '' G.E := by
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  rw [cylinderSphereDrawing, GM07.embedDrawing_E]

/-- The sphere image matches the original drawing, with no vertex
removed, so graph walks can be carried in both directions. -/
theorem cylinderSphereDrawing_isMatched (G : Drawing ClosedCylinder) :
    GM07.IsMatched G (cylinderSphereDrawing G) cylinderToSphere ∅ := by
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  rw [cylinderSphereDrawing]
  exact GM07.embedDrawing_isMatched isClosedEmbedding_cylinderToSphere G

/-- A cylinder drawing with a connected point set has open-disc regions
when viewed in the sphere. -/
theorem cylinderSphereDrawing_isTwoCell
    {G : Drawing ClosedCylinder} (hconn : IsConnected G.U) : (cylinderSphereDrawing G).IsTwoCell := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  apply isTwoCell_of_connected_drawing_in_sphere hS.1 hsph
  rw [cylinderSphereDrawing_U]
  exact hconn.image cylinderToSphere continuous_cylinderToSphere.continuousOn

end GraphMinor.GM06
