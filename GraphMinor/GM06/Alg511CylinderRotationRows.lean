module

public import GraphMinor.GM06.Alg511RotationRows
public import GraphMinor.GM06.Alg511SphereGraph
import GraphMinor.GM11.PerimeterPull

/-!
# Geometric rotation rows for an actual cylinder drawing

Use the same finite vertex and edge labels in the sphere image of
the cylinder, then apply the rotation-row coverage theorem. The
result supplies all original edge directions and their local order
for the input of VI (5.11), page 134. Cuff-marker directions and
region-boundary walks are separate parts of the successor layout.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set unitInterval

/-- The original finite labels of every cylinder drawing have
simultaneous geometric rotation rows in its sphere image. -/
theorem alg511_exists_cylinder_rotation_rows
    (x : GM06SuccessorInput) {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) :
    ∃ (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
      (rows : List (List ℕ)), EdgePar (cylinderSphereDrawing G) γ ∧
      (∀ i : Fin rep.pairs.length,
        γ (cylinderToSphere '' (rep.edge i).val) 0 =
          cylinderToSphere (rep.vertex rep.pairs[i.val].1).val ∧
        γ (cylinderToSphere '' (rep.edge i).val) 1 =
          cylinderToSphere (rep.vertex rep.pairs[i.val].2).val) ∧
      rows.length = x.vertexCount ∧
      ∀ v : Fin x.vertexCount,
        Alg511RotationRowRep x (alg511SphereGraphRep rep) γ v (rows.getD v.val []) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GraphMinor.GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  exact alg511_exists_rotation_rows hS x (alg511SphereGraphRep rep)

end GraphMinor.GM06
