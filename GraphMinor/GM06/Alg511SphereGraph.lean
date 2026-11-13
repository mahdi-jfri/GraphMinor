module

public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM06.Section5CapDrawing
public import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

/-!
# The same finite graph labels in the cylinder's sphere image

For the drawing input of VI (5.11), page 134, use the existing round
annulus embedding to interpret vertex rotations on the sphere.
The vertex and edge labels are unchanged. The closed embedding
preserves the exact endpoint pair of every edge, including loops.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

private theorem sphere_isLink {G : Drawing ClosedCylinder}
    {e : Set ClosedCylinder} {a b : ClosedCylinder} (he : G.toGraph.IsLink e a b) :
    (cylinderSphereDrawing G).toGraph.IsLink
      (cylinderToSphere '' e) (cylinderToSphere a) (cylinderToSphere b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cylinderSphereDrawing_E]
    exact ⟨e, he.1, rfl⟩
  · rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ he.2.1
  · rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ he.2.2.1
  · rw [isClosedEmbedding_cylinderToSphere.closure_image_eq, cylinderSphereDrawing_V,
      ← Set.image_inter injective_cylinderToSphere, he.2.2.2]
    simp

/-- The original finite graph labels also represent the actual
sphere image of the cylinder drawing, with the same endpoint array. -/
noncomputable def alg511SphereGraphRep {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) :
    GM06SuccessorGraphRep x (cylinderSphereDrawing G).toGraph where
  vertex := rep.vertex.trans
    ((Equiv.Set.image cylinderToSphere G.V injective_cylinderToSphere).trans
      (Set.equivOfEq (cylinderSphereDrawing_V G).symm))
  pairs := rep.pairs
  endpoints := rep.endpoints
  edge := rep.edge.trans
    ((Equiv.Set.image (fun e : Set ClosedCylinder => cylinderToSphere '' e) G.E
      (Set.image_injective.mpr injective_cylinderToSphere)).trans
        (Set.equivOfEq (cylinderSphereDrawing_E G).symm))
  link i := by
    change (cylinderSphereDrawing G).toGraph.IsLink (cylinderToSphere '' (rep.edge i).val)
      (cylinderToSphere (rep.vertex rep.pairs[i.val].1).val)
      (cylinderToSphere (rep.vertex rep.pairs[i.val].2).val)
    exact sphere_isLink (rep.link i)

end GraphMinor.GM06
