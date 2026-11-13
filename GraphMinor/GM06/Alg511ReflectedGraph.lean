module

public import GraphMinor.Compute.GM06Alg511ReflectedInput
public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM06.Section5ReflectionDrawing
public import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

/-!
# Graph incidence for the reflected finite drawing

For VI (5.11), page 134, the finite reflection keeps vertex and edge
labels and changes their geometric interpretation by the actual plane
reflection. Images preserve the endpoint incidence of each edge.
Thus the unchanged endpoint array still represents the reflected
graph, including loops and parallel edges.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

private theorem reflected_isLink {k : ℕ} {G : Drawing ClosedCylinder}
    {e : Set ClosedCylinder} {a b : ClosedCylinder} (he : G.toGraph.IsLink e a b) :
    (section5ReflectedDrawing k G).toGraph.IsLink
      (section5CylinderReflection k '' e)
      (section5CylinderReflection k a) (section5CylinderReflection k b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [section5ReflectedDrawing_E]
    exact ⟨e, he.1, rfl⟩
  · rw [section5ReflectedDrawing_V]
    exact mem_image_of_mem _ he.2.1
  · rw [section5ReflectedDrawing_V]
    exact mem_image_of_mem _ he.2.2.1
  · rw [← (section5CylinderReflection k).image_closure,
      section5ReflectedDrawing_V, ← Set.image_inter (section5CylinderReflection k).injective,
      he.2.2.2]
    simp

/-- The old finite graph labels, interpreted by the reflected actual
vertices and edges, represent the unchanged endpoint array. -/
noncomputable def alg511ReflectedGraphRep {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) :
    GM06SuccessorGraphRep (x.reflected.withLinkage [])
      (section5ReflectedDrawing x.pathCount G).toGraph where
  vertex := rep.vertex.trans
    ((Equiv.Set.image (section5CylinderReflection x.pathCount) G.V
      (section5CylinderReflection x.pathCount).injective).trans
        (Set.equivOfEq (section5ReflectedDrawing_V x.pathCount G).symm))
  pairs := rep.pairs
  endpoints := rep.endpoints
  edge := rep.edge.trans
    ((Equiv.Set.image (fun e : Set ClosedCylinder => section5CylinderReflection x.pathCount '' e)
      G.E (Set.image_injective.mpr (section5CylinderReflection x.pathCount).injective)).trans
        (Set.equivOfEq (section5ReflectedDrawing_E x.pathCount G).symm))
  link i := by
    change (section5ReflectedDrawing x.pathCount G).toGraph.IsLink
      (section5CylinderReflection x.pathCount '' (rep.edge i).val)
      (section5CylinderReflection x.pathCount (rep.vertex rep.pairs[i.val].1).val)
      (section5CylinderReflection x.pathCount (rep.vertex rep.pairs[i.val].2).val)
    exact reflected_isLink (rep.link i)

end GraphMinor.GM06
