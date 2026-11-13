module

public import GraphMinor.Compute.GM06Alg34VertexBfs
public import GraphMinor.Compute.GM02BalancedSeparationInput

/-!
# Component marks as vertex membership bits

The component search returns reachability marks. The induced-drawing
mask update uses finite-set membership bits. These are the same arrays,
independently of the decision procedures used to evaluate membership.
-/

public section
namespace GraphMinor.Compute

/-- Reachability marks are exactly the membership bits of the source component. -/
theorem gm06VertexReachData_eq_vertexBits (x : GM06DrawingData) (source : Fin x.n) :
    gm06VertexReachData x source = gm02VertexBits (reachSet x.vertexGraph source) := by
  classical
  unfold gm06VertexReachData gm02VertexBits
  congr 1
  funext v
  by_cases hv : x.vertexGraph.Reachable source v
  · have hm := (mem_reachSet x.vertexGraph source v).mpr hv
    simp only [hv, hm, ite_true]
  · have hm : v ∉ reachSet x.vertexGraph source :=
      fun h => hv ((mem_reachSet x.vertexGraph source v).mp h)
    simp only [hv, hm, ite_false]

end GraphMinor.Compute
