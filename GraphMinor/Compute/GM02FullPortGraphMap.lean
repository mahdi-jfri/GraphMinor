module

public import GraphMinor.Compute.GM02PortPositionEmbedding
public import GraphMinor.Compute.GM02PortAssignment
public import Mathlib.Combinatorics.SimpleGraph.Maps
import GraphMinor.Compute.GM02PortPositionAdjacency
import GraphMinor.Compute.GM02FullPortEdgeRange

/-!
# The numeric split graph is the embedded abstract split graph

Restrict the abstract port adjacency to its retained vertices and push
it forward by the numeric embedding. Adjacency on the image agrees by
the vertex-type comparison. Every numeric edge has both endpoints in
the image, so the remaining numeric positions contribute only isolates.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The abstract split simple graph on precisely its retained vertex subtype. -/
@[expose] def gm02RetainedPortSimpleGraph (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) {k : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (assignment : GM02PortAssignment x) (hvalid : gm02PortAssignmentValid x gflags hflags assignment) :
    SimpleGraph (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) :=
  (portSimpleGraph (gm02ActiveGraph x.G.graph gflags)
    (fun p => ((gm02PortChoiceOfAssignment x gflags hflags edge assignment hvalid).edge p).val)).induce
      (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k)

/-- The numeric construction adds only isolated positions to the embedded abstract split graph. -/
theorem gm02FullPortGraph_eq_map (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    gm02FullPortGraph x gflags hflags code K =
      (gm02RetainedPortSimpleGraph x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid).map
        (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · intro h
    obtain ⟨hu, hv⟩ := gm02FullPortGraph_adj_mem_range x gflags hflags code edge hK h
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    exact ⟨a, b, (gm02PortPositionEmbedding_adj_iff x gflags hflags code K hK edge hvalid a b).1 h,
      rfl, rfl⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact (gm02PortPositionEmbedding_adj_iff x gflags hflags code K hK edge hvalid a b).2 hab

end GraphMinor.Compute
