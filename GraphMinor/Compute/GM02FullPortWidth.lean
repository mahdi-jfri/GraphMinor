module

public import GraphMinor.Compute.GM02RetainedPortShadow
public import GraphMinor.GM02.TreeDecomposition
import GraphMinor.GM02.PortWidth
import GraphMinor.GM02.TreeWidthEmbedding

/-!
# The width bound for the numeric split graph

The retained simple graph is the actual-vertex shadow of the abstract
port graph. Transfer its corrected width estimate through the numeric
embedding and add the unused isolated positions. The number of active
pattern edges is at most the supplied count, hence at most the fixed
bound `K` used by the machine.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The numeric split graph has width at most `max w 2 + 2K` whenever the active host has width at most `w`. -/
theorem gm02FullPortGraph_treeWidthLE (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K w : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (hW : TreeWidthLE (gm02ActiveGraph x.G.graph gflags) w) :
    TreeWidthLE (Graph.ofSimpleGraph (gm02FullPortGraph x gflags hflags code K)) (max w 2 + 2 * K) := by
  have hkcard : k = E(gm02ActiveGraph x.H hflags).ncard := by
    simpa only [Nat.card_fin] using (Nat.card_congr edge).trans (Nat.card_coe_set_eq _)
  have hk : k ≤ K := hkcard ▸ (gm02ActivePattern_ncard_edges_le x hflags).trans hK
  have hV : V(gm02ActiveGraph x.G.graph gflags).Finite := x.G.finite_vertices
  have hE : E(gm02ActiveGraph x.G.graph gflags).Finite :=
    x.G.finite_edges.subset (gm02ActiveGraph_le x.G.graph gflags).edgeSet_mono
  have hport := portGraph_treeWidthLE (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
    (gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid) hV hE hW
  have hsource : TreeWidthLE (Graph.ofSimpleGraph
      (gm02RetainedPortSimpleGraph x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid))
      (max w 2 + 2 * k) := by
    rw [gm02RetainedPortSimpleGraph_eq_shadow]
    exact (treeWidthLE_onVertices_iff _ _).2 hport
  have hnumeric := treeWidthLE_mapEmbedding
    (gm02RetainedPortSimpleGraph x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)
    (gm02PortPositionEmbedding x gflags hflags edge hK) (max w 2 + 2 * k) hsource
  rw [← gm02FullPortGraph_eq_map x gflags hflags code K hK edge hvalid] at hnumeric
  obtain ⟨ι, hι, T, B, hD, hwidth⟩ := hnumeric
  exact ⟨ι, hι, T, B, hD, fun i => (hwidth i).trans (by omega)⟩

end GraphMinor.Compute
