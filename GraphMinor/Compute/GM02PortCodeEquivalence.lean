module

public import GraphMinor.Compute.GM02PortAssignmentExtend
public import GraphMinor.GM02.PortTermination
import GraphMinor.GM02.PortSplitEquivalence

/-!
# The finite code form of the corrected split reduction

Every active split choice extends to the supplied pattern slots and
therefore has an integer code in the fixed polynomial range. Conversely,
a valid decoded assignment gives an actual split choice. Combining this
with the proved split equivalence makes the finite code search exactly
the topological-containment test after branch-loop removal.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- After branch-loop removal, a polynomial code search covers exactly all feasible corrected split
choices. -/
theorem gm02TopologicallyContains_iff_codePortFeasible (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hNoLoop : ∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph gflags).IsLoopAt e v) :
    TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) ↔
      ∃ code < (x.G.edges.length + 1) ^ (2 * K),
        ∃ hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
          let choice := gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid
          (portTermination (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) choice).Feasible
            (portGraph (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) choice) := by
  have hV : V(gm02ActiveGraph x.G.graph gflags).Finite := x.G.finite_vertices
  have hVH : V(gm02ActiveGraph x.H hflags) ⊆ V(gm02ActiveGraph x.G.graph gflags) := x.pattern_vertices_subset
  constructor
  · intro hTopo
    obtain ⟨choice, hChoice⟩ := exists_portFeasible_of_topologicallyContains
      (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) edge
      (gm02ActivePatternEnds x hflags edge) (gm02ActivePatternEnds_isLink x hflags edge) hNoLoop hTopo
    let assignment := gm02PortAssignmentOfChoice x gflags hflags edge choice
    have hvalid : gm02PortAssignmentValid x gflags hflags assignment :=
      gm02PortAssignmentOfChoice_valid x gflags hflags edge choice
    obtain ⟨code, hcode, hEq⟩ := exists_gm02PortAssignmentCode x K hK assignment
    have hvalidCode : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code) := hEq.symm ▸ hvalid
    refine ⟨code, hcode, hvalidCode, ?_⟩
    have hChoiceEq : gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalidCode = choice := by
      have hc := gm02PortChoiceOfAssignment_ofChoice x gflags hflags edge choice
      simpa only [hEq] using hc
    exact hChoiceEq.symm ▸ hChoice
  · rintro ⟨code, hcode, hvalid, hfeas⟩
    exact topologicallyContains_of_portFeasible (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
      hV hVH edge (gm02ActivePatternEnds x hflags edge) (gm02ActivePatternEnds_isLink x hflags edge)
      (gm02PortChoiceOfAssignment x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid) hfeas

end GraphMinor.Compute
