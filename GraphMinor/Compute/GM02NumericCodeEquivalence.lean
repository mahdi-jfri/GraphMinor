module

public import GraphMinor.Compute.GM02FullPortFeasibility
public import GraphMinor.GM02.TopologicalContainment
import GraphMinor.Compute.GM02PortCodeEquivalence

/-!
# The finite code test on numeric terminated graphs

Combine the complete incident-choice code enumeration with the numeric
feasibility transfer. After branch loops are removed, containment holds
exactly when a valid code in the fixed polynomial range gives a feasible
numeric terminated graph. This is the correctness criterion for the
actual graph-builder and code-scan commands in II (4.6), page 319.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The numeric terminated-graph tests cover exactly the topological containment question. -/
theorem gm02TopologicallyContains_iff_numericCodeFeasible (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hNoLoop : ∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph gflags).IsLoopAt e v) :
    TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) ↔
      ∃ code < (x.G.edges.length + 1) ^ (2 * K),
        ∃ hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
          (gm02FullPortTermination x gflags hflags code K hK edge hvalid).Feasible
            (Graph.ofSimpleGraph (gm02FullPortGraph x gflags hflags code K)) := by
  rw [gm02TopologicallyContains_iff_codePortFeasible x gflags hflags K hK edge hNoLoop]
  constructor
  · rintro ⟨code, hcode, hvalid, hfeas⟩
    exact ⟨code, hcode, hvalid,
      (gm02FullPortTermination_feasible_iff x gflags hflags code K hK edge hvalid).2 hfeas⟩
  · rintro ⟨code, hcode, hvalid, hfeas⟩
    exact ⟨code, hcode, hvalid,
      (gm02FullPortTermination_feasible_iff x gflags hflags code K hK edge hvalid).1 hfeas⟩

end GraphMinor.Compute
