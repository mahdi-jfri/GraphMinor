module

public import GraphMinor.Compute.GM02CanonicalTerminalList
public import GraphMinor.Compute.GM02TerminatedInput
import GraphMinor.Compute.GM02TerminalPrefix

/-!
# The plain terminated input for a valid numeric split candidate

Package the constructed numeric simple graph and its renamed terminal
pairs as the input of II (3.2). Its ordinary encoding is exactly the
graph array followed by the active terminal suffix built by the machine.
This identifies the actual bytes passed to the recursive path program.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The numeric terminated graph associated with one valid candidate assignment. -/
@[expose] noncomputable def gm02NumericTerminatedInput (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) : GM02SimpleTerminatedInput where
  n := gm02FullPortSize x K
  G := gm02FullPortGraph x gflags hflags code K
  A := gm02FullPortTermination x gflags hflags code K hK edge hvalid

/-- The typed terminated input has one pair per active pattern edge. -/
theorem gm02NumericTerminatedInput_index (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).A.index = k :=
  gm02FullPortTermination_index x gflags hflags code K hK edge hvalid

/-- Its plain encoding is exactly the separately constructed graph prefix and terminal suffix. -/
theorem gm02NumericTerminatedInput_enc (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).enc =
      encGraph (gm02FullPortGraph x gflags hflags code K) ++
        [(gm02ActiveTerminalList x hflags K hK).length] ++ flatEdges (gm02ActiveTerminalList x hflags K hK) := by
  have hpairs := gm02ActiveTerminalList_eq_edgeListOf x gflags hflags code K hK edge hvalid
  have hlen := gm02Termination_pairList_length (gm02FullPortTermination x gflags hflags code K hK edge hvalid)
  rw [← hpairs] at hlen
  change encGraph (gm02FullPortGraph x gflags hflags code K) ++
    [(gm02FullPortTermination x gflags hflags code K hK edge hvalid).index] ++
      flatEdges (edgeListOf (gm02FullPortTermination x gflags hflags code K hK edge hvalid).pairGraph) = _
  rw [← hpairs, ← hlen]

/-- The terminal suffix count is bounded by the supplied pattern edge count. -/
theorem gm02ActiveTerminalList_length_le (x : GM02TopologicalInput) (hflags : List ℕ)
    (K : ℕ) (hK : x.edges.length ≤ K) : (gm02ActiveTerminalList x hflags K hK).length ≤ x.edges.length := by
  simpa only [gm02TerminalPrefix_full] using gm02TerminalPrefix_length_le x hflags K hK x.edges.length

/-- The constructed plain input length is bounded by all numeric pairs and the supplied pattern edge count. -/
theorem gm02NumericTerminatedInput_enc_length_le (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).enc.length ≤
      3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length := by
  have hm : (edgeListOf (gm02FullPortGraph x gflags hflags code K)).length ≤
      gm02FullPortSize x K * gm02FullPortSize x K := by
    simpa only [gm02EdgePrefix_full] using gm02EdgePrefix_length_le
      (gm02FullPortGraph x gflags hflags code K) (gm02FullPortSize x K * gm02FullPortSize x K)
  have hr := gm02ActiveTerminalList_length_le x hflags K hK
  rw [gm02NumericTerminatedInput_enc]
  simp only [List.length_append, List.length_cons, List.length_nil, length_encGraph, length_flatEdges]
  omega

end GraphMinor.Compute
