module

public import GraphMinor.Compute.GM02NumericTerminatedInput
public import GraphMinor.Compute.GM02ConcatArrays
import GraphMinor.Compute.GM02RowMajorPairs

/-!
# Joining the constructed arrays into the plain path-program input

Concatenate the exact numeric graph encoding and canonical terminal
suffix. Their proved encoding identity identifies the result with the
ordinary input of II (3.2). Edge and pair counts bound the allocation and
copying time, and all original arrays and low registers are retained.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Join the graph prefix and terminal suffix into the plain input array 28. -/
@[expose] def gm02JoinPortInputProg : Cmd := gm02ConcatArraysProg 25 27 28

/-- Joining the constructed arrays gives exactly the plain terminated input with a polynomial copying bound. -/
theorem gm02JoinPortInputProg_exec {w K code : ℕ} (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) (s : State)
    (hgraph : s.arrs 25 = encGraph (gm02FullPortGraph x gflags hflags code K))
    (hterm : s.arrs 27 = [(gm02ActiveTerminalList x hflags K hK).length] ++
      flatEdges (gm02ActiveTerminalList x hflags K hK))
    (hw : 1 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hjoin : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02JoinPortInputProg s s' t ∧
      t ≤ 68 + 32 * (gm02FullPortSize x K * gm02FullPortSize x K) + 32 * x.edges.length ∧
      s'.arrs 28 = (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).enc ∧
      (∀ a, a ≠ 28 → s'.arrs a = s.arrs a) ∧ (∀ r < 290, s'.regs r = s.regs r) := by
  let F := gm02FullPortGraph x gflags hflags code K
  let L := gm02ActiveTerminalList x hflags K hK
  let N := gm02FullPortSize x K
  have hm : (edgeListOf F).length ≤ N * N := by
    simpa only [N, F, gm02EdgePrefix_full] using gm02EdgePrefix_length_le F (N * N)
  have hr : L.length ≤ x.edges.length := gm02ActiveTerminalList_length_le x hflags K hK
  have hmw : (edgeListOf F).length < 2 ^ w := by dsimp only [N] at hm; omega
  have hrw : L.length < 2 ^ w := by omega
  have hlen : (encGraph F).length + ([L.length] ++ flatEdges L).length < 2 ^ w := by
    simp only [length_encGraph, List.length_append, List.length_cons, List.length_nil, length_flatEdges]
    dsimp only [N] at hm
    omega
  have hgw : ∀ a ∈ encGraph F, a < 2 ^ w := by
    intro a ha
    simp only [encGraph, List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact hN
    · exact hmw
    · exact all_lt_flatEdges (edgeListOf F) hN a ha
  have htw : ∀ a ∈ [L.length] ++ flatEdges L, a < 2 ^ w := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact (List.mem_singleton.1 ha) ▸ hrw
    · exact all_lt_flatEdges L hN a ha
  obtain ⟨s', t, he, ht, hout, ha, hr⟩ := gm02ConcatArraysProg_exec 25 27 28 (by decide) (by decide)
    (encGraph F) ([L.length] ++ flatEdges L) s hgraph hterm hw hlen hgw htw
  refine ⟨s', t, he, ?_, ?_, ha, hr⟩
  · simp only [length_encGraph, List.length_append, List.length_cons, List.length_nil, length_flatEdges] at ht
    dsimp only [N] at hm
    omega
  · exact hout.trans (by simpa only [List.append_assoc] using
      (gm02NumericTerminatedInput_enc x gflags hflags code K hK edge hvalid).symm)

end GraphMinor.Compute
