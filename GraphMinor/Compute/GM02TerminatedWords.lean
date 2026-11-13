module

public import GraphMinor.Compute.GM02TerminatedInput
import GraphMinor.Compute.MultiDigraph

/-!
# Word bounds for plain terminated inputs

The vertex count bounds every endpoint word. The complete encoding
length bounds its graph-edge count and terminal index. These two size
checks therefore ensure that every supplied word fits the chosen machine
word size, including the two header words preceding the endpoint slice.
-/

public section
namespace GraphMinor.Compute

/-- Vertex-count and encoding-length bounds suffice for every input word. -/
theorem GM02SimpleTerminatedInput.enc_all_lt {w : ℕ} (x : GM02SimpleTerminatedInput)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) : ∀ v ∈ x.enc, v < 2 ^ w := by
  have hl := x.enc_length
  intro v hv
  simp only [GM02SimpleTerminatedInput.enc, encGraph, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with (((rfl | rfl) | hv) | rfl) | hv
  · exact hn
  · omega
  · exact all_lt_flatEdges (edgeListOf x.G) hn v hv
  · omega
  · exact all_lt_flatEdges (edgeListOf x.A.pairGraph) hn v hv

end GraphMinor.Compute
