module

public import GraphMinor.Compute.GM02MultiTerminatedInput
import GraphMinor.Compute.GM02TerminatedEncoding
import GraphMinor.Compute.GM02TerminatedWords

/-!
# Reading the original multigraph and termination encoding

The original graph prefix has one triple per active directed pair. Its
length locates the terminal index and endpoint suffix. That suffix is
already the one needed by the underlying-simple-graph instance. Its
words are bounded vertex names and an index, even when the original
edge multiplicities exceed the machine's word range.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The supplied terminal-index word and canonical terminal endpoint list. -/
noncomputable def GM02MultiTerminatedInput.terminalWords (x : GM02MultiTerminatedInput) : List ℕ :=
  [x.A.index] ++ flatEdges (edgeListOf x.simple.A.pairGraph)

/-- The original encoding is its multiplicity prefix followed by the supplied terminal suffix. -/
theorem GM02MultiTerminatedInput.enc_eq (x : GM02MultiTerminatedInput) :
    x.enc = x.G.enc ++ x.terminalWords := by
  simp only [GM02MultiTerminatedInput.enc, GM02MultiTerminatedInput.terminalWords, List.append_assoc]

/-- Replacing only the graph prefix produces exactly the simple instance's plain encoding. -/
theorem GM02MultiTerminatedInput.simple_enc (x : GM02MultiTerminatedInput) :
    x.simple.enc = encGraph x.G.toSimpleGraph ++ x.terminalWords := by
  change (encGraph x.G.toSimpleGraph ++ [x.simple.A.index] ++ flatEdges (edgeListOf x.simple.A.pairGraph)) = _
  rw [x.simple_index]
  simp only [GM02MultiTerminatedInput.terminalWords, List.append_assoc]

/-- The termination suffix uses one header and two words per prescribed pair. -/
theorem GM02MultiTerminatedInput.terminalWords_length (x : GM02MultiTerminatedInput) :
    x.terminalWords.length = 1 + 2 * x.A.index := by
  simp only [GM02MultiTerminatedInput.terminalWords, List.length_append, List.length_singleton,
    length_flatEdges, gm02Termination_pairList_length, x.simple_index]

/-- The original array length depends on active pairs and supplied terminal pairs. -/
theorem GM02MultiTerminatedInput.enc_length (x : GM02MultiTerminatedInput) :
    x.enc.length = 3 + 3 * x.G.numActivePairs + 2 * x.A.index := by
  rw [x.enc_eq, List.length_append, x.G.length_enc, x.terminalWords_length]
  omega

/-- The original encoding is quadratic in vertices regardless of edge multiplicities. -/
theorem GM02MultiTerminatedInput.enc_length_le (x : GM02MultiTerminatedInput) :
    x.enc.length ≤ 3 + 3 * x.n ^ 2 + x.n := by
  have hm := x.G.numActivePairs_le_sq
  have hk := x.simple.support_size_bound
  rw [x.simple_index, x.simple_n] at hk
  rw [x.enc_length]
  simpa only [Nat.pow_two] using (show 3 + 3 * x.G.numActivePairs + 2 * x.A.index ≤
      3 + 3 * (x.n * x.n) + x.n by omega)

/-- The first header word is the original vertex count. -/
theorem GM02MultiTerminatedInput.enc_zero (x : GM02MultiTerminatedInput) : x.enc[0]? = some x.n := by
  simp [GM02MultiTerminatedInput.enc, MultiDigraph.enc]

/-- The second header word is the original active-pair count. -/
theorem GM02MultiTerminatedInput.enc_one (x : GM02MultiTerminatedInput) :
    x.enc[1]? = some x.G.numActivePairs := by
  simp [GM02MultiTerminatedInput.enc, MultiDigraph.enc]

/-- The original graph-prefix length locates the prescribed terminal index. -/
theorem GM02MultiTerminatedInput.enc_index (x : GM02MultiTerminatedInput) :
    x.enc[2 + 3 * x.G.numActivePairs]? = some x.A.index := by
  rw [← x.G.length_enc]
  simp only [GM02MultiTerminatedInput.enc, List.append_assoc,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.cons_append,
    List.nil_append, List.getElem?_cons_zero]

/-- Every terminal suffix word fits whenever the reduced input does. -/
theorem GM02MultiTerminatedInput.terminalWords_all_lt {w : ℕ} (x : GM02MultiTerminatedInput)
    (hn : x.n < 2 ^ w) (hlen : x.simple.enc.length < 2 ^ w) :
    ∀ v ∈ x.terminalWords, v < 2 ^ w := by
  intro v hv
  apply x.simple.enc_all_lt hn hlen v
  rw [x.simple_enc]
  exact List.mem_append_right _ hv

end GraphMinor.Compute
