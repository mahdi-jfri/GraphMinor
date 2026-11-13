module

public import GraphMinor.Compute.GM02PatternLoopSearch
import GraphMinor.GM02.Section4Loops

/-!
# Correctness of one matched loop deletion

For a host loop at a pattern vertex, search the actual active pattern
edges. If a matching loop exists, clear both flags and apply II (4.3).
If none exists, clear only the host flag and apply II (4.2). The active
array deletion theorem identifies both updates with the actual graph
deletions appearing in those lemmas.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Clear the matching active pattern loop if the finite search finds one. -/
def gm02MatchedPatternFlags (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ) : List ℕ :=
  match gm02FindPatternLoop x flags v with
  | none => flags
  | some f => flags.set f.val 0

/-- One host-loop update and its matching pattern-loop update preserve exactly the topological test. -/
theorem gm02MatchedLoopDeletion_correct (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (e v : ℕ) (he : e < gflags.length) (hHlen : hflags.length = x.edges.length)
    (hv : v ∈ V(x.H)) (hloop : (gm02ActiveGraph x.G.graph gflags).IsLoopAt e v) :
    TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) ↔
      TopologicallyContains (gm02ActiveGraph x.G.graph (gflags.set e 0))
        (gm02ActiveGraph x.H (gm02MatchedPatternFlags x hflags v)) := by
  have hVH : V(gm02ActiveGraph x.H hflags) ⊆ V(gm02ActiveGraph x.G.graph gflags) :=
    x.pattern_vertices_subset
  cases hfind : gm02FindPatternLoop x hflags v with
  | none =>
    simp only [gm02MatchedPatternFlags, hfind]
    rw [gm02ActiveGraph_set_zero x.G.graph gflags e he]
    exact GraphMinor.GM02.theorem_4_2_proof hVH hloop hv ((gm02FindPatternLoop_none_iff x hflags v).1 hfind)
  | some f =>
    have hf : f.val < hflags.length := by rw [hHlen]; exact f.isLt
    simp only [gm02MatchedPatternFlags, hfind]
    rw [gm02ActiveGraph_set_zero x.G.graph gflags e he, gm02ActiveGraph_set_zero x.H hflags f.val hf]
    exact GraphMinor.GM02.theorem_4_3_proof hVH hloop (gm02FindPatternLoop_some x hflags v f hfind)

/-- A matching-loop update preserves the length of the pattern's active-edge array. -/
theorem gm02MatchedPatternFlags_length (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ) :
    (gm02MatchedPatternFlags x flags v).length = flags.length := by
  unfold gm02MatchedPatternFlags
  split
  · rfl
  · exact List.length_set

/-- Clearing a matching pattern flag preserves the zero-or-one flag invariant. -/
theorem gm02MatchedPatternFlags_bits (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ)
    (hbits : ∀ b ∈ flags, b ≤ 1) : ∀ b ∈ gm02MatchedPatternFlags x flags v, b ≤ 1 := by
  unfold gm02MatchedPatternFlags
  split
  · exact hbits
  · exact gm02ActiveFlags_set_zero_bits flags _ hbits

end GraphMinor.Compute
