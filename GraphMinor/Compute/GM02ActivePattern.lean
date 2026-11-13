module

public import GraphMinor.Compute.GM02ActiveEdges
public import GraphMinor.Compute.GM02TopologicalInputFacts

/-!
# Original positions and ends of active pattern edges

Loop removal retains the supplied edge names. An edge of the active
pattern is therefore exactly a supplied position marked one. Its two
ends are still the original supplied endpoint words. These elementary
identities connect the indexed split construction to the active arrays
used by the machine.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- An active pattern edge retains its bounded original supplied position. -/
def gm02ActivePatternIndex (x : GM02TopologicalInput) (flags : List ℕ)
    (e : E(gm02ActiveGraph x.H flags)) : Fin x.edges.length :=
  ⟨e.val, x.pattern_edges.le e.property.1⟩

/-- The original supplied name of an active edge is unchanged. -/
theorem gm02ActivePatternIndex_val (x : GM02TopologicalInput) (flags : List ℕ)
    (e : E(gm02ActiveGraph x.H flags)) : (gm02ActivePatternIndex x flags e).val = e.val := rfl

/-- An active edge's original flag is one. -/
theorem gm02ActivePatternIndex_flag (x : GM02TopologicalInput) (flags : List ℕ)
    (e : E(gm02ActiveGraph x.H flags)) : flags[(gm02ActivePatternIndex x flags e).val]? = some 1 := e.property.2

/-- A supplied position marked one is an actual active pattern edge. -/
def gm02ActivePatternEdge (x : GM02TopologicalInput) (flags : List ℕ) (f : Fin x.edges.length)
    (hf : flags[f.val]? = some 1) : E(gm02ActiveGraph x.H flags) :=
  ⟨f.val, x.pattern_edges.ge f.isLt, hf⟩

/-- Passing to the active edge and back retains the supplied bounded position. -/
theorem gm02ActivePatternIndex_edge (x : GM02TopologicalInput) (flags : List ℕ)
    (f : Fin x.edges.length) (hf : flags[f.val]? = some 1) :
    gm02ActivePatternIndex x flags (gm02ActivePatternEdge x flags f hf) = f := Fin.ext rfl

/-- The active pattern's indexed endpoint pairs come directly from the supplied edge positions. -/
def gm02ActivePatternEnds (x : GM02TopologicalInput) (flags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H flags)) (i : Fin k) : ℕ × ℕ :=
  x.ends (gm02ActivePatternIndex x flags (edge i))

/-- Original supplied endpoints still link each active pattern edge. -/
theorem gm02ActivePatternEnds_isLink (x : GM02TopologicalInput) (flags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H flags)) (i : Fin k) :
    (gm02ActiveGraph x.H flags).IsLink (edge i).val
      (gm02ActivePatternEnds x flags edge i).1 (gm02ActivePatternEnds x flags edge i).2 :=
  ⟨gm02ActivePatternIndex_flag x flags (edge i), x.ends_isLink (gm02ActivePatternIndex x flags (edge i))⟩

/-- The active pattern has no more actual edges than its original supplied list. -/
theorem gm02ActivePattern_ncard_edges_le (x : GM02TopologicalInput) (flags : List ℕ) :
    E(gm02ActiveGraph x.H flags).ncard ≤ x.edges.length := by
  have h := Set.ncard_le_ncard (gm02ActiveGraph_le x.H flags).edgeSet_mono x.pattern_finite_edges
  simpa only [x.ncard_edges] using h

/-- The active pattern edge set is finite even when every supplied edge was removed. -/
theorem gm02ActivePattern_finite_edges (x : GM02TopologicalInput) (flags : List ℕ) :
    E(gm02ActiveGraph x.H flags).Finite := x.pattern_finite_edges.subset (gm02ActiveGraph_le x.H flags).edgeSet_mono

end GraphMinor.Compute
