module

public import GraphMinor.Compute.GM02ActiveEdges
public import GraphMinor.Compute.GM02TopologicalInputFacts

/-!
# Finding a matching active pattern loop

Search the supplied pattern edge positions in order. A position matches
when its active flag is one and both supplied endpoints equal the chosen
branch vertex. The test is equivalent to an actual loop in the current
pattern subgraph. Failure of the finite search means there is no such
loop, as needed to apply II (4.2) rather than (4.3).
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- The explicit endpoint-and-flag test for a matching pattern loop. -/
def gm02PatternLoopTest (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ)
    (f : Fin x.edges.length) : Bool :=
  decide (flags[f.val]? = some 1 ∧ (x.ends f).1 = v ∧ (x.ends f).2 = v)

/-- Search the supplied edge positions for the first active loop at the branch vertex. -/
def gm02FindPatternLoop (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ) :
    Option (Fin x.edges.length) := (List.finRange x.edges.length).find? (gm02PatternLoopTest x flags v)

/-- The machine's endpoint-and-flag test means precisely an actual active pattern loop. -/
theorem gm02PatternLoopTest_iff (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ)
    (f : Fin x.edges.length) :
    gm02PatternLoopTest x flags v f = true ↔ (gm02ActiveGraph x.H flags).IsLoopAt f.val v := by
  rw [gm02PatternLoopTest, decide_eq_true_eq]
  constructor
  · rintro ⟨hf, h₁, h₂⟩
    refine ⟨hf, ?_⟩
    exact (x.ends_isLink f).isLink_iff.2 (Or.inl ⟨h₁, h₂⟩)
  · rintro ⟨hf, hl⟩
    rcases (x.ends_isLink f).isLink_iff.1 hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨hf, h₁, h₂⟩
    · exact ⟨hf, h₁, h₂⟩

/-- A returned position is a genuine active loop at the requested branch vertex. -/
theorem gm02FindPatternLoop_some (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ)
    (f : Fin x.edges.length) (h : gm02FindPatternLoop x flags v = some f) :
    (gm02ActiveGraph x.H flags).IsLoopAt f.val v :=
  (gm02PatternLoopTest_iff x flags v f).1 (List.find?_some h)

/-- Search failure says that no active pattern edge is a loop at the requested vertex. -/
theorem gm02FindPatternLoop_none_iff (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ) :
    gm02FindPatternLoop x flags v = none ↔ ∀ f, ¬(gm02ActiveGraph x.H flags).IsLoopAt f v := by
  constructor
  · intro h f hf
    have hfH : f ∈ E(x.H) := ((gm02ActiveGraph_le x.H flags).isLink_mono hf).edge_mem
    have hfLen : f < x.edges.length := x.pattern_edges.le hfH
    let i : Fin x.edges.length := ⟨f, hfLen⟩
    have ht : gm02PatternLoopTest x flags v i = true := (gm02PatternLoopTest_iff x flags v i).2 hf
    exact (List.find?_eq_none.1 h i (List.mem_finRange i)) ht
  · intro h
    apply List.find?_eq_none.2
    intro i _ hi
    exact h i.val ((gm02PatternLoopTest_iff x flags v i).1 hi)

end GraphMinor.Compute
