module

public import GraphMinor.Compute.Parse
public import GraphMinor.GM02.TerminationGraph
public import GraphMinor.GM02.Feasibility
public import GraphMinor.GM02.TreeDecomposition
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Plain terminated inputs for the alternating simple-graph routines

The internal A1/A2 routines of II, pages 316–317, take a simple graph and
a termination. Encode the graph in the standard edge-list format, then
the index and the terminal pairs in increasing endpoint order. A pair
graph lists those matching pairs without adding any solution data. The
three output flags mean feasible, infeasible, or the width threshold.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 Classical

/-- A numbered simple terminated graph for A1 and A2, Graph Minors II,
pages 310 and 316. The termination fields are precisely its printed
endpoint and disjointness conditions. -/
structure GM02SimpleTerminatedInput where
  /-- Number of input vertices. -/
  n : ℕ
  /-- The input simple graph. -/
  G : SimpleGraph (Fin n)
  /-- Adjacency is finite input data. -/
  [decAdj : DecidableRel G.Adj]
  /-- The prescribed disjoint endpoint pairs. -/
  A : Termination (Set.univ : Set (Fin n))

attribute [instance] GM02SimpleTerminatedInput.decAdj

/-- The matching graph lists exactly the termination pairs. -/
theorem gm02Termination_edgeFinset {n : ℕ} (A : Termination (Set.univ : Set (Fin n)))
    [F : Fintype A.pairGraph.edgeSet] :
    A.pairGraph.edgeFinset = A.pairs := by
  ext p
  rw [SimpleGraph.mem_edgeFinset]
  change p ∈ (SimpleGraph.fromEdgeSet (A.pairs : Set (Sym2 (Fin n)))).edgeSet ↔ p ∈ A.pairs
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨And.left, fun hp => ⟨hp, A.not_diag p hp⟩⟩

/-- The canonical terminal-pair list has exactly the prescribed index. -/
theorem gm02Termination_pairList_length {n : ℕ} (A : Termination (Set.univ : Set (Fin n))) :
    (edgeListOf A.pairGraph).length = A.index := by
  rw [length_edgeListOf_eq_card_edgeFinset]
  exact congrArg Finset.card (gm02Termination_edgeFinset A (F := A.pairGraph.fintypeEdgeSet))

/-- Plain graph prefix, terminal-pair count, and terminal-pair endpoints.
No linkage, separator, or recursive answer is present in the input. -/
def GM02SimpleTerminatedInput.enc (x : GM02SimpleTerminatedInput) : List ℕ :=
  encGraph x.G ++ [x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph)

/-- The vertex count is the size parameter for the simple-graph routines. -/
def gm02SimpleTerminatedSize (x : GM02SimpleTerminatedInput) : ℕ := x.n

/-- The input length counts only graph edges and the supplied endpoint pairs. -/
theorem GM02SimpleTerminatedInput.enc_length (x : GM02SimpleTerminatedInput) :
    x.enc.length = 3 + 2 * (edgeListOf x.G).length + 2 * x.A.index := by
  simp only [GM02SimpleTerminatedInput.enc, List.length_append, length_encGraph,
    List.length_singleton, length_flatEdges, gm02Termination_pairList_length]
  omega

/-- Distinct endpoints bound the index by half the vertex count. -/
theorem GM02SimpleTerminatedInput.support_size_bound (x : GM02SimpleTerminatedInput) :
    2 * x.A.index ≤ x.n := by
  have h := Set.ncard_le_ncard (Set.subset_univ x.A.support) Set.finite_univ
  simpa only [x.A.support_ncard, Set.ncard_univ, Nat.card_fin] using h

/-- The mathematical width of the numbered input graph. -/
noncomputable def GM02SimpleTerminatedInput.width (x : GM02SimpleTerminatedInput) : ℕ :=
  treeWidth (Graph.ofSimpleGraph x.G) Set.finite_univ (Set.toFinite _)

/-- Internal A1/A2 output flags: one means feasible, zero infeasible, and
two means tree-width at least the internal width parameter, II pages 316–317. -/
def GM02SimpleTerminatedInput.recursiveCorrect (x : GM02SimpleTerminatedInput) (w : ℕ)
    (s : State) : Prop :=
  (s.regs outReg = 1 ∧ x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
  (s.regs outReg = 0 ∧ ¬x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
  (s.regs outReg = 2 ∧ w ≤ x.width)

/-- The strict width comparison in the final output of II (3.2), page 318. -/
def GM02SimpleTerminatedInput.correct (x : GM02SimpleTerminatedInput) (w : ℤ) (s : State) : Prop :=
  (s.regs outReg = 1 ∧ x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
  (s.regs outReg = 0 ∧ ¬x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
  (s.regs outReg = 2 ∧ w < (x.width : ℤ))

/-- Raising the internal threshold turns its non-strict width report into
the strict width report required by (3.2). -/
theorem GM02SimpleTerminatedInput.correct_of_recursiveCorrect (x : GM02SimpleTerminatedInput)
    {q : ℕ} {w : ℤ} {s : State} (hw : w < (q : ℤ)) (h : x.recursiveCorrect q s) : x.correct w s := by
  rcases h with hyes | hno | ⟨htag, hwidth⟩
  · exact Or.inl hyes
  · exact Or.inr (Or.inl hno)
  · have hq : (q : ℤ) ≤ (x.width : ℤ) := by exact_mod_cast hwidth
    exact Or.inr (Or.inr ⟨htag, hw.trans_le hq⟩)

end GraphMinor.Compute
