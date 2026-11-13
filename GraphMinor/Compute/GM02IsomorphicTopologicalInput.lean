module

public import GraphMinor.Compute.GM02EdgeListInput
public import GraphMinor.GM02.TopologicalContainment

/-!
# Output meanings for the plain-host algorithm of II (4.7)

The fixed target is not part of the input array. The three flags assert
existence of a topologically contained isomorphic copy, its absence,
or host tree-width above the fixed threshold, as on page 319.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02

/-- The three alternatives printed in Graph Minors II (4.7), page 319. -/
def gm02IsomorphicTopologicalCorrect {A B : Type*} (H : Graph A B) (w : ℤ)
    (G : GM02EdgeListInput) (s : State) : Prop :=
  (s.regs outReg = 1 ∧ ∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H L)) ∨
    (s.regs outReg = 0 ∧ ¬∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H L)) ∨
    (s.regs outReg = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))

end GraphMinor.Compute
