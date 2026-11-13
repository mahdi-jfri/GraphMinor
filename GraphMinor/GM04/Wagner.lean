module

public import GraphMinor.Statement
import GraphMinor.GM20.Assembled

/-!
# Wagner's conjecture as numbered in Graph Minors IV

Graph Minors IV states the conjecture as (1.1). Graph Minors XX proves it.
This file gives the assembled proof its earlier number.
-/

public section

namespace GraphMinor.GM04

open Graph

/-- Graph Minors IV, (1.1), page 228: "If $G_1, G_2, \dots$ is any countable sequence of graphs then there exist $j > i \ge 1$ such that $G_i$ is isomorphic to a minor of $G_j$."
The proof is the graph minor theorem of Graph Minors XX. -/
theorem theorem_1_1_proof {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) :=
  GM20.graph_minor_theorem_assembled G hV hE

end GraphMinor.GM04
