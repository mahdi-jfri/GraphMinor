module

public import GraphMinor.GM05.FullPlanar

/-!
# Planar exclusion in the introduction of Graph Minors XVI

The introductory planar exclusion theorem is the full finite-graph theorem
of Graph Minors V. Both the excluded graph and the host may have loops and
parallel edges.
-/

public section
namespace GraphMinor.GM16
open Graph

/-- Graph Minors XVI, (1.1), page 44:
"For any planar graph $L$ there is a number $N$ such that every graph with no $L$-minor has tree-width $\le N$."

This is proved by `GM05.Full.theorem_1_5_proof`, allowing loops and parallel edges
in both graphs. The host has finite vertex and edge sets. -/
theorem theorem_1_1_proof {α β α' β' : Type*} (L : Graph α' β') (hL : IsPlanar L) :
    ∃ N : ℕ, ∀ G : Graph α β, V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor L G → GM05.Full.TreeWidthLE G N := by
  exact GM05.Full.theorem_1_5_proof L hL

end GraphMinor.GM16
