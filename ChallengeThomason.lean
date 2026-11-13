module

public import GraphMinor.GM09.Defs
public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Thomason's bound: the statement to be proved

`GraphMinor.thomason_bound` is the bound of A. Thomason, *An extremal function for contractions of
graphs*, Math. Proc. Cambridge Philos. Soc. **95** (1984), 261–265, in the form stated as (5.5) of
Graph Minors XIII (page 83):

> (5.5) Let $p \ge 1$ be an integer, and let $G$ be a non-null simple graph with
> $|E(G)| \ge 2.68\, p (\log_2 p)^{1/2} |V(G)|$. Then $G$ has a $K_p$-minor.

Thomason's paper gives the constant 2.68 only asymptotically. The theorem here holds for every
$p \ge 1$. A graph is Mathlib's multigraph `Graph α β`. `GraphMinor.GM09.IsSimpleGraph` says
that it has no loops and no parallel edges, `GraphMinor.GM16.completeGraph p` is $K_p$, and
`GraphMinor.GM13.HasGraphModel H G` says that `G` has a model of `H`, that is, an `H`-minor
(Graph Minors XIII, Section 2, page 68). `SolutionThomason.lean` proves the theorem.
-/

public section

namespace GraphMinor

open Graph

universe u v

/-- **Thomason's bound**, as stated in Graph Minors XIII, (5.5), page 83, for every `p ≥ 1`: a
finite non-null simple graph `G` with `|E(G)| ≥ 2.68 p (log₂ p) ^ (1/2) |V(G)|` has a `K_p`
minor. -/
theorem thomason_bound {α : Type u} {β : Type v} (G : Graph α β) (p : ℕ) (hp : 1 ≤ p)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty) (hs : GM09.IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (GM16.completeGraph p) G :=
  sorry

end GraphMinor
