module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Results cited in Graph Minors XIII

This file states as `Prop`s the external results cited in *Graph Minors. XIII. The Disjoint Paths
Problem* (J. Combin. Theory Ser. B **63** (1995), 65–110):

* `Thomason84Statement`: A. Thomason, *An extremal function for contractions of graphs*,
  Math. Proc. Cambridge Philos. Soc. **95** (1984), 261–265 (reference [28] of XIII), stated as
  (5.5) of XIII (page 83) and used in the digression (5.6) (page 83).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph SimpleGraph Hypergraph
open GraphMinor.GM09 GraphMinor.GM16

universe u v

/-- A. Thomason, *An extremal function for contractions of graphs*, Math. Proc. Cambridge Philos.
Soc. **95** (1984), 261–265 (reference [28] of Graph Minors XIII), stated as (5.5) in Graph Minors
XIII (page 83):
"(5.5) *Let $p \ge 1$ be an integer, and let $G$ be a non-null simple graph with*
$$|E(G)| \ge 2.68 p(\log_2(p))^{1/2} |V(G)|.$$
*Then $G$ has a $K_p$-minor.*" -/
def Thomason84Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (p : ℕ),
    1 ≤ p → V(G).Finite → E(G).Finite → V(G).Nonempty → IsSimpleGraph G →
    (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) * (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ) →
    HasGraphModel (completeGraph p) G

end GraphMinor.GM13
