module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.PathWidth

/-!
# The branching-tree bound used in the main theorem

Graph Minors I proves (1.1) by first reducing to (3.1), the uniform
path-width bound for graphs excluding one of the odd-depth trees `Y_ℓ`.
This file states that numbered result with its printed hypotheses, so the
reduction can name its precise remaining dependency.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph

universe u v

/-- Graph Minors I, (3.1), page 51:
"For $\lambda \ge 1$, odd, there is a number $w(\lambda)$ such that every graph with no minor isomorphic to $\mathbf{Y}_\lambda$ has path-with $\le w(\lambda)$."

The graph has finite vertex and edge sets, following the paper's convention
on page 39. The exponent and grid parameters of (3.2) are not part of this
statement. -/
def GM01Theorem31Statement : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Odd ℓ → ∃ w : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β), V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor (forestTreeGraph ℓ) G → HasPathWidthLE G w

end GraphMinor.GM01
