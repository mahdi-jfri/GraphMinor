module

import GraphMinor.Minor.Basic

public import GraphMinor.GM05.FullTreeWidth
public import GraphMinor.GM05.Planar

/-!
# Planar exclusion bounds for graphs with loops and parallel edges

The simple shadow is a minor of the original graph. Thus exclusion of any
fixed target, even one with loops or parallel edges, passes to the shadow.
The simple-host bound and the vertex-bag transfer then give the full bound.
-/

public section
namespace GraphMinor.GM05.Full
open Graph
variable {α β α' β' : Type*}

/-- Graph Minors V, (2.1), page 95, for arbitrary finite hosts:
"If $H$ is a planar graph, then every graph with no minor isomorphic to $H$ has tree-width at most $\theta_9(\theta(H))$."

`GM05.theorem_2_1_simple` is the simple-host version. This numbered version permits
loops and parallel edges in both the host and the excluded graph. -/
theorem theorem_2_1_proof {H : Graph α' β'} (hH : IsPlanar H) {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hno : ¬ IsIsoMinor H G) :
    TreeWidthLE G (θ₉ (θOf H)) := by
  apply treeWidthLE_iff.mpr
  exact GM05.theorem_2_1_simple hH hV
    (fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE)))

/-- Graph Minors V, (1.5), page 93, for arbitrary finite hosts.
For every planar graph `H`, excluding `H` bounds tree-width.
`GM05.theorem_1_5_simple` is the simple-host version. As in (2.1), the bound here
also applies to nonplanar hosts. -/
theorem theorem_1_5_proof (H : Graph α' β') (hH : IsPlanar H) :
    ∃ w : ℕ, ∀ (G : Graph α β), V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor H G → TreeWidthLE G w :=
  ⟨θ₉ (θOf H), fun _ hV hE hno => theorem_2_1_proof hH hV hE hno⟩

end GraphMinor.GM05.Full
