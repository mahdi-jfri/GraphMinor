module

public import GraphMinor.GM10.Section7TreeWidth
public import GraphMinor.GM01.Defs
public import GraphMinor.Minor.Basic
import GraphMinor.GM10.Section7GridMinor
import GraphMinor.GM10.Section7SimpleMinor
import GraphMinor.GM05.Main
import GraphMinor.GM01.Basic

/-!
# The grid theorem cited in Graph Minors X

Graph Minors X, (7.4), page 173, cites Graph Minors V. We apply that
proved theorem to the underlying simple graph. Its vertex bags give a
GM10 decomposition of the original graph, and its grid minor is also a
minor of the original graph. Taking the contrapositive gives the result.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph

universe u v

/-- Graph Minors X, (7.4), page 173:
"For every $\theta \ge 2$ there exists $\phi \ge 0$ such that every graph with tree-width
$\ge \phi$ has a $\theta$-grid minor."
The cited result of Graph Minors V is used with its proof. -/
theorem theorem_7_4_proof (θ : ℕ) (_hθ : 2 ≤ θ) :
    ∃ φ : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β)
      (hV : V(G).Finite) (hE : E(G).Finite),
      (φ : ℤ) ≤ treeWidth (Hypergraph.ofGraph G hV hE) →
      IsIsoMinor (GM01.gridGraph θ) G := by
  refine ⟨GM05.θ₉ (2 * (θ + 3)) + 1, ?_⟩
  intro α β G hV hE hwidth
  classical
  let : Fintype V(G) := hV.fintype
  let S := SimpleGraph.toSubgraph G.toSimpleGraph le_top
  by_contra hno
  have hnoS : ¬ IsIsoMinor (GM01.gridGraph θ) (GM01.toGraph S) := by
    intro hm
    have hm' : IsIsoMinor (GM01.gridGraph θ) (Graph.ofSimpleGraph G.toSimpleGraph) := by
      rwa [GM01.ofSimpleGraph_eq_toGraph]
    exact hno (hm'.trans (isIsoMinor_ofSimpleGraph_toSimpleGraph G))
  have hbound := GM05.treeWidthLE_of_not_isIsoMinor_proved
    (θ := 2 * (θ + 3)) (by omega)
    (show Even (2 * (θ + 3)) from ⟨θ + 3, by omega⟩)
    (Set.toFinite S.verts) hnoS
    (isIsoMinor_gridGraph_of_le (show θ ≤ 2 * (θ + 3) by omega))
  have hplus := treeWidthPlusOne_le_of_toSimpleGraph_treeWidthLE G hV hE hbound
  unfold treeWidth at hwidth
  omega

end GraphMinor.GM10
