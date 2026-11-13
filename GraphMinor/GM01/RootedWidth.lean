module

public import GraphMinor.GM01.QuantitativeParity
public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.PathWidth
import GraphMinor.GM01.RootedWidthHeightInduction
import GraphMinor.GM01.RootedSimplification
import GraphMinor.GM01.SimplificationConnected
import GraphMinor.GM01.SimplificationMinor
import GraphMinor.GM01.PathWidthSimplification
import GraphMinor.Minor.Basic

/-!
# The rooted width bounds of Graph Minors I

The closed Parts 1–3 induction proves the two bounds for finite
edge-label types. For a general graph with finite vertex set, pass
to its underlying simple graph with the same distinguished root.
Its vertex and edge-label types are finite. Connectivity and grid
exclusion pass to it, and any forbidden rooted model lifts back.
Finally transfer its path decomposition to the original graph,
including coverage of loops. This proves (3.7) over the paper's
general finite graphs with no result hypothesis.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

private theorem simplification_graphConnected {α β : Type*} (G : RootedGraph α β)
    (hConn : GraphConnected G.graph) : GraphConnected G.simplification.graph := by
  have hS := toSimpleGraph_connected hConn
  refine ⟨⟨G.root,mem_univ _⟩,?_⟩
  intro x _ y _
  obtain ⟨p⟩ := hS x y
  induction p with
  | nil => exact .refl
  | @cons a b z hadj p ih =>
    exact (Relation.ReflTransGen.single ⟨s(a,b),rfl,hadj⟩).trans (ih (mem_univ _) (mem_univ _))

/-- The closed rooted bounds for any finite-vertex general graph.
Simplification removes the finite-label restriction of the auxiliary
height induction while retaining both printed bounds of GM01 (3.7). -/
theorem rooted_width_bounds {α β : Type*} (lam : ℕ) (hodd : Odd lam)
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (hConn : GraphConnected G.graph)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) :
    ((∀ γ : ℕ, γ ≤ lam → ∀ (δ : ℕ) (hδ : 2 ≤ δ),
      (¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G) →
      HasPathWidthLE G.graph (pathWidthBound lam γ δ)) ∧
    (∀ (γ : ℕ) (hγ : 0 < γ), γ ≤ lam → ∀ (δ : ℕ) (hδ : 2 ≤ δ),
      (¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G) →
      HasPathWidthLE G.graph (forkWidthBound lam γ δ))) := by
  let : Finite V(G.graph) := hV.to_subtype
  let S := G.simplification
  have hSV : V(S.graph).Finite := Set.finite_univ
  have hSC : GraphConnected S.graph := simplification_graphConnected G hConn
  have hSGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) S.graph := by
    intro h
    exact hGrid (h.trans (simplification_isIsoMinor G.graph))
  constructor
  · intro γ hγlam δ hδ hNo
    have hSNo : ¬ HasRootedMinor (rootedPathComb γ δ (by omega)) S :=
      fun h ↦ hNo (HasRootedMinor.of_simplification (G := G) h)
    have hWidth := (rooted_width_bounds_of_finite_edge_labels
      (α := V(G.graph)) (β := Sym2 V(G.graph)) lam hodd γ hγlam).1
      δ hδ S hSV hSC hSGrid hSNo
    exact HasPathWidthLE.of_toSimpleGraph hV hWidth
  · intro γ hγ hγlam δ hδ hNo
    have hSNo : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) S :=
      fun h ↦ hNo (HasRootedMinor.of_simplification (G := G) h)
    have hWidth := (rooted_width_bounds_of_finite_edge_labels
      (α := V(G.graph)) (β := Sym2 V(G.graph)) lam hodd γ hγlam).2
      hγ δ hδ S hSV hSC hSGrid hSNo
    exact HasPathWidthLE.of_toSimpleGraph hV hWidth

/-- Graph Minors I, (3.7), page 54:
"If $G \in \mathscr{F}_\theta$, and is rooted and connected, and has no rooted minor isomorphic to $P(\gamma, \delta)$, then $G$ has path-width at most $p(\gamma, \delta)$, for $0 \le \gamma \le \lambda$, $\delta \ge 2$."
"If $G \in \mathscr{F}_\theta$, and is rooted and connected, and has no rooted minor isomorphic to $Q(\gamma, \delta)$, then $G$ has path-width at most $q(\gamma, \delta)$, for $1 \le \gamma \le \lambda$, $\delta \ge 2$."

The height and length inductions follow Parts 1–3, pages 54–61. -/
theorem theorem_3_7_proof {α β : Type*} (lam : ℕ) (_hlam : 1 ≤ lam) (hodd : Odd lam)
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (_hE : E(G.graph).Finite)
    (hConn : GraphConnected G.graph)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) :
    ((∀ γ : ℕ, γ ≤ lam → ∀ (δ : ℕ) (hδ : 2 ≤ δ),
      (¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G) →
      HasPathWidthLE G.graph (pathWidthBound lam γ δ)) ∧
    (∀ (γ : ℕ) (hγ : 0 < γ), γ ≤ lam → ∀ (δ : ℕ) (hδ : 2 ≤ δ),
      (¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G) →
      HasPathWidthLE G.graph (forkWidthBound lam γ δ))) :=
  rooted_width_bounds lam hodd G hV hConn hGrid

end GraphMinor.GM01
