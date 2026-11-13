module

public import GraphMinor.GM01.RootedPathWidth
public import GraphMinor.GM01.RootedSimplification
import GraphMinor.GM01.SimplificationConnected
import GraphMinor.GM01.PathWidthSimplification
import GraphMinor.GM01.Basic

/-!
# The rooted path bound for general graphs

Part 1 of the rooted argument for Graph Minors I, (1.1), page 54, deletes
the root and inducts in its components. The simple-graph proof already
performs that induction. Connectivity survives simplification, rooted
models lift back, and path-width bounds transfer back even when the
original graph has loops. These facts give the paper's general-graph
form of this base case.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The general-graph form of Part 1 on page 54 of Graph Minors I:
excluding the path rooted at one end gives width at most `δ−2`.
The proof uses the proved deletion induction on the underlying simple
graph and lifts any forbidden model back to the original graph. -/
theorem pathWidthLE_of_not_rootedPathComb_graph {α β : Type*}
    (G : RootedGraph α β) (hfin : V(G.graph).Finite)
    (hconn : GraphConnected G.graph) {δ : ℕ} (hδ : 0 < δ)
    (hno : ¬ HasRootedMinor (rootedPathComb 0 δ hδ) G) :
    HasPathWidthLE G.graph (δ - 2) := by
  let : Finite V(G.graph) := hfin.to_subtype
  let S := SimpleGraph.toSubgraph G.graph.toSimpleGraph le_top
  let root : S.verts := ⟨G.root, mem_univ _⟩
  have hSconn : S.Connected := by
    let f : G.graph.toSimpleGraph →g S.coe :=
      { toFun := fun x ↦ ⟨x, mem_univ _⟩
        map_rel' := fun h ↦ h }
    exact ⟨(toSimpleGraph_connected hconn).map f (fun x ↦ ⟨x.val, rfl⟩)⟩
  have hSno : ¬ HasRootedMinor (rootedPathComb 0 δ hδ)
      (⟨toGraph S, root⟩ : RootedGraph V(G.graph) (Sym2 V(G.graph))) := by
    intro hmodel
    apply hno
    apply HasRootedMinor.of_simplification
    obtain ⟨M⟩ := hmodel
    exact ⟨M.mono (le_of_eq (ofSimpleGraph_eq_toGraph G.graph.toSimpleGraph).symm) rfl⟩
  have hwidth := pathWidthLE_of_not_rootedPathComb S Set.finite_univ hSconn root hδ hSno
  apply HasPathWidthLE.of_toSimpleGraph hfin
  rwa [ofSimpleGraph_eq_toGraph]

end GraphMinor.GM01
