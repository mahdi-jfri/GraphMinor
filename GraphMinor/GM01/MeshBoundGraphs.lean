module

public import GraphMinor.GM01.Defs
public import GraphMinor.Minor.Model
import GraphMinor.GM01.MeshBound
import GraphMinor.GM01.SeparatorGraphBridge
import GraphMinor.GM01.ConnectedInducedSets

/-!
# The connected-family bound for general graphs

Graph Minors I, (2.10), page 50, allows loops and parallel edges.
Pass to the underlying simple graph, keeping the original vertex
sets of the two families. Their induced simple subgraphs remain
connected and disjoint. Apply the proved simple form, obtained
from Graph Minors V (5.3), and return the disjoint pair through
the inclusion of the original vertex subtype.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

universe u v

/-- Graph Minors I, (2.10), page 50: "There is an integer $\theta' > 0$
such that if $A_1, \dots, A_{\theta'}$ are disjoint connected subgraphs
of a graph $G \in \mathscr{F}_\theta$, and $B_1, \dots, B_{\theta'}$ are
also disjoint connected subgraphs of $G$, then some $A_i$ is disjoint
from some $B_j$."
Use the proved GM05 (5.3) through the simple form, then lift the
vertex-set conclusion to the general graph. The fixed even grid
parameter satisfies the standing Section 2 condition `θ ≥ 6`. -/
theorem theorem_2_10_proof {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    ∃ n : ℕ, 0 < n ∧ ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → ¬ IsIsoMinor (gridGraph θ) G →
      ∀ (A B : Fin n → Graph α β),
        (∀ i, A i ≤ G) → (∀ j, B j ≤ G) →
        (∀ i, GraphConnected (A i)) → (∀ j, GraphConnected (B j)) →
        (Pairwise fun i j ↦ Disjoint V(A i) V(A j)) →
        (Pairwise fun i j ↦ Disjoint V(B i) V(B j)) →
        ∃ i j, Disjoint V(A i) V(B j) := by
  obtain ⟨n, hn, hSimple⟩ := theorem_2_10_simple.{u} hθ heven
  refine ⟨n, hn, ?_⟩
  intro α β G hV hGrid A B hA hB hAC hBC hAD hBD
  let : Finite V(G) := hV.to_subtype
  have hAs : ∀ i, (simpleInducedVertices G V(A i)).Connected := by
    intro i
    exact simpleInducedVertices_connected G V(A i) (hA i).vertexSet_mono
      (graphConnected_induce_of_subgraph (hA i) (hAC i))
  have hBs : ∀ i, (simpleInducedVertices G V(B i)).Connected := by
    intro i
    exact simpleInducedVertices_connected G V(B i) (hB i).vertexSet_mono
      (graphConnected_induce_of_subgraph (hB i) (hBC i))
  obtain ⟨i, j, hij⟩ := hSimple (SimpleGraph.toSubgraph G.toSimpleGraph le_top)
    Set.finite_univ (simplification_mem_gridFree G hGrid)
    (fun i ↦ simpleInducedVertices G V(A i)) (fun j ↦ simpleInducedVertices G V(B j))
    (fun _ ↦ simpleInducedVertices_le G _) (fun _ ↦ simpleInducedVertices_le G _)
    hAs hBs
    (fun i j h ↦ Set.disjoint_left.mpr (fun _ hx hy ↦ Set.disjoint_left.mp (hAD h) hx hy))
    (fun i j h ↦ Set.disjoint_left.mpr (fun _ hx hy ↦ Set.disjoint_left.mp (hBD h) hx hy))
  refine ⟨i, j, Set.disjoint_left.mpr ?_⟩
  intro x hx hy
  let x' : V(G) := ⟨x, (hA i).vertexSet_mono hx⟩
  have hx' : x' ∈ (simpleInducedVertices G V(A i)).verts := hx
  have hy' : x' ∈ (simpleInducedVertices G V(B j)).verts := hy
  exact Set.disjoint_left.mp hij hx' hy'

end GraphMinor.GM01
