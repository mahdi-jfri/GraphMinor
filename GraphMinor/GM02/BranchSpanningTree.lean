module

public import GraphMinor.GM02.RealizeBranchTree
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import GraphMinor.GM05.ShadowMinor
import GraphMinor.GM05.ExpansionConnected

/-!
# Spanning trees inside connected multigraph branches

Discarding loops and merging parallel edges does not change connectivity.
Choose a spanning tree in the resulting simple graph and realize each of
its edges by one original edge. This supplies the actual subgraphs used
when pruning the branches in II (4.8).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set
universe u v

/-- A connected multigraph has a connected underlying simple graph. -/
theorem toSimpleGraph_connected_of_graphConnected {α : Type u} {β : Type v}
    {G : Graph α β} (h : GraphConnected G) : G.toSimpleGraph.Connected := by
  have hshadow := (GM05.graphConnected_iff_simpleShadow_connected G).1 h
  let φ : (GM05.simpleShadow G).coe ≃g G.toSimpleGraph := {
    toEquiv := Equiv.refl _
    map_rel_iff' := by
      intro x y
      change (x ≠ y ∧ G.Adj x.val y.val) ↔ (x.val ≠ y.val ∧ G.Adj x.val y.val)
      constructor
      · rintro ⟨hne, hxy⟩
        exact ⟨fun he => hne (Subtype.ext he), hxy⟩
      · rintro ⟨hne, hxy⟩
        exact ⟨fun he => hne (congrArg Subtype.val he), hxy⟩ }
  exact φ.connected_iff.mp hshadow.coe

/-- A connected simple graph, viewed as a multigraph, is connected. -/
theorem graphConnected_ofSimpleGraph {α : Type*} {T : SimpleGraph α}
    (h : T.Connected) : GraphConnected (Graph.ofSimpleGraph T) := by
  have lift : ∀ {a b : α}, T.Walk a b →
      Relation.ReflTransGen (Graph.ofSimpleGraph T).Adj a b := by
    intro a b p
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | cons hadj _ ih =>
      exact (Relation.ReflTransGen.single ((Graph.ofSimpleGraph_adj_iff _ _).2 hadj)).trans ih
  obtain ⟨a⟩ := h.nonempty
  exact ⟨⟨a, trivial⟩, fun a _ b _ => (h a b).elim lift⟩

/-- Every connected multigraph has a connected spanning subgraph isomorphic
to a simple tree. Its vertices are unchanged, and its edges are original
edges, with one chosen representative for each tree edge. -/
theorem exists_realized_spanning_tree {α : Type u} {β : Type v}
    (G : Graph α β) (hconn : GraphConnected G) :
    ∃ (T : SimpleGraph V(G)) (K : Graph α β),
      T.IsTree ∧ T ≤ G.toSimpleGraph ∧ K ≤ G ∧ V(K) = V(G) ∧
        GraphConnected K ∧ Nonempty (Iso (Graph.ofSimpleGraph T) K) := by
  obtain ⟨T, hTle, hT⟩ :=
    (toSimpleGraph_connected_of_graphConnected hconn).exists_isTree_le
  obtain ⟨K, hK, hV, φ, _⟩ := exists_subgraph_iso_of_simple_graph_on
    G V(G) (Subset.refl _) T (fun h => (hTle h).2)
  exact ⟨T, K, hT, hTle, hK, hV,
    GM05.graphConnected_of_iso φ (graphConnected_ofSimpleGraph hT.connected), ⟨φ⟩⟩

end GraphMinor.GM02
