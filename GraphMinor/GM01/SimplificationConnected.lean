module

public import GraphMinor.Minor.Model
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity after graph simplification

The rooted proof of Graph Minors I, (1.1), passes to simple-graph paths.
A connected graph remains connected after loops are removed and parallel
edges are merged. Each original adjacency either stays an adjacency of
distinct vertices or repeats a vertex and can be omitted.
-/

public section

namespace GraphMinor.GM01

open Graph SimpleGraph

/-- Reachability between original vertices is preserved by simplification.
Repeated endpoints of loop steps are omitted. -/
theorem toSimpleGraph_reachable {α β : Type*} {G : Graph α β} {a b : α}
    (hr : Relation.ReflTransGen G.Adj a b) :
    ∀ (ha : a ∈ V(G)) (hb : b ∈ V(G)), G.toSimpleGraph.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction hr with
  | refl => intro ha hb; exact .refl _
  | @tail b c hr hbc ih =>
    intro ha hc
    obtain ⟨e, he⟩ := hbc
    have hr' := ih ha he.left_mem
    by_cases hEq : b = c
    · subst c
      exact hr'
    · exact hr'.trans (SimpleGraph.Adj.reachable ⟨fun heq ↦ hEq (congrArg Subtype.val heq), e, he⟩)

/-- Connectivity is preserved by the underlying simple graph, even in
the presence of loops and parallel edges. -/
theorem toSimpleGraph_connected {α β : Type*} {G : Graph α β}
    (h : GraphConnected G) : G.toSimpleGraph.Connected := by
  obtain ⟨a, ha⟩ := h.1
  let : Nonempty V(G) := ⟨⟨a, ha⟩⟩
  exact ⟨fun a b ↦ toSimpleGraph_reachable (h.2 a.val a.property b.val b.property) a.property b.property⟩

end GraphMinor.GM01
