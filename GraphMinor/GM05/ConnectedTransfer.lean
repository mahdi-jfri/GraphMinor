module

public import GraphMinor.GM05.ShadowMinor
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Lifting connected vertex sets from the simple shadow

Inducing on a vertex set commutes with taking the simple shadow. A connected
subgraph of the shadow therefore gives a connected induced subgraph of the
original graph on exactly the same vertices. Taking the shadow gives the
reverse passage for connected subgraphs.
-/

public section
namespace GraphMinor.GM05
open Graph Set SimpleGraph
variable {α β : Type*}

/-- Inducing on a vertex set preserves the shadow adjacency condition. -/
theorem simpleShadow_induce (G : Graph α β) (X : Set α) :
    simpleShadow (G.induce X) = (simpleShadow G).induce X := by
  ext x y
  · rfl
  · change (x ≠ y ∧ ∃ e, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X) ↔
      x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ G.Adj x y
    constructor
    · rintro ⟨hne, e, he, hx, hy⟩
      exact ⟨hx, hy, hne, e, he⟩
    · rintro ⟨hx, hy, hne, e, he⟩
      exact ⟨hne, e, he, hx, hy⟩

/-- Connectedness of an induced graph is a condition on its shadow. -/
theorem graphConnected_induce_iff (G : Graph α β) (X : Set α) :
    GraphConnected (G.induce X) ↔ ((simpleShadow G).induce X).Connected := by
  rw [graphConnected_iff_simpleShadow_connected, simpleShadow_induce]

/-- Connectivity without the requirement of having a vertex. This is the
convention used for the empty prefix and suffix in V (6.1), page 103. -/
@[expose] def GraphPreconnected (G : Graph α β) : Prop :=
  ∀ x ∈ V(G), ∀ y ∈ V(G), Relation.ReflTransGen G.Adj x y

/-- Preconnectedness, including the empty case, is unchanged by taking the shadow. -/
theorem graphPreconnected_iff (G : Graph α β) :
    GraphPreconnected G ↔ (simpleShadow G).Preconnected := by
  by_cases hne : V(G).Nonempty
  · have hconn : GraphPreconnected G ↔ GraphConnected G :=
      ⟨fun h => ⟨hne, h⟩, fun h => h.2⟩
    rw [hconn, graphConnected_iff_simpleShadow_connected,
      SimpleGraph.Subgraph.connected_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hne⟩⟩
  · have hempty : V(G) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    constructor
    · intro _
      rw [SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph]
      intro x y hx
      exact (hempty ▸ hx : x ∈ (∅ : Set α)).elim
    · intro _ x hx
      exact (hempty ▸ hx : x ∈ (∅ : Set α)).elim

/-- Preconnectedness of an induced graph is determined by its shadow. -/
theorem graphPreconnected_induce_iff (G : Graph α β) (X : Set α) :
    GraphPreconnected (G.induce X) ↔ ((simpleShadow G).induce X).Preconnected := by
  rw [graphPreconnected_iff, simpleShadow_induce]

/-- A connected subgraph of the shadow lifts on its vertex set. All edges
of the original graph with both ends in this set may be retained. -/
theorem exists_connected_subgraph_of_shadow {G : Graph α β}
    {C : (⊤ : SimpleGraph α).Subgraph} (hle : C ≤ simpleShadow G) (hc : C.Connected) :
    ∃ K : Graph α β, K ≤ G ∧ GraphConnected K ∧ V(K) = C.verts := by
  refine ⟨G.induce C.verts, Graph.induce_le hle.1, ?_, rfl⟩
  apply (graphConnected_induce_iff _ _).mpr
  refine SimpleGraph.Subgraph.Connected.mono (H := C) (H' := (simpleShadow G).induce C.verts) ?_ rfl hc
  exact ⟨fun _ h => h, fun _ _ h => ⟨C.edge_vert h, C.edge_vert h.symm, hle.2 h⟩⟩

end GraphMinor.GM05
