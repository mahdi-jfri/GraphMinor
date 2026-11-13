module

public import GraphMinor.GM02.FeasibilityVertices
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Combinatorics.Graph.Delete

/-!
# A simple graph embedded in a larger vertex type

The numeric split construction for II (4.6), page 319, retains unused
positions as isolated vertices. Restrict the pushed-forward graph to the
embedding's range. This keeps its entire path shadow, and its graph on
actual vertices is isomorphic to the original simple graph.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set
universe u v

/-- The pushed-forward simple graph with precisely the embedding's range as vertices. -/
def embeddedSimpleGraph {α : Type u} {β : Type v} (F : SimpleGraph α) (f : α ↪ β) :
    Graph β (Sym2 β) := (Graph.ofSimpleGraph (F.map f)).induce (Set.range f)

/-- Removing the unused positions leaves all adjacency and hence the entire path shadow intact. -/
theorem embeddedSimpleGraph_pathGraph {α : Type u} {β : Type v}
    (F : SimpleGraph α) (f : α ↪ β) : pathGraph (embeddedSimpleGraph F f) = F.map f := by
  ext a b
  constructor
  · rintro ⟨⟨e, he⟩, _⟩
    rw [embeddedSimpleGraph, Graph.induce_isLink] at he
    exact (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, he.1⟩
  · intro h
    obtain ⟨a', b', _, ha, hb⟩ := (SimpleGraph.map_adj f F a b).1 h
    refine ⟨⟨s(a, b), ?_⟩, (F.map f).ne_of_adj h⟩
    rw [embeddedSimpleGraph, Graph.induce_isLink]
    exact ⟨⟨rfl, (SimpleGraph.mem_edgeSet _).2 h⟩, ⟨a', ha⟩, ⟨b', hb⟩⟩

/-- Restricting an injective graph image to the image vertex set recovers the original graph. -/
noncomputable def embeddedSimpleGraphIso {α : Type u} {β : Type v}
    (F : SimpleGraph α) (f : α ↪ β) : F ≃g (F.map f).induce (Set.range f) where
  toEquiv := Equiv.ofInjective f f.injective
  map_rel_iff' := by
    intro a b
    change (F.map f).Adj (f a) (f b) ↔ F.Adj a b
    exact SimpleGraph.map_adj_apply

end GraphMinor.GM02
