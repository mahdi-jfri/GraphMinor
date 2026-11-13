module

public import GraphMinor.GM02.EmbeddedSimpleGraph
public import GraphMinor.GM02.SimpleGraphRenaming
import GraphMinor.GM02.AddIsolatedVertices

/-!
# Width of an injectively embedded simple graph

First rename a decomposition onto the embedding's range. Regard this as
a decomposition of the partial graph on that range. Finally add the
finitely many unused ambient positions as isolated vertices, using
singleton leaf bags. The natural-number width bound stays unchanged.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set
universe u v

private theorem embeddedSimpleGraph_induce_univ {α : Type u} {β : Type v}
    (F : SimpleGraph α) (f : α ↪ β) :
    (embeddedSimpleGraph F f).induce Set.univ = Graph.ofSimpleGraph (F.map f) := by
  apply Graph.ext (by simp [Graph.ofSimpleGraph])
  intro e a b
  rw [Graph.induce_isLink, embeddedSimpleGraph, Graph.induce_isLink]
  constructor
  · exact fun h => h.1.1
  · intro h
    have hab := (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, h⟩
    obtain ⟨a', b', _, ha, hb⟩ := (SimpleGraph.map_adj f F a b).1 hab
    exact ⟨⟨h, ⟨a', ha⟩, ⟨b', hb⟩⟩, trivial, trivial⟩

/-- Injectively embedding a simple graph in a finite ambient type preserves every natural-number width bound. -/
theorem treeWidthLE_mapEmbedding {α : Type u} {β : Type v} [Finite β]
    (F : SimpleGraph α) (f : α ↪ β) (w : ℕ)
    (hW : TreeWidthLE (Graph.ofSimpleGraph F) w) :
    TreeWidthLE (Graph.ofSimpleGraph (F.map f)) w := by
  have hrenamed := (treeWidthLE_simpleIso_iff (embeddedSimpleGraphIso F f) w).1 hW
  have hpartial : TreeWidthLE (embeddedSimpleGraph F f) w := by
    apply (treeWidthLE_onVertices_iff (embeddedSimpleGraph F f) w).1
    rw [embeddedSimpleGraph_pathGraph]
    exact hrenamed
  have hfull := treeWidthLE_add_isolated_vertices (embeddedSimpleGraph F f) w hpartial
    Set.univ Set.finite_univ
  rw [Set.union_univ, embeddedSimpleGraph_induce_univ] at hfull
  exact hfull

end GraphMinor.GM02
