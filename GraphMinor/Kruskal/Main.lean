module

public import GraphMinor.GM04.Cited
import GraphMinor.Kruskal.TreeRepresentation
import GraphMinor.Kruskal.TopologicalEmbedding
import GraphMinor.Minor.Basic

/-!
# Kruskal's theorem for finite multigraph trees

Represent every finite tree by an ordered rooted tree, apply the minimal
bad sequence proof of well-quasi-ordering, and turn the resulting recursive
embedding into a finite sequence of edge subdivisions. Transport through
the representation isomorphisms gives the exact cited statement of IV.
The proof follows Nash-Williams, Theorem 1, pages 833–835 (1963), using
Mathlib's Higman lemma for branch lists.
-/

public section

namespace GraphMinor.Kruskal

open Graph

universe u v

/-- Kruskal's tree theorem in the exact multigraph and topological-containment
interface used by Graph Minors IV (1.2), page 229. The proof uses the minimal
bad sequence argument of Nash-Williams, Theorem 1, pages 834–835. -/
theorem kruskal_tree : GM04.KruskalTreeStatement.{u, v} := by
  intro α β G hV _hE hT
  choose t hIso using fun n ↦ exists_orderedTree_graph_iso (G n) (hV n) (hT n)
  obtain ⟨i, j, hij, hemb⟩ := OrderedTree.wellQuasiOrdered_embeds t
  obtain ⟨φi⟩ := hIso i
  obtain ⟨φj⟩ := hIso j
  refine ⟨i, j, hij, ?_⟩
  exact isTopologicalMinor_iso_target φj
    (isTopologicalMinor_iso_source φi.symm hemb.isTopologicalMinor)

end GraphMinor.Kruskal
