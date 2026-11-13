module

public import GraphMinor.GM01.SimpleEdgeSelection
public import GraphMinor.Minor.Basic

/-!
# The underlying simple graph is a minor

To apply the simple-graph separator lemmas in the proof of Graph Minors I,
(4.2), retain one original edge for each adjacent pair of distinct vertices.
The selected subgraph has all original vertices and is explicitly
isomorphic to the underlying simple graph. This uses neither a loopless
assumption nor nonemptiness of the edge-label type. Grid exclusion can
therefore be transferred to the simple graph by minor transitivity.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Selecting one edge for each simple adjacency gives a subgraph
isomorphic to the underlying simple graph, with the identity vertex map. -/
theorem exists_simplification_subgraph {α β : Type*} (G : Graph α β) :
    ∃ K : Graph α β, K ≤ G ∧ Nonempty (GraphMinor.Iso (Graph.ofSimpleGraph G.toSimpleGraph) K) := by
  classical
  obtain ⟨f, hf⟩ := exists_simpleGraph_edge_embedding G
  let selected : Set β := range (fun e : G.toSimpleGraph.edgeSet ↦ (f e).val)
  let K := G.restrict selected
  have hSelected (e : G.toSimpleGraph.edgeSet) : (f e).val ∈ selected := ⟨e, rfl⟩
  let mapEdge : E(Graph.ofSimpleGraph G.toSimpleGraph) → E(K) := fun e ↦
    ⟨(f e).val, ⟨(f e).property, hSelected e⟩⟩
  have hinj : Function.Injective mapEdge := by
    intro e e' heq
    exact f.injective (Subtype.ext (congrArg (fun e : E(K) ↦ e.val) heq))
  have hsurj : Function.Surjective mapEdge := by
    intro e
    have heSelected : e.val ∈ selected := e.property.2
    obtain ⟨e', he'⟩ := heSelected
    exact ⟨e', Subtype.ext he'⟩
  refine ⟨K, Graph.restrict_le, ⟨?_⟩⟩
  refine
    { vertexEquiv :=
        { toFun := fun x ↦ x.val
          invFun := fun x ↦ ⟨x, mem_univ _⟩
          left_inv := fun x ↦ Subtype.ext rfl
          right_inv := fun x ↦ rfl }
      edgeEquiv := Equiv.ofBijective mapEdge ⟨hinj, hsurj⟩
      isLink_iff := ?_ }
  intro e x y
  change (e.val = s(x.val,y.val) ∧ e.val ∈ G.toSimpleGraph.edgeSet) ↔
    ((f e).val ∈ selected ∧ G.IsLink (f e) x.val y.val)
  exact ⟨fun he ↦ ⟨hSelected e, (hf e x.val y.val).mpr he.1⟩,
    fun he ↦ ⟨(hf e x.val y.val).mp he.2, e.property⟩⟩

/-- The underlying simple graph is isomorphic to a minor of the original
graph, including empty and loop-only graphs. -/
theorem simplification_isIsoMinor {α β : Type*} (G : Graph α β) :
    IsIsoMinor (Graph.ofSimpleGraph G.toSimpleGraph) G := by
  obtain ⟨K, hKG, ⟨e⟩⟩ := exists_simplification_subgraph G
  have hminor := e.isIsoMinor_left (IsIsoMinor.refl K)
  obtain ⟨J, hJK, C, hC, hIso⟩ := hminor
  exact ⟨J, hJK.trans hKG, C, hC, hIso⟩

end GraphMinor.GM01
