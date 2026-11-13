module

public import GraphMinor.GM16.Defs
import GraphMinor.GM16.TorsoEdgePiece
import GraphMinor.GM09.Basic

/-!
# Removing one core edge by a location separation

In the refinement of the lifted location for XVI (1.3), pages 51–52,
put a core edge alone on the left and retain every vertex on the right.
The separator consists of its at most two ends. These separations
remove edges incident with the exceptional vertices from the core
without removing any core vertex.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- The graph consisting of an edge and its ends. -/
def singleEdgeGraph {α : Type u} {β : Type v} (G : Graph α β) (e : β) : Graph α β :=
  (G.induce {x | G.Inc e x}).restrict {e}

/-- The separation that removes one edge from a location core. -/
def singleEdgePair {α : Type u} {β : Type v} (G : Graph α β) (e : β) :
    Graph α β × Graph α β :=
  (singleEdgeGraph G e, G.deleteEdges {e})

/-- The single-edge graph is a subgraph of its ambient graph. -/
theorem singleEdgeGraph_le {α : Type u} {β : Type v} (G : Graph α β) (e : β) :
    singleEdgeGraph G e ≤ G := by
  apply restrict_le.trans
  apply G.induce_le
  rintro x ⟨y, hxy⟩
  exact hxy.left_mem

/-- The single-edge graph has exactly its chosen edge. -/
theorem edgeSet_singleEdgeGraph {α : Type u} {β : Type v}
    {G : Graph α β} {e : β} (he : e ∈ E(G)) : E(singleEdgeGraph G e) = {e} := by
  apply edgeSet_induce_restrict_eq_of_ends_subset (singleton_subset_iff.mpr he)
  rintro f rfl x hx
  exact hx

/-- Any subgraph containing the edge contains its single-edge graph. -/
theorem singleEdgeGraph_le_of_mem {α : Type u} {β : Type v}
    {G H : Graph α β} (hHG : H ≤ G) {e : β} (he : e ∈ E(H)) :
    singleEdgeGraph G e ≤ H := by
  rw [(Compatible.of_le_le (singleEdgeGraph_le G e) hHG).le_iff]
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hxy⟩
    exact ((hHG.isLink_iff he).mpr hxy).left_mem
  · rw [edgeSet_singleEdgeGraph (hHG.edgeSet_mono he)]
    exact singleton_subset_iff.mpr he

/-- A subgraph that omits the chosen edge lies in the right side. -/
theorem le_singleEdgePair_right {α : Type u} {β : Type v}
    {G H : Graph α β} (hHG : H ≤ G) {e : β} (he : e ∉ E(H)) :
    H ≤ (singleEdgePair G e).2 := by
  change H ≤ G.deleteEdges {e}
  rw [(Compatible.of_le_le hHG Graph.deleteEdges_le).le_iff]
  refine ⟨hHG.vertexSet_mono, ?_⟩
  intro f hf
  exact ⟨hHG.edgeSet_mono hf, fun hfe => he (hfe ▸ hf)⟩

/-- An edge and the graph with that edge deleted form a separation. -/
theorem singleEdgePair_isSeparation {α : Type u} {β : Type v}
    {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    IsGraphSeparation G (singleEdgePair G e).1 (singleEdgePair G e).2 := by
  refine ⟨singleEdgeGraph_le G e, Graph.deleteEdges_le, ?_, ?_, ?_⟩
  · exact union_eq_self_of_subset_left (singleEdgeGraph_le G e).vertexSet_mono
  · change E(singleEdgeGraph G e) ∪ (E(G) \ {e}) = E(G)
    rw [edgeSet_singleEdgeGraph he]
    exact union_sdiff_cancel (singleton_subset_iff.mpr he)
  · change Disjoint E(singleEdgeGraph G e) (E(G) \ {e})
    rw [edgeSet_singleEdgeGraph he]
    exact disjoint_sdiff_self_right

/-- The single-edge separation has order at most two, including when
its edge is a loop. -/
theorem singleEdgePair_order_le_two {α : Type u} {β : Type v}
    {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    (V((singleEdgePair G e).1) ∩ V((singleEdgePair G e).2)).ncard ≤ 2 := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have hEnds : {z | G.Inc e z} = ({x, y} : Set α) := by
    ext z
    constructor
    · rintro ⟨w, hzw⟩
      exact hzw.left_eq_or_eq hxy
    · rintro (rfl | rfl)
      · exact ⟨y, hxy⟩
      · exact ⟨x, hxy.symm⟩
  have hfin : {z | G.Inc e z}.Finite := hEnds.symm ▸ (finite_singleton y).insert x
  have hCount : {z | G.Inc e z}.ncard ≤ 2 := by
    rw [hEnds]
    simpa only [ncard_singleton, Nat.one_add] using ncard_insert_le x ({y} : Set α)
  exact (ncard_le_ncard inter_subset_left hfin).trans hCount

end GraphMinor.GM16
