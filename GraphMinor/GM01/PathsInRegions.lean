module

public import GraphMinor.GM01.VertexAvoidanceRegions
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.SubdivisionConnected

/-!
# Replacing paths inside an avoidance region

The tail minor in Graph Minors I, (4.1), page 55, uses the replacing paths
of a consecutive subcomb. Each such path avoids the earlier cut centre
and has an end in the tail region. Following it from that end keeps every
vertex in the region. This proves that its entire induced subgraph can
be retained inside the last block.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09

/-- A connected subgraph avoiding the cut and meeting its avoidance
region lies wholly in that region. Reachability from the last vertex
extends along each path in the subgraph. -/
theorem connected_subgraph_subset_vertexAvoidanceRegion {α β : Type*}
    {G K : Graph α β} (hKG : K ≤ G) (hconn : GraphConnected K)
    {last cut a : α} (haK : a ∈ V(K))
    (ha : a ∈ vertexAvoidanceRegion G last cut) (hcut : cut ∉ V(K)) :
    V(K) ⊆ vertexAvoidanceRegion G last cut := by
  intro x hx
  have hr := hconn.2 a haK x hx
  have hrDel : ReflTransGen (G.deleteVerts {cut}).Adj a x := by
    apply ReflTransGen.mono ?_ a x hr
    intro y z hyz
    obtain ⟨e, he⟩ := hyz
    exact ⟨e, (G.deleteVerts_isLink {cut}).mpr ⟨he.mono hKG,
      fun hy ↦ hcut (hy ▸ he.left_mem), fun hz ↦ hcut (hz ▸ he.right_mem)⟩⟩
  refine ⟨?_, ha.2.trans hrDel⟩
  rw [vertexSet_deleteVerts]
  exact ⟨hKG.vertexSet_mono hx, fun h ↦ hcut (h ▸ hx)⟩

/-- A replacing path avoiding the cut lies in the region containing its
initial end. This is the path restriction used for the tail comb. -/
theorem path_subset_vertexAvoidanceRegion {α β : Type*} {G P : Graph α β}
    {a b last cut : α} (hP : IsGraphPathWithEnds G P a b)
    (ha : a ∈ vertexAvoidanceRegion G last cut) (hcut : cut ∉ V(P)) :
    V(P) ⊆ vertexAvoidanceRegion G last cut :=
  connected_subgraph_subset_vertexAvoidanceRegion hP.le
    (graphConnected_of_isGraphPath hP) hP.left_mem ha hcut

end GraphMinor.GM01
