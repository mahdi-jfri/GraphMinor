module

public import GraphMinor.Minor.Model
import Mathlib.Combinatorics.Graph.Delete

/-!
# Regions beyond a deleted vertex

Graph Minors I, page 55, defines the regions `R_j` by paths to the last
spine vertex avoiding a chosen spine vertex. We use reachability in the
graph with that vertex deleted. A region is closed under adjacency away
from the deleted vertex. If another cut vertex lies outside it, the
region is contained in the region obtained by deleting that other vertex.
These elementary facts support the block decomposition for (1.1).
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph Relation

/-- The vertices joined to `last` while avoiding `cut`, as in the regions
on page 55 of Graph Minors I. -/
def vertexAvoidanceRegion {α β : Type*} (G : Graph α β) (last cut : α) : Set α :=
  {x | x ∈ V(G.deleteVerts {cut}) ∧
    ReflTransGen (G.deleteVerts {cut}).Adj last x}

/-- Every vertex in the region lies in the graph and differs from the
vertex that was deleted. -/
theorem vertexAvoidanceRegion_subset {α β : Type*} (G : Graph α β) (last cut : α) :
    vertexAvoidanceRegion G last cut ⊆ V(G) \ {cut} := by
  intro x hx
  exact (G.vertexSet_deleteVerts {cut}) ▸ hx.1

/-- The last vertex belongs to its region whenever it is not deleted. -/
theorem last_mem_vertexAvoidanceRegion {α β : Type*} {G : Graph α β}
    {last cut : α} (hlast : last ∈ V(G)) (hne : last ≠ cut) :
    last ∈ vertexAvoidanceRegion G last cut := by
  refine ⟨?_, .refl⟩
  rw [vertexSet_deleteVerts]
  exact ⟨hlast, hne⟩

/-- An edge can leave a region only through its deleted vertex. -/
theorem vertexAvoidanceRegion_adj_closed {α β : Type*} {G : Graph α β}
    {last cut x y : α} (hx : x ∈ vertexAvoidanceRegion G last cut)
    (hxy : G.Adj x y) (hy : y ≠ cut) :
    y ∈ vertexAvoidanceRegion G last cut := by
  obtain ⟨e, he⟩ := hxy
  have hxne : x ≠ cut := (vertexAvoidanceRegion_subset G last cut hx).2
  have hlink := (G.deleteVerts_isLink {cut}).mpr ⟨he, hxne, hy⟩
  exact ⟨hlink.right_mem, hx.2.tail ⟨e, hlink⟩⟩

/-- A region avoiding `cut` is contained in the region avoiding any vertex
outside it. This will give the nested regions along the subdivided spine
once the order of its cut vertices is established. -/
theorem vertexAvoidanceRegion_subset_of_not_mem {α β : Type*} {G : Graph α β}
    {last cut other : α} (hlast : last ∈ V(G)) (hne : last ≠ cut)
    (hother : other ∉ vertexAvoidanceRegion G last cut) :
    vertexAvoidanceRegion G last cut ⊆ vertexAvoidanceRegion G last other := by
  have hstart := last_mem_vertexAvoidanceRegion hlast hne
  have lift : ∀ {x : α}, ReflTransGen (G.deleteVerts {cut}).Adj last x →
      x ∈ vertexAvoidanceRegion G last cut ∧
      ReflTransGen (G.deleteVerts {other}).Adj last x := by
    intro x hr
    induction hr with
    | refl => exact ⟨hstart, .refl⟩
    | tail hr hstep ih =>
      obtain ⟨e, he⟩ := hstep
      have hx := vertexAvoidanceRegion_adj_closed ih.1
        ⟨e, he.mono Graph.deleteVerts_le⟩
        (by
          have hmem := he.right_mem
          rw [vertexSet_deleteVerts] at hmem
          exact hmem.2)
      have hprevne : _ ≠ other := fun h ↦ hother (h ▸ ih.1)
      have hxne : _ ≠ other := fun h ↦ hother (h ▸ hx)
      have hlink := (G.deleteVerts_isLink {other}).mpr
        ⟨he.mono Graph.deleteVerts_le, hprevne, hxne⟩
      exact ⟨hx, ih.2.tail ⟨e, hlink⟩⟩
  intro x hx
  have hxlift := lift hx.2
  refine ⟨?_, hxlift.2⟩
  rw [vertexSet_deleteVerts]
  exact ⟨(vertexAvoidanceRegion_subset G last cut hx).1,
    fun heq ↦ hother (heq ▸ hx)⟩

/-- Each nonempty avoidance region induces a connected subgraph. Paths
from the last vertex remain inside the region because every prefix
still avoids the cut vertex. -/
theorem vertexAvoidanceRegion_connected {α β : Type*} {G : Graph α β}
    {last cut : α} (hlast : last ∈ V(G)) (hne : last ≠ cut) :
    GraphConnected (G.induce (vertexAvoidanceRegion G last cut)) := by
  have hstart := last_mem_vertexAvoidanceRegion hlast hne
  have lift : ∀ {x : α}, ReflTransGen (G.deleteVerts {cut}).Adj last x →
      x ∈ vertexAvoidanceRegion G last cut ∧
      ReflTransGen (G.induce (vertexAvoidanceRegion G last cut)).Adj last x := by
    intro x hr
    induction hr with
    | refl => exact ⟨hstart, .refl⟩
    | tail hr hstep ih =>
      obtain ⟨e, he⟩ := hstep
      have hx := vertexAvoidanceRegion_adj_closed ih.1
        ⟨e, he.mono Graph.deleteVerts_le⟩
        (by
          have hmem := he.right_mem
          rw [vertexSet_deleteVerts] at hmem
          exact hmem.2)
      exact ⟨hx, ih.2.tail ⟨e, he.mono Graph.deleteVerts_le, ih.1, hx⟩⟩
  refine ⟨⟨last, hstart⟩, ?_⟩
  intro x hx y hy
  exact (Std.Symm.symm _ _ (lift hx.2).2).trans (lift hy.2).2

end GraphMinor.GM01
