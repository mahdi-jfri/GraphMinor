module

public import GraphMinor.GM01.VertexAvoidanceRegions

/-!
# Connected differences of avoidance regions

The blocks on page 55 of Graph Minors I are differences of regions
beyond consecutive pairs of spine cuts. A vertex outside the later
region can be reached from its cut without entering that region: follow
a path from the last vertex until it leaves the region. An edge leaving
it must pass through the cut. Keeping this argument inside the earlier
region proves that the difference is connected.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation

/-- The difference of two avoidance regions is connected when the second
cut belongs to the first region. This is the connected-block step needed
on page 55 of Graph Minors I. -/
theorem vertexAvoidanceRegion_diff_connected {α β : Type*} {G : Graph α β}
    {last cut next : α} (hlast : last ∈ V(G)) (hne : last ≠ cut)
    (hnext : next ∈ vertexAvoidanceRegion G last cut) :
    GraphConnected (G.induce
      (vertexAvoidanceRegion G last cut \ vertexAvoidanceRegion G last next)) := by
  let A := vertexAvoidanceRegion G last cut
  let B := vertexAvoidanceRegion G last next
  have hstart : last ∈ A := last_mem_vertexAvoidanceRegion hlast hne
  have hnextnot : next ∉ B := by
    intro h
    exact (vertexAvoidanceRegion_subset G last next h).2 rfl
  have lift : ∀ {x : α}, ReflTransGen (G.deleteVerts {cut}).Adj last x →
      x ∈ A ∧ (x ∉ B → ReflTransGen (G.induce (A \ B)).Adj next x) := by
    intro x hr
    induction hr with
    | refl =>
      refine ⟨hstart, ?_⟩
      intro hnot
      have heq : last = next := by
        by_contra hne'
        exact hnot (last_mem_vertexAvoidanceRegion hlast hne')
      subst next
      exact .refl
    | @tail x y hr hstep ih =>
      obtain ⟨e, he⟩ := hstep
      have hxy : G.Adj x y := ⟨e, he.mono Graph.deleteVerts_le⟩
      have hycut : y ≠ cut := by
        have hmem := he.right_mem
        rw [vertexSet_deleteVerts] at hmem
        exact hmem.2
      have hyA : y ∈ A := vertexAvoidanceRegion_adj_closed ih.1 hxy hycut
      refine ⟨hyA, ?_⟩
      intro hyB
      by_cases hxB : x ∈ B
      · have heq : y = next := by
          by_contra hne'
          exact hyB (vertexAvoidanceRegion_adj_closed hxB hxy hne')
        subst y
        exact .refl
      · exact (ih.2 hxB).tail ⟨e, he.mono Graph.deleteVerts_le,
          ⟨ih.1, hxB⟩, ⟨hyA, hyB⟩⟩
  refine ⟨⟨next, hnext, hnextnot⟩, ?_⟩
  intro x hx y hy
  exact (Std.Symm.symm _ _ ((lift hx.1.2).2 hx.2)).trans ((lift hy.1.2).2 hy.2)

/-- The first block is the complement of an avoidance region. In a
connected graph it is connected and contains the cut vertex. When a path
leaves the region, its first vertex outside must be that cut vertex. -/
theorem vertexAvoidanceRegion_compl_connected {α β : Type*} {G : Graph α β}
    (hconn : GraphConnected G) (last cut : α) (hcut : cut ∈ V(G)) :
    GraphConnected (G.induce (V(G) \ vertexAvoidanceRegion G last cut)) := by
  let B := vertexAvoidanceRegion G last cut
  have hcutnot : cut ∉ B := by
    intro h
    exact (vertexAvoidanceRegion_subset G last cut h).2 rfl
  have lift : ∀ {x : α}, ReflTransGen G.Adj cut x →
      x ∈ V(G) ∧ (x ∉ B → ReflTransGen (G.induce (V(G) \ B)).Adj cut x) := by
    intro x hr
    induction hr with
    | refl => exact ⟨hcut, fun _ ↦ .refl⟩
    | @tail x y hr hstep ih =>
      obtain ⟨e, he⟩ := hstep
      refine ⟨he.right_mem, ?_⟩
      intro hyB
      by_cases hxB : x ∈ B
      · have heq : y = cut := by
          by_contra hne
          exact hyB (vertexAvoidanceRegion_adj_closed hxB ⟨e, he⟩ hne)
        subst y
        exact .refl
      · exact (ih.2 hxB).tail ⟨e, he, ⟨ih.1, hxB⟩, ⟨he.right_mem, hyB⟩⟩
  refine ⟨⟨cut, hcut, hcutnot⟩, ?_⟩
  intro x hx y hy
  have hxreach := (lift (hconn.2 cut hcut x hx.1)).2 hx.2
  have hyreach := (lift (hconn.2 cut hcut y hy.1)).2 hy.2
  exact (Std.Symm.symm _ _ hxreach).trans hyreach

end GraphMinor.GM01
