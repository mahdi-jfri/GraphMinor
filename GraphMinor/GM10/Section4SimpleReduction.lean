module

public import GraphMinor.GM10.Section4LocalReductions
public import GraphMinor.Minor.Basic
import GraphMinor.GM01.Basic
import GraphMinor.GM10.Section7SimpleMinor

/-!
# The active simple graph in the width-two induction

For Graph Minors X, (4.2)(iii), page 165, Dirac's theorem is applied after
loops and parallel edges are removed. We also omit isolated vertices.
The resulting simple graph is a minor of the original graph. At each
of its vertices, its number of neighbours bounds the number of incident
edges in the original simple graph.
-/

@[expose] public section

namespace GraphMinor.GM10

open Graph Hypergraph SimpleGraph Classical

universe u v

/-- The simple graph on the nonisolated vertices of a loopless graph,
used in the induction for Graph Minors X, (4.2)(iii), page 165. -/
def nonisolatedSimpleGraph {α : Type u} {β : Type v} (G : Graph α β) [G.Loopless] :
    SimpleGraph {x : α // ∃ e, G.Inc e x} where
  Adj x y := G.Adj x.val y.val
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun x h ↦ G.not_adj_self x.val h⟩

/-- Omitting isolated vertices from the underlying simple graph gives
an isomorphic minor of the original graph. -/
theorem nonisolatedSimpleGraph_isIsoMinor
    {α : Type u} {β : Type v} (G : Graph α β) [G.Loopless]
    (hV : V(G).Finite) :
    IsIsoMinor (Graph.ofSimpleGraph (nonisolatedSimpleGraph G)) G := by
  classical
  let A := {x : α // ∃ e, G.Inc e x}
  have hactive : {x : α | ∃ e, G.Inc e x}.Finite :=
    hV.subset (fun x ⟨e, he⟩ ↦ he.vertex_mem)
  let : Fintype A := hactive.fintype
  let : Fintype V(G) := hV.fintype
  let j : A → V(G) := fun x ↦ ⟨x.val, x.property.choose_spec.vertex_mem⟩
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : V(G) ↦ z.val) hxy)
  let Γ := SimpleGraph.toSubgraph G.toSimpleGraph le_top
  let K := fun x : A ↦ (GM01.Path.singleton (j x)).toSubgraph
  have hm : IsIsoMinor (Graph.ofSimpleGraph (nonisolatedSimpleGraph G)) (GM01.toGraph Γ) := by
    apply GM01.isIsoMinor_ofSimpleGraph_of_connected_subgraphs
      (nonisolatedSimpleGraph G) (Set.toFinite Γ.verts) K
    · intro x
      refine ⟨fun _ _ ↦ trivial, fun a b hab ↦ ?_⟩
      have : ¬ (GM01.Path.singleton (j x)).toSubgraph.Adj a b := by
        simp [GM01.Path.singleton, GM01.Path.toSubgraph]
      exact (this hab).elim
    · intro x
      exact (GM01.Path.singleton _).connected_toSubgraph
    · intro x y hxy
      change Disjoint (GM01.Path.singleton (j x)).verts (GM01.Path.singleton (j y)).verts
      rw [GM01.Path.singleton_verts, GM01.Path.singleton_verts, Set.disjoint_singleton]
      exact hj.ne hxy
    · intro x y hxy
      refine ⟨j x, ?_, j y, ?_, ?_⟩
      · change j x ∈ (GM01.Path.singleton (j x)).verts
        simp
      · change j y ∈ (GM01.Path.singleton (j y)).verts
        simp
      · have hgxy : G.Adj x.val y.val := hxy
        exact ⟨fun h ↦ hgxy.ne (congrArg (fun z : V(G) ↦ z.val) h), hgxy⟩
  rw [← GM01.ofSimpleGraph_eq_toGraph] at hm
  exact hm.trans (isIsoMinor_ofSimpleGraph_toSimpleGraph G)

/-- In a simple graph, different incident edges give different neighbours
in the active simple graph. -/
theorem ncard_incident_edges_le_nonisolated_neighbors
    {α : Type u} {β : Type v} (G : Graph α β) [G.Simple]
    (hV : V(G).Finite) (x : {x : α // ∃ e, G.Inc e x}) :
    {e ∈ E(G) | G.Inc e x.val}.ncard ≤
      ((nonisolatedSimpleGraph G).neighborSet x).ncard := by
  classical
  have hactive : {y : α | ∃ e, G.Inc e y}.Finite :=
    hV.subset (fun y ⟨e, he⟩ ↦ he.vertex_mem)
  let : Fintype {y : α // ∃ e, G.Inc e y} := hactive.fintype
  let f : β → {y : α // ∃ e, G.Inc e y} := fun e ↦
    if h : G.Inc e x.val then ⟨h.other, e, h.inc_other⟩ else x
  have hlink : ∀ e, G.Inc e x.val → G.IsLink e x.val (f e).val := by
    intro e he
    simpa only [f, he, ↓reduceDIte] using he.isLink_other
  apply Set.ncard_le_ncard_of_injOn f ?_ ?_ (Set.toFinite _)
  · intro e he
    exact (hlink e he.2).adj
  · intro e he d hd hed
    have hl : G.IsLink d x.val (f e).val := by
      rw [hed]
      exact hlink d hd.2
    exact (hlink e he.2).eq hl

/-- A vertex with at most two neighbours in the active simple graph
provides the local reduction in the proof of Graph Minors X, (4.2)(iii). -/
theorem exists_smaller_minor_at_small_neighbor_set
    {α : Type u} {β : Type v} (G : Graph α β) [G.Simple]
    (hV : V(G).Finite) (hE : E(G).Finite) (hcard : 2 ≤ E(G).ncard)
    (x : {x : α // ∃ e, G.Inc e x})
    (hx : ((nonisolatedSimpleGraph G).neighborSet x).ncard ≤ 2) :
    ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
      IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
        (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
          branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) :=
  exists_smaller_minor_at_low_valency G hV hE hcard x.val x.property
    ((ncard_incident_edges_le_nonisolated_neighbors G hV x).trans hx)

end GraphMinor.GM10
