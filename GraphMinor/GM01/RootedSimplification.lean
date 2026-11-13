module

public import GraphMinor.GM01.RootedGraphs
public import GraphMinor.GM01.SimpleEdgeSelection

/-!
# Lifting rooted models from the underlying simple graph

The proof of Graph Minors I, (1.1), uses rooted paths and trees while the
ambient graphs may have loops and parallel edges. Map each branch from
the vertex subtype back to the original vertex set and select an actual
edge for each simple edge. Injectivity of both maps preserves branch
disjointness and edge distinctness, and paths inside branches lift too.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- Give the underlying simple graph the same distinguished root. This
changes only edge data, as needed for the rooted proof of (1.1). -/
def RootedGraph.simplification {α β : Type*} (G : RootedGraph α β) :
    RootedGraph V(G.graph) (Sym2 V(G.graph)) :=
  ⟨Graph.ofSimpleGraph G.graph.toSimpleGraph, ⟨G.root, mem_univ _⟩⟩

/-- Lift a rooted model through simplification. Branches are images under
the subtype inclusion and each simple edge is represented by its chosen
original edge. -/
noncomputable def RootedMinorModel.of_simplification {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ}
    (M : RootedMinorModel H G.simplification) : RootedMinorModel H G := by
  classical
  let f := (exists_simpleGraph_edge_embedding G.graph).choose
  have hf := (exists_simpleGraph_edge_embedding G.graph).choose_spec
  refine
    { branch := fun x ↦ Subtype.val '' M.branch x
      branch_subset := ?_
      branch_disjoint := ?_
      branch_connected := ?_
      edgeMap := M.edgeMap.trans f
      edge_links := ?_
      root_mem := ⟨G.root, M.root_mem, rfl⟩ }
  · rintro x a ⟨b, _, rfl⟩
    exact b.property
  · intro x y hxy
    apply disjoint_left.mpr
    rintro a ⟨b, hb, hba⟩ ⟨c, hc, hca⟩
    have hbc : b = c := Subtype.ext (hba.trans hca.symm)
    subst c
    exact (disjoint_left.mp (M.branch_disjoint hxy)) hb hc
  · intro x
    obtain ⟨⟨a, ha⟩, hconn⟩ := M.branch_connected x
    refine ⟨⟨a.val, ⟨a, ha, rfl⟩⟩, ?_⟩
    rintro b ⟨b', hb, rfl⟩ c ⟨c', hc, rfl⟩
    have hr := hconn b' hb c' hc
    have lift_step : ∀ {p q : V(G.graph)},
        (G.simplification.graph.induce (M.branch x)).Adj p q →
        (G.graph.induce (Subtype.val '' M.branch x)).Adj p.val q.val := by
      intro p q hpq
      obtain ⟨e, he⟩ := hpq
      have hadj : G.graph.toSimpleGraph.Adj p q := by
        have hm := he.1.2
        rw [he.1.1] at hm
        exact hm
      obtain ⟨edge, hedge⟩ := hadj.2
      exact ⟨edge, hedge, ⟨p, he.2.1, rfl⟩, ⟨q, he.2.2, rfl⟩⟩
    induction hr with
    | refl => exact .refl
    | tail hr hstep ih =>
      obtain ⟨edge, hedge⟩ := hstep
      exact (ih hedge.2.1).tail (lift_step ⟨edge, hedge⟩)
  · intro e x y he
    obtain ⟨a, ha, b, hb, hab⟩ := M.edge_links e x y he
    refine ⟨a.val, ⟨a, ha, rfl⟩, b.val, ⟨b, hb, rfl⟩, ?_⟩
    exact (hf (M.edgeMap e) a b).mpr hab.1

/-- Any rooted minor represented in the underlying simple graph is also
represented in the original rooted graph. -/
theorem HasRootedMinor.of_simplification {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ}
    (h : HasRootedMinor H G.simplification) : HasRootedMinor H G := by
  obtain ⟨M⟩ := h
  exact ⟨M.of_simplification⟩

end GraphMinor.GM01
