module

public import GraphMinor.GM10.Section4K4
import GraphMinor.GM10.DiracAttachments
import GraphMinor.GM10.DiracModel
import GraphMinor.GM01.Basic

/-!
# The low-valency theorem used in Graph Minors X, (4.2)

We prove the external assertion used in the induction on page 165:
a nonempty finite simple graph without a `K₄` minor has a vertex with
at most two neighbours. The proof uses the maximal-component cycle
argument of Illingworth and Wood, Theorem 7, page 450, rather than
assuming a citation. Only the weaker minor conclusion needed here is
proved. Disconnected graphs are handled in one connected component.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph Classical

universe u

private theorem isIsoMinor_ofSimpleGraph_induce
    {V : Type u} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    IsIsoMinor (Graph.ofSimpleGraph (G.induce S)) (Graph.ofSimpleGraph G) := by
  classical
  let Γ := SimpleGraph.toSubgraph G le_top
  let K := fun x : S ↦ (GM01.Path.singleton x.val).toSubgraph
  rw [GM01.ofSimpleGraph_eq_toGraph G]
  apply GM01.isIsoMinor_ofSimpleGraph_of_connected_subgraphs
    (G.induce S) (Set.toFinite Γ.verts) K
  · intro x
    refine ⟨fun _ _ ↦ trivial, fun a b hab ↦ ?_⟩
    have : ¬ (GM01.Path.singleton x.val).toSubgraph.Adj a b := by
      simp [GM01.Path.singleton, GM01.Path.toSubgraph]
    exact (this hab).elim
  · intro x
    exact (GM01.Path.singleton _).connected_toSubgraph
  · intro x y hxy
    change Disjoint (GM01.Path.singleton x.val).verts (GM01.Path.singleton y.val).verts
    rw [GM01.Path.singleton_verts, GM01.Path.singleton_verts, Set.disjoint_singleton]
    exact Subtype.val_injective.ne hxy
  · intro x y hxy
    refine ⟨x.val, ?_, y.val, ?_, hxy⟩
    · change x.val ∈ (GM01.Path.singleton x.val).verts
      simp
    · change y.val ∈ (GM01.Path.singleton y.val).verts
      simp

/-- A finite connected simple graph with at least three neighbours at
every vertex has a `K₄` minor. This proves the external input to X (4.2)
by the maximal-component cycle argument. -/
theorem isIsoMinor_completeGraphGraph_four_of_three_le_neighbors
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hconn : G.Connected)
    (hdeg : ∀ x, 3 ≤ (G.neighborSet x).ncard) :
    IsIsoMinor (completeGraphGraph 4) (Graph.ofSimpleGraph G) := by
  obtain ⟨H, z, p, hH, hp, havoid, hzH, x, y, hxy, hxz, hyz, hx, hy, hxH, hyH⟩ :=
    exists_cycle_with_three_attachments G hconn hdeg
  exact isIsoMinor_completeGraphGraph_four_of_cycle_attachments G H hH p hp havoid hzH
    hxy hxz hyz hx hy hxH hyH

/-- The external low-valency theorem cited in Graph Minors X, proof of
(4.2)(iii), page 165, with its hypotheses proved rather than assumed:
a nonempty finite simple graph with no `K₄` minor has a vertex with at
most two neighbours. -/
theorem exists_small_neighbor_set_of_not_completeGraphGraph_four_minor
    {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hno : ¬ IsIsoMinor (completeGraphGraph 4) (Graph.ofSimpleGraph G)) :
    ∃ x, (G.neighborSet x).ncard ≤ 2 := by
  classical
  by_contra! hbad
  have hdeg : ∀ x, 3 ≤ (G.neighborSet x).ncard := fun x ↦ by
    have := hbad x
    omega
  obtain ⟨a⟩ := ‹Nonempty V›
  let C := G.connectedComponentMk a
  let : Fintype C := Fintype.ofFinite C
  have hdegC : ∀ x : C, 3 ≤ (C.toSimpleGraph.neighborSet x).ncard := by
    intro x
    have heq : Subtype.val '' C.toSimpleGraph.neighborSet x = G.neighborSet x.val := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hxy
        have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxy
        exact ⟨⟨y, hyC⟩, hxy, rfl⟩
    have hcard := congrArg Set.ncard heq
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hcard
    rw [hcard]
    exact hdeg x.val
  have hminorC := isIsoMinor_completeGraphGraph_four_of_three_le_neighbors C.toSimpleGraph
    C.connected_toSimpleGraph hdegC
  exact hno (hminorC.trans (isIsoMinor_ofSimpleGraph_induce G C.supp))

end GraphMinor.GM10
