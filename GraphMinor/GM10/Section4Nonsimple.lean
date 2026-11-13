module

public import GraphMinor.GM10.Section4LocalReductions

/-!
# Removing loops and parallel edges in the width-two induction

Before applying Dirac's theorem in Graph Minors X, (4.2)(iii), page 165,
we reduce a nonsimple graph. Deleting a loop or one of two parallel
edges gives a smaller minor. The edge-restoration lemmas prove that the
bound two is preserved when the deleted edge is put back.
-/

public section

namespace GraphMinor.GM10

open Graph Hypergraph Classical

universe u v

/-- A deletable edge with private or shared ends gives a smaller minor
whose branch-width bound two lifts back to the original graph. -/
theorem exists_smaller_minor_of_private_ends
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) {d e : β}
    (hd : d ∈ E(G)) (he : e ∈ E(G)) (hed : e ≠ d)
    (hattach : ∀ x, G.Inc d x → G.Inc e x ∨ ∀ a, G.Inc a x → a = d) :
    ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
      IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
        (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
          branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) := by
  let H := G.deleteEdges {d}
  have hVH : V(H).Finite := hV
  have hEH : E(H).Finite := hE.subset Set.sdiff_subset
  have hlt : E(H).ncard < E(G).ncard := by
    apply Set.ncard_lt_ncard ?_ hE
    exact ⟨Set.sdiff_subset, fun h ↦ (h hd).2 (Set.mem_singleton d)⟩
  refine ⟨H, hVH, hEH, isIsoMinor_of_le Graph.deleteEdges_le, hlt, ?_⟩
  intro hw
  let G₀ := Hypergraph.ofGraph G hV hE
  have hγG : 1 ≤ maxEdgeSize G₀ := one_le_maxEdgeSize_ofGraph ⟨d, hd⟩
  have heH : e ∈ E(H) := ⟨he, hed⟩
  have hγH : 1 ≤ maxEdgeSize (G₀.deleteEdges {d}) := by
    rw [← ofGraph_deleteEdges G hV hE {d}]
    exact one_le_maxEdgeSize_ofGraph ⟨e, heH⟩
  rw [ofGraph_deleteEdges G hV hE {d}] at hw
  exact branchWidth_le_of_delete_edge_with_private_ends he hed hattach hγG hγH
    (maxEdgeSize_ofGraph_le_two G hV hE) hw

/-- A loop can be deleted in the induction for Graph Minors X, (4.2)(iii).
An isolated loop is grouped with any surviving edge. -/
theorem exists_smaller_minor_of_loop
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (hcard : 2 ≤ E(G).ncard)
    {d : β} {v : α} (hd : G.IsLoopAt d v) :
    ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
      IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
        (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
          branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) := by
  classical
  by_cases hex : ∃ e, G.Inc e v ∧ e ≠ d
  · obtain ⟨e, hev, hed⟩ := hex
    apply exists_smaller_minor_of_private_ends G hV hE hd.edge_mem hev.edge_mem hed
    intro x hdx
    have hxv : x = v := (hdx.eq_or_eq_of_isLink hd).elim id id
    exact Or.inl (hxv ▸ hev)
  · have hnt := (Set.one_lt_ncard_iff_nontrivial_and_finite).1 (show 1 < E(G).ncard by omega)
    obtain ⟨e, he, hed⟩ := hnt.1.exists_ne d
    apply exists_smaller_minor_of_private_ends G hV hE hd.edge_mem he hed
    intro x hdx
    have hxv : x = v := (hdx.eq_or_eq_of_isLink hd).elim id id
    subst x
    refine Or.inr (fun a hav ↦ ?_)
    by_contra had
    exact hex ⟨a, hav, had⟩

/-- Parallel edges can be reduced to one in the induction for Graph
Minors X, (4.2)(iii), page 165. -/
theorem exists_smaller_minor_of_parallel_edges
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite)
    {d e : β} {u v : α} (hd : G.IsLink d u v) (he : G.IsLink e u v) (hed : d ≠ e) :
    ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
      IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
        (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
          branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) := by
  apply exists_smaller_minor_of_private_ends G hV hE hd.edge_mem he.edge_mem hed.symm
  intro x hdx
  rcases hdx.eq_or_eq_of_isLink hd with rfl | rfl
  · exact Or.inl he.inc_left
  · exact Or.inl he.inc_right

/-- Every nonsimple graph with at least two edges has one of the loop
or parallel-edge reductions used in Graph Minors X, (4.2)(iii). -/
theorem exists_smaller_minor_of_not_simple
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (hcard : 2 ≤ E(G).ncard)
    (hsimple : ¬ G.Simple) :
    ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
      IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
        (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
          branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) := by
  classical
  by_cases hl : G.Loopless
  · have hex : ∃ d e u v, G.IsLink d u v ∧ G.IsLink e u v ∧ d ≠ e := by
      by_contra hn
      apply hsimple
      refine { toLoopless := hl, eq_of_isLink := ?_ }
      intro d e u v hd he
      by_contra hde
      exact hn ⟨d, e, u, v, hd, he, hde⟩
    obtain ⟨d, e, u, v, hd, he, hde⟩ := hex
    exact exists_smaller_minor_of_parallel_edges G hV hE hd he hde
  · have hex : ∃ d v, G.IsLoopAt d v := by
      by_contra! hn
      exact hl ⟨hn⟩
    obtain ⟨d, v, hd⟩ := hex
    exact exists_smaller_minor_of_loop G hV hE hcard hd

end GraphMinor.GM10
