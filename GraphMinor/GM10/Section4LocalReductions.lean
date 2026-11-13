module

public import GraphMinor.GM10.Section4Series

/-!
# Small-valency reductions for branch-width two

The induction in Graph Minors X, (4.2)(iii), page 165, removes a vertex
of valency at most two. This file proves the edge-deletion case for a
vertex of valency one and packages the local finite-graph reductions.
-/

public section

namespace GraphMinor.GM10

open Graph Hypergraph Classical

universe u v

/-- Viewing a finite graph as a hypergraph commutes with deleting edges. -/
theorem ofGraph_deleteEdges {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (F : Set β) :
    Hypergraph.ofGraph (G.deleteEdges F) hV (hE.subset Set.sdiff_subset) =
      (Hypergraph.ofGraph G hV hE).deleteEdges F := by
  apply Hypergraph.ext
  · rfl
  · rfl
  · funext e x
    exact propext Graph.deleteEdges_inc

/-- A finite graph, viewed as a hypergraph, has maximum edge size at most two. -/
theorem maxEdgeSize_ofGraph_le_two {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    maxEdgeSize (Hypergraph.ofGraph G hV hE) ≤ 2 :=
  maxEdgeSize_le_iff.2 (fun e _ ↦ edgeSize_ofGraph_le_two G hV hE e)

/-- Restoring an edge at a vertex of valency one preserves the bound two.
If it is an isolated edge, it is grouped with any surviving edge. -/
theorem branchWidth_le_two_of_delete_leaf_edge
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) {d : β} {v u : α}
    (hd : G.IsLink d v u) (honly : ∀ a, G.Inc a v → a = d)
    (hcard : 2 ≤ E(G).ncard)
    (hw : branchWidth (Hypergraph.ofGraph (G.deleteEdges {d}) hV
      (hE.subset Set.sdiff_subset)) ≤ 2) :
    branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 := by
  classical
  let G₀ := Hypergraph.ofGraph G hV hE
  have he_other : ∃ e ∈ E(G), e ≠ d := by
    have hnt := (Set.one_lt_ncard_iff_nontrivial_and_finite).1 (show 1 < E(G).ncard by omega)
    exact hnt.1.exists_ne d
  have hchoice : ∃ e ∈ E(G), e ≠ d ∧
      ∀ x, G.Inc d x → G.Inc e x ∨ ∀ a, G.Inc a x → a = d := by
    by_cases hex : ∃ e, G.Inc e u ∧ e ≠ d
    · obtain ⟨e, heu, hed⟩ := hex
      refine ⟨e, heu.edge_mem, hed, ?_⟩
      intro x hdx
      rcases hdx.eq_or_eq_of_isLink hd with rfl | rfl
      · exact Or.inr honly
      · exact Or.inl heu
    · obtain ⟨e, he, hed⟩ := he_other
      refine ⟨e, he, hed, ?_⟩
      intro x hdx
      rcases hdx.eq_or_eq_of_isLink hd with rfl | rfl
      · exact Or.inr honly
      · refine Or.inr (fun a hau ↦ ?_)
        by_contra had
        exact hex ⟨a, hau, had⟩
  obtain ⟨e, he, hed, hattach⟩ := hchoice
  have hγG : 1 ≤ maxEdgeSize G₀ := one_le_maxEdgeSize_ofGraph ⟨d, hd.edge_mem⟩
  have heH : e ∈ E(G.deleteEdges {d}) := ⟨he, hed⟩
  have hγH : 1 ≤ maxEdgeSize (G₀.deleteEdges {d}) := by
    rw [← ofGraph_deleteEdges G hV hE {d}]
    exact one_le_maxEdgeSize_ofGraph ⟨e, heH⟩
  rw [ofGraph_deleteEdges G hV hE {d}] at hw
  exact branchWidth_le_of_delete_edge_with_private_ends he hed hattach hγG hγH
    (maxEdgeSize_ofGraph_le_two G hV hE) hw

private theorem edge_card_sdiff_singleton_lt
    {α : Type u} {β : Type v} {G : Graph α β} (hE : E(G).Finite)
    {d : β} (hd : d ∈ E(G)) : (E(G) \ {d}).ncard < E(G).ncard := by
  apply Set.ncard_lt_ncard ?_ hE
  refine ⟨Set.sdiff_subset, ?_⟩
  intro h
  exact (h hd).2 (Set.mem_singleton d)

/-- At a nonisolated vertex incident with at most two edges in a loopless
graph, the induction for Graph Minors X, (4.2)(iii), reduces the number
of edges. Restoring the deleted edge or suppressed vertex preserves the
bound two. All minor and restoration properties are conclusions. -/
theorem exists_smaller_minor_at_low_valency
    {α : Type u} {β : Type v} (G : Graph α β) [G.Loopless]
    (hV : V(G).Finite) (hE : E(G).Finite) (hcard : 2 ≤ E(G).ncard)
    (v : α) (hactive : ∃ d, G.Inc d v)
    (hdeg : {a ∈ E(G) | G.Inc a v}.ncard ≤ 2) :
    ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
      IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
        (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
          branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) := by
  classical
  obtain ⟨d, hdv⟩ := hactive
  obtain ⟨u, hdu⟩ := hdv
  by_cases hex : ∃ e, G.Inc e v ∧ d ≠ e
  · obtain ⟨e, hev, hed⟩ := hex
    have hsub : ({d, e} : Set β) ⊆ {a ∈ E(G) | G.Inc a v} := by
      rintro a (rfl | rfl)
      · exact ⟨hdu.edge_mem, hdu.inc_left⟩
      · exact ⟨hev.edge_mem, hev⟩
    have heq : ({d, e} : Set β) = {a ∈ E(G) | G.Inc a v} :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hed]; exact hdeg)
        (hE.subset fun _ h ↦ h.1)
    have honly : ∀ a, G.Inc a v → a = d ∨ a = e := by
      intro a ha
      change a ∈ ({d, e} : Set β)
      rw [heq]
      exact ⟨ha.edge_mem, ha⟩
    let q : α → α := fun x ↦ if x = v then u else x
    let H := (G.map q).deleteEdges {d}
    have hVH : V(H).Finite := hV.image q
    have hEH : E(H).Finite := hE.subset Set.sdiff_subset
    have hminor : IsIsoMinor H G := isIsoMinor_contractSingleEdge hdu hdu.ne
    have hlt : E(H).ncard < E(G).ncard := edge_card_sdiff_singleton_lt hE hdu.edge_mem
    refine ⟨H, hVH, hEH, hminor, hlt, ?_⟩
    intro hw
    exact branchWidth_le_two_of_suppress_degree_two G H hV hE hVH hEH hdu.symm
      hdu.ne.symm hed hev honly rfl hw
  · have honly : ∀ a, G.Inc a v → a = d := by
      intro a ha
      by_contra had
      exact hex ⟨a, ha, fun h ↦ had h.symm⟩
    let H := G.deleteEdges {d}
    have hVH : V(H).Finite := hV
    have hEH : E(H).Finite := hE.subset Set.sdiff_subset
    refine ⟨H, hVH, hEH, isIsoMinor_of_le Graph.deleteEdges_le,
      edge_card_sdiff_singleton_lt hE hdu.edge_mem, ?_⟩
    intro hw
    exact branchWidth_le_two_of_delete_leaf_edge G hV hE hdu honly hcard hw

end GraphMinor.GM10
