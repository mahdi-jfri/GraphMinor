module

public import GraphMinor.GM02.Section4Suppression

/-!
# Deleting loops: Graph Minors II, (4.2) and (4.3)

Graph Minors II, page 318, says "The following two results are clear." Both
are about a loop `e` of `G` at a vertex `v` of `H`.

For (4.2), no loop of `H` is at `v`. A suppression never removes a loop, so if
`e` lies in the subgraph we start from, then `e` is still a loop at `v` at the
end, and the isomorphism gives a loop of `H` at `v`. Hence the subgraph avoids
`e`, and lies in `G \ e`.

For (4.3), `H` has a loop `f` at `v`. In one direction, if the subgraph avoids
`e`, we pass to the subgraph that gives `H \ f`. If it contains `e`, we delete
`e` throughout the sequence and use `e` in place of the loop that represents
`f`. In the other direction we add `e` to the subgraph and let it represent
`f`. To add `e` safely, we first rename edges so that no suppression creates
an edge named `e`.
-/

public section

namespace GraphMinor.GM02

open Graph Set Relation

universe u v

variable {α : Type u} {β : Type v}

/-- Graph Minors II, (4.2), page 318:
"*If $V(H) \subseteq V(G)$ and $e$ is a loop of $G$ incident with $v \in V(H)$, and
no loop of $H$ is incident with $v$, then $G$ topologically contains $H$ if and only
if $G \setminus e$ does.*"

The paper says this is clear. The hypotheses `V(H) ⊆ V(G)` and `v ∈ V(H)` are
not needed in the proof. -/
theorem theorem_4_2_proof {G H : Graph α β} {e : β} {v : α} (_hVH : V(H) ⊆ V(G))
    (he : G.IsLoopAt e v) (_hv : v ∈ V(H)) (hH : ∀ f, ¬ H.IsLoopAt f v) :
    TopologicallyContains G H ↔ TopologicallyContains (G.deleteEdges {e}) H := by
  constructor
  · intro h
    obtain ⟨K, hK, L, hs, σ, hV, hbij, hlink⟩ := topologicallyContains_iff_isoFix.1 h
    by_cases heK : e ∈ E(K)
    · -- The loop `e` survives in `L`, so `H` has a loop at `v`.
      have hKe : K.IsLoopAt e v := (Graph.IsSubgraph.isLink_iff hK heK).2 he
      have hLe : L.IsLoopAt e v := isLoopAt_of_reflTransGen hs hKe
      obtain ⟨f, hf, hfe⟩ := hbij.surjOn hLe.edge_mem
      have hfv : H.IsLoopAt f v := (hlink f hf v v).2 (hfe ▸ hLe)
      exact (hH f hfv).elim
    · exact topologicallyContains_iff_isoFix.2
        ⟨K, le_deleteEdges_of_notMem hK heK, L, hs, σ, hV, hbij, hlink⟩
  · intro h
    exact h.mono Graph.deleteEdges_le

/-- The graph `K` with the loop `e` of `G` added back. -/
private theorem exists_add_loop {G K : Graph α β} {e : β} {v : α} (hK : K ≤ G.deleteEdges {e})
    (he : G.IsLoopAt e v) (hv : v ∈ V(K)) :
    ∃ N ≤ G, N.IsLoopAt e v ∧ N.deleteEdges {e} = K := by
  have hKG : K ≤ G := hK.trans Graph.deleteEdges_le
  have heK : e ∉ E(K) := fun h => ((hK.isLink_mono (K.exists_isLink_of_mem_edgeSet h).choose_spec.choose_spec).2
    (Set.mem_singleton_iff.2 rfl))
  let N : Graph α β := (G.induce V(K)).restrict (insert e E(K))
  have hN : ∀ g a b, N.IsLink g a b ↔ g ∈ insert e E(K) ∧ G.IsLink g a b ∧ a ∈ V(K) ∧ b ∈ V(K) :=
    fun _ _ _ => Iff.rfl
  refine ⟨N, Graph.restrict_le.trans (Graph.induce_le hKG.vertexSet_mono), ?_, ?_⟩
  · exact (hN e v v).2 ⟨Or.inl rfl, he, hv, hv⟩
  · refine Graph.ext rfl fun g a b => ?_
    change N.IsLink g a b ∧ g ∉ ({e} : Set β) ↔ K.IsLink g a b
    rw [hN]
    constructor
    · rintro ⟨⟨hg | hg, hl, -, -⟩, hge⟩
      · exact (hge (Set.mem_singleton_iff.2 hg)).elim
      · exact (Graph.IsSubgraph.isLink_iff hKG hg).2 hl
    · intro hl
      refine ⟨⟨Or.inr hl.edge_mem, hl.mono hKG, hl.left_mem, hl.right_mem⟩, fun h => heK ?_⟩
      rw [← Set.mem_singleton_iff.1 h]
      exact hl.edge_mem

/-- Graph Minors II, (4.3), page 318:
"*If $V(H) \subseteq V(G)$, and $e$ is a loop of $G$ and $f$ is a loop of $H$, both
incident with the same vertex, then $G$ topologically contains $H$ if and only if
$G \setminus e$ topologically contains $H \setminus f$.*"

The paper says this is clear. The hypothesis `V(H) ⊆ V(G)` is not needed in the
proof. -/
theorem theorem_4_3_proof {G H : Graph α β} {e f : β} {v : α} (_hVH : V(H) ⊆ V(G))
    (he : G.IsLoopAt e v) (hf : H.IsLoopAt f v) :
    TopologicallyContains G H ↔
      TopologicallyContains (G.deleteEdges {e}) (H.deleteEdges {f}) := by
  constructor
  · intro h
    obtain ⟨K, hK, L, hs, σ, hσ⟩ := topologicallyContains_iff_isoFix.1 h
    have hLf : L.IsLoopAt (σ f) v := (hσ.2.2 f hf.edge_mem v v).1 hf
    have hdel := hσ.deleteEdges hf.edge_mem
    by_cases heK : e ∈ E(K)
    · -- Delete `e` throughout. In `L` it is a second loop at `v`.
      have hKe : K.IsLoopAt e v := (Graph.IsSubgraph.isLink_iff hK heK).2 he
      have hLe : L.IsLoopAt e v := isLoopAt_of_reflTransGen hs hKe
      refine topologicallyContains_iff_isoFix.2 ⟨K.deleteEdges {e},
        Graph.deleteEdges_mono_left hK {e}, L.deleteEdges {e},
        reflTransGen_deleteEdges_of_isLoopAt hs hKe, ?_⟩
      exact IsoFix.trans ⟨σ, hdel⟩ (isoFix_deleteEdges_loops hLe hLf)
    · -- The subgraph avoids `e`. Pass to the part that gives `L \ σ f`.
      obtain ⟨K', hK', hs'⟩ := exists_le_reflTransGen hs
        (Graph.deleteEdges_le (G := L) (F := {σ f}))
      exact topologicallyContains_iff_isoFix.2 ⟨K',
        hK'.trans (le_deleteEdges_of_notMem hK heK), _, hs', σ, hdel⟩
  · intro h
    obtain ⟨K, hK, L, hs, hiso⟩ := topologicallyContains_iff_isoFix.1 h
    have hvH : v ∈ V(H.deleteEdges {f}) := hf.vertex_mem
    have hvL : v ∈ V(L) := hiso.choose_spec.1 ▸ hvH
    -- Rename edges so that no suppression makes an edge named `e`.
    obtain ⟨L₀, hs₀, hiso₀⟩ := (IsoFix.refl K).exists_keep hs
    have hvL₀ : v ∈ V(L₀) := hiso₀.choose_spec.1 ▸ hvL
    have hvK : v ∈ V(K) := vertexSet_subset_of_reflTransGen hs hvL
    obtain ⟨N, hNG, hNe, hNK⟩ := exists_add_loop hK he hvK
    obtain ⟨L', hs', hL', hL'e⟩ := exists_lift_loop_of_keep hs₀ hNe hNK hvL₀
    obtain ⟨τ, hτ⟩ := hiso.trans hiso₀
    rw [← hL'] at hτ
    exact topologicallyContains_iff_isoFix.2 ⟨N, hNG, L', hs', hτ.extend_loop hf hL'e⟩

end GraphMinor.GM02
