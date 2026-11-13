module

public import GraphMinor.GM02.Section4Loops

/-!
# Removing the branch-vertex loops in algorithm (4.6)

Follow the first sentence of the proof on page 319. Delete a loop of
`G` incident with a vertex of `H`. If `H` has a loop there, delete one
of its loops too and use (4.3). Otherwise use (4.2). The number of edges
of `G` strictly decreases, so this process ends with no host loop at a
pattern vertex. Vertex labels and topological containment are preserved.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The loop-removal step in the proof of II (4.6), page 319, terminates without changing containment. -/
theorem exists_loop_elimination {α : Type u} {β : Type v} {G H : Graph α β}
    (hE : E(G).Finite) (hVH : V(H) ⊆ V(G)) :
    ∃ G₀ H₀ : Graph α β, G₀ ≤ G ∧ H₀ ≤ H ∧ V(G₀) = V(G) ∧ V(H₀) = V(H) ∧
      (∀ e a, a ∈ V(H₀) → ¬ G₀.IsLoopAt e a) ∧
      (TopologicallyContains G H ↔ TopologicallyContains G₀ H₀) := by
  induction hn : E(G).ncard using Nat.strong_induction_on generalizing G H with
  | _ n ih =>
    by_cases hloops : ∃ e a, a ∈ V(H) ∧ G.IsLoopAt e a
    · obtain ⟨e, a, ha, he⟩ := hloops
      let Gd := G.deleteEdges {e}
      have hEd : E(Gd).Finite := hE.subset Graph.deleteEdges_le.edgeSet_mono
      have hless : E(Gd).ncard < n := by
        change (E(G) \ {e}).ncard < n
        rw [← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem he.edge_mem hE
      by_cases hloopH : ∃ f, H.IsLoopAt f a
      · obtain ⟨f, hf⟩ := hloopH
        let Hd := H.deleteEdges {f}
        have hVHd : V(Hd) ⊆ V(Gd) := hVH
        obtain ⟨G₀, H₀, hG₀, hH₀, hVG₀, hVH₀, hNo, hTopo⟩ :=
          ih (G := Gd) (H := Hd) _ hless hEd hVHd rfl
        exact ⟨G₀, H₀, hG₀.trans Graph.deleteEdges_le, hH₀.trans Graph.deleteEdges_le,
          hVG₀, hVH₀, hNo, (theorem_4_3_proof hVH he hf).trans hTopo⟩
      · have hVHd : V(H) ⊆ V(Gd) := hVH
        obtain ⟨G₀, H₀, hG₀, hH₀, hVG₀, hVH₀, hNo, hTopo⟩ :=
          ih (G := Gd) (H := H) _ hless hEd hVHd rfl
        exact ⟨G₀, H₀, hG₀.trans Graph.deleteEdges_le, hH₀, hVG₀, hVH₀, hNo,
          (theorem_4_2_proof hVH he ha (fun f hf => hloopH ⟨f, hf⟩)).trans hTopo⟩
    · refine ⟨G, H, le_rfl, le_rfl, rfl, rfl, ?_, Iff.rfl⟩
      intro e a ha he
      exact hloops ⟨e, a, ha, he⟩

end GraphMinor.GM02
