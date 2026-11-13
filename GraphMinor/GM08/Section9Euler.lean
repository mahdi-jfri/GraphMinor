module

public import GraphMinor.GM08.Section9
import GraphMinor.GM09.Basic

/-!
# Monotonicity of the cycle count

For the cyclomatic-number comparison in VIII (9.1), page 270, a nonempty
subgraph of a connected finite graph has no larger edge-minus-vertex count.
Grow its vertex set one vertex at a time. Connectivity supplies an edge to
a new vertex, so each growth step adds one edge and one vertex.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph

universe u v

private theorem exists_link_crossing_set {α : Type u} {β : Type v} {G : Graph α β}
    {A : Set α} {a b : α} (W : GraphWalk G a b) (ha : a ∈ A) (hb : b ∉ A) :
    ∃ e x y, G.IsLink e x y ∧ x ∈ A ∧ y ∉ A := by
  induction W with
  | nil _ => exact False.elim (hb ha)
  | @cons a c b e hl rest ih =>
    by_cases hc : c ∈ A
    · exact ih hc hb
    · exact ⟨e, a, c, hl, ha, hc⟩

/-- The edge-minus-vertex count of a nonempty subgraph is bounded by that
of a connected finite graph. This is the monotonicity step in the cycle-count
argument of Graph Minors VIII (9.1), page 270. -/
theorem card_edges_add_vertices_le_of_connected_supergraph
    {α : Type u} {β : Type v} {G H : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hG : GM06.IsGraphConnected G)
    (hHG : H ≤ G) (hH : V(H).Nonempty) :
    E(H).ncard + V(G).ncard ≤ E(G).ncard + V(H).ncard := by
  classical
  induction hn : (V(G) \ V(H)).ncard using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    have hVH : V(H).Finite := hVG.subset hHG.vertexSet_mono
    have hEH : E(H).Finite := hEG.subset hHG.edgeSet_mono
    by_cases hfull : V(G) ⊆ V(H)
    · have heq : V(H) = V(G) := subset_antisymm hHG.vertexSet_mono hfull
      have hle := Set.ncard_le_ncard hHG.edgeSet_mono hEG
      rw [heq]
      exact Nat.add_le_add_right hle _
    · obtain ⟨b, hbG, hbH⟩ := Set.not_subset.mp hfull
      obtain ⟨a, haH⟩ := hH
      obtain ⟨W⟩ := hG.2 a (hHG.vertexSet_mono haH) b hbG
      obtain ⟨e, x, y, hl, hxH, hyH⟩ := exists_link_crossing_set W haH hbH
      let K := (G.induce (insert y V(H))).restrict (insert e E(H))
      have hVK : V(K) = insert y V(H) := rfl
      have hKG : K ≤ G := Graph.restrict_le.trans (Graph.induce_le
        (Set.insert_subset hl.right_mem hHG.vertexSet_mono))
      have hHK : H ≤ K := by
        refine ⟨fun z hz => Set.mem_insert_of_mem _ hz, fun f u v hf => ?_⟩
        exact ⟨Set.mem_insert_of_mem _ hf.edge_mem, hf.mono hHG,
          Set.mem_insert_of_mem _ hf.left_mem, Set.mem_insert_of_mem _ hf.right_mem⟩
      have heH : e ∉ E(H) := fun he => hyH (((hHG.isLink_iff he).mpr hl).right_mem)
      have hEK : E(K) = insert e E(H) := by
        change E(G.induce (insert y V(H))) ∩ insert e E(H) = insert e E(H)
        apply inter_eq_right.mpr
        rintro f (rfl | hf)
        · exact ⟨x, y, hl, Set.mem_insert_of_mem _ hxH, Set.mem_insert _ _⟩
        · obtain ⟨u, v, hfuv⟩ := H.exists_isLink_of_mem_edgeSet hf
          exact ⟨u, v, hfuv.mono hHG, Set.mem_insert_of_mem _ hfuv.left_mem,
            Set.mem_insert_of_mem _ hfuv.right_mem⟩
      have hdiff : V(G) \ V(K) = (V(G) \ V(H)) \ {y} := by
        rw [hVK]
        ext z
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      have hlt : (V(G) \ V(K)).ncard < n := by
        rw [hdiff, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem ⟨hl.right_mem, hyH⟩ hVG.sdiff
      have hrec := ih _ hlt hKG ⟨a, hHK.vertexSet_mono haH⟩ rfl
      rw [hEK, hVK, Set.ncard_insert_of_notMem heH hEH,
        Set.ncard_insert_of_notMem hyH hVH] at hrec
      omega

end GraphMinor.GM08
