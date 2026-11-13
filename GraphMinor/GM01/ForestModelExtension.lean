module

public import GraphMinor.GM01.ForestModels

/-!
# Adding one vertex to a forest minor model

For the elementary forest-minor observation in Graph Minors I, proof of
(1.1), page 51, we extend a model after restoring a leaf or an isolated
vertex. Each old branch set grows at its chosen outer vertex. The restored
vertex gets a singleton branch set at the other child of its neighbour's
outer vertex, or at an unused outer vertex if it is isolated.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

/-- Restore one source vertex after removing it. The attachment vertex is
chosen at the outer representative of its sole neighbour, if there is one.
All conclusions are constructed in the next finite tree. -/
theorem forestTree_model_add_vertex {α : Type*}
    (H : (⊤ : SimpleGraph α).Subgraph) {x : α} {n : ℕ}
    (K : α → (⊤ : SimpleGraph ForestTreeVertex).Subgraph)
    (r : α → ForestTreeVertex) (spare : ForestTreeVertex)
    (hK : ∀ u ∈ (H.deleteVerts {x}).verts,
      K u ≤ forestTree n ∧ (K u).Connected ∧ r u ∈ (K u).verts ∧ forestTreeDepth (r u) = n)
    (hdisj : ∀ u ∈ (H.deleteVerts {x}).verts, ∀ v ∈ (H.deleteVerts {x}).verts,
      u ≠ v → Disjoint (K u).verts (K v).verts)
    (hedge : ∀ u v, (H.deleteVerts {x}).Adj u v →
      ∃ a ∈ (K u).verts, ∃ b ∈ (K v).verts, (forestTree n).Adj a b)
    (hsd : forestTreeDepth spare = n)
    (hspare : ∀ u ∈ (H.deleteVerts {x}).verts, spare ∉ (K u).verts)
    (anchor : ForestTreeVertex) (had : forestTreeDepth anchor = n)
    (hattach : ∀ u, H.Adj x u → anchor = r u) :
    ∃ (K' : α → (⊤ : SimpleGraph ForestTreeVertex).Subgraph)
      (r' : α → ForestTreeVertex) (spare' : ForestTreeVertex),
      (∀ u ∈ H.verts, K' u ≤ forestTree (n + 1) ∧ (K' u).Connected ∧
        r' u ∈ (K' u).verts ∧ forestTreeDepth (r' u) = n + 1) ∧
      (∀ u ∈ H.verts, ∀ v ∈ H.verts, u ≠ v → Disjoint (K' u).verts (K' v).verts) ∧
      (∀ u v, H.Adj u v →
        ∃ a ∈ (K' u).verts, ∃ b ∈ (K' v).verts, (forestTree (n + 1)).Adj a b) ∧
      forestTreeDepth spare' = n + 1 ∧ (∀ u ∈ H.verts, spare' ∉ (K' u).verts) := by
  classical
  let bit (u : α) : Bool := if r u = anchor then true else false
  let child := forestTreeChild false anchor
  let K' (u : α) := if u = x then (⊤ : SimpleGraph ForestTreeVertex).singletonSubgraph child
    else forestTreeBranchGrow (K u) (r u) (bit u)
  let r' (u : α) := if u = x then child else forestTreeChild (bit u) (r u)
  let spare' := forestTreeChild true spare
  have old {u : α} (hu : u ∈ H.verts) (hne : u ≠ x) : u ∈ (H.deleteVerts {x}).verts :=
    ⟨hu, hne⟩
  have hchildmem : child ∈ (forestTree (n + 1)).verts :=
    forestTreeChild_mem (show anchor ∈ (forestTree n).verts from had.le) false
  have hneq (u : α) : child ≠ forestTreeChild (bit u) (r u) := by
    intro heq
    have hp : anchor = r u := forestTreeChild_parent_injective heq
    have hb := forestTreeChild_bit_injective heq
    have hbit : bit u = true := by simp only [bit, hp.symm, ↓reduceIte]
    rw [hbit] at hb
    cases hb
  have hchildout {u : α} (hu : u ∈ (H.deleteVerts {x}).verts) :
      child ∉ (forestTreeBranchGrow (K u) (r u) (bit u)).verts :=
    forestTreeChild_not_mem_grow (hK u hu).1 (hK u hu).2.2.1 had (hneq u)
  refine ⟨K', r', spare', ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hux : u = x
    · subst u
      simp only [K', r', ↓reduceIte]
      refine ⟨?_, Subgraph.singletonSubgraph_connected, by simp, ?_⟩
      · exact (singletonSubgraph_le_iff _ _).mpr hchildmem
      · exact (forestTreeDepth_child false anchor).trans (congrArg (· + 1) had)
    · obtain ⟨hKu, hKc, hKr, hKd⟩ := hK u (old hu hux)
      simp only [K', r', hux, ↓reduceIte]
      refine ⟨forestTreeBranchGrow_le hKu hKr _, forestTreeBranchGrow_connected hKc hKr _, ?_, ?_⟩
      · rw [forestTreeBranchGrow_verts hKr]
        exact Set.mem_insert _ _
      · exact (forestTreeDepth_child _ _).trans (congrArg (· + 1) hKd)
  · intro u hu v hv huv
    by_cases hux : u = x
    · subst u
      have hvx : v ≠ x := Ne.symm huv
      simp only [K', hvx, ↓reduceIte, singletonSubgraph_verts]
      exact Set.disjoint_singleton_left.mpr (hchildout (old hv hvx))
    · by_cases hvx : v = x
      · subst v
        simp only [K', hux, ↓reduceIte, singletonSubgraph_verts]
        exact Set.disjoint_singleton_right.mpr (hchildout (old hu hux))
      · simp only [K', hux, hvx, ↓reduceIte]
        have hu' := old hu hux
        have hv' := old hv hvx
        exact forestTreeBranchGrow_disjoint (hK u hu').1 (hK v hv').1
          (hdisj u hu' v hv' huv) (hK u hu').2.2.1 (hK v hv').2.2.1
          (hK u hu').2.2.2 (hK v hv').2.2.2 _ _
  · intro u v huv
    by_cases hux : u = x
    · subst u
      have hvx : v ≠ x := huv.ne.symm
      have hv' := old huv.snd_mem hvx
      refine ⟨child, ?_, r v, ?_, ?_⟩
      · simp [K']
      · simp only [K', hvx, ↓reduceIte]
        exact (le_forestTreeBranchGrow _ _ _).1 (hK v hv').2.2.1
      · rw [← hattach v huv]
        exact (forestTree_adj_child (show anchor ∈ (forestTree n).verts from had.le) false).symm
    · by_cases hvx : v = x
      · subst v
        have hu' := old huv.fst_mem hux
        refine ⟨r u, ?_, child, ?_, ?_⟩
        · simp only [K', hux, ↓reduceIte]
          exact (le_forestTreeBranchGrow _ _ _).1 (hK u hu').2.2.1
        · simp [K']
        · rw [← hattach u huv.symm]
          exact forestTree_adj_child (show anchor ∈ (forestTree n).verts from had.le) false
      · have hdel : (H.deleteVerts {x}).Adj u v :=
          Subgraph.deleteVerts_adj.mpr ⟨huv.fst_mem, hux, huv.snd_mem, hvx, huv⟩
        obtain ⟨a, ha, b, hb, hab⟩ := hedge u v hdel
        refine ⟨a, ?_, b, ?_, (forestTree_mono (Nat.le_succ n)).2 hab⟩
        · simp only [K', hux, ↓reduceIte]
          exact (le_forestTreeBranchGrow _ _ _).1 ha
        · simp only [K', hvx, ↓reduceIte]
          exact (le_forestTreeBranchGrow _ _ _).1 hb
  · exact (forestTreeDepth_child true spare).trans (congrArg (· + 1) hsd)
  · intro u hu
    by_cases hux : u = x
    · subst u
      simp only [K', ↓reduceIte, singletonSubgraph_verts, Set.mem_singleton_iff]
      intro heq
      have hb := forestTreeChild_bit_injective heq
      cases hb
    · simp only [K', hux, ↓reduceIte]
      have hu' := old hu hux
      apply forestTreeChild_not_mem_grow (hK u hu').1 (hK u hu').2.2.1 hsd
      intro heq
      have hp := forestTreeChild_parent_injective heq
      exact hspare u hu' (hp ▸ (hK u hu').2.2.1)

end GraphMinor.GM01
