module

public import GraphMinor.Surface.Defs
import GraphMinor.GM06.Section3Dual

/-!
# A spanning forest with the same components

The proof of IV (9.2), page 254, takes a spanning forest of a finite
realization. Delete one edge from a circuit at each step. The rest of the
circuit replaces that edge in any walk, so deleting it preserves all
components. Induction on the number of edges terminates at a forest.
-/

public section

namespace GraphMinor.GM04

open Set Surface Graph

universe u v

private def walkToRestrictDiff {α : Type u} {β : Type v} {C : Graph α β} {e₀ : β}
    {x y : α} (W : GraphWalk C x y)
    (hedges : ∀ e ∈ W.edges, e ≠ e₀) : GraphWalk (C.restrict (E(C) \ {e₀})) x y :=
  match W with
  | .nil hx => .nil hx
  | @GraphWalk.cons _ _ _ x v y e h rest =>
    have hne : e ≠ e₀ := hedges e (by simp [GraphWalk.edges])
    have hlink' : (C.restrict (E(C) \ {e₀})).IsLink e x v := by
      rw [restrict_isLink]
      exact ⟨⟨h.edge_mem, hne⟩, h⟩
    .cons hlink'
      (walkToRestrictDiff rest fun e' he' => hedges e' (by simp [GraphWalk.edges, he']))

private theorem walkAvoidEdge {α : Type u} {β : Type v} {C : Graph α β} {e₀ : β} {u₀ w₀ : α}
    (hlink₀ : C.IsLink e₀ u₀ w₀)
    (P : GraphWalk (C.restrict (E(C) \ {e₀})) w₀ u₀)
    {x y : α} (W : GraphWalk C x y) :
    Nonempty (GraphWalk (C.restrict (E(C) \ {e₀})) x y) := by
  classical
  induction W with
  | nil hx => exact ⟨.nil hx⟩
  | @cons a b y e h rest ih =>
    obtain ⟨W_rest⟩ := ih
    rcases eq_or_ne a b with rfl | hab
    · exact ⟨W_rest⟩
    · rcases eq_or_ne e e₀ with rfl | hne
      · rcases h.left_eq_or_eq hlink₀ with rfl | rfl
        · rcases h.symm.left_eq_or_eq hlink₀ with rfl | rfl
          · exact (hab rfl).elim
          · exact ⟨P.reverse.append W_rest⟩
        · rcases h.symm.left_eq_or_eq hlink₀.symm with rfl | rfl
          · exact (hab rfl).elim
          · exact ⟨P.append W_rest⟩
      · have hlink' : (C.restrict (E(C) \ {e₀})).IsLink e a b := by
          rw [restrict_isLink]
          exact ⟨⟨h.edge_mem, hne⟩, h⟩
        exact ⟨.cons hlink' W_rest⟩

/-- A graph with finitely many edges has a spanning forest with exactly
the same walk connections. This supplies the spanning forest in the proof
of Graph Minors IV, (9.2), page 254. -/
theorem exists_spanning_forest {α : Type u} {β : Type v} (G : Graph α β)
    (hE : E(G).Finite) :
    ∃ F ≤ G, V(F) = V(G) ∧ IsGraphForest F ∧
      ∀ x y, Nonempty (GraphWalk F x y) ↔ Nonempty (GraphWalk G x y) := by
  classical
  induction hn : E(G).ncard using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    by_cases hF : IsGraphForest G
    · exact ⟨G, le_rfl, rfl, hF, fun _ _ ↦ Iff.rfl⟩
    · unfold IsGraphForest at hF
      push Not at hF
      obtain ⟨u, W, hW, hlen⟩ := hF
      cases W with
      | nil _ => exact (hlen rfl).elim
      | @cons _ w _ e he rest =>
        have hnot : e ∉ rest.edges := (List.nodup_cons.mp hW.2).1
        let G' := G.restrict (E(G) \ {e})
        have hE' : E(G') = E(G) \ {e} := by
          ext f
          simp only [G', edgeSet_restrict, mem_inter_iff, mem_sdiff, mem_singleton_iff]
          tauto
        let P : GraphWalk G' w u := walkToRestrictDiff rest
          (fun f hf heq ↦ hnot (heq ▸ hf))
        have hfin : E(G').Finite := hE.subset (hE' ▸ sdiff_subset)
        have hlt : E(G').ncard < n := by
          rw [hE', ← hn]
          exact ncard_sdiff_singleton_lt_of_mem he.edge_mem hE
        obtain ⟨F, hFG', hVF, hforest, hwalk⟩ := ih _ hlt G' hfin rfl
        refine ⟨F, hFG'.trans restrict_le, hVF, hforest, fun x y ↦ ?_⟩
        refine (hwalk x y).trans ⟨?_, ?_⟩
        · rintro ⟨W⟩
          exact ⟨W.mono restrict_le⟩
        · rintro ⟨W⟩
          exact walkAvoidEdge he P W

end GraphMinor.GM04
