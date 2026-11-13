module

public import GraphMinor.GM05.ConnectedTransfer
public import GraphMinor.GM05.FullTreeWidth
public import GraphMinor.GM05.Section6

/-!
# Connected packings and separators in arbitrary finite graphs

Connected subgraphs lift on the same vertices. Induced connectivity and
vertex separations transfer exactly. As in the full version of (1.6),
components are represented by their vertex sets in the simple shadow.
-/

@[expose] public section
namespace GraphMinor.GM05.Full
open Graph
variable {α β : Type*}

/-- Graph Minors V, (6.1), page 103, for hosts with loops and parallel edges.
Enumerate a 2-connected graph with connected prefixes and suffixes, allowing
the empty prefix or suffix. Two-connectivity uses the shadow, since it is
unchanged by loops and parallel edges. `GM05.theorem_6_1_simple` is the simple-host version. -/
theorem theorem_6_1_proof {G : Graph α β} (hV : V(G).Finite)
    (h2 : GM05.IsTwoConnected (simpleShadow G)) :
    ∃ v : Fin V(G).ncard → α, Function.Injective v ∧ Set.range v = V(G) ∧
      ∀ i : ℕ, i ≤ V(G).ncard →
        GraphPreconnected (G.induce {x | ∃ j : Fin V(G).ncard, j.1 < i ∧ v j = x}) ∧
        GraphPreconnected (G.induce {x | ∃ j : Fin V(G).ncard, i ≤ j.1 ∧ v j = x}) := by
  obtain ⟨v, hinj, hrange, hv⟩ := GM05.theorem_6_1_simple hV h2
  refine ⟨v, hinj, hrange, fun i hi => ?_⟩
  exact ⟨(graphPreconnected_induce_iff _ _).mpr (hv i hi).1,
    (graphPreconnected_induce_iff _ _).mpr (hv i hi).2⟩

/-- Alternative (i) of V (6.2), page 103, using connectivity in the original graph. -/
def Cond62_i (G : Graph α β) (w : α → ℕ) (k : ℕ) : Prop :=
  ∃ A B : Set α, A ⊆ V(G) ∧ B ⊆ V(G) ∧ Disjoint A B ∧
    GraphConnected (G.induce A) ∧ GraphConnected (G.induce B) ∧
    k ≤ weightSum w A ∧ k ≤ weightSum w B

private theorem cond62_i_iff {G : Graph α β} {w : α → ℕ} {k : ℕ} :
    Cond62_i G w k ↔ GM05.Cond62_i (simpleShadow G) w k := by
  unfold Cond62_i GM05.Cond62_i
  simp only [graphConnected_induce_iff]
  rfl

/-- Graph Minors V, (6.2), page 103, for hosts with loops and parallel edges.
Exactly one of a heavy connected split and a vertex hitting all heavy
components exists. Components use the shadow representation of (1.6).
`GM05.theorem_6_2_simple` is the simple-host version. -/
theorem theorem_6_2_proof {G : Graph α β} (hV : V(G).Finite)
    (hc : GraphConnected G) (w : α → ℕ) {k : ℕ} (hk : 0 < k)
    (hbound : k ≤ (weightSum w V(G) + 2) / 3) :
    (Cond62_i G w k ∨ GM05.Cond62_ii (simpleShadow G) w k) ∧
      ¬ (Cond62_i G w k ∧ GM05.Cond62_ii (simpleShadow G) w k) := by
  rw [cond62_i_iff]
  exact GM05.theorem_6_2_simple hV
    ((graphConnected_iff_simpleShadow_connected G).mp hc) w hk hbound

/-- Graph Minors V, (6.3), page 104, for hosts with loops and parallel edges.
Pack `k` large connected subgraphs or delete fewer than `k` vertices to leave
only small components. Components use the shadow representation of (1.6).
`GM05.theorem_6_3_simple` is the simple-host version. -/
theorem theorem_6_3_proof {G : Graph α β} (hV : V(G).Finite)
    (hc : GraphConnected G) {k : ℕ} (hk : 0 < k) :
    (∃ B : Fin k → Graph α β,
      (∀ i, B i ≤ G ∧ GraphConnected (B i) ∧
        2 * V(G).ncard ≤ (3 ^ k - 1) * V(B i).ncard) ∧
      Pairwise (fun i j => Disjoint V(B i) V(B j))) ∨
    GM05.Cond63_ii (simpleShadow G) k := by
  rcases GM05.theorem_6_3_simple hV
    ((graphConnected_iff_simpleShadow_connected G).mp hc) hk with ⟨B, hB, hd⟩ | hsmall
  · left
    have hlift := fun i => exists_connected_subgraph_of_shadow (hB i).1 (hB i).2.1
    choose K hK hconn hv using hlift
    refine ⟨K, fun i => ⟨hK i, hconn i, ?_⟩, ?_⟩
    · rw [hv i]
      exact (hB i).2.2
    · intro i j hij
      rw [hv i, hv j]
      exact hd hij
  · exact Or.inr hsmall

/-- Graph Minors V, (6.4), page 106, for hosts with loops and parallel edges.
Pack `k` large connected subgraphs or find a small balanced separation.
`GM05.theorem_6_4_simple` is the simple-host version. -/
theorem theorem_6_4_proof {G : Graph α β} (hV : V(G).Finite) {k : ℕ} (hk : 0 < k) :
    (∃ B : Fin k → Graph α β,
      (∀ i, B i ≤ G ∧ GraphConnected (B i) ∧
        4 * V(G).ncard ≤ 3 * (3 ^ k - 1) * V(B i).ncard) ∧
      Pairwise (fun i j => Disjoint V(B i) V(B j))) ∨
    (∃ A B : Set α, IsSeparation G A B ∧ (A ∩ B).ncard < k ∧
      3 * (A \ B).ncard ≤ 2 * V(G).ncard ∧
      3 * (B \ A).ncard ≤ 2 * V(G).ncard) := by
  rcases GM05.theorem_6_4_simple (G := simpleShadow G) hV hk with ⟨B, hB, hd⟩ | ⟨A, B, hs, hrest⟩
  · left
    have hlift := fun i => exists_connected_subgraph_of_shadow (hB i).1 (hB i).2.1
    choose K hK hconn hv using hlift
    refine ⟨K, fun i => ⟨hK i, hconn i, ?_⟩, ?_⟩
    · rw [hv i]
      exact (hB i).2.2
    · intro i j hij
      rw [hv i, hv j]
      exact hd hij
  · exact Or.inr ⟨A, B, isSeparation_iff.mpr hs, hrest⟩

end GraphMinor.GM05.Full
