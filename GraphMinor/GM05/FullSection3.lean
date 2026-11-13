module

public import GraphMinor.GM05.PathTransfer
public import GraphMinor.GM05.ConnectedTransfer
public import GraphMinor.GM05.Section3
import GraphMinor.Minor.Basic
import GraphMinor.GM05.Quoted

/-!
# Packing connected subgraphs in arbitrary finite hosts

Apply the simple-host packing theorem to the shadow. Lift each selected
connected subgraph on its vertex set. For the hitting alternative, take the
shadow of any connected subgraph of the original graph.
-/

public section
namespace GraphMinor.GM05.Full
open Graph GM01
variable {α β : Type*}

/-- Graph Minors V, (3.1), page 95, for hosts with loops and parallel edges.
Link selected disjoint connected subgraphs to a prescribed vertex set, or
separate almost all of them with a bounded vertex set.
`GM05.theorem_3_1_simple` is the simple-host version. -/
theorem theorem_3_1_proof {G : Graph α β} {θ n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (B : Fin n → Graph α β) (hle : ∀ j, B j ≤ G)
    (hc : ∀ j, GraphConnected (B j))
    (hd : Pairwise fun i j => Disjoint V(B i) V(B j))
    (V' : Set α) (hV' : V' ⊆ V(G)) (r : ℕ) :
    (∃ (J : Finset (Fin n)) (P : J → Path α), J.card = r ∧
      (∀ j : J, PathFromTo (P j) G V(B j.1) V') ∧
      Pairwise (fun i j : J => Disjoint (P i).verts (P j).verts) ∧
      ∀ j : J, Disjoint (P j).internalVerts (V' ∪ ⋃ j' ∈ J, V(B j'))) ∨
    (∃ (X : Set α) (J : Finset (Fin n)), X ⊆ V(G) ∧
      X.ncard + J.card ≤ 2 ^ (r * θ ^ 4) ∧
      ∀ j : Fin n, j ∉ J → Separates G X V' V(B j)) := by
  simp_rw [pathFromTo_iff, separates_iff]
  exact GM05.theorem_3_1_simple hθ heven hV
    (fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE)))
    (fun j => simpleShadow (B j)) (fun j => simpleShadow_mono (hle j))
    (fun j => (graphConnected_iff_simpleShadow_connected _).mp (hc j)) hd V' hV' r

/-- Graph Minors V, (3.2), pages 95–96, for hosts with loops and parallel edges.
Either `n` disjoint connected subgraphs meet every prescribed set, or fewer
than `α θ k n` vertices meet every such connected subgraph.
`GM05.theorem_3_2_simple` is the simple-host version. -/
theorem theorem_3_2_proof {G : Graph α β} {θ k n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hk : 2 ≤ k)
    (S : Fin k → Set α) (hS : ∀ i, S i ⊆ V(G)) :
    (∃ B : Fin n → Graph α β,
      (∀ j, B j ≤ G) ∧ (∀ j, GraphConnected (B j)) ∧
      Pairwise (fun i j => Disjoint V(B i) V(B j)) ∧
      ∀ i j, (V(B j) ∩ S i).Nonempty) ∨
    (∃ X ⊆ V(G), X.ncard < GM05.α θ k n ∧
      ∀ B : Graph α β, B ≤ G → GraphConnected B →
        (∀ i, (V(B) ∩ S i).Nonempty) → (V(B) ∩ X).Nonempty) := by
  have hs : simpleShadow G ∈ 𝓕 θ :=
    fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE))
  rcases GM05.theorem_3_2_simple hθ heven hV hs hk S hS with
    ⟨B, hle, hc, hd, hm⟩ | ⟨X, hX, hcard, hhit⟩
  · left
    have hlift := fun j => exists_connected_subgraph_of_shadow (hle j) (hc j)
    choose K hK hconn hverts using hlift
    refine ⟨K, hK, hconn, ?_, ?_⟩
    · intro i j hij
      rw [hverts i, hverts j]
      exact hd hij
    · intro i j
      rw [hverts j]
      exact hm i j
  · exact Or.inr ⟨X, hX, hcard, fun B hB hc hm =>
      hhit (simpleShadow B) (simpleShadow_mono hB)
        ((graphConnected_iff_simpleShadow_connected B).mp hc) hm⟩

end GraphMinor.GM05.Full
