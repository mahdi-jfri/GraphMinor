module

public import GraphMinor.Thomason.ContractionMinor
import GraphMinor.Minor.Basic

/-!
# A minimal dense minor has many triangles through every edge

Choose a non-null dense minor with the fewest vertices. If two adjacent
vertices had fewer than `d` common neighbours, contracting their edge would
preserve the density `d` and reduce the vertex count. This proves the first
part of Thomason's Lemma 2.1, *Extremal functions for graph minors* (2006),
page 363. The choice of a smallest minor is proved with the least natural
number principle.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph

universe u

/-- Among the non-null finite simple minors with at least `d` edges per
vertex, there is one with the fewest vertices. Minimality is derived from
the least natural number principle. -/
theorem exists_vertex_minimal_dense_minor {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      d * Fintype.card W ≤ H.edgeFinset.card ∧
      ∀ (X : Type u) (_ : Fintype X) (K : SimpleGraph X) (_ : DecidableRel K.Adj)
        (_ : Nonempty X),
        IsIsoMinor (Graph.ofSimpleGraph K) (Graph.ofSimpleGraph H) →
        d * Fintype.card X ≤ K.edgeFinset.card → Fintype.card W ≤ Fintype.card X := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W), Fintype.card W = n ∧
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      d * Fintype.card W ≤ H.edgeFinset.card
  have hex : ∃ n, P n := by
    exact ⟨Fintype.card V, V, inferInstance, G, inferInstance, inferInstance, rfl,
      IsIsoMinor.refl _, hd⟩
  obtain ⟨W, hW, H, hH, hne, hcard, hm, hden⟩ := Nat.find_spec hex
  let := hW
  let := hH
  let := hne
  refine ⟨W, hW, H, hH, hne, hm, hden, ?_⟩
  intro X hX K hK hneX hminor hdK
  let := hX
  let := hK
  let := hneX
  have hPX : P (Fintype.card X) :=
    ⟨X, hX, K, hK, hneX, rfl, hminor.trans hm, hdK⟩
  rw [hcard]
  exact Nat.find_min' hex hPX

/-- A non-null finite graph with at least `d` edges per vertex has a
non-null simple minor with the same density in which the ends of every
edge have at least `d` common neighbours. This is the triangle assertion
of Thomason's Lemma 2.1, page 363. -/
theorem exists_dense_minor_with_many_commonNeighbors {V : Type u}
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      d * Fintype.card W ≤ H.edgeFinset.card ∧
      ∀ u v : W, H.Adj u v → d ≤ (H.commonNeighbors u v).ncard := by
  classical
  obtain ⟨W, hW, H, hH, hne, hm, hden, hmin⟩ :=
    exists_vertex_minimal_dense_minor G d hd
  let := hW
  let := hH
  let := hne
  refine ⟨W, hW, H, hH, hne, hm, hden, fun u v huv => ?_⟩
  have hcn : (H.commonNeighbors u v).ncard =
      (H.neighborFinset v ∩ H.neighborFinset u).card := by
    simp only [Set.ncard_eq_toFinset_card', SimpleGraph.commonNeighbors_eq,
      Set.toFinset_inter, ← SimpleGraph.neighborFinset_def, Finset.inter_comm]
  rw [hcn]
  by_contra hsmall
  have hc : (H.neighborFinset v ∩ H.neighborFinset u).card + 1 ≤ d := by omega
  let K := edgeContraction H u v
  have hneK : Nonempty ({v}ᶜ : Set W) := ⟨⟨u, huv.ne⟩⟩
  have hcount := edgeContraction_card_edges H huv
  have hverts := edgeContraction_card_vertices v
  have hdenK : d * Fintype.card ({v}ᶜ : Set W) ≤ K.edgeFinset.card := by
    rw [← hverts, Nat.mul_add, Nat.mul_one] at hden
    dsimp only [K]
    omega
  have hle := hmin ({v}ᶜ : Set W) inferInstance K inferInstance hneK
    (edgeContraction_isIsoMinor H huv) hdenK
  omega

end GraphMinor.Thomason
