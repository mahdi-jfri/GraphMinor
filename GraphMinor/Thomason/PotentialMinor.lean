module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.DensitySubgraphs
import GraphMinor.Minor.Basic

/-!
# A minimal minor for a vertex-dependent edge bound

Thomason's Lemma 1, page 262 (1984), minimizes over graphs with at least
`m` vertices and an edge threshold depending on their order. The least
natural number principle gives the minimum vertex count, and edge deletion
gives equality in the integer edge threshold. This construction works for
any natural-valued threshold function.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph

universe u

/-- For any edge threshold depending on the number of vertices, choose a
minor with the minimum permitted vertex count and exactly the threshold
number of edges. This is the selection step in Thomason's Lemma 1, p. 262. -/
theorem exists_minimal_potential_minor {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ → ℕ) (m : ℕ)
    (hm : m ≤ Fintype.card V) (hd : f (Fintype.card V) ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      m ≤ Fintype.card W ∧
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      H.edgeFinset.card = f (Fintype.card W) ∧
      ∀ (X : Type u) (_ : Fintype X) (K : SimpleGraph X) (_ : DecidableRel K.Adj)
        (_ : Nonempty X), m ≤ Fintype.card X →
        IsIsoMinor (Graph.ofSimpleGraph K) (Graph.ofSimpleGraph H) →
        f (Fintype.card X) ≤ K.edgeFinset.card → Fintype.card W ≤ Fintype.card X := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W), Fintype.card W = n ∧ m ≤ n ∧
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      f n ≤ H.edgeFinset.card
  have hex : ∃ n, P n :=
    ⟨Fintype.card V, V, inferInstance, G, inferInstance, inferInstance, rfl, hm,
      IsIsoMinor.refl _, hd⟩
  obtain ⟨W, hW, H, hH, hne, hcard, hmW, hminor, hden⟩ := Nat.find_spec hex
  let := hW
  let := hH
  let := hne
  rw [← hcard] at hmW hden
  have hden' : f (Fintype.card W) ≤ H.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hden
  obtain ⟨J, hJH, hJcard⟩ := exists_spanning_subgraph_card H (f (Fintype.card W)) hden'
  have hJcard' : J.edgeFinset.card = f (Fintype.card W) := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hJcard
  have hminorJH := isIsoMinor_ofSimpleGraph_of_le hJH
  refine ⟨W, hW, J, inferInstance, hne, hmW, hminorJH.trans hminor, hJcard', ?_⟩
  intro X hX K hK hneX hmX hmK hdK
  let := hX
  let := hK
  let := hneX
  have hPX : P (Fintype.card X) :=
    ⟨X, hX, K, hK, hneX, rfl, hmX, hmK.trans (hminorJH.trans hminor), hdK⟩
  rw [hcard]
  exact Nat.find_min' hex hPX

end GraphMinor.Thomason
