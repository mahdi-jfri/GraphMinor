module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.MinimalDenseMinor
import GraphMinor.Thomason.DensitySubgraphs
import GraphMinor.Minor.Basic

/-!
# Trimming a minimal dense minor to exact density

A spanning subgraph with exactly `d|V|` edges retains the minimum vertex
count among non-null dense minors. This is the edge-deletion step used
before the degree-sum argument in Thomason's Lemma 2.1, page 363 of
*Extremal functions for graph minors* (2006).
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph

universe u

/-- A non-null finite graph with at least `d` edges per vertex has a
vertex-minimal dense minor with exactly `d` edges per vertex. -/
theorem exists_vertex_minimal_dense_minor_with_exact_edges {V : Type u}
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      H.edgeFinset.card = d * Fintype.card W ∧
      ∀ (X : Type u) (_ : Fintype X) (K : SimpleGraph X) (_ : DecidableRel K.Adj)
        (_ : Nonempty X),
        IsIsoMinor (Graph.ofSimpleGraph K) (Graph.ofSimpleGraph H) →
        d * Fintype.card X ≤ K.edgeFinset.card → Fintype.card W ≤ Fintype.card X := by
  classical
  obtain ⟨W, hW, H, hH, hne, hm, hden, hmin⟩ :=
    exists_vertex_minimal_dense_minor G d hd
  let := hW
  let := hH
  let := hne
  have hden' : d * Fintype.card W ≤ H.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hden
  obtain ⟨K, hKH, hcard⟩ := exists_spanning_subgraph_card H (d * Fintype.card W) hden'
  have hcard' : K.edgeFinset.card = d * Fintype.card W := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hcard
  have hminorKH := isIsoMinor_ofSimpleGraph_of_le hKH
  refine ⟨W, hW, K, inferInstance, hne, hminorKH.trans hm, hcard', ?_⟩
  intro X hX J hJ hneX hmJ hdenJ
  exact hmin X hX J hJ hneX (hmJ.trans hminorKH) hdenJ

end GraphMinor.Thomason
