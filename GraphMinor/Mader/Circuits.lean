module

public import GraphMinor.GM04.TopologicalContainment
public import GraphMinor.GM09.Basic
public import Mathlib.Combinatorics.Graph.Simple
import GraphMinor.Kruskal.ForestSimple

/-!
# Small circuit bounds

Excluding one circuit is the forest condition used by Kruskal's theorem.
Excluding two vertex-disjoint circuits says that every pair of circuits
meets. These checks include loops and pairs of parallel edges, as required
by Graph Minors IV (1.3), page 229.
-/

public section

namespace GraphMinor.Mader

open Graph Surface GM09

/-- A positive simple closed walk gives a circuit on its vertices and edges. -/
theorem isGraphCircuit_walkSubgraph {α β : Type*} {G : Graph α β} {u : α}
    (W : GraphWalk G u u) (hW : W.IsSimpleClosed) (hlen : 0 < W.length) :
    IsGraphCircuit G (walkSubgraph W) := by
  obtain ⟨W', hs, he⟩ := exists_walk_walkSubgraph W
  refine ⟨walkSubgraph_le W, u, W', ?_, ?_, ?_, ?_⟩
  · simpa only [GraphWalk.IsSimpleClosed, hs, he] using hW
  · simpa only [GraphWalk.length, he] using hlen
  · rw [vertexSet_walkSubgraph, hs]
  · rw [edgeSet_walkSubgraph, he]

/-- The walk definition of a forest agrees with the absence of circuit subgraphs. -/
theorem isGraphForest_iff_no_circuit {α β : Type*} (G : Graph α β) :
    IsGraphForest G ↔ ¬ ∃ C, IsGraphCircuit G C := by
  constructor
  · intro hforest ⟨C, hCG, u, W, hW, hlen, _, _⟩
    obtain ⟨W', hs, he⟩ := exists_walk_up_of_le hCG W
    have hsimp : W'.IsSimpleClosed := by
      simpa only [GraphWalk.IsSimpleClosed, hs, he] using hW
    have hzero := hforest u W' hsimp
    have hzero' : W.length = 0 := by
      simpa only [GraphWalk.length, he] using hzero
    exact Nat.ne_of_gt hlen hzero'
  · intro hno u W hW
    by_contra hlen
    exact hno ⟨walkSubgraph W,
      isGraphCircuit_walkSubgraph W hW (Nat.pos_of_ne_zero hlen)⟩

/-- A family of one circuit is just a circuit. -/
theorem hasDisjointCircuits_one_iff {α β : Type*} (G : Graph α β) :
    GM04.HasDisjointCircuits G 1 ↔ ∃ C, IsGraphCircuit G C := by
  constructor
  · rintro ⟨C, hC, _⟩
    exact ⟨C 0, hC 0⟩
  · rintro ⟨C, hC⟩
    refine ⟨fun _ ↦ C, fun _ ↦ hC, ?_⟩
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-- The bound `n = 0` in Mader's statement is precisely the class of forests. -/
theorem not_hasDisjointCircuits_one_iff {α β : Type*} (G : Graph α β) :
    ¬ GM04.HasDisjointCircuits G 1 ↔ IsGraphForest G := by
  rw [hasDisjointCircuits_one_iff, isGraphForest_iff_no_circuit]

/-- The bound `n = 0` excludes loops and distinct parallel edges. -/
theorem simple_of_not_hasDisjointCircuits_one {α β : Type*} {G : Graph α β}
    (h : ¬ GM04.HasDisjointCircuits G 1) : G.Simple :=
  Kruskal.forest_simple ((not_hasDisjointCircuits_one_iff G).mp h)

/-- Two vertex-disjoint circuits are two circuit subgraphs with disjoint vertex sets. -/
theorem hasDisjointCircuits_two_iff {α β : Type*} (G : Graph α β) :
    GM04.HasDisjointCircuits G 2 ↔
      ∃ C D, IsGraphCircuit G C ∧ IsGraphCircuit G D ∧ Disjoint V(C) V(D) := by
  constructor
  · rintro ⟨C, hC, hd⟩
    exact ⟨C 0, C 1, hC 0, hC 1, hd (by decide)⟩
  · rintro ⟨C, D, hC, hD, hd⟩
    refine ⟨![C, D], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hC
      · exact hD
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hd
      · exact hd.symm
      · exact (hij rfl).elim

/-- The bound `n = 1` permits circuits, but requires any two to meet. -/
theorem not_hasDisjointCircuits_two_iff {α β : Type*} (G : Graph α β) :
    ¬ GM04.HasDisjointCircuits G 2 ↔
      ∀ C D, IsGraphCircuit G C → IsGraphCircuit G D → (V(C) ∩ V(D)).Nonempty := by
  rw [hasDisjointCircuits_two_iff]
  constructor
  · intro h C D hC hD
    by_contra hdis
    exact h ⟨C, D, hC, hD, Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hdis)⟩
  · rintro h ⟨C, D, hC, hD, hd⟩
    obtain ⟨v, hvC, hvD⟩ := h C D hC hD
    exact Set.disjoint_left.mp hd hvC hvD

end GraphMinor.Mader
