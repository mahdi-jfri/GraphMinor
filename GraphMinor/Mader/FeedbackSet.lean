module

public import GraphMinor.GM04.TopologicalContainment
public import GraphMinor.GM09.Defs
import GraphMinor.Mader.Circuits
import GraphMinor.GM05.CircuitPacking

/-!
# Reducing a circuit bound to a bounded vertex deletion

Graph Minors V (8.1), page 109 supplies a bounded set of vertices meeting
all circuits. The circuit predicates of IV and V agree. After deleting
this set, the remaining graph is a forest in the walk definition used by
Kruskal's theorem. The bound is uniform over the whole graph sequence.
-/

public section

namespace GraphMinor.Mader

open Graph Surface GM09

universe u v

/-- The circuit packing bound of V (8.1) supplies a bounded vertex set whose
removal leaves a forest. The hypothesis is exactly the exclusion in
Mader's statement, including loops and parallel-edge circuits. -/
theorem exists_forest_deletion_bound (n : ℕ) : ∃ b : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → E(G).Finite → ¬ GM04.HasDisjointCircuits G (n + 1) →
      ∃ X ⊆ V(G), X.ncard ≤ b ∧ IsGraphForest (deleteVertices G X) := by
  obtain ⟨b, hb⟩ := GM05.theorem_8_1_proof.{u, v} (n + 1)
  refine ⟨b, ?_⟩
  intro α β G hV hE hno
  rcases hb G hV hE with hpack | ⟨X, hX, hcard, hforest⟩
  · exact (hno hpack).elim
  · exact ⟨X, hX, hcard, (isGraphForest_iff_no_circuit _).mpr hforest⟩

/-- A sequence with a fixed circuit bound has forest deletion sets with a
common size bound. This chooses actual vertex sets, rather than assuming
the existence of an encoding or an embedding. -/
theorem exists_forest_deletion_sets (n : ℕ) {α : Type u} {β : Type v}
    (G : ℕ → Graph α β) (hV : ∀ i, V(G i).Finite) (hE : ∀ i, E(G i).Finite)
    (hno : ∀ i, ¬ GM04.HasDisjointCircuits (G i) (n + 1)) :
    ∃ (b : ℕ) (X : ℕ → Set α), ∀ i,
      X i ⊆ V(G i) ∧ (X i).Finite ∧ (X i).ncard ≤ b ∧
        IsGraphForest (deleteVertices (G i) (X i)) := by
  obtain ⟨b, hb⟩ := exists_forest_deletion_bound.{u, v} n
  choose X hX hcard hforest using fun i ↦ hb (G i) (hV i) (hE i) (hno i)
  exact ⟨b, X, fun i ↦ ⟨hX i, (hV i).subset (hX i), hcard i, hforest i⟩⟩

end GraphMinor.Mader
