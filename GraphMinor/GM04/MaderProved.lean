module

public import GraphMinor.GM04.TopologicalContainment
import GraphMinor.Mader.Main

/-!
# Graph Minors IV (1.3) without the Mader hypothesis

The circuit-bound theorem is proved in `GraphMinor.Mader.Main` from a
bounded forest deletion and labelled Kruskal. For positive `k`, excluding
`k` disjoint circuits gives Mader's bound `k - 1`. For `k = 0`, every
graph has the empty circuit family, so the class is empty.
-/

public section

namespace GraphMinor.GM04

open Graph

universe u v

/-- Graph Minors IV, (1.3), page 229:
"For any integer $k \ge 0$, the class of all graphs without $k$ vertex-disjoint circuits is well-quasi-ordered by topological containment."
The external statement is supplied by `Mader.mader_circuit`. -/
theorem theorem_1_3_proved (k : ℕ) {α : Type u} {β : Type v}
    (G : ℕ → Graph α β) (hV : ∀ i, V(G i).Finite) (hE : ∀ i, E(G i).Finite)
    (hC : ∀ i, ¬ HasDisjointCircuits (G i) k) :
    ∃ i j, i < j ∧ IsTopologicalMinor (G i) (G j) := by
  cases k with
  | zero => exact (hC 0 (hasDisjointCircuits_zero (G 0))).elim
  | succ n => exact Mader.mader_circuit.{u, v} n G hV hE hC

end GraphMinor.GM04
