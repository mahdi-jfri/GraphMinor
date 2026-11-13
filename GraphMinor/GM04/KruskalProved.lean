module

public import GraphMinor.GM04.Cited
import GraphMinor.Kruskal.Main

/-!
# Graph Minors IV (1.2) without the Kruskal hypothesis

The external tree theorem is proved in `GraphMinor.Kruskal.Main` by the
minimal bad sequence argument and a conversion to edge subdivisions.
This file supplies the numbered theorem without an external hypothesis.
-/

public section

namespace GraphMinor.GM04

open Graph

universe u v

/-- Graph Minors IV, (1.2), page 229:
"The class of all trees is well-quasi-ordered by topological containment."
The cited tree theorem is supplied by `Kruskal.kruskal_tree`. -/
theorem theorem_1_2_proved {α : Type u} {β : Type v} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hT : ∀ n, IsUndirectedTree (G n)) :
    ∃ i j, i < j ∧ IsTopologicalMinor (G i) (G j) :=
  Kruskal.kruskal_tree.{u, v} G hV hE hT

end GraphMinor.GM04
