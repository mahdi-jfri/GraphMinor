module

public import GraphMinor.Planar.Defs
public import GraphMinor.Minor.Basic
import GraphMinor.GM04.PlanarExcluded

/-!
# A comparable pair in a sequence beginning with a planar graph

Graph Minors V cites (1.7) from Graph Minors IV, where it follows from IV (1.4) (IV, page 229:
"It is easy to see that (1.4) is equivalent to the result stated earlier in this section").
If some later graph has a minor isomorphic to the first one, we are done. Otherwise the later
graphs all exclude the planar first graph, and IV (1.4) (`GM04.theorem_1_4`) gives a comparable
pair among them.
-/

public section
namespace GraphMinor.GM05
open Graph

/-- Graph Minors V, (1.7), page 93:
"If $G_1, G_2, \ldots$ is a countable sequence of graphs and $G_1$ is planar, then there exist $i, j$ with $j > i$ such that $G_i$ is isomorphic to a minor of $G_j$."

The sequence is indexed from zero. The proof is IV's: either a later graph contains the first
one as a minor, or IV (1.4) (`GM04.theorem_1_4`) applies to the later graphs. -/
theorem theorem_1_7_proof {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hPlanar : IsPlanar (G 0)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  by_cases h : ∃ j, IsIsoMinor (G 0) (G (j + 1))
  · obtain ⟨j, hj⟩ := h
    exact ⟨0, j + 1, Nat.succ_pos j, hj⟩
  · simp only [not_exists] at h
    obtain ⟨i, j, hij, hm⟩ := GM04.theorem_1_4_proof (G 0) hPlanar (fun n => G (n + 1))
      (fun n => hV (n + 1)) (fun n => hE (n + 1)) h
    exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, hm⟩

end GraphMinor.GM05
