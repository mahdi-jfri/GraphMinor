module

public import GraphMinor.GM02.PortContainment
import GraphMinor.GM02.ContainmentEdgeRoutes
import GraphMinor.GM02.PortRouteFeasible

/-!
# The corrected split test for arbitrary patterns

After the branch loops are removed in II (4.6), topological containment
is equivalent to feasibility for some choice of incident terminal edges.
One direction projects split paths to host routes and suppresses their
interiors. The other traces the suppression sequence, chooses terminal
incidences, and extracts disjoint paths in the route reservations.

Unlike the printed (4.5), this test retains host-edge names and requires
different choices at the two ends of a pattern loop. These changes avoid
the loop and parallel-edge counterexamples to (4.5) (see the correction to (4.5) in
`corrections/GM02.md`).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Containment gives a feasible corrected split choice after host branch loops are removed. -/
theorem exists_portFeasible_of_topologicallyContains {α : Type u} {β : Type v} {k : ℕ}
    (G H : Graph α β) (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (hNoLoop : ∀ e a, a ∈ V(H) → ¬G.IsLoopAt e a)
    (hTopo : TopologicallyContains G H) :
    ∃ choice : PortChoice G ends,
      (portTermination G H choice).Feasible (portGraph G H choice) := by
  obtain ⟨inner, W, hW, hDis⟩ := exists_edgeRoutes_of_topologicallyContains G H edge ends hH hTopo
  exact exists_portFeasible_of_routes G H ends inner W (fun i => (hH i).left_mem) hNoLoop
    (fun i => (hW i).1) (fun i => (hW i).2.2.1)
    (fun i => (hW i).2.2.2.1) (fun i => (hW i).2.2.2.2) hDis

/-- The split test with host-edge vertices is valid for loops and parallel pattern edges. -/
theorem topologicallyContains_iff_exists_portFeasible {α : Type u} {β : Type v} {k : ℕ}
    (G H : Graph α β) (hV : V(G).Finite) (hVH : V(H) ⊆ V(G))
    (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (hNoLoop : ∀ e a, a ∈ V(H) → ¬G.IsLoopAt e a) :
    TopologicallyContains G H ↔ ∃ choice : PortChoice G ends,
      (portTermination G H choice).Feasible (portGraph G H choice) := by
  constructor
  · exact exists_portFeasible_of_topologicallyContains G H edge ends hH hNoLoop
  · rintro ⟨choice, hchoice⟩
    exact topologicallyContains_of_portFeasible G H hV hVH edge ends hH choice hchoice

end GraphMinor.GM02
