module

public import GraphMinor.GM02.PortGeometricFamily
public import GraphMinor.GM02.EdgeRouteContainment

/-!
# Feasibility of the corrected split test implies containment

Project a feasible split family to disjoint edge-labelled host routes,
then suppress their interiors. Unlike the printed construction in II
(4.5), the edge vertices prevent two routes from sharing a host edge,
and the terminal choices rule out a false one-edge pattern loop.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- The corrected split test cannot certify false containment, for arbitrary patterns. -/
theorem topologicallyContains_of_portFeasible {α : Type u} {β : Type v} {k : ℕ}
    (G H : Graph α β) (hV : V(G).Finite) (hVH : V(H) ⊆ V(G))
    (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (choice : PortChoice G ends)
    (hfeas : (portTermination G H choice).Feasible (portGraph G H choice)) :
    TopologicallyContains G H := by
  obtain ⟨inner, W, hW, hdis⟩ := exists_portGeometric_family G H choice hVH
    (fun i => ⟨(hH i).left_mem, (hH i).right_mem⟩) hfeas
  exact topologicallyContains_of_edgeRoutes G H hV hVH edge ends hH inner W
    (fun i => (hW i).1) (fun i => (hW i).2.1) (fun i => (hW i).2.2.1)
    (fun i j hij => (hdis i j hij).1)
    (fun i => (hW i).2.2.2.1) (fun i => (hW i).2.2.2.2)
    (fun i j hij => (hdis i j hij).2)

end GraphMinor.GM02
