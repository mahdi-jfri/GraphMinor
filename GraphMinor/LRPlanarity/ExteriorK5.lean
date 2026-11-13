module

public import GraphMinor.HP25.Web
import GraphMinor.Crossing.PlanarEuler
import Mathlib.Tactic.NormNum

/-!
# The Euler obstruction in the exterior-arc argument

Part IV, Section 7c of the planarity note ends by counting the vertices and
edges of the constructed complete graph. This file proves that final
contradiction. The construction from alternating exterior arcs is a separate
geometric obligation.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, Section 7c: a plane drawing of the complete graph on five vertices
would have ten edges, whereas Euler's bound permits only nine. -/
theorem not_planeEmbedding_K5 :
    ¬ Nonempty (HP25.PlaneEmbedding (⊤ : SimpleGraph (Fin 5)) Set.univ) := by
  intro h
  have bound := Crossing.planar_edge_bound_univ h (by decide)
  have edges : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by decide
  rw [edges] at bound
  norm_num at bound

end GraphMinor.LRPlanarity
