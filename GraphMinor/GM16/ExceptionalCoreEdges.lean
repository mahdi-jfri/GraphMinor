module

public import GraphMinor.GM16.LocationEdgeRefinement
public import GraphMinor.GM16.LocationLift
import GraphMinor.GM09.Basic

/-!
# Clearing exceptional edges from the lifted core

The enlargement verification in XVI (1.3), pages 51–52, requires that
the restored exceptional vertices add no core edges. We refine the
lifted location by the single-edge separations of its core edges
incident with those vertices. The resulting core has the old core's
edges and the lifted core's vertices.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- Core edges incident with the exceptional vertex set. -/
def exceptionalCoreEdges {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α)
    (ℒ : Set (Graph α β × Graph α β)) : Set β :=
  {e ∈ E(graphLocationCore G ℒ) | ∃ x ∈ Z, G.Inc e x}

/-- The exceptional core edge set is finite in a finite graph. -/
theorem exceptionalCoreEdges_finite {α : Type u} {β : Type v}
    {G : Graph α β} (hE : E(G).Finite) (Z : Set α)
    (ℒ : Set (Graph α β × Graph α β)) : (exceptionalCoreEdges G Z ℒ).Finite :=
  hE.subset (fun _ he => (graphLocationCore_le G ℒ).edgeSet_mono he.1)

/-- Removing the exceptional core edges leaves exactly the edges that
survive deleting the exceptional vertices. -/
theorem edgeSet_core_sdiff_exceptional {α : Type u} {β : Type v}
    (G : Graph α β) (Z : Set α) (ℒ : Set (Graph α β × Graph α β)) :
    E(graphLocationCore G ℒ) \ exceptionalCoreEdges G Z ℒ =
      E(deleteVertices (graphLocationCore G ℒ) Z) := by
  let C := graphLocationCore G ℒ
  have hCG : C ≤ G := graphLocationCore_le G ℒ
  ext e
  constructor
  · rintro ⟨heC, heNot⟩
    obtain ⟨x, y, hxy⟩ := C.exists_isLink_of_mem_edgeSet heC
    have hxZ : x ∉ Z := fun hx => heNot ⟨heC, x, hx, (hxy.mono hCG).inc_left⟩
    have hyZ : y ∉ Z := fun hy => heNot ⟨heC, y, hy, (hxy.mono hCG).inc_right⟩
    exact ((deleteVertices_isLink C Z).mpr ⟨hxy, hxZ, hyZ⟩).edge_mem
  · intro heDel
    have heC := (deleteVertices_le C Z).edgeSet_mono heDel
    refine ⟨heC, ?_⟩
    rintro ⟨_, x, hxZ, y, hxy⟩
    have hxyDel := (((deleteVertices_le C Z).trans hCG).isLink_iff heDel).mpr hxy
    exact hxyDel.left_mem.2 hxZ

/-- The refined lift used to verify the design enlargement in the
proof of XVI (1.3), page 51. -/
def restoredLocation {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α)
    (ℒ : Set (Graph α β × Graph α β)) : Set (Graph α β × Graph α β) :=
  refineLocationEdges G (liftedLocation G Z ℒ)
    (exceptionalCoreEdges G Z (liftedLocation G Z ℒ))

/-- The restored and refined pairs form a location. -/
theorem IsGraphLocation.restore {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G)) (hE : E(G).Finite)
    {ℒ : Set (Graph α β × Graph α β)} (h : IsGraphLocation (deleteVertices G Z) ℒ) :
    IsGraphLocation G (restoredLocation G Z ℒ) :=
  (h.lift hZ).refineEdges (exceptionalCoreEdges_finite hE Z _)
    (fun _ he => he.1)

/-- The restored core has the old core vertices together with the
exceptional vertices. -/
theorem vertexSet_restored_core {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    (ℒ : Set (Graph α β × Graph α β)) :
    V(graphLocationCore G (restoredLocation G Z ℒ)) =
      V(graphLocationCore (deleteVertices G Z) ℒ) ∪ Z :=
  (vertexSet_refined_core G _ _).trans (vertexSet_lifted_core hZ ℒ)

/-- Unlike the unrefined lift, the restored core adds no core edges.
This is the edge condition in the design enlargement of XVI, page 47. -/
theorem edgeSet_restored_core {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G)) (hE : E(G).Finite)
    {ℒ : Set (Graph α β × Graph α β)} (h : IsGraphLocation (deleteVertices G Z) ℒ) :
    E(graphLocationCore G (restoredLocation G Z ℒ)) =
      E(graphLocationCore (deleteVertices G Z) ℒ) := by
  rw [restoredLocation, edgeSet_refined_core (h.lift hZ)
    (exceptionalCoreEdges_finite hE Z _) (fun _ he => he.1),
    edgeSet_core_sdiff_exceptional, deleteVertices_lifted_core hZ h]

end GraphMinor.GM16
