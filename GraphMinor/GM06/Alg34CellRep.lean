module

public import GraphMinor.Compute.GM06Alg34Cells
import GraphMinor.GM11.Defs
import GraphMinor.GM11.Regions

/-!
# Interpreting the supplied cell closure lists

The finite cell labels denote vertex points, open edges, and regions of
the represented drawing. Each cell is connected. The supplied endpoint
and region-boundary equations give exactly its closure as a union of
labelled cells. These facts connect finite incidence calculations with
the region-update criterion for (3.3)(i).
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM11

universe u

/-- The actual subset denoted by one finite drawing-cell label. -/
def cell {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) : GM06CellIndex x → Set S
  | .inl v => {(h.vertex v).val}
  | .inr (.inl e) => (h.edge e).val
  | .inr (.inr r) => (h.region r).val

/-- Every supplied cell denotes a nonempty connected subset. -/
theorem cell_isConnected {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) (a : GM06CellIndex x) :
    IsConnected (h.cell a) := by
  rcases a with v | e | r
  · exact isConnected_singleton
  · exact (h.edge e).property.2.2.1.isConnected
  · exact ⟨region_nonempty (h.region r).property, region_isPreconnected (h.region r).property⟩

/-- The supplied finite closure list is exactly the topological closure
of the corresponding vertex, edge, or region cell. -/
theorem closure_cell {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) (a : GM06CellIndex x) :
    closure (h.cell a) = ⋃ b ∈ x.cellClosure a, h.cell b := by
  rcases a with v | e | r
  · simp [cell, GM06DrawingData.cellClosure]
  · have heq : closure (h.edge e).val = (h.edge e).val ∪
        {(h.vertex x.ends[e].1).val, (h.vertex x.ends[e].2).val} := by
      calc
        closure (h.edge e).val =
            (closure (h.edge e).val \ G.V) ∪ (closure (h.edge e).val ∩ G.V) :=
          (sdiff_union_inter _ _).symm
        _ = _ := by rw [G.closure_diff_V (h.edge e).property, h.ends e]
    simpa [cell, GM06DrawingData.cellClosure, union_assoc, insert_comm] using heq
  · have heq : closure (h.region r).val = (h.region r).val ∪
        (closure (h.region r).val \ (h.region r).val) := by
      ext p
      constructor
      · intro hp
        by_cases hr : p ∈ (h.region r).val
        · exact Or.inl hr
        · exact Or.inr ⟨hp, hr⟩
      · exact fun hp => hp.elim (fun hp => subset_closure hp) (fun hp => hp.1)
    rw [show h.cell (.inr (.inr r)) = (h.region r).val from rfl, heq, h.boundary r]
    ext p
    simp [GM06DrawingData.cellClosure, cell, eq_comm]

end GraphMinor.Compute.GM06DrawingRep
