module

public import GraphMinor.GM06.Alg34InducedCells
public import GraphMinor.GM06.Alg34FiniteCellComponents

/-!
# Recomputing regions after deletion by finite incidence

The supplied cells partition the ambient space. The complement of the
induced drawing is therefore exactly the union of its inactive cells:
deleted vertices, deleted edges, and all original regions. Its connected
components are the reachability classes in the supplied incidence table.
This gives the mathematical correctness of the finite region update
needed after the singleton reduction (3.3)(i).
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 Relation

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- In the supplied cell partition, complementing a cell union selects
exactly the other cell labels. -/
theorem complement_cell_union (h : GM06DrawingRep x G Δ) (K : Set (GM06CellIndex x)) :
    (⋃ a ∈ K, h.cell a)ᶜ = ⋃ a ∈ Kᶜ, h.cell a := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, hpa⟩ := h.exists_cell_of_point p
    have ha : a ∉ K := fun ha => hp (mem_iUnion₂.mpr ⟨a, ha, hpa⟩)
    exact mem_iUnion₂.mpr ⟨a, ha, hpa⟩
  · intro hp hpK
    obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp hp
    obtain ⟨b, hb, hpb⟩ := mem_iUnion₂.mp hpK
    have hab := h.cell_index_eq_of_mem hpa hpb
    exact ha (hab.symm ▸ hb)

/-- Deletion adds precisely the inactive original cells to the complement. -/
theorem induced_complement_eq_cells [T1Space S] (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) :
    (induceDrawing G (h.vertexImage vs)).Uᶜ =
      ⋃ a ∈ {a | x.activeCell vs a = false}, h.cell a := by
  rw [h.induced_U_eq_active_cells, h.complement_cell_union]
  apply congrArg (fun K : Set (GM06CellIndex x) => ⋃ a ∈ K, h.cell a)
  ext a
  cases hc : x.activeCell vs a <;> simp [hc]

/-- Regions of the induced drawing are computed by finite reachability
through inactive cells, using only the supplied closure-incidence table. -/
theorem induced_region_component_iff [T1Space S] (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) {a b : GM06CellIndex x}
    (ha : x.activeCell vs a = false) (hb : x.activeCell vs b = false)
    {p q : S} (hp : p ∈ h.cell a) (hq : q ∈ h.cell b) :
    q ∈ connectedComponentIn ((induceDrawing G (h.vertexImage vs)).Uᶜ) p ↔
      ReflTransGen (fun c d => x.activeCell vs c = false ∧
        x.activeCell vs d = false ∧ x.cellTouch c d = true) a b := by
  rw [h.induced_complement_eq_cells vs]
  exact h.finite_cell_component_iff {a | x.activeCell vs a = false} ha hb hp hq

end GraphMinor.Compute.GM06DrawingRep
