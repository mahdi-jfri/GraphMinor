module

public import GraphMinor.GM06.Alg34RegionClosure
import GraphMinor.Compute.GM06Alg34RegionBoundaryFacts

/-!
# Exact finite boundary lists after vertex deletion

The closure table computes the closure of each new region. Any inactive
cell in that closure already belongs to the same complement component,
so subtracting the region leaves exactly the active closure cells.
Splitting those cells into vertices and edges gives the supplied finite
boundary lists required for the updated drawing representation.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The boundary of a recomputed region consists exactly of the active
cells in its finite closure table. -/
theorem regionClass_boundary_cells (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (r : Fin x.cellCount) :
    closure (h.regionClass vs r) \ h.regionClass vs r =
      ⋃ b ∈ {b | x.activeCell vs b = true ∧ x.regionClosureHit vs r b = true}, h.cell b := by
  ext p
  constructor
  · rintro ⟨hpcl, hpnot⟩
    rw [h.closure_regionClass vs r] at hpcl
    obtain ⟨b, hb, hpb⟩ := mem_iUnion₂.mp hpcl
    cases ha : x.activeCell vs b with
    | false =>
      have hreach := (x.regionClosureHit_inactive_iff vs r b ha).mp hb
      exact False.elim (hpnot (mem_iUnion₂.mpr ⟨b, ⟨ha, hreach⟩, hpb⟩))
    | true => exact mem_iUnion₂.mpr ⟨b, ⟨ha, hb⟩, hpb⟩
  · intro hp
    obtain ⟨b, ⟨hactive, hhit⟩, hpb⟩ := mem_iUnion₂.mp hp
    refine ⟨(h.mem_closure_regionClass_iff vs r b hpb).mpr hhit, ?_⟩
    intro hpclass
    obtain ⟨c, ⟨hc, _⟩, hpc⟩ := mem_iUnion₂.mp hpclass
    have hbc := h.cell_index_eq_of_mem hpb hpc
    rw [← hbc, hactive] at hc
    exact Bool.noConfusion hc

/-- The computed vertex and edge lists are exactly the topological
boundary of the new region, in the form required by the drawing input. -/
theorem regionClass_boundary_eq (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (r : Fin x.cellCount) :
    closure (h.regionClass vs r) \ h.regionClass vs r =
      {p | ∃ v ∈ x.regionBoundaryVertices vs r, (h.vertex v).val = p} ∪
      ⋃ e ∈ x.regionBoundaryEdges vs r, (h.edge e).val := by
  rw [h.regionClass_boundary_cells vs r]
  ext p
  constructor
  · intro hp
    obtain ⟨b, ⟨hactive, hhit⟩, hpb⟩ := mem_iUnion₂.mp hp
    rcases b with v | e | s
    · have hv : v ∈ vs := by simpa only [GM06DrawingData.activeCell, decide_eq_true_eq] using hactive
      have hlist := (x.mem_regionBoundaryVertices_iff vs r v).mpr ⟨hv, hhit⟩
      exact Or.inl ⟨v, hlist, hpb.symm⟩
    · have hlist := (x.mem_regionBoundaryEdges_iff vs r e).mpr ⟨hactive, hhit⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨e, hlist, hpb⟩)
    · simp only [GM06DrawingData.activeCell, Bool.false_eq_true] at hactive
  · rintro (⟨v, hv, heq⟩ | hp)
    · obtain ⟨hactive, hhit⟩ := (x.mem_regionBoundaryVertices_iff vs r v).mp hv
      refine mem_iUnion₂.mpr ⟨.inl v, ⟨?_, hhit⟩, heq.symm⟩
      simpa only [GM06DrawingData.activeCell, decide_eq_true_eq] using hactive
    · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
      obtain ⟨hactive, hhit⟩ := (x.mem_regionBoundaryEdges_iff vs r e).mp he
      exact mem_iUnion₂.mpr ⟨.inr (.inl e), ⟨hactive, hhit⟩, hpe⟩

end GraphMinor.Compute.GM06DrawingRep
