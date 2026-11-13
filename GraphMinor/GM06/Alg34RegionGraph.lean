module

public import GraphMinor.GM06.Alg34ComplementCells
public import GraphMinor.Compute.GM06Alg34CellGraph

/-!
# Regions represented by the finite complement graph

The graph on packed inactive-cell labels computes the regions of the
induced drawing. Each of its classes of inactive cells has an actual
region as its union, and every point in such a class has exactly the
corresponding connected-component membership. These facts justify
using a finite graph routine for the region update after (3.3)(i).
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- Reachability in the ordinary packed finite graph computes exactly
the new region containing two inactive cells. -/
theorem regionGraph_component_iff (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    {a b : GM06CellIndex x} (ha : x.activeCell vs a = false) (hb : x.activeCell vs b = false)
    {p q : S} (hp : p ∈ h.cell a) (hq : q ∈ h.cell b) :
    q ∈ connectedComponentIn ((induceDrawing G (h.vertexImage vs)).Uᶜ) p ↔
      (x.complementGraph vs).Reachable (x.cellNumbering a) (x.cellNumbering b) :=
  (h.induced_region_component_iff vs ha hb hp hq).trans
    (x.complementGraph_reachable_iff vs a b).symm

/-- The union computed by one inactive cell's finite reachability class
is exactly a region of the vertex-induced drawing. -/
theorem regionGraph_class_mem_regions (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (a : GM06CellIndex x) (ha : x.activeCell vs a = false) :
    (⋃ b ∈ {b | x.activeCell vs b = false ∧
      (x.complementGraph vs).Reachable (x.cellNumbering a) (x.cellNumbering b)}, h.cell b) ∈
        (induceDrawing G (h.vertexImage vs)).R := by
  obtain ⟨p, hp⟩ := (h.cell_isConnected a).1
  have hpU : p ∈ (induceDrawing G (h.vertexImage vs)).Uᶜ := by
    rw [h.induced_complement_eq_cells vs]
    exact mem_iUnion₂.mpr ⟨a, ha, hp⟩
  have heq : (⋃ b ∈ {b | x.activeCell vs b = false ∧
      (x.complementGraph vs).Reachable (x.cellNumbering a) (x.cellNumbering b)}, h.cell b) =
      connectedComponentIn ((induceDrawing G (h.vertexImage vs)).Uᶜ) p := by
    ext q
    constructor
    · intro hq
      obtain ⟨b, ⟨hb, hab⟩, hqb⟩ := mem_iUnion₂.mp hq
      exact (h.regionGraph_component_iff vs ha hb hp hqb).mpr hab
    · intro hq
      have hqU := connectedComponentIn_subset _ _ hq
      rw [h.induced_complement_eq_cells vs] at hqU
      obtain ⟨b, hb, hqb⟩ := mem_iUnion₂.mp hqU
      exact mem_iUnion₂.mpr ⟨b, ⟨hb, (h.regionGraph_component_iff vs ha hb hp hqb).mp hq⟩, hqb⟩
  rw [heq]
  exact ⟨p, ⟨mem_univ p, hpU⟩, by
    congr 1
    ext q
    simp only [mem_sdiff, mem_univ, true_and, mem_compl_iff]⟩

end GraphMinor.Compute.GM06DrawingRep
