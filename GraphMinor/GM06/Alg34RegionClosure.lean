module

public import GraphMinor.GM06.Alg34RegionLabels
public import GraphMinor.Compute.GM06Alg34RegionBoundary

/-!
# Closures of recomputed regions from the finite table

A new region is a finite union of original cells. Closure commutes with
that finite union, and each original closure is described by its supplied
list. Thus the finite closure-hit test computes the exact closure of the
new region. This is the first part of the boundary-update proof for
singleton deletion.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The closure of a new region is exactly the cell union computed by
the finite closure-hit test. This holds for any packed starting label. -/
theorem closure_regionClass (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (r : Fin x.cellCount) :
    closure (h.regionClass vs r) =
      ⋃ b ∈ {b | x.regionClosureHit vs r b = true}, h.cell b := by
  rw [regionClass, Set.Finite.closure_biUnion (Set.toFinite _)]
  simp_rw [h.closure_cell]
  ext p
  simp only [mem_iUnion, exists_prop, mem_ofPred_eq,
    GM06DrawingData.regionClosureHit, decide_eq_true_eq]
  constructor
  · rintro ⟨c, ⟨hc, hrc⟩, b, hb, hpb⟩
    exact ⟨b, ⟨c, hc, hrc, hb⟩, hpb⟩
  · rintro ⟨b, ⟨c, hc, hrc, hb⟩, hpb⟩
    exact ⟨c, ⟨hc, hrc⟩, b, hb, hpb⟩

/-- At a point of a labelled cell, closure membership of a new region
is exactly the finite hit test for that cell label. -/
theorem mem_closure_regionClass_iff (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (r : Fin x.cellCount) (b : GM06CellIndex x) {p : S} (hp : p ∈ h.cell b) :
    p ∈ closure (h.regionClass vs r) ↔ x.regionClosureHit vs r b = true := by
  rw [h.closure_regionClass vs r]
  constructor
  · intro hcl
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp hcl
    exact h.cell_index_eq_of_mem hp hpc ▸ hc
  · intro hb
    exact mem_iUnion₂.mpr ⟨b, hb, hp⟩

end GraphMinor.Compute.GM06DrawingRep
