module

public import GraphMinor.Compute.GM06Alg34GapRegionUpdate
public import GraphMinor.GM06.Alg34InducedLabels

/-!
# Correct interpretation of reindexed gap regions

The old region cell remains inactive under deletion. Its computed new
root is reachable from that cell in the complement graph. The exact
cell-component interpretation therefore puts the whole old region in
the new region denoted by the computed label. In particular any supplied
gap point keeps the correct incident region after deletion.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The canonical new region selected for an old gap region contains
that entire old region, not merely a chosen representative point. -/
theorem regionAfterDeletion_contains (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (r : Fin x.regions.length) :
    (h.region r).val ⊆
      (h.inducedRegion vs (Fin.cast (x.inducedData_regions_length vs)
        (x.regionAfterDeletion vs r))).val := by
  intro p hp
  change p ∈ h.regionClass vs (x.regionRootAfterDeletion vs r)
  exact mem_iUnion₂.mpr ⟨.inr (.inr r),
    ⟨rfl, (x.regionAfterDeletion_reachable vs r).symm⟩, hp⟩

/-- A supplied gap point stays in its computed incident region after deletion. -/
theorem gap_point_mem_regionAfterDeletion (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (r : Fin x.regions.length) {p : S}
    (hp : p ∈ (h.region r).val) :
    p ∈ (h.inducedRegion vs (Fin.cast (x.inducedData_regions_length vs)
      (x.regionAfterDeletion vs r))).val := h.regionAfterDeletion_contains vs r hp

end GraphMinor.Compute.GM06DrawingRep
