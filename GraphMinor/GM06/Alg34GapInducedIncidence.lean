module

public import GraphMinor.GM06.Alg34GapInducedSegments
public import GraphMinor.GM06.Alg34GapRegionUpdateCorrect
import GraphMinor.GM06.Alg34GapRegions

/-!
# Incident regions at retained gap points

The old gap segment lies in its supplied incident region. That whole
region remains in the computed new complement region after vertex
deletion. Its retained gap point therefore witnesses incidence between
the computed new region and the new boundary segment.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06 GM06DrawingData

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The selected gap point belongs to its computed new incident region. -/
theorem inducedPoint_mem_region (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (vs : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    g.inducedPoint vs i ∈
      (h.inducedRegion vs (Fin.cast (x.inducedData_regions_length vs)
        (x.regionAfterDeletion vs (g.region (gm06InducedGapPosition x vs x.cuffs[c] i))))).val := by
  let j := gm06InducedGapPosition x vs x.cuffs[c] i
  have hs : g.segment j ∈ segmentsOf (bd S) (G.V ∩ bd S) := by
    have hh := g.segment_mem j
    rw [h.disc_cuff_eq_bd hS] at hh
    exact hh
  have hp : g.point j ∈ (h.region (g.region j)).val :=
    GM06DrawingRep.gap_subset_region hproper hs (h.region (g.region j)).property
      (g.region_meets j) (g.point_mem j)
  exact h.regionAfterDeletion_contains vs (g.region j) hp

/-- A retained point witnesses the exact new region/segment incidence. -/
theorem induced_region_meets (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (vs : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    ((h.inducedRegion vs (Fin.cast (x.inducedData_regions_length vs)
        (x.regionAfterDeletion vs (g.region (gm06InducedGapPosition x vs x.cuffs[c] i))))).val ∩
      g.inducedSegment vs i).Nonempty :=
  ⟨g.inducedPoint vs i, g.inducedPoint_mem_region hS hproper vs i,
    g.inducedPoint_mem_segment vs i⟩

end GraphMinor.Compute.GM06CuffGapRep
