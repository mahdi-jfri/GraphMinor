module

public import GraphMinor.GM06.Section5CappedRegions
public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Regions
import GraphMinor.GM06.Section5LinkageDrawing
import GraphMinor.GM06.Section5RegionPoint

/-!
# Strip regions in the linkage and cuff comparison

For Lemma 10 in the proof of VI (5.7), page 133, the comparison
contains only linkage paths and cuffs. Its sphere regions adjoining
the inner gaps are therefore exactly the strips off the cuffs.
The region of the full graph at a gap lies in the corresponding
strip, so any comparison region containing it is that strip region.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

/-- In the sphere comparison drawing, a linkage strip off the cuffs
is an actual region, including when there is just one linkage path. -/
theorem sphere_strip_region_of_linkage_cuffs {k : ℕ} {G H : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hHU : H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder) (i : Fin k) :
    cylinderToSphere '' (cylinderStrip L i \ bd ClosedCylinder) ∈ (cylinderSphereDrawing H).R := by
  obtain ⟨A, _, hAU, _, _, hA, _⟩ := exists_linkage_union_drawing L hG
  have hHA : H.U = A.U ∪ bd ClosedCylinder := by rw [hAU]; exact hHU
  have hh := image_region_sdiff_boundary_mem_sphere_regions hHA (cylinderRegion_mem_regions hA i)
  simpa only [cylinderRegion, hAU, cylinderStrip] using hh

/-- A comparison region containing the graph region at the inner
gap is precisely the corresponding strip region off the cuffs. -/
theorem comparison_region_eq_strip_of_contains {k : ℕ} {G F H : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hHU : H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder)
    (i : Fin k) (s : (cylinderSphereDrawing H).R)
    (hs : cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder) ⊆ s.val) :
    s.val = cylinderToSphere '' (cylinderStrip L i \ bd ClosedCylinder) := by
  have hr := image_region_sdiff_boundary_mem_sphere_regions hFU (cylinderRegion_mem_regions hG i)
  obtain ⟨p, hp⟩ := region_nonempty hr
  have hstrip : p ∈ cylinderToSphere '' (cylinderStrip L i \ bd ClosedCylinder) := by
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q, ⟨cylinderRegion_subset_strip L i hq.1, hq.2⟩, rfl⟩
  exact region_eq_of_mem s.property (sphere_strip_region_of_linkage_cuffs L hG hHU i)
    (hs hp) hstrip

end GraphMinor.GM06
