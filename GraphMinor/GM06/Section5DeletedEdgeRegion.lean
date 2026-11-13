module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Regions

/-!
# The region containing a deleted edge

In VI (5.5), the deleted edge is connected and misses the remaining
drawing, so it lies in one of its regions. The retained linkage
still bounds every such region. Connectedness therefore puts the
region in the old linkage strip that it meets.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- The deleted edge lies in one region of the drawing left after
its deletion, as chosen in VI (5.5), page 130. -/
theorem exists_region_containing_deleted_edge {G G' : Drawing ClosedCylinder} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hU : G'.U = G.U \ e) :
    ∃ R : Set ClosedCylinder, R ∈ G'.R ∧ e ⊆ R := by
  obtain ⟨x, hxe⟩ := he.1
  have hxoff : x ∉ G'.U := by
    rw [hU]
    exact fun hx => hx.2 hxe
  obtain ⟨R, hR, hxR⟩ := GM11.exists_region_of_notMem hxoff
  refine ⟨R, hR, GM11.subset_region hR he.2.2.1.isConnected.isPreconnected ?_ hxe hxR⟩
  refine disjoint_left.mpr ?_
  intro y hye hyU
  rw [hU] at hyU
  exact hyU.2 hye
/-- A region of a drawing containing the unchanged linkage lies
inside the old strip that it meets. This is the strip confinement
used for the deleted-edge region in VI (5.5), pages 131–132. -/
theorem region_subset_strip_of_retained_linkage {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hpaths : L'.pathDrawing = L.pathDrawing) {R : Set ClosedCylinder} (hR : R ∈ G'.R)
    (i : Fin k) (hmeet : (R ∩ cylinderStrip L i).Nonempty) : R ⊆ cylinderStrip L i := by
  obtain ⟨x, hxR, hxS⟩ := hmeet
  have hsub : R ⊆ univ \ ⋃ j, (L.pathDrawing j).U := by
    intro y hyR
    refine ⟨mem_univ _, ?_⟩
    intro hyP
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyP
    have hU : (L.pathDrawing j).U ⊆ G'.U := by
      have hh := (L'.isSubdrawing j).2
      rw [hpaths] at hh
      exact hh
    exact GM11.region_subset hR hyR (hU hyj)
  have hcomp := (GM11.region_isPreconnected hR).subset_connectedComponentIn hxR hsub
  have heq := connectedComponentIn_eq hxS
  change cylinderStrip L i = connectedComponentIn (univ \ ⋃ j, (L.pathDrawing j).U) x at heq
  rw [← heq] at hcomp
  exact hcomp
end GraphMinor.GM06
