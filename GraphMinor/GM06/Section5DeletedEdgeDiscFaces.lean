module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section5DeletedEdgeFaces
import GraphMinor.GM06.Section5DiscFrontierPaths
import GraphMinor.GM06.Section5DiscSphereEmbedding
import GraphMinor.GM06.RegionLocal
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.Regions
import GraphMinor.Surface.DiscNbhd

/-!
# The old approach face with cut-disc vertex copies fixed

For VI (5.5), page 131, perform the old-face choice in the cut disc.
Embed the disc in the sphere. Because the drawing contains its
boundary, each disc region is a sphere region of the embedded
drawing. The closed-surface old-face choice pulls back to an old
disc region incident with the specified endpoint copy of the
removed edge and with the last visit point.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

/-- The old approach region in a cut disc retains the prescribed
vertex copies, as required for the sided Reduction 1 proof of VI (5.5). -/
theorem exists_old_disc_region_at_deleted_edge_region_closure
    {S : Type u} [TopologicalSpace S] [T2Space S] (hDisc : IsClosedDiscSpace S)
    {G : Drawing S} (hbd : bd S ⊆ G.U) {e R : Set S}
    (he : e ∈ G.E) (heBd : Disjoint e (bd S))
    (hR : R ∈ (G.deleteEdge e).R) (heR : e ⊆ R)
    {s w : S} (hs : s ∈ closure e) (hw : w ∈ closure R) :
    ∃ r ∈ G.R, r ⊆ R ∧ s ∈ closure r ∧ w ∈ closure r := by
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace hDisc
  obtain ⟨x₀, hx₀⟩ := region_nonempty hR
  let : Nonempty S := ⟨x₀⟩
  have hS : IsSurface S := ⟨inferInstance, inferInstance,
    fun p => isManifoldPoint_of_disc hDisc.isClosedDisc_univ Filter.univ_mem⟩
  obtain ⟨j, hj, hopen, _⟩ := exists_closedDisc_sphere_embedding hDisc
  let A := GM07.embedDrawing hj G
  let D := G.deleteEdge e
  let es := j '' e
  have hDb : bd S ⊆ D.U := by
    intro x hx
    rw [deleteEdge_U G he]
    exact ⟨hbd hx, fun h => disjoint_left.mp heBd h hx⟩
  have hes : es ∈ A.E := by
    rw [GM07.embedDrawing_E]
    exact mem_image_of_mem _ he
  have hAB : (A.deleteEdge es).U = (GM07.embedDrawing hj D).U := by
    rw [deleteEdge_U A hes, GM07.embedDrawing_U, GM07.embedDrawing_U,
      show D.U = G.U \ e from deleteEdge_U G he, image_sdiff hj.injective]
  have hJR : j '' R ∈ (A.deleteEdge es).R := by
    change j '' R ∈ componentsIn (univ \ (A.deleteEdge es).U)
    rw [hAB]
    exact image_region_of_boundary_subset hS hj hopen hDb hR
  have heJR : es ⊆ j '' R := image_mono heR
  have hwJR : j w ∈ closure (j '' R) := mem_closure_image hj.continuous.continuousAt hw
  have hSphere : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  obtain ⟨a, ha, haJR, hea, hwa⟩ :=
    exists_old_region_at_deleted_edge_region_closure hSphere hes hJR heJR hwJR
  obtain ⟨x, hxa⟩ := region_nonempty ha
  obtain ⟨y, hyR, hyx⟩ := haJR hxa
  have hyoff : y ∉ G.U := by
    intro hyG
    exact region_subset ha hxa (by
      rw [GM07.embedDrawing_U]
      exact ⟨y, hyG, hyx⟩)
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyoff
  have hJr := image_region_of_boundary_subset hS hj hopen hbd hr
  have heqa : j '' r = a := region_eq_of_mem hJr ha ⟨y, hyr, hyx⟩ hxa
  have hrR : r ⊆ R := by
    apply subset_region hR (region_isPreconnected hr) _ hyr hyR
    refine disjoint_left.mpr ?_
    intro y hyr hyD
    rw [deleteEdge_U G he] at hyD
    exact region_subset hr hyr hyD.1
  have hsa : j s ∈ closure a :=
    closure_minimal hea isClosed_closure (mem_closure_image hj.continuous.continuousAt hs)
  have hback {v : S} (hv : j v ∈ closure a) : v ∈ closure r := by
    rw [← heqa, hj.closure_image_eq] at hv
    obtain ⟨z, hz, hzv⟩ := hv
    exact hj.injective hzv ▸ hz
  exact ⟨r, hr, hrR, hback hsa, hback hwa⟩

end GraphMinor.GM06
