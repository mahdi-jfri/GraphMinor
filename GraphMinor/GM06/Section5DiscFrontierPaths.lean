module

public import GraphMinor.GM06.Section5DiscSphereEmbedding
public import GraphMinor.GM06.Section5EmbeddedPaths
import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5SphereRegions
import GraphMinor.GM06.Section5FrontierPaths
import GraphMinor.Surface.DiscNbhd
import GraphMinor.GM11.Regions
import GraphMinor.GM11.PerimeterPull

/-!
# Boundary paths in the augmented cut disc

Embed the cut disc in the sphere. Since its whole boundary belongs
to the augmented drawing, each old region has open image and remains
a whole region. A connected drawing has disc regions in the sphere.
The region walk therefore joins two frontier vertices while avoiding
an added boundary edge, which has at most one side in the region.
Pull the path back to the disc. This is the boundary-path construction
used in the one-path case of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

/-- A closed embedding with open interior image carries each region of
a drawing containing the surface boundary to a region of its image drawing. -/
theorem image_region_of_boundary_subset
    {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S] [Nonempty S]
    (hS : IsSurface S) {j : S → OnePoint EuclideanPlane} (hj : IsClosedEmbedding j)
    (hopen : IsOpen (j '' (bd S)ᶜ)) {F : Drawing S} (hbd : bd S ⊆ F.U)
    {r : Set S} (hr : r ∈ F.R) : r.image j ∈ (GM07.embedDrawing hj F).R := by
  let : LocallyConnectedSpace S := IsSurface.locallyConnected hS
  have hro := region_isOpen hr
  have hrbd : r ⊆ (bd S)ᶜ := fun x hx hxb => region_subset hr hx (hbd hxb)
  obtain ⟨O, hO, hOr⟩ := hj.isEmbedding.isInducing.image_eq_isOpen_inter_range hro
  have him : j '' r = O ∩ (j '' (bd S)ᶜ) := by
    ext z
    constructor
    · intro hz
      exact ⟨(hOr ▸ hz).1, image_mono hrbd hz⟩
    · rintro ⟨hz, x, hx, rfl⟩
      rw [hOr]
      exact ⟨hz, mem_range_self x⟩
  have hio : IsOpen (j '' r) := him ▸ hO.inter hopen
  have hdis : Disjoint (j '' r) (GM07.embedDrawing hj F).U := by
    rw [GM07.embedDrawing_U]
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    exact region_subset hr hx (hj.injective hyx ▸ hy)
  have hfr : frontier (j '' r) ⊆ (GM07.embedDrawing hj F).U := by
    intro z hz
    have hzc := hz.1
    rw [hj.closure_image_eq] at hzc
    obtain ⟨x, hx, rfl⟩ := hzc
    rcases closure_region_subset hr hx with hxr | hxF
    · exact False.elim (hz.2 (hio.interior_eq.symm ▸ mem_image_of_mem j hxr))
    · rw [GM07.embedDrawing_U]
      exact mem_image_of_mem j hxF
  exact region_of_connected_open_frontier
    ((show IsConnected r from ⟨region_nonempty hr, region_isPreconnected hr⟩).image
      j hj.continuous.continuousOn) hio hdis hfr

/-- Distinct vertices incident with a region of a connected drawing
containing the disc boundary are joined along the region closure while
avoiding any specified boundary edge. -/
theorem exists_subpath_in_disc_region_closure_avoiding_boundary_edge
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hconn : IsConnected F.U) (hbd : bd S ⊆ F.U)
    {r : Set S} (hr : r ∈ F.R) {a b : S}
    (ha : a ∈ F.V ∩ closure r) (hb : b ∈ F.V ∩ closure r) (hab : a ≠ b)
    {e : Set S} (he : e ∈ F.E) (heBd : e ⊆ bd S) :
    ∃ Q : Drawing S, IsSubpathOf F Q a b ∧ Q.U ⊆ closure r ∧ e ∉ Q.E := by
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace hDisc
  let : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  let : Nonempty S := ⟨a⟩
  have hS : IsSurface S := ⟨inferInstance, inferInstance,
    fun p => isManifoldPoint_of_disc hDisc.isClosedDisc_univ Filter.univ_mem⟩
  obtain ⟨j, hj, hopen, hjbd⟩ := exists_closedDisc_sphere_embedding hDisc
  let H := GM07.embedDrawing hj F
  let R := j '' r
  have hR : R ∈ H.R := image_region_of_boundary_subset hS hj hopen hbd hr
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hSphere := IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hSphere.2
  have hH : H.IsTwoCell := by
    apply isTwoCell_of_connected_drawing_in_sphere hSphere.1 hsph
    rw [GM07.embedDrawing_U]
    exact hconn.image j hj.continuous.continuousOn
  have heH : j '' e ∈ H.E := by
    rw [GM07.embedDrawing_E]
    exact ⟨e, he, rfl⟩
  have hfront (x : S) (hx : x ∈ F.V ∩ closure r) : j x ∈ H.V ∩ frontier R := by
    constructor
    · rw [GM07.embedDrawing_V]
      exact mem_image_of_mem j hx.1
    · constructor
      · rw [show R = j '' r from rfl, hj.closure_image_eq]
        exact mem_image_of_mem j hx.2
      · intro hxi
        obtain ⟨y, hy, hyx⟩ := interior_subset hxi
        exact region_subset hr (hj.injective hyx ▸ hy) (F.V_subset_U hx.1)
  have hone : ¬ IsTwoSided R (j '' e) := by
    rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
    have hsub : R ∪ (j '' e) ⊆ range j :=
      union_subset (image_subset_range _ _) (image_subset_range _ _)
    exact hjbd x (heBd hx) (interior_mono hsub hz)
  obtain ⟨P, hP, hPU, heP⟩ := exists_subpath_in_region_frontier_avoiding_one_sided_edge
    hSphere.1 hsph hH ⟨_, heH⟩ hR (hfront a ha) (hfront b hb)
    (fun h => hab (hj.injective h)) heH hone
  obtain ⟨Q, hQ, hQU, heQ⟩ := exists_subpath_of_embedded_subpath_avoiding_edge hj hab hP heP
  refine ⟨Q, hQ, ?_, heQ⟩
  intro x hx
  have hxcl := (hPU (hQU (mem_image_of_mem j hx))).1
  change j x ∈ closure (j '' r) at hxcl
  rw [hj.closure_image_eq] at hxcl
  obtain ⟨y, hy, hyx⟩ := hxcl
  exact hj.injective hyx ▸ hy

end GraphMinor.GM06
