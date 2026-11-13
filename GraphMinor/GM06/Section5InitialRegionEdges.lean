module

public import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Section5InitialRegionIncidence
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Corners

/-!
# Counting region edges at an initial vertex

For the boundary-contact step of VI (5.1), page 129, every edge
incident with a vertex gives a half-edge there. The bound of two
half-edges therefore bounds the number of incident edges as well.
The closed embedding of the cylinder preserves edge closures, so
this bound pulls back from the capped drawing to the cylinder.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

private theorem incident_edges_image_halfEdges
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {γ : Set S → I → S} (hγ : EdgePar D γ)
    {s : S} (hs : s ∈ D.V) (r : Set S) :
    {e ∈ D.E | s ∈ closure e ∧ e ⊆ closure r} =
      (fun j : halfEdges D γ s => j.1.1) ''
        {j : halfEdges D γ s | j.1.1 ⊆ closure r} := by
  ext e
  constructor
  · rintro ⟨he, hse, her⟩
    obtain ⟨b, hb⟩ := exists_end_eq hγ he hs hse
    exact ⟨⟨(e, b), he, hb⟩, her, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.2.1, ?_, hj⟩
    have hend := end_mem_closure hγ j.2.1 j.1.2
    rwa [j.2.2] at hend

/-- Each region of the capped drawing has at most two edges incident
with a fixed initial vertex in the unreduced case of VI (5.1). -/
theorem ncard_initial_capped_region_edges_le_two
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V) (i : Fin k)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ (cylinderSphereDrawing F).R)
    (hsr : cylinderToSphere (cylinderM1Point k i) ∈ closure r) :
    {e ∈ (cylinderSphereDrawing F).E |
      cylinderToSphere (cylinderM1Point k i) ∈ closure e ∧ e ⊆ closure r}.ncard ≤ 2 := by
  obtain ⟨γ, hγ⟩ := exists_edgePar (cylinderSphereDrawing F)
  have hs : cylinderToSphere (cylinderM1Point k i) ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V, hFV]
    exact mem_image_of_mem cylinderToSphere
      ((L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1)
  rw [incident_edges_image_halfEdges hγ hs r]
  have hfinite : Finite (halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i))) := (finite_halfEdges _ _ _).to_subtype
  exact (ncard_image_le (toFinite _)).trans
    (ncard_initial_region_halfEdges_le_two L hk hG hno hFU hFV i hγ hr hsr)

/-- In the cylinder drawing with cuffs adjoined, at most two edges
at an initial vertex are incident with its designated region Rᵢ. -/
theorem ncard_initial_region_edges_le_two
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V) (i : Fin k) :
    {e ∈ F.E | cylinderM1Point k i ∈ closure e ∧ e ⊆ closure (cylinderRegion k G i)}.ncard ≤ 2 := by
  let A := {e ∈ F.E | cylinderM1Point k i ∈ closure e ∧ e ⊆ closure (cylinderRegion k G i)}
  let Y := cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder)
  have hr := cylinderRegion_mem_regions hG i
  have hY : Y ∈ (cylinderSphereDrawing F).R := image_region_sdiff_boundary_mem_sphere_regions hFU hr
  have hclY : closure Y = cylinderToSphere '' closure (cylinderRegion k G i) :=
    closure_image_region_sdiff_boundary hr
  have hsY : cylinderToSphere (cylinderM1Point k i) ∈ closure Y := by
    rw [hclY]
    exact mem_image_of_mem cylinderToSphere (initial_vertices_mem_closure_cylinderRegion hG i).1
  have hsub : (image cylinderToSphere) '' A ⊆
      {e ∈ (cylinderSphereDrawing F).E |
        cylinderToSphere (cylinderM1Point k i) ∈ closure e ∧ e ⊆ closure Y} := by
    rintro e ⟨a, ha, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [cylinderSphereDrawing_E]; exact mem_image_of_mem _ ha.1
    · rw [isClosedEmbedding_cylinderToSphere.closure_image_eq]
      exact mem_image_of_mem cylinderToSphere ha.2.1
    · rw [hclY]
      exact image_mono ha.2.2
  have hinj : Function.Injective (image cylinderToSphere) :=
    fun a b h => (Set.image_injective.mpr injective_cylinderToSphere) h
  have hfin : {e ∈ (cylinderSphereDrawing F).E |
      cylinderToSphere (cylinderM1Point k i) ∈ closure e ∧ e ⊆ closure Y}.Finite :=
    (cylinderSphereDrawing F).finite_edges.subset (fun _ h => h.1)
  have hle := ncard_le_ncard hsub hfin
  rw [ncard_image_of_injective A hinj] at hle
  exact hle.trans (ncard_initial_capped_region_edges_le_two L hk hG hno hFU hFV i hY hsY)

end GraphMinor.GM06
