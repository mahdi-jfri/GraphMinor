module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section3Dual
import GraphMinor.GM06.Section5ConnectedComponentBarrier
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section4PathTools

/-!
# The actual augmented component containing both cuffs

For Reduction 2 of VI (5.5), page 130, adjoining the cuffs puts
both of them in one graph component. Any one linkage path connects
the two cuff circles. Their connected union is contained in the
component of its initial vertex, also after embedding in the sphere.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The sphere image of a drawing containing the linkage and the
cuffs has a graph component containing both cuff images. -/
theorem exists_sphere_component_containing_cuffs
    {k : ℕ} {G F : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (hGF : G.IsSubdrawing F)
    (hbdF : bd ClosedCylinder ⊆ F.U) :
    ∃ C : Graph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)),
      IsGraphComponent C (cylinderSphereDrawing F).toGraph ∧
      cylinderToSphere '' bd ClosedCylinder ⊆ compPointSet C := by
  let i : Fin k := ⟨0, hk⟩
  let P := L.curve i
  have hP0 : P 0 ∈ cylinderCuff1 := by rw [(L.curve_parametrizes i).2.2.1]; rfl
  have hP1 : P 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  have hCU1 := isConnected_of_isOArc isOArc_cylinderCuff1
  have hCU2 := isConnected_of_isOArc isOArc_cylinderCuff2
  have hCP := isConnected_range P.continuous
  let B := (cylinderCuff1 ∪ range P) ∪ cylinderCuff2
  have hBC : IsConnected B :=
    (hCU1.union ⟨P 0, hP0, mem_range_self 0⟩ hCP).union
      ⟨P 1, Or.inr (mem_range_self 1), hP1⟩ hCU2
  have hBbd : bd ClosedCylinder ⊆ B := by
    rw [bd_closedCylinder]
    exact union_subset (fun _ h => Or.inl (Or.inl h)) (fun _ h => Or.inr h)
  have hPsub : range P ⊆ F.U := by
    rw [show range P = (L.pathDrawing i).U from (L.curve_parametrizes i).2.1]
    exact (L.isSubdrawing i).2.trans hGF.U_subset
  have hBF : B ⊆ F.U := by
    rintro x ((hx | hx) | hx)
    · exact hbdF (by rw [bd_closedCylinder]; exact Or.inl hx)
    · exact hPsub hx
    · exact hbdF (by rw [bd_closedCylinder]; exact Or.inr hx)
  have haG : P 0 ∈ G.V := by
    rw [(L.curve_parametrizes i).2.2.1]
    exact (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
  have haF : cylinderToSphere (P 0) ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ (hGF.1 haG)
  let C := compOf (cylinderSphereDrawing F).toGraph (cylinderToSphere (P 0))
  have hC : IsGraphComponent C (cylinderSphereDrawing F).toGraph := isGraphComponent_compOf haF
  have hBX : IsPreconnected (cylinderToSphere '' B) :=
    hBC.isPreconnected.image _ continuous_cylinderToSphere.continuousOn
  have hBsub : cylinderToSphere '' B ⊆ (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    exact image_mono hBF
  have hmeet : (cylinderToSphere '' B ∩ compPointSet C).Nonempty := by
    refine ⟨cylinderToSphere (P 0), mem_image_of_mem _ (Or.inl (Or.inr (mem_range_self 0))), ?_⟩
    exact Or.inl (self_mem_reachSet haF)
  exact ⟨C, hC, (image_mono hBbd).trans
    (subset_compPointSet_of_isPreconnected _ hC hBX hBsub hmeet)⟩

end GraphMinor.GM06
