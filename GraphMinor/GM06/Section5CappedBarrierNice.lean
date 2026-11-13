module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.NiceStatements
import GraphMinor.GM06.Section5CappedInitialPath
import GraphMinor.GM06.Section5CappedCuffSubdrawings
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.Walks

/-!
# The capped linkage-and-cuff barrier is a union of drawing atoms

For VI (5.7), page 133, each linkage path is a subdrawing of the
augmented graph. The two cuffs are circuit subdrawings in the
capped sphere. Their point sets are closed nice sets. Taking their
union shows that every drawing atom meeting the full barrier is
contained in it, as needed to keep a polar ray off that barrier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- The full capped linkage-and-cuff barrier is nice in the capped
augmented drawing, for every positive linkage size. -/
theorem isGammaNice_capped_linkage_and_cuffs
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U) :
    IsGammaNice (cylinderSphereDrawing F)
      (cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder)) := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) := IsClosedSurface.locallyConnectedSpace hS.1
  have hnice {P : Drawing (OnePoint EuclideanPlane)} (hP : P.IsSubdrawing (cylinderSphereDrawing F)) :
      IsGammaNice (cylinderSphereDrawing F) P.U :=
    isGammaNice_of_frontier hP subset_rfl
      (frontier_subset_closure.trans (by rw [P.isClosed_U.closure_eq]))
  have hpaths (j : Fin k) : IsGammaNice (cylinderSphereDrawing F)
      (cylinderSphereDrawing (L.pathDrawing j)).U :=
    hnice (cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing j).1.trans hGF))
  have hpathUnion : IsGammaNice (cylinderSphereDrawing F)
      (⋃ j : Fin k, (cylinderSphereDrawing (L.pathDrawing j)).U) := by
    apply isGammaNice_of_sat
    rintro a ha ⟨x, hxa, hx⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact (nice_atom (hpaths j) ha ⟨x, hxa, hxj⟩).trans (fun y hy => mem_iUnion.mpr ⟨j, hy⟩)
  obtain ⟨C₁, C₂, hC₁F, hC₂F, hC₁U, hC₂U, _, _⟩ := exists_capped_cuff_subdrawings F hbdF
  have htotal := hpathUnion.union ((hnice hC₁F).union (hnice hC₂F))
  have heq : cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) =
      (⋃ j : Fin k, (cylinderSphereDrawing (L.pathDrawing j)).U) ∪ (C₁.U ∪ C₂.U) := by
    rw [image_union, bd_closedCylinder, image_union, hC₁U, hC₂U]
    simp only [image_iUnion, cylinderSphereDrawing_U]
  exact heq.symm ▸ htotal

end GraphMinor.GM06
