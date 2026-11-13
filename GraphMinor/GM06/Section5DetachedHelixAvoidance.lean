module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section3Dual
import GraphMinor.GM06.Section5CylinderComponentEnclosures
import GraphMinor.GM06.Section5FiniteDiscAvoidance
import GraphMinor.GM11.Walks

/-!
# Removing helix visits to components detached from the cuffs

For Reduction 2 of VI (5.5), page 130, first put cuff arcs into
the old drawing. Its component containing the cuffs is the retained
barrier. The constructed cylinder discs cover all other components.
Their boundaries miss the whole old drawing, so finite disc detours
remove those contacts without increasing the retained helix potential.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A retained helix can avoid every old component detached from
a root containing the cuffs. The enclosures and detours are constructed
from the actual old drawing and its root component. -/
theorem exists_helix_avoiding_components_detached_from_cuffs
    {k : ℕ} {G H : Drawing ClosedCylinder} (hHG : H.IsSubdrawing G)
    {C : Graph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))}
    (hC : IsGraphComponent C (cylinderSphereDrawing G).toGraph)
    (hCbd : cylinderToSphere '' bd ClosedCylinder ⊆ compPointSet C)
    (f : Curve ClosedCylinder) (hf : IsHelix k H f) :
    ∃ g : Curve ClosedCylinder, IsHelix k H g ∧ curvePhi k H g ≤ curvePhi k H f ∧
      range g ∩ G.U ⊆ cylinderToSphere ⁻¹' compPointSet C := by
  let A := G.U \ cylinderToSphere ⁻¹' compPointSet C
  obtain ⟨F, hF, hdisc, hcover⟩ := exists_cylinder_discs_enclosing_detached_components G hC hCbd
  have hbd (D) (hD : D ∈ F) : Disjoint (discBd D) (H.U ∪ A) :=
    (hdisc D hD).2.2.mono_right (union_subset hHG.U_subset sdiff_subset)
  obtain ⟨g, hg, hgA, hφ⟩ := exists_helix_avoiding_finitely_enclosed_set
    hF A (fun D hD => (hdisc D hD).1) hbd
    (fun D hD => (hdisc D hD).2.1) hcover f hf
  refine ⟨g, hg, hφ, ?_⟩
  rintro x ⟨hxg, hxG⟩
  by_contra hroot
  exact disjoint_left.mp hgA hxg ⟨hxG, hroot⟩

end GraphMinor.GM06
