module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5CoverSides
import Mathlib.Topology.Compactness.Compact

/-!
# A compact lifted curve meets finitely many lifted vertices

For the attachment detour in VI (5.5), page 130, a normal curve
may initially visit a vertex infinitely many times. Its compact
angular lift still contains only finitely many distinct lifted
vertices. The projection is a local homeomorphism, so its preimage
of the finite vertex set is discrete. Intersecting with the compact
curve image gives a finite set, available for arc simplification.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Only finitely many distinct lifted vertices lie on a compact
angular-cover curve, regardless of its number of vertex times. -/
theorem finite_lifted_vertices_on_curve
    (G : Drawing ClosedCylinder) (q : C(unitInterval, CylinderCover)) :
    (range q ∩ cylinderCoverProjection ⁻¹' G.V).Finite := by
  let K := range q ∩ cylinderCoverProjection ⁻¹' G.V
  have hc : IsCompact K := (isCompact_range q.continuous).inter_right
    (G.finite_V.isClosed.preimage continuous_cylinderCoverProjection)
  have him : (cylinderCoverProjection '' K).Finite := G.finite_V.subset (by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2)
  have hlocal : IsLocalHomeomorphOn cylinderCoverProjection K :=
    fun x _ => isLocalHomeomorph_cylinderCoverProjection x
  exact hc.finite (hlocal.isDiscrete_of_image him.isDiscrete)

end GraphMinor.GM06
