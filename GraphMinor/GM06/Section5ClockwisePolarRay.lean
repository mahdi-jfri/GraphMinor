module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5ClockwiseGerm
import GraphMinor.GM06.Section5PolarEdgeAccess

/-!
# Clockwise certificates from local polar directions

The rotation test for VI (5.7), page 133, uses a small polar chart
of the capped drawing. A radial edge segment pulls back to the
cylinder and then through an inverse angular-cover chart. If its
endpoint lies in the clockwise strip, the lifted access criterion
puts the whole edge on that side. This applies to either directed
end of a loop.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A local edge access in an inverse chart gives the corrected
clockwise-side certificate. -/
theorem isClockwiseInitialEdge_of_chart_access
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    (f : Curve ClosedCylinder) (hf0 : f 0 = cylinderM1Point k i)
    (hfT : ∀ t, f t ∈ η.target) (hfe : ∀ t, 0 < t → f t ∈ e)
    (hoff : Disjoint e (⋃ j : Fin k, (L.pathDrawing j).U))
    (hside : η.symm (f 1) ∈ cylinderCoverStrip L (i.val : ℤ)) :
    IsClockwiseInitialEdge L i e := by
  let g : Curve CylinderCover := ⟨fun t => η.symm (f t),
    η.symm.continuousOn.comp_continuous f.continuous hfT⟩
  have hg0 : g 0 = cylinderInitialLift k i := by
    change η.symm (f 0) = _
    rw [hf0]
    have hs : η (cylinderInitialLift k i) = cylinderM1Point k i := by
      rw [hη]
      rfl
    rw [← hs, η.left_inv hsη]
  apply isClockwiseInitialEdge_of_lifted_access L i he g hg0 _ hoff hside
  intro t ht
  change cylinderCoverProjection (η.symm (f t)) ∈ e
  rw [← hη, η.right_inv (hfT t)]
  exact hfe t ht

/-- A radial edge direction in a sufficiently small capped polar chart
is clockwise when its endpoint in the chosen cover sheet is clockwise. -/
theorem isClockwiseInitialEdge_of_polar_edge_ray
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    (hGF : G.IsSubdrawing F) {e : Set ClosedCylinder} (he : e ∈ G.E)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    {x : ClosedUnitDisc} (hx : x ≠ polarCentre) {y : ClosedCylinder}
    (hxy : Φ x = cylinderToSphere y) (hy : y ∈ e)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    (hsmall : ∀ t : I, Φ (discScale t x) ∈ cylinderToSphere '' η.target)
    (hoff : Disjoint e (⋃ j : Fin k, (L.pathDrawing j).U))
    (hside : η.symm y ∈ cylinderCoverStrip L (i.val : ℤ)) :
    IsClockwiseInitialEdge L i e := by
  have heF : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ (hGF.2 he)
  obtain ⟨f, hf0, hf1, hfe, hf⟩ := exists_polar_edge_access_of_embedding
    isClosedEmbedding_cylinderToSphere.isEmbedding hp heF hx hxy hy
  have hfT (t : I) : f t ∈ η.target := by
    obtain ⟨z, hz, hze⟩ := hsmall t
    have hzf : z = f t := injective_cylinderToSphere (hze.trans (hf t).symm)
    exact hzf ▸ hz
  apply isClockwiseInitialEdge_of_chart_access L i he η hη hsη f hf0 hfT hfe hoff
  rwa [hf1]

end GraphMinor.GM06
