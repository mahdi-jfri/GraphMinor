module

public import GraphMinor.GM06.Section5CapDrawing
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5PrecedingStripClosure
import GraphMinor.GM06.Section5CoverInteriorDensity
import GraphMinor.GM06.Section5CoverSides
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Clockwise side points off the local barrier

For VI (5.7), page 133, the selected cover strip approaches the
initial lift. Intersect it with an arbitrary sphere neighbourhood
and the chosen inverse chart. This is a nonempty open cover set,
so it contains a point strictly between the cuff radii. Such a
point misses both the linkage and the cuffs. Its local closed-side
representative therefore has a point away from the whole barrier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Cover strips are open in the angular cover, including on its cuffs. -/
theorem isOpen_cylinderCoverStrip
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (m : ℤ) :
    IsOpen (cylinderCoverStrip L m) := by
  let : LocallyPathConnectedSpace (Icc (1 : ℝ) 2) := (convex_Icc (1 : ℝ) 2).locallyPathConnectedSpace
  let : LocallyConnectedSpace CylinderCover := inferInstance
  have hLc : IsClosed (⋃ j : Fin k, (L.pathDrawing j).U) :=
    isClosed_iUnion_of_finite fun j => (L.pathDrawing j).isClosed_U
  have hLo : IsOpen (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) := by
    simpa only [compl_eq_univ_sdiff] using hLc.isOpen_compl
  exact (hLo.preimage continuous_cylinderCoverProjection).connectedComponentIn

/-- Any sphere neighbourhood of the initial point contains a point
of the chosen cover strip strictly between the cuff radii. -/
theorem exists_clockwise_point_in_sphere_neighbourhood
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hsη : cylinderInitialLift k i ∈ η.source)
    {W : Set (OnePoint EuclideanPlane)} (hWo : IsOpen W)
    (hsW : cylinderToSphere (cylinderM1Point k i) ∈ W) :
    ∃ p : CylinderCover, p ∈ η.source ∧ p ∈ cylinderCoverStrip L (i.val : ℤ) ∧
      1 < p.1.1 ∧ p.1.1 < 2 ∧ cylinderToSphere (cylinderCoverProjection p) ∈ W := by
  let N := η.source ∩ (fun p => cylinderToSphere (cylinderCoverProjection p)) ⁻¹' W
  have hNo : IsOpen N := η.open_source.inter
    (hWo.preimage (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
  have hsN : cylinderInitialLift k i ∈ N := ⟨hsη, hsW⟩
  obtain ⟨p, hpN, hpCW⟩ := mem_closure_iff.mp
    (cylinderInitialLift_mem_closure_preceding_cover_strip L hG hθ i) N hNo hsN
  obtain ⟨q, hq, hq1, hq2⟩ := exists_strict_radius_point_in_open_cover
    (hNo.inter (isOpen_cylinderCoverStrip L (i.val : ℤ))) ⟨p, hpN, hpCW⟩
  exact ⟨q, hq.1.1, hq.2, hq1, hq2, hq.1.2⟩

/-- A closed-side representative with the local cover membership
property has a point off the barrier in every initial neighbourhood. -/
theorem exists_local_clockwise_side_point_off_barrier
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    {B O : Set (OnePoint EuclideanPlane)} (hOo : IsOpen O)
    (hsO : cylinderToSphere (cylinderM1Point k i) ∈ O)
    (hmem : ∀ y : ClosedCylinder, cylinderToSphere y ∈ O → y ∈ η.target ∧
      (y ∉ ⋃ j, (L.pathDrawing j).U →
        (cylinderToSphere y ∈ B ↔ η.symm y ∈ cylinderCoverStrip L (i.val : ℤ))))
    {W : Set (OnePoint EuclideanPlane)} (hWo : IsOpen W)
    (hsW : cylinderToSphere (cylinderM1Point k i) ∈ W) :
    ∃ z ∈ W, z ∈ B ∧ z ∉ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
  obtain ⟨p, hpη, hpCW, hp1, hp2, hpWO⟩ := exists_clockwise_point_in_sphere_neighbourhood
    L hG hθ i η hsη (hWo.inter hOo) ⟨hsW, hsO⟩
  have hpOff : cylinderCoverProjection p ∉ ⋃ j, (L.pathDrawing j).U :=
    (connectedComponentIn_subset _ _ hpCW).2
  have hback : η.symm (cylinderCoverProjection p) = p := by rw [← hη, η.left_inv hpη]
  refine ⟨cylinderToSphere (cylinderCoverProjection p), hpWO.1, ?_, ?_⟩
  · apply ((hmem _ hpWO.2).2 hpOff).mpr
    rwa [hback]
  · rintro ⟨y, hy, hyκ⟩
    have hyP : y = cylinderCoverProjection p := injective_cylinderToSphere hyκ
    rw [hyP] at hy
    rcases hy with hyL | hyBd
    · exact hpOff hyL
    · rw [bd_closedCylinder] at hyBd
      rcases hyBd with hy1 | hy2
      · exact hp1.ne' hy1
      · exact hp2.ne hy2

end GraphMinor.GM06
