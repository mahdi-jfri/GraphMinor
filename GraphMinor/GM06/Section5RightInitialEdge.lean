module

public import GraphMinor.GM06.Section5CoverTranslation

/-!
# Edges approaching the right initial copy

An edge lifted inside the following one-path strip and incident with
its right initial copy is clockwise at the original initial vertex.
Shift the connected lifted edge back one full turn. The strip index
changes from one to zero, the right initial copy becomes the canonical
initial lift, and projection is unchanged. This is the side-sensitive
Reduction 1 test needed in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A connected lifted edge approaching the right initial copy from
inside the following strip satisfies corrected Reduction 1's side test. -/
theorem isClockwiseInitialEdge_of_incident_right_initialLift
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    {A : Set CylinderCover} {e : Set ClosedCylinder}
    (hA : IsConnected A) (himage : cylinderCoverProjection '' A = e)
    (hinc : (⟨1, by norm_num⟩, 4 * π) ∈ closure A)
    (hstrip : A ⊆ cylinderCoverStrip L 1) : IsClockwiseInitialEdge L 0 e := by
  let E := cylinderCoverTranslation (-1)
  have hpoint : E (⟨1, by norm_num⟩, 4 * π) = cylinderInitialLift 1 0 := by
    apply Prod.ext
    · rfl
    · change 4 * π + ((-1 : ℤ) : ℝ) * (2 * π) = _
      norm_num [cylinderInitialLift]
      ring
  have hshift : E '' cylinderCoverStrip L 1 = cylinderCoverStrip L 0 := by
    simpa only [Int.reduceAdd] using image_cylinderCoverStrip_translation L 1 (-1)
  refine ⟨E '' A, hA.image E E.continuous.continuousOn, ?_, ?_, ?_⟩
  · rw [image_image]
    have hcomp : cylinderCoverProjection ∘ E = cylinderCoverProjection := by
      funext p
      exact cylinderCoverProjection_translation (-1) p
    change (cylinderCoverProjection ∘ E) '' A = e
    rw [hcomp, himage]
  · rw [← hpoint]
    exact mem_closure_image E.continuous.continuousAt hinc
  · exact hshift ▸ image_mono hstrip

end GraphMinor.GM06
