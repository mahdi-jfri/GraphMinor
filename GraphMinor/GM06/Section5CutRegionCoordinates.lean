module

public import GraphMinor.GM06.Section5CutSheetComponent
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Section5CoverSides
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Lifting the selected region into the cut disc

The angular coordinates embed the closed strip disc into the cover.
The selected region and its closure lie in that embedded disc. Pulling
back therefore preserves connectedness and every boundary incidence.
These facts provide the region on which the one-path argument of
VI Section 5 follows the boundary of the drawing.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A strip disc embeds as a closed subset of the angular cover. -/
theorem isClosedEmbedding_single_strip_coverMap
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    IsClosedEmbedding (fun p : D => planeToCylinderCover p.1) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  apply (continuous_planeToCylinderCover.comp continuous_subtype_val).isClosedEmbedding
  intro p q hpq
  have h := congrArg cylinderCoverCoordinates hpq
  change (max 1 (min 2 p.1.1), p.1.2) = (max 1 (min 2 q.1.1), q.1.2) at h
  rw [min_eq_right (hstrip p.2).2, max_eq_right (hstrip p.2).1,
    min_eq_right (hstrip q.2).2, max_eq_right (hstrip q.2).1] at h
  exact Subtype.ext h

/-- The selected lifted region is open, including at its cuff points. -/
theorem isOpen_cylinderCoverRegion (k : ℕ) (G : Drawing ClosedCylinder) (i : Fin k) :
    IsOpen (cylinderCoverRegion k G i) := by
  let : LocallyPathConnectedSpace (Icc (1 : ℝ) 2) := (convex_Icc (1 : ℝ) 2).locallyPathConnectedSpace
  let : LocallyConnectedSpace CylinderCover := inferInstance
  unfold cylinderCoverRegion
  exact ((isOpen_univ.sdiff G.isClosed_U).preimage continuous_cylinderCoverProjection).connectedComponentIn

/-- Pulling the chosen cover region into the closed cut disc gives an
open preconnected set, and its closure has exactly the original incidences. -/
theorem preimage_coverRegion_on_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    let a : D → CylinderCover := fun p => planeToCylinderCover p.1
    IsOpen (a ⁻¹' cylinderCoverRegion 1 G 0) ∧
      IsPreconnected (a ⁻¹' cylinderCoverRegion 1 G 0) ∧
      a '' closure (a ⁻¹' cylinderCoverRegion 1 G 0) = closure (cylinderCoverRegion 1 G 0) := by
  dsimp only
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  have he := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hsub : cylinderCoverRegion 1 G 0 ⊆ range a := by
    intro p hp
    obtain ⟨q, hq, heq⟩ := closure_cylinderCoverRegion_subset_single_strip L hG hθ hD hBd hstrip
      (subset_closure hp)
    exact ⟨⟨q, hq⟩, heq⟩
  have him : a '' (a ⁻¹' cylinderCoverRegion 1 G 0) = cylinderCoverRegion 1 G 0 :=
    image_preimage_eq_of_subset hsub
  refine ⟨(isOpen_cylinderCoverRegion 1 G 0).preimage he.continuous,
    isPreconnected_connectedComponentIn.preimage_of_isClosedMap he.injective he.isClosedMap hsub, ?_⟩
  rw [← he.closure_image_eq, him]

end GraphMinor.GM06
