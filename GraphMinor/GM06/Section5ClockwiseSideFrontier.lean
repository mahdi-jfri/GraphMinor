module

public import GraphMinor.GM06.Section5CapDrawing
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5ClosedClockwiseSide
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5CoverSides
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Boundary of a closed local clockwise side

For the rim interpretation of VI (5.7), page 133, a closed local
strip side can have boundary only on the linkage or on a cuff.
Away from them, membership in the cover component is open. The
inverse angular chart and the off-cuff sphere chart carry this
open neighbourhood into the closed local side. Such a point is
interior, so it cannot lie on that side's frontier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The local frontier of a closed clockwise-side representative
contains only linkage or cuff points. -/
theorem frontier_closed_clockwise_side_subset_barrier
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    {B O : Set (OnePoint EuclideanPlane)} (hBc : IsClosed B) (hOo : IsOpen O)
    (hBr : B ⊆ range cylinderToSphere)
    (hmem : ∀ y : ClosedCylinder, cylinderToSphere y ∈ O → y ∈ η.target ∧
      (y ∉ ⋃ j, (L.pathDrawing j).U →
        (cylinderToSphere y ∈ B ↔ η.symm y ∈ cylinderCoverStrip L (i.val : ℤ)))) :
    frontier B ∩ O ⊆ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
  have hLc : IsClosed (⋃ j : Fin k, (L.pathDrawing j).U) :=
    isClosed_iUnion_of_finite fun j => (L.pathDrawing j).isClosed_U
  let : LocallyPathConnectedSpace (Icc (1 : ℝ) 2) := (convex_Icc (1 : ℝ) 2).locallyPathConnectedSpace
  let : LocallyConnectedSpace CylinderCover := inferInstance
  have hCWopen : IsOpen (cylinderCoverStrip L (i.val : ℤ)) := by
    change IsOpen (connectedComponentIn
      (cylinderCoverProjection ⁻¹' (univ \ ⋃ j : Fin k, (L.pathDrawing j).U)) _)
    have hLo : IsOpen (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) := by
      simpa only [compl_eq_univ_sdiff] using hLc.isOpen_compl
    exact (hLo.preimage continuous_cylinderCoverProjection).connectedComponentIn
  let V := (η.target ∩ η.symm ⁻¹' cylinderCoverStrip L (i.val : ℤ)) ∩
    cylinderToSphere ⁻¹' O ∩ (⋃ j, (L.pathDrawing j).U)ᶜ
  have hVo : IsOpen V :=
    ((η.symm.isOpen_inter_preimage hCWopen).inter
      (hOo.preimage continuous_cylinderToSphere)).inter hLc.isOpen_compl
  rintro z ⟨hzfr, hzO⟩
  have hzB : z ∈ B := hBc.closure_eq ▸ frontier_subset_closure hzfr
  obtain ⟨y, rfl⟩ := hBr hzB
  by_cases hyL : y ∈ ⋃ j, (L.pathDrawing j).U
  · exact ⟨y, Or.inl hyL, rfl⟩
  by_cases hybd : y ∈ bd ClosedCylinder
  · exact ⟨y, Or.inr hybd, rfl⟩
  have hyV : y ∈ V := ⟨⟨⟨(hmem y hzO).1, ((hmem y hzO).2 hyL).mp hzB⟩, hzO⟩, hyL⟩
  obtain ⟨ζ, hyζ, hζ⟩ := isLocalHomeomorphOn_cylinderToSphere_off_boundary y hybd
  have hζapp (t : ClosedCylinder) : ζ t = cylinderToSphere t := congrFun hζ.symm t
  let W := ζ '' (ζ.source ∩ V)
  have hWo : IsOpen W := ζ.isOpen_image_of_subset_source (ζ.open_source.inter hVo) inter_subset_left
  have hyW : cylinderToSphere y ∈ W := ⟨y, ⟨hyζ, hyV⟩, hζapp y⟩
  have hWB : W ⊆ B := by
    rintro _ ⟨t, ⟨_, htV⟩, rfl⟩
    rw [hζapp]
    exact ((hmem t htV.1.2).2 htV.2).mpr htV.1.1.2
  have hyint : cylinderToSphere y ∈ interior B :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hWo.mem_nhds hyW) hWB)
  exact False.elim (hzfr.2 hyint)

/-- The closed local side supplied by the lifted disc has no local
frontier away from linkage paths and cylinder cuffs. -/
theorem exists_closed_local_clockwise_side_with_frontier
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source) :
    ∃ B O : Set (OnePoint EuclideanPlane), IsClosed B ∧ IsOpen O ∧
      cylinderToSphere (cylinderM1Point k i) ∈ O ∧ B ⊆ range cylinderToSphere ∧
      (∀ y : ClosedCylinder, cylinderToSphere y ∈ O → y ∈ η.target ∧
        (y ∉ ⋃ j, (L.pathDrawing j).U →
          (cylinderToSphere y ∈ B ↔ η.symm y ∈ cylinderCoverStrip L (i.val : ℤ)))) ∧
      frontier B ∩ O ⊆ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
  obtain ⟨B, O, hBc, hOo, hsO, hBr, hmem⟩ :=
    exists_closed_local_clockwise_side L hG hθ i η hη hsη
  exact ⟨B, O, hBc, hOo, hsO, hBr, hmem,
    frontier_closed_clockwise_side_subset_barrier L i η hBc hOo hBr hmem⟩

end GraphMinor.GM06
