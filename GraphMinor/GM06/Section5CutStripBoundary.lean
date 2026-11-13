module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutStripGraph
import GraphMinor.GM06.Section5AdjoinDiscBoundary
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5StripImage

/-!
# The augmented finite graph on the one-path cut disc

The graph off the seam is proper on the cut disc. Its vertices
include the two initial seam points, so the boundary circle can be
adjoined with exactly its existing boundary vertices. The resulting
finite graph has the full preimage of the original vertex set. Its
point set is the preimage of the original graph together with the
disc boundary, as needed for the region-boundary argument in VI (5.1).
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The actual finite graph on the cut disc with its boundary adjoined.
Every non-boundary edge is the full lift of an original edge off the
sole linkage path. The vertex set is exactly the lifted original one. -/
theorem exists_augmented_drawing_on_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    ∃ F : Drawing D,
      F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D ∧
      F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V ∧
      ∀ ec ∈ F.E, ec ⊆ bd D ∨
        ∃ e ∈ G.E \ (L.pathDrawing 0).E,
          ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
  obtain ⟨H, HC, _, _, _, hU, hHCproper, hCU, hCV, hEdges⟩ :=
    exists_off_seam_drawing_on_single_strip L hG hθ hD hBd hstrip
  let p := liftedLinkageCurve hG.1 L 1 0
  have hpB : p ∈ discBd D := by
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self 0)))
  have hpD : p ∈ D := discBd_subset D hpB
  let pD : D := ⟨p, hpD⟩
  have hpBd : pD ∈ bd D := by
    obtain ⟨q, hq, heq⟩ := hpB
    exact (Subtype.ext heq : q = pD) ▸ hq
  have hpProj : radialCylinderProjection pD.1 = cylinderM1Point 1 0 := by
    rw [radialCylinderProjection_liftedLinkageCurve]
    have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
    rw [hi]
    exact (L.curve_parametrizes 0).2.2.1
  have hpV : pD ∈ HC.V := by
    rw [hCV]
    change radialCylinderProjection pD.1 ∈ G.V
    rw [hpProj]
    exact (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).1
  have hDisc : IsClosedDiscSpace D := hD
  obtain ⟨F, _, hFU, hFV, hFE⟩ := exists_drawing_adjoining_disc_boundary hDisc HC hHCproper
    ⟨pD, hpV, hpBd⟩
  have hPbd : (fun p : D => radialCylinderProjection p.1) ⁻¹' (L.pathDrawing 0).U ⊆ bd D := by
    intro q hq
    exact preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip ▸ Or.inr hq
  refine ⟨F, ?_, hFV.trans hCV, ?_⟩
  · rw [hFU, hCU, hU, preimage_union, union_assoc, union_eq_right.mpr hPbd]
  · intro ec hec
    rcases hFE ec hec with heHC | heBd
    · exact Or.inr (hEdges ec heHC)
    · exact Or.inl heBd

end GraphMinor.GM06
