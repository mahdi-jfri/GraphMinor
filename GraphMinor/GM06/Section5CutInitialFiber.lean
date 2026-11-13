module

public import GraphMinor.GM06.Section5CutInitialGap
public import GraphMinor.GM06.Section5CutSeam
import GraphMinor.GM06.Section5StripImage

/-!
# The initial vertex has exactly its two cut copies

The inverse image of the sole linkage path consists of the two
seams. An initial vertex on either seam has parameter zero, since
the original path is injective. The explicit lifted initial angles
identify these two points with the ends of the lifted cuff gap.
This fixes the side of initial-edge incidence in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- Every cut-disc point above the initial vertex is one of the two
ends of the lifted initial cuff gap. -/
theorem eq_gap_end_of_projecting_to_initial
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    {p : D} (hp : radialCylinderProjection p.1 = cylinderM1Point 1 0) : p = g 0 ∨ p = g 1 := by
  have hproj (n : ℤ) (t : unitInterval) :
      radialCylinderProjection (liftedLinkageCurve hG.1 L n t) = L.curve 0 t := by
    rw [radialCylinderProjection_liftedLinkageCurve]
    have hi : modIdx 1 hG.1 n = 0 := Subsingleton.elim _ _
    rw [hi]
  have htime (n : ℤ) (t : unitInterval)
      (ht : radialCylinderProjection (liftedLinkageCurve hG.1 L n t) = cylinderM1Point 1 0) : t = 0 := by
    apply (L.curve_parametrizes 0).1
    rw [← hproj n t, (L.curve_parametrizes 0).2.2.1]
    exact ht
  have hzero (n : ℤ) : liftedLinkageCurve hG.1 L n 0 = (1, 2 * (n : ℝ) * π) := by
    apply Prod.ext
    · exact (liftedLinkageCurve_props_raw hG.1 L n).2.1
    · simpa only [Nat.cast_one, div_one] using (liftedLinkageCurve_props_raw hG.1 L n).2.2.2.1
  have hpSeam : p.1 ∈ range (liftedLinkageCurve hG.1 L 1) ∪
      range (liftedLinkageCurve hG.1 L (1 + 1)) := by
    rw [← preimage_path_inter_single_strip_eq_seams L hG hθ 1 hD hBd hstrip]
    refine ⟨p.2, ?_⟩
    change radialCylinderProjection p.1 ∈ (L.pathDrawing 0).U
    rw [hp]
    exact (L.curve_parametrizes 0).2.1 ▸ ⟨0, (L.curve_parametrizes 0).2.2.1⟩
  rcases hpSeam with ⟨t, ht⟩ | ⟨t, ht⟩
  · have ht0 := htime 1 t ((congrArg radialCylinderProjection ht).trans hp)
    left
    apply Subtype.ext
    rw [← ht, ht0, hzero, hgcoord]
    norm_num
  · have ht0 := htime (1 + 1) t ((congrArg radialCylinderProjection ht).trans hp)
    right
    apply Subtype.ext
    rw [← ht, ht0, hzero, hgcoord]
    norm_num

end GraphMinor.GM06
