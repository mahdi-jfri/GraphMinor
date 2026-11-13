module

public import GraphMinor.GM06.Section5CoverLiftUnique
public import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5StripImage

/-!
# The indexed linkage lift agrees with the aligned cover lift

The plane curve used to bound a cut strip already lifts the linkage
curve, and its initial angle is the indexed prescribed angle.
Uniqueness of the aligned cover lift therefore identifies the two
constructions point by point. This relates the seam contact in the
cut-disc argument to the lift in corrected Reduction 4 of VI Section 5.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- The indexed linkage lift in plane coordinates is the chosen
cover lift aligned at its indexed initial angle. -/
theorem cylinderCurveLiftAt_eq_indexed_linkage_lift
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k) (L : CylinderLinkage k G)
    (m : ℤ) (t : unitInterval) :
    cylinderCurveLiftAt (L.curve (modIdx k hk m)) (2 * (m : ℝ) * π / k) t =
      planeToCylinderCover (liftedLinkageCurve hk L m t) := by
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun t => planeToCylinderCover (liftedLinkageCurve hk L m t),
      continuous_planeToCylinderCover.comp (liftedLinkageCurve hk L m).continuous⟩
  have hproj (u : unitInterval) : cylinderCoverProjection (q u) = L.curve (modIdx k hk m) u := by
    change radialCylinderProjection (liftedLinkageCurve hk L m u) = _
    exact radialCylinderProjection_liftedLinkageCurve hk L m u
  have h0 : (q 0).2 = 2 * (m : ℝ) * π / k :=
    (liftedLinkageCurve_props_raw hk L m).2.2.2.1
  have h := cylinderCurveLiftAt_eq_of_cover_lift (L.curve (modIdx k hk m)) q hproj
  rw [h0] at h
  exact congrArg (fun c : C(unitInterval, CylinderCover) => c t) h

end GraphMinor.GM06
